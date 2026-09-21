import Lax391470Proofs.TokModel

/-!
Tokenizing a bit stream against a format, as a one-pass scan.

Phase `0` stands at a token boundary or inside the unary length of a number; phase `1`
reads the digits of a number; phase `2` has rejected. The scan is the model a machine
program is proved against.
-/

namespace Lax391470Proofs.TokScan

open Lax391470.BinaryEncoding Lax434930.PolynomialTime Lax391470Proofs.Encoding
open Lax391470Proofs.TokModel

set_option genInjectivity false in
set_option genSizeOfSpec false in
structure St where
  ph : ℕ
  L : ℕ
  val : ℕ
  pw : ℕ
  dg : List Bool
  toks : List Tok

def init : St := ⟨0, 0, 0, 1, [], []⟩

def dead (s : St) : St := { s with ph := 2 }

variable (E : Format)

def step (s : St) (b : Bool) : St :=
  match s.ph with
  | 0 =>
    match E s.toks with
    | .done => dead s
    | .bit => if s.L = 0 then { s with toks := s.toks ++ [.bit b] } else dead s
    | .num =>
      if b then { s with L := s.L + 1 }
      else if s.L = 0 then { s with toks := s.toks ++ [.num 0] }
      else { s with ph := 1, val := 0, pw := 1, dg := [] }
  | 1 =>
    if s.dg.length + 1 = s.L then
      (if b then ⟨0, 0, 0, 1, [], s.toks ++ [.num (s.val + s.pw)]⟩ else dead s)
    else { s with val := s.val + (if b then s.pw else 0), pw := 2 * s.pw, dg := s.dg ++ [b] }
  | _ => dead s

def run (s : St) (w : Word) : St := w.foldl (step E) s

@[simp] lemma run_nil (s : St) : run E s [] = s := rfl
@[simp] lemma run_cons (s : St) (b : Bool) (w : Word) :
    run E s (b :: w) = run E (step E s b) w := rfl
lemma run_append (s : St) (u v : Word) : run E s (u ++ v) = run E (run E s u) v := by
  simp [run, List.foldl_append]

/-- The scan has read a whole stream that the format accepts. -/
def Accepts (s : St) : Prop := s.ph = 0 ∧ s.L = 0 ∧ E s.toks = .done

/-- The tokens so far follow the format. -/
def Follows (ts : List Tok) : Prop :=
  ∀ k < ts.length, (ts.getD k (.bit false)).kind = E (ts.take k)

lemma follows_snoc {ts : List Tok} {t : Tok} (h : Follows E ts) (ht : t.kind = E ts) :
    Follows E (ts ++ [t]) := by
  intro k hk
  simp only [List.length_append, List.length_singleton] at hk
  rcases Nat.lt_or_ge k ts.length with h1 | h1
  · rw [List.getD_append _ _ _ _ h1, List.take_append_of_le_length (by omega)]
    exact h k h1
  · have : k = ts.length := by omega
    subst this
    simp [ht]

/-- The bits consumed so far, read back off the state. -/
def consumed (s : St) : Word :=
  match s.ph with
  | 0 => code s.toks ++ List.replicate s.L true
  | 1 => code s.toks ++ (List.replicate s.L true ++ [false] ++ s.dg)
  | _ => []

inductive Good (s : St) : Prop where
  | mk
    (fol : Follows E s.toks)
    (num : s.ph = 1 ∨ 0 < s.L → E s.toks = .num)
    (dig : s.ph = 1 → s.dg.length < s.L ∧ s.val = ofBits s.dg ∧ s.pw = 2 ^ s.dg.length)
    (ph : s.ph ≤ 1)

variable {E : Format} in
theorem Good.fol
    {s : St}
    (h : Good E s) : Follows E s.toks :=
  match h with | ⟨x, _, _, _⟩ => x

variable {E : Format} in
theorem Good.num
    {s : St}
    (h : Good E s) : s.ph = 1 ∨ 0 < s.L → E s.toks = .num :=
  match h with | ⟨_, x, _, _⟩ => x

lemma encodeNat_zero : encodeNat 0 = [false] := by simp [encodeNat]

lemma step_inv {s : St} {b : Bool} (hg : Good E s) (h : (step E s b).ph ≤ 1) :
    Good E (step E s b) ∧ consumed (step E s b) = consumed s ++ [b] := by
  obtain ⟨ph, L, val, pw, dg, toks⟩ := s
  obtain ⟨hfol, hnum, hdig, hph⟩ := hg
  simp only at hfol hnum hdig hph
  have hcases : ph = 0 ∨ ph = 1 := by omega
  rcases hcases with rfl | rfl
  · -- boundary, or the unary length
    rcases hE : E toks with _ | _ | _
    · -- a number is expected
      cases b
      · by_cases hL : L = 0
        · subst hL
          refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [step, hE, consumed]
          · exact follows_snoc E hfol (by simp [Tok.kind, hE])
          · simp [code, Tok.code, encodeNat_zero]
        · refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [step, hE, hL, consumed]
          all_goals first
            | exact hfol
            | exact hE
            | exact ⟨by omega, by simp [ofBits]⟩
      · refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [step, hE, consumed]
        all_goals first
          | exact hfol
          | exact hE
          | simp [List.replicate_succ']
    · -- a raw bit is expected
      by_cases hL : L = 0
      · subst hL
        refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [step, hE, consumed]
        · exact follows_snoc E hfol (by simp [Tok.kind, hE])
        · simp [code, Tok.code]
      · simp [step, hE, hL, dead] at h
    · simp [step, hE, dead] at h
  · -- the digits
    obtain ⟨hlt, hval, hpw⟩ := hdig rfl
    have hE := hnum (Or.inl rfl)
    by_cases hlast : dg.length + 1 = L
    · cases b
      · simp [step, hlast, dead] at h
      · have hv : val + pw = ofBits (dg ++ [true]) := by
          rw [ofBits_append, hval, hpw]; simp
        have henc := encodeNat_ofBits (dg ++ [true]) (Or.inr (by simp))
        refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [step, hlast, consumed]
        · exact follows_snoc E hfol (by simp [Tok.kind, hE])
        · rw [code_append, hv]
          simp only [code, List.flatMap_cons, List.flatMap_nil, List.append_nil, Tok.code, henc,
            List.length_append, List.length_singleton, hlast]
          simp [List.append_assoc]
    · refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [step, hlast, consumed]
      all_goals first
        | exact hfol
        | exact hE
        | (refine ⟨by omega, ?_, by rw [hpw]; ring⟩
           rw [ofBits_append, hval, hpw])

lemma step_alive {s : St} {b : Bool} (h : (step E s b).ph ≤ 1) : s.ph ≤ 1 := by
  by_contra hc
  obtain ⟨ph, L, val, pw, dg, toks⟩ := s
  simp only at hc
  match ph, hc with
  | k + 2, _ => simp [step, dead] at h

lemma good_init : Good E init :=
  ⟨fun k hk => by simp [init] at hk, by simp [init], by simp [init], by simp [init]⟩

lemma run_inv (w : Word) (h : (run E init w).ph ≤ 1) :
    Good E (run E init w) ∧ consumed (run E init w) = w := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨good_init E, by simp [consumed, init, code]⟩
  | append_singleton u b ih =>
      rw [run_append] at h ⊢
      simp only [run_cons, run_nil] at h ⊢
      have ih' := ih (step_alive E h)
      obtain ⟨hg, hc⟩ := step_inv E ih'.1 h
      exact ⟨hg, by rw [hc, ih'.2]⟩

/-- **Soundness**: an accepting scan has read the code of a conforming stream. -/
theorem accept_sound {w : Word} (h : Accepts E (run E init w)) :
    code (run E init w).toks = w ∧ Conforms E (run E init w).toks := by
  obtain ⟨h0, hL, hE⟩ := h
  obtain ⟨hg, hc⟩ := run_inv E w (by omega)
  refine ⟨?_, hg.fol, hE⟩
  have h1 : consumed (run E init w) = code (run E init w).toks := by
    simp [consumed, h0, hL]
  rw [← h1, hc]

/-! ### Completeness -/

lemma bits_last {n : ℕ} (h : n ≠ 0) : n.bits.getLast? = some true := by
  induction n using Nat.binaryRec' with
  | zero => exact absurd rfl h
  | bit b n hb ih =>
    rw [Nat.bits_append_bit n b hb]
    by_cases hn : n = 0
    · subst hn; simp [hb rfl]
    · have := ih hn
      rcases hbits : n.bits with _ | ⟨c, t⟩
      · rw [hbits] at this; simp at this
      · rw [hbits] at this; simpa [List.getLast?_cons_cons] using this

/-- The boundary state after the tokens `toks`. -/
def bd (toks : List Tok) : St := ⟨0, 0, 0, 1, [], toks⟩

lemma run_ones (toks : List Tok) (hE : E toks = .num) (L k : ℕ) (w : Word) :
    run E ⟨0, L, 0, 1, [], toks⟩ (List.replicate k true ++ w) =
      run E ⟨0, L + k, 0, 1, [], toks⟩ w := by
  induction k generalizing L with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, run_cons]
    have : step E ⟨0, L, 0, 1, [], toks⟩ true = ⟨0, L + 1, 0, 1, [], toks⟩ := by
      simp [step, hE]
    rw [this, ih]; congr 2; omega

lemma run_digits (toks : List Tok) (L : ℕ) (ds : List Bool) (hlast : ds.getLast? = some true)
    (dg : List Bool) (hlen : dg.length + ds.length = L) (w : Word) :
    run E ⟨1, L, ofBits dg, 2 ^ dg.length, dg, toks⟩ (ds ++ w) =
      run E (bd (toks ++ [.num (ofBits (dg ++ ds))])) w := by
  induction ds generalizing dg with
  | nil => simp at hlast
  | cons b t ih =>
    rw [List.cons_append, run_cons]
    rcases t with _ | ⟨c, u⟩
    · have hb : b = true := by simpa using hlast
      subst hb
      have hL : dg.length + 1 = L := by simpa using hlen
      have : step E ⟨1, L, ofBits dg, 2 ^ dg.length, dg, toks⟩ true =
          bd (toks ++ [.num (ofBits dg + 2 ^ dg.length)]) := by
        simp [step, hL, bd]
      rw [this, ofBits_append]; simp
    · have hne : dg.length + 1 ≠ L := by simp at hlen; omega
      have : step E ⟨1, L, ofBits dg, 2 ^ dg.length, dg, toks⟩ b =
          ⟨1, L, ofBits (dg ++ [b]), 2 ^ (dg ++ [b]).length, dg ++ [b], toks⟩ := by
        simp [step, hne, ofBits_append, pow_succ, Nat.mul_comm]
      rw [this, ih (by simpa [List.getLast?_cons_cons] using hlast) (dg ++ [b])
        (by simp at hlen ⊢; omega)]
      simp

lemma run_tok (toks : List Tok) (t : Tok) (ht : t.kind = E toks) (w : Word) :
    run E (bd toks) (t.code ++ w) = run E (bd (toks ++ [t])) w := by
  cases t with
  | bit b =>
    have hE : E toks = .bit := ht.symm
    simp [Tok.code, step, bd, hE]
  | num v =>
    have hE : E toks = .num := ht.symm
    by_cases hv : v = 0
    · subst hv
      simp [Tok.code, encodeNat_zero, step, bd, hE]
    · have hlast := bits_last hv
      have hsz : v.bits.length ≠ 0 := by
        intro h0
        have : v.bits = [] := List.length_eq_zero_iff.mp h0
        rw [this] at hlast; simp at hlast
      simp only [Tok.code, encodeNat, List.append_assoc, bd]
      rw [run_ones E toks hE 0 v.bits.length, List.singleton_append, run_cons]
      have hstep : step E ⟨0, 0 + v.bits.length, 0, 1, [], toks⟩ false =
          ⟨1, v.bits.length, ofBits [], 2 ^ ([] : List Bool).length, [], toks⟩ := by
        simp [step, hE, hsz, ofBits]
      rw [hstep, run_digits E toks v.bits.length v.bits hlast [] (by simp)]
      simp [ofBits_bits, bd]

lemma run_toks (ts : List Tok) (toks : List Tok)
    (hf : ∀ k < ts.length, (ts.getD k (.bit false)).kind = E (toks ++ ts.take k)) (w : Word) :
    run E (bd toks) (code ts ++ w) = run E (bd (toks ++ ts)) w := by
  induction ts generalizing toks with
  | nil => simp [code]
  | cons t rest ih =>
    have h0 := hf 0 (by simp)
    simp only [List.getD_cons_zero, List.take_zero, List.append_nil] at h0
    have : code (t :: rest) ++ w = t.code ++ (code rest ++ w) := by simp [code]
    rw [this, run_tok E toks t h0, ih (toks ++ [t]) (fun k hk => by
      have := hf (k + 1) (by simpa using hk)
      simpa [List.append_assoc] using this)]
    simp

/-- **Completeness**: the code of a conforming stream is accepted, the stream recovered. -/
theorem accept_complete (ts : List Tok) (hc : Conforms E ts) :
    Accepts E (run E init (code ts)) ∧ (run E init (code ts)).toks = ts := by
  have h := run_toks E ts [] (fun k hk => by simpa using hc.1 k hk) []
  simp only [List.append_nil, List.nil_append, run_nil] at h
  have hi : init = bd [] := rfl
  rw [hi, h]
  exact ⟨⟨rfl, rfl, hc.2⟩, rfl⟩

end Lax391470Proofs.TokScan
