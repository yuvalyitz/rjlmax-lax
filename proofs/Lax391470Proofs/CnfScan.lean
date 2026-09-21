import Lax391470Proofs.DecodeSound
import Lax429075.EncodingCorrect

/-!
Decoding a formula as a finite-state scan of its bits.

The encoding of a formula is recognised by one left-to-right pass with a four-valued
phase, one bit a step. The scan is the model a machine program is proved against; what it
accepts is settled here: the bits it has consumed are always recoverable from its state,
so an accepting scan has read exactly the encoding of the clauses it collected, and it
agrees with the decoder of the encoding.
-/

namespace Lax391470Proofs.CnfScan

open Lax429075.CNF Lax429075.Encoding Lax434930.PolynomialTime

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The state of the scan: the phase, the unary counter, the clauses completed, and the
literals of the clause being read. -/
structure St where
  ph : ℕ
  n : ℕ
  done : List Clause
  cur : Clause

def init : St := ⟨0, 0, [], []⟩

/-- One bit. Phases: `0` between clauses, `1` between literals, `2` in a variable index,
`3` at a sign, `4` finished, `5` rejected. -/
def step (s : St) (b : Bool) : St :=
  match s.ph with
  | 0 => if b then { s with ph := 1 } else { s with ph := 4 }
  | 1 => if b then { s with ph := 2, n := 0 } else ⟨0, s.n, s.done ++ [s.cur], []⟩
  | 2 => if b then { s with n := s.n + 1 } else { s with ph := 3 }
  | 3 => ⟨1, s.n, s.done, s.cur ++ [⟨s.n, b⟩]⟩
  | _ => { s with ph := 5 }

def run (s : St) (w : Word) : St := w.foldl step s

@[simp] lemma run_nil (s : St) : run s [] = s := rfl
@[simp] lemma run_cons (s : St) (b : Bool) (w : Word) : run s (b :: w) = run (step s b) w := rfl
lemma run_append (s : St) (u v : Word) : run s (u ++ v) = run (run s u) v := by
  simp [run, List.foldl_append]

lemma encodeList_eq {α : Type} (e : α → Word) (l : List α) :
    encodeList e l = l.flatMap (fun a => true :: e a) ++ [false] := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [encodeList, ih]

def curBits (c : Clause) : Word := c.flatMap fun l => true :: encodeLiteral l

def doneBits (d : List Clause) : Word := d.flatMap fun c => true :: encodeClause c

/-- The bits consumed so far, read back off the state. -/
def consumed (s : St) : Word :=
  match s.ph with
  | 0 => doneBits s.done
  | 1 => doneBits s.done ++ true :: curBits s.cur
  | 2 => doneBits s.done ++ true :: curBits s.cur ++ true :: List.replicate s.n true
  | 3 => doneBits s.done ++ true :: curBits s.cur ++ true :: List.replicate s.n true ++ [false]
  | 4 => doneBits s.done ++ [false]
  | _ => []

/-- Between clauses no literal is pending. -/
def Good (s : St) : Prop := s.ph = 0 ∨ s.ph = 4 → s.cur = []

lemma step_alive {s : St} {b : Bool} (h : (step s b).ph ≤ 4) : s.ph ≤ 3 := by
  by_contra hc
  have : 4 ≤ s.ph := by omega
  obtain ⟨ph, n, d, c⟩ := s
  simp only at this
  match ph, this with
  | k + 4, _ => simp [step] at h

lemma step_inv {s : St} {b : Bool} (hg : Good s) (h : (step s b).ph ≤ 4) :
    Good (step s b) ∧ consumed (step s b) = consumed s ++ [b] := by
  have hph := step_alive h
  obtain ⟨ph, n, d, c⟩ := s
  simp only [Good] at hg hph
  have hcases : ph = 0 ∨ ph = 1 ∨ ph = 2 ∨ ph = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · have hc : c = [] := hg (Or.inl rfl)
    subst hc
    cases b
    · exact ⟨by simp [Good, step], by simp [step, consumed]⟩
    · exact ⟨by simp [Good, step], by simp [step, consumed, curBits]⟩
  · cases b
    · exact ⟨by simp [Good, step],
        by simp [step, consumed, doneBits, encodeClause, encodeList_eq, curBits]⟩
    · exact ⟨by simp [Good, step], by simp [step, consumed]⟩
  · cases b
    · exact ⟨by simp [Good, step], by simp [step, consumed]⟩
    · exact ⟨by simp [Good, step], by simp [step, consumed, List.replicate_succ']⟩
  · exact ⟨by simp [Good, step],
      by simp [step, consumed, curBits, encodeLiteral, encodeNat]⟩

lemma run_inv (w : Word) (h : (run init w).ph ≤ 4) :
    Good (run init w) ∧ consumed (run init w) = w := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨by simp [Good, init], rfl⟩
  | append_singleton u b ih =>
      rw [run_append] at h ⊢
      simp only [run_cons, run_nil] at h ⊢
      have ih' := ih (by have := step_alive h; omega)
      obtain ⟨hg, hc⟩ := step_inv ih'.1 h
      exact ⟨hg, by rw [hc, ih'.2]⟩

/-- **Soundness of the scan**: if it accepts, the word is the encoding of the clauses it
collected. -/
theorem accept_sound {w : Word} (h : (run init w).ph = 4) :
    encodeCNF (run init w).done = w := by
  obtain ⟨-, hc⟩ := run_inv w (by omega)
  have : consumed (run init w) = encodeCNF (run init w).done := by
    simp [consumed, h, encodeCNF, encodeList_eq, doneBits]
  rw [← this, hc]

lemma run_ones (n0 m : ℕ) (d : List Clause) (c : Clause) (w : Word) :
    run ⟨2, n0, d, c⟩ (List.replicate m true ++ w) = run ⟨2, n0 + m, d, c⟩ w := by
  induction m generalizing n0 with
  | zero => simp
  | succ m ih =>
      rw [List.replicate_succ, List.cons_append, run_cons]
      have : step ⟨2, n0, d, c⟩ true = ⟨2, n0 + 1, d, c⟩ := by simp [step]
      rw [this, ih]; congr 2; omega

lemma run_lit (n0 : ℕ) (d : List Clause) (c : Clause) (l : Literal) (w : Word) :
    run ⟨1, n0, d, c⟩ (true :: encodeLiteral l ++ w) = run ⟨1, l.index, d, c ++ [l]⟩ w := by
  have h1 : step ⟨1, n0, d, c⟩ true = ⟨2, 0, d, c⟩ := by simp [step]
  rw [List.cons_append, run_cons, h1, encodeLiteral, encodeNat, List.append_assoc,
    List.append_assoc, run_ones]
  simp only [List.cons_append, List.nil_append, run_cons, Nat.zero_add]
  have h2 : step ⟨2, l.index, d, c⟩ false = ⟨3, l.index, d, c⟩ := by simp [step]
  have h3 : step ⟨3, l.index, d, c⟩ l.positive = ⟨1, l.index, d, c ++ [l]⟩ := by simp [step]
  rw [h2, h3]

lemma run_lits (c' : Clause) (n0 : ℕ) (d : List Clause) (c : Clause) (w : Word) :
    ∃ n1, run ⟨1, n0, d, c⟩ (curBits c' ++ w) = run ⟨1, n1, d, c ++ c'⟩ w := by
  induction c' generalizing n0 c with
  | nil => exact ⟨n0, by simp [curBits]⟩
  | cons l t ih =>
      obtain ⟨n1, h⟩ := ih l.index (c ++ [l])
      refine ⟨n1, ?_⟩
      have : curBits (l :: t) ++ w = true :: encodeLiteral l ++ (curBits t ++ w) := by
        simp [curBits]
      rw [this, run_lit, h]; simp

lemma run_clause (n0 : ℕ) (d : List Clause) (c : Clause) (w : Word) :
    ∃ n1, run ⟨0, n0, d, []⟩ (true :: encodeClause c ++ w) = run ⟨0, n1, d ++ [c], []⟩ w := by
  have h0 : step ⟨0, n0, d, []⟩ true = ⟨1, n0, d, []⟩ := by simp [step]
  obtain ⟨n1, h⟩ := run_lits c n0 d [] (false :: w)
  refine ⟨n1, ?_⟩
  have hw : encodeClause c ++ w = curBits c ++ (false :: w) := by
    simp [encodeClause, encodeList_eq, curBits]
  rw [List.cons_append, run_cons, h0, hw, h, run_cons]
  simp [step]

lemma run_formula (F : List Clause) (n0 : ℕ) (d : List Clause) (w : Word) :
    ∃ n1, run ⟨0, n0, d, []⟩ (doneBits F ++ w) = run ⟨0, n1, d ++ F, []⟩ w := by
  induction F generalizing n0 d with
  | nil => exact ⟨n0, by simp [doneBits]⟩
  | cons c t ih =>
      obtain ⟨n1, h1⟩ := run_clause n0 d c (doneBits t ++ w)
      obtain ⟨n2, h2⟩ := ih n1 (d ++ [c])
      refine ⟨n2, ?_⟩
      have : doneBits (c :: t) ++ w = true :: encodeClause c ++ (doneBits t ++ w) := by
        simp [doneBits]
      rw [this, h1, h2]; simp

/-- **Completeness of the scan**: it accepts the encoding of a formula, having collected
the formula. -/
theorem accept_complete (F : Formula) :
    (run init (encodeCNF F)).ph = 4 ∧ (run init (encodeCNF F)).done = F := by
  obtain ⟨n1, h⟩ := run_formula F 0 [] [false]
  have : encodeCNF F = doneBits F ++ [false] := by simp [encodeCNF, encodeList_eq, doneBits]
  rw [this, init, h]
  simp [step]

/-- **The scan is the decoder.** -/
theorem decodeCNF_eq (w : Word) :
    decodeCNF w = if (run init w).ph = 4 then some (run init w).done else none := by
  split
  · next h =>
    have := accept_sound h
    conv_lhs => rw [← this]
    exact Lax429075.EncodingCorrect.roundtrip _
  · next h =>
    cases hd : decodeCNF w with
    | none => rfl
    | some F =>
      have hw := DecodeSound.decodeCNF_sound w F hd
      exact absurd (hw ▸ (accept_complete F).1) h

end Lax391470Proofs.CnfScan
