import Lax391470Proofs.InstFormat
import Lax391470Proofs.TokProg

/-!
The format of an instance followed by a schedule: after the tokens of the instance, a
sign and an absolute value for the start time of every job.
-/

namespace Lax391470Proofs.V1Format

open Lax391470 Lax391470.BinaryEncoding Lax391470Proofs.TokModel Lax391470Proofs.TokScan
open Lax391470Proofs.InstFormat Lax434930.PolynomialTime

/-- The kind of the token at position `j` after the count. -/
def kind2 (n j : ℕ) : Kind :=
  if j < 5 * n then (if j % 5 = 0 ∨ j % 5 = 2 then .bit else .num)
  else if j < 7 * n then (if (j - 5 * n) % 2 = 0 then .bit else .num)
  else .done

/-- The format: an instance, then `n` start times. -/
def E2 : Format := fun ts =>
  match ts with
  | .num n :: rest => kind2 n rest.length
  | [] => .num
  | _ => .done

lemma E2_cons (n : ℕ) (rest : List Tok) : E2 (.num n :: rest) = kind2 n rest.length := rfl

lemma kind2_lt {n j : ℕ} (h : j < 5 * n) : kind2 n j = kindAt n j := by
  unfold kind2 kindAt; rw [if_pos h, if_pos h]

/-- Inside the instance the two formats agree. -/
lemma E2_eq_EI {ts : List Tok} {n : ℕ} (h : ts = [] ∨ ∃ rest, ts = .num n :: rest ∧
    rest.length < 5 * n) : E2 ts = EI ts := by
  rcases h with rfl | ⟨rest, rfl, hl⟩
  · rfl
  · rw [E2_cons, EI_cons, kind2_lt hl]

/-- The two tokens of a start time. -/
def schedRec (t : ℕ → ℤ) (j : ℕ) : List Tok := [.bit (decide (t j < 0)), .num (t j).natAbs]

lemma schedRec_length (t : ℕ → ℤ) (j : ℕ) : (schedRec t j).length = 2 := rfl

/-- The tokens of `n` start times. -/
def schedToks (t : ℕ → ℤ) (n : ℕ) : List Tok := (List.range n).flatMap (schedRec t)

lemma schedToks_length (t : ℕ → ℤ) (n : ℕ) : (schedToks t n).length = 2 * n :=
  RecList.length_flatMap_const _ 2 (schedRec_length t) _

/-- An instance followed by a schedule. -/
def toks2 (I : Scheduling.Instance) (t : ℕ → ℤ) : List Tok := toksOf I ++ schedToks t I.jobs

lemma toks2_eq (I : Scheduling.Instance) (t : ℕ → ℤ) :
    toks2 I t = .num I.jobs :: (body I ++ schedToks t I.jobs) := rfl

lemma rest_kind (I : Scheduling.Instance) (t : ℕ → ℤ) (k : ℕ) (hk : k < 7 * I.jobs) :
    ((body I ++ schedToks t I.jobs).getD k (.bit false)).kind = kind2 I.jobs k := by
  by_cases h5 : k < 5 * I.jobs
  · rw [List.getD_append _ _ _ _ (by rw [body_length]; exact h5), body_kind I k h5, kind2_lt h5]
  · rw [List.getD_append_right _ _ _ _ (by rw [body_length]; omega), body_length]
    unfold kind2
    rw [if_neg h5, if_pos hk]
    set m := k - 5 * I.jobs with hm
    have e : m = 2 * (m / 2) + m % 2 := by omega
    unfold schedToks
    rw [e, RecList.getD_flatMap_const _ 2 (schedRec_length t) _ _ _ (by omega) (by omega), ← e]
    have h2 : m % 2 = 0 ∨ m % 2 = 1 := by omega
    rcases h2 with h | h <;> simp [h, schedRec, Tok.kind]

/-- **An instance followed by a schedule conforms to the format.** -/
theorem conforms_toks2 (I : Scheduling.Instance) (t : ℕ → ℤ) : Conforms E2 (toks2 I t) := by
  rw [toks2_eq]
  have hl : (body I ++ schedToks t I.jobs).length = 7 * I.jobs := by
    rw [List.length_append, body_length, schedToks_length]; omega
  constructor
  · intro k hk
    simp only [List.length_cons] at hk
    rcases k with _ | j
    · rfl
    · simp only [List.getD_cons_succ, List.take_succ_cons, E2_cons]
      rw [List.length_take, hl, Nat.min_eq_left (by omega)]
      exact rest_kind I t j (by omega)
  · rw [E2_cons, hl]; unfold kind2; rw [if_neg (by omega), if_neg (by omega)]

/-! ### Tokens are only ever appended -/

lemma step_toks (E : Format) (s : St) (b : Bool) : ∃ l, (step E s b).toks = s.toks ++ l := by
  unfold step dead
  repeat' split
  all_goals first
    | exact ⟨_, rfl⟩
    | exact ⟨[], (List.append_nil _).symm⟩

lemma run_toks_prefix (E : Format) (s : St) (w : Word) : ∃ l, (run E s w).toks = s.toks ++ l := by
  induction w generalizing s with
  | nil => exact ⟨[], by simp⟩
  | cons b t ih =>
    obtain ⟨l1, h1⟩ := step_toks E s b
    obtain ⟨l2, h2⟩ := ih (step E s b)
    exact ⟨l1 ++ l2, by rw [run_cons, h2, h1, List.append_assoc]⟩

/-! ### A scan that stops at the end of the instance -/

/-- **The boundary.** If the scan of a word stops between two tokens, having read exactly
the tokens of an instance, the word is the code of these tokens and they conform to the
format of instances. -/
theorem boundary {w : Word} (h0 : (run E2 init w).ph = 0) (hL : (run E2 init w).L = 0)
    (hT : (run E2 init w).toks.length = 1 + 5 * ((run E2 init w).toks.map TokProg.Tok.val).getD 0 0) :
    code (run E2 init w).toks = w ∧ Conforms EI (run E2 init w).toks := by
  obtain ⟨hg, hc⟩ := run_inv E2 w (by omega)
  set s := run E2 init w with hs
  have h1 : consumed s = code s.toks := by simp [consumed, h0, hL]
  refine ⟨by rw [← h1, hc], ?_⟩
  have hf := hg.fol
  rcases hts : s.toks with _ | ⟨a, rest⟩
  · rw [hts] at hT; simp at hT
  rw [hts] at hT hf
  have ha : a.kind = .num := by simpa [E2] using hf 0 (by simp)
  obtain ⟨n, rfl⟩ : ∃ n, a = .num n := ⟨_, AuxFormat.tok_of_num ha⟩
  have hlen : rest.length = 5 * n := by
    simp [TokProg.Tok.val] at hT; omega
  constructor
  · intro k hk
    rw [hf k hk]
    apply E2_eq_EI (n := n)
    rcases k with _ | j
    · exact Or.inl rfl
    · right
      refine ⟨rest.take j, rfl, ?_⟩
      simp only [List.length_cons] at hk
      rw [List.length_take]; omega
  · rw [EI_cons, hlen]; simp [kindAt]

/-- The length of a conforming stream. -/
lemma conf2_length {ts : List Tok} (hc : Conforms E2 ts) :
    ts.length = 1 + 7 * (ts.map TokProg.Tok.val).getD 0 0 := by
  obtain ⟨hf, hd⟩ := hc
  rcases ts with _ | ⟨a, rest⟩
  · simp [E2] at hd
  have ha : a.kind = .num := by simpa [E2] using hf 0 (by simp)
  obtain ⟨n, rfl⟩ : ∃ n, a = .num n := ⟨_, AuxFormat.tok_of_num ha⟩
  rw [E2_cons] at hd
  have h1 : ¬ rest.length < 7 * n := by
    intro hlt
    unfold kind2 at hd
    split_ifs at hd
  have h2 : rest.length = 7 * n := by
    by_contra hne
    have hk := hf (1 + 7 * n) (by simp; omega)
    have e : (Tok.num n :: rest).take (1 + 7 * n) = .num n :: rest.take (7 * n) := by
      rw [show 1 + 7 * n = 7 * n + 1 by ring]; rfl
    rw [e, E2_cons, List.length_take, Nat.min_eq_left (by omega)] at hk
    have : kind2 n (7 * n) = .done := by
      unfold kind2; rw [if_neg (by omega), if_neg (by omega)]
    rw [this] at hk
    exact AuxFormat.kind_ne_done _ hk
  simp [TokProg.Tok.val, h2]; omega

end Lax391470Proofs.V1Format
