import Lax391470Proofs.L1Model

/-!
The conditions on the deadlines of an instance of the auxiliary problem, as a test on the
token values of its encoding.
-/

namespace Lax391470Proofs.L1Ordered

open Lax391470 Lax391470Proofs.TokModel Lax391470Proofs.AuxFormat Lax391470Proofs.TokProg
open Lax391470Proofs.L1Model

/-- Deadline `c` of pair `i`, read off the token values. -/
def ev (tk : List ℕ) (n i c : ℕ) : ℕ := tk.getD (2 + (3 * n + (4 * i + c))) 0

/-- Pair `i` meets the conditions, including those linking it to the next pair. -/
def PairOK (tk : List ℕ) (n N i : ℕ) : Prop :=
  ev tk n i 0 ≤ ev tk n i 1 ∧ ev tk n i 2 ≤ ev tk n i 3 ∧ ev tk n i 1 ≤ ev tk n i 2 ∧
    (i + 1 < N → ev tk n i 1 ≤ ev tk n (i + 1) 0 ∧ ev tk n i 3 ≤ ev tk n (i + 1) 2)

instance (tk : List ℕ) (n N i : ℕ) : Decidable (PairOK tk n N i) := by
  unfold PairOK; infer_instance

/-- All pairs meet the conditions. -/
def OrdOK (tk : List ℕ) : Prop := ∀ i < tk.getD 1 0, PairOK tk (tk.getD 0 0) (tk.getD 1 0) i

instance (tk : List ℕ) : Decidable (OrdOK tk) := by unfold OrdOK; infer_instance

variable (A : AuxiliaryProblem.Instance)

lemma ev_eq (i : ℕ) (hi : i < A.pairs) :
    ev (tkOf A) A.ordinary i 0 = A.longEarly ⟨i, hi⟩ ∧
    ev (tkOf A) A.ordinary i 1 = A.longDue ⟨i, hi⟩ ∧
    ev (tkOf A) A.ordinary i 2 = A.shortEarly ⟨i, hi⟩ ∧
    ev (tkOf A) A.ordinary i 3 = A.shortDue ⟨i, hi⟩ := by
  unfold ev
  rw [tk_pair A i 0 hi (by omega), tk_pair A i 1 hi (by omega), tk_pair A i 2 hi (by omega),
    tk_pair A i 3 hi (by omega)]
  simp [pairRec, hi, Tok.val]

theorem ordered_iff : A.Ordered ↔ OrdOK (tkOf A) := by
  unfold OrdOK
  rw [tk_zero, tk_one]
  constructor
  · intro h i hi
    obtain ⟨e0, e1, e2, e3⟩ := ev_eq A i hi
    refine ⟨by rw [e0, e1]; exact h.longEarly_le _, by rw [e2, e3]; exact h.shortEarly_le _,
      by rw [e1, e2]; exact h.longDue_le_shortEarly _, fun hi' => ?_⟩
    obtain ⟨f0, -, f2, -⟩ := ev_eq A (i + 1) hi'
    exact ⟨by rw [e1, f0]; exact h.longDue_le ⟨i, hi⟩ ⟨i + 1, hi'⟩ rfl,
      by rw [e3, f2]; exact h.shortDue_le ⟨i, hi⟩ ⟨i + 1, hi'⟩ rfl⟩
  · intro h
    refine ⟨fun i => ?_, fun i j hij => ?_, fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
    · obtain ⟨e0, e1, -, -⟩ := ev_eq A i i.isLt
      have := (h i i.isLt).1; rwa [e0, e1] at this
    · obtain ⟨-, e1, -, -⟩ := ev_eq A i i.isLt
      have hj : (i : ℕ) + 1 < A.pairs := by rw [hij]; exact j.isLt
      obtain ⟨f0, -, -, -⟩ := ev_eq A ((i : ℕ) + 1) hj
      have := ((h i i.isLt).2.2.2 hj).1
      rw [e1, f0] at this
      have hjj : (⟨(i : ℕ) + 1, hj⟩ : Fin A.pairs) = j := Fin.ext hij
      rwa [hjj] at this
    · obtain ⟨-, -, e2, e3⟩ := ev_eq A i i.isLt
      have := (h i i.isLt).2.1; rwa [e2, e3] at this
    · obtain ⟨-, -, -, e3⟩ := ev_eq A i i.isLt
      have hj : (i : ℕ) + 1 < A.pairs := by rw [hij]; exact j.isLt
      obtain ⟨-, -, f2, -⟩ := ev_eq A ((i : ℕ) + 1) hj
      have := ((h i i.isLt).2.2.2 hj).2
      rw [e3, f2] at this
      have hjj : (⟨(i : ℕ) + 1, hj⟩ : Fin A.pairs) = j := Fin.ext hij
      rwa [hjj] at this
    · obtain ⟨-, e1, e2, -⟩ := ev_eq A i i.isLt
      have := (h i i.isLt).2.2.1; rwa [e1, e2] at this

end Lax391470Proofs.L1Ordered
