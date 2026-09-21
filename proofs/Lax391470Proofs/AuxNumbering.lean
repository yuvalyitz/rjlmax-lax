import Lax391470Proofs.StackedBridge

/-!
Transport between an instance of the auxiliary problem whose ordinary jobs are named
structurally and one whose jobs are numbered.
-/

namespace Lax391470Proofs.AuxNumbering

open Lax391470 Lax391470.AuxiliaryProblem Lax391470Proofs.RjLmax Lax391470Proofs.Renumbering
open Lax391470Proofs.StackedBridge

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A numbering of the ordinary jobs of `B` that turns it into `A`; the pairs are already
numbered on both sides. -/
structure AuxNum {p q : ℕ} (B : RjLmax.Aux p q) (A : AuxiliaryProblem.Instance) where
  eo : B.Ord ≃ Fin A.ordinary
  hN : B.N = A.pairs
  r_eq : ∀ o, (A.r (eo o) : ℤ) = B.r o
  d_eq : ∀ o, (A.d (eo o) : ℤ) = B.d o
  len_eq : ∀ o, (if A.long (eo o) then p else q) = B.len o
  dp'_eq : ∀ i : Fin B.N, (A.longEarly (Fin.cast hN i) : ℤ) = B.dp' i
  dp_eq : ∀ i : Fin B.N, (A.longDue (Fin.cast hN i) : ℤ) = B.dp i
  dq'_eq : ∀ i : Fin B.N, (A.shortEarly (Fin.cast hN i) : ℤ) = B.dq' i
  dq_eq : ∀ i : Fin B.N, (A.shortDue (Fin.cast hN i) : ℤ) = B.dq i

variable {p q : ℕ} {B : RjLmax.Aux p q} {A : AuxiliaryProblem.Instance} (ν : AuxNum B A)

/-- The deadlines of the numbered instance are ordered, because those of the typed one
are. -/
theorem ordered (ν : AuxNum B A) : A.Ordered := by
  have cast_surj : ∀ i : Fin A.pairs, ∃ i' : Fin B.N, Fin.cast ν.hN i' = i :=
    fun i => ⟨Fin.cast ν.hN.symm i, by simp⟩
  refine ⟨fun i => ?_, fun i j h => ?_, fun i => ?_, fun i j h => ?_, fun i => ?_⟩
  · obtain ⟨i', rfl⟩ := cast_surj i
    have := B.dp'_le_dp i'
    rw [← ν.dp'_eq, ← ν.dp_eq] at this
    exact_mod_cast this
  · obtain ⟨i', rfl⟩ := cast_surj i
    obtain ⟨j', rfl⟩ := cast_surj j
    have := B.dp_le_dp'_succ i' j' (by simpa using h)
    rw [← ν.dp'_eq, ← ν.dp_eq] at this
    exact_mod_cast this
  · obtain ⟨i', rfl⟩ := cast_surj i
    have := B.dq'_le_dq i'
    rw [← ν.dq'_eq, ← ν.dq_eq] at this
    exact_mod_cast this
  · obtain ⟨i', rfl⟩ := cast_surj i
    obtain ⟨j', rfl⟩ := cast_surj j
    have := B.dq_le_dq'_succ i' j' (by simpa using h)
    rw [← ν.dq'_eq, ← ν.dq_eq] at this
    exact_mod_cast this
  · obtain ⟨i', rfl⟩ := cast_surj i
    have := B.dp_le_dq' i'
    rw [← ν.dq'_eq, ← ν.dp_eq] at this
    exact_mod_cast this

/-- The numbering of all jobs induced by that of the ordinary ones. -/
def jobEquiv : B.Job ≃ Fin (A.ordinary + A.pairs + A.pairs) :=
  (Equiv.sumCongr ν.eo (Equiv.sumCongr (finCongr ν.hN) (finCongr ν.hN))).trans (auxEquiv A)

lemma jobEquiv_ord (o : B.Ord) : ((jobEquiv ν (Sum.inl o) : Fin _) : ℕ) = ν.eo o := by
  simp [jobEquiv]

lemma jobEquiv_long (i : Fin B.N) :
    ((jobEquiv ν (Sum.inr (Sum.inl i)) : Fin _) : ℕ) = A.ordinary + (Fin.cast ν.hN i : ℕ) := by
  simp [jobEquiv]

lemma jobEquiv_short (i : Fin B.N) :
    ((jobEquiv ν (Sum.inr (Sum.inr i)) : Fin _) : ℕ) =
      A.ordinary + A.pairs + (Fin.cast ν.hN i : ℕ) := by
  simp [jobEquiv]

/-- The underlying scheduling instances, numbered. -/
def numbering : Numbering B.toInstance (A.toInstance p q) where
  e := jobEquiv ν
  r_eq := by
    rintro (o | i | i)
    · exact (r_of_ord p q (ν.eo o) (jobEquiv_ord ν o)).trans (ν.r_eq o)
    · exact r_of_pending p q (le_of_le_of_eq (Nat.le_add_right _ _) (jobEquiv_long ν i).symm)
    · exact r_of_pending p q (le_of_le_of_eq (by omega) (jobEquiv_short ν i).symm)
  d_eq := by
    rintro (o | i | i)
    · exact (d_of_ord p q (ν.eo o) (jobEquiv_ord ν o)).trans (ν.d_eq o)
    · exact (d_of_long p q _ (jobEquiv_long ν i)).trans (ν.dp_eq i)
    · exact (d_of_short p q _ (jobEquiv_short ν i)).trans (ν.dq_eq i)
  p_eq := by
    rintro (o | i | i)
    · exact (p_of_ord p q (ν.eo o) (jobEquiv_ord ν o)).trans (ν.len_eq o)
    · exact p_of_long p q _ (jobEquiv_long ν i)
    · exact p_of_short p q _ (jobEquiv_short ν i)

lemma jobEquiv_longJob (i : Fin B.N) :
    jobEquiv ν (Sum.inr (Sum.inl i)) = A.longJob p q (Fin.cast ν.hN i) :=
  Fin.ext (by rw [jobEquiv_long]; rfl)

lemma jobEquiv_shortJob (i : Fin B.N) :
    jobEquiv ν (Sum.inr (Sum.inr i)) = A.shortJob p q (Fin.cast ν.hN i) :=
  Fin.ext (by rw [jobEquiv_short]; rfl)

/-- **The typed and the numbered instance are solvable together.** -/
theorem yes_iff (ν : AuxNum B A) : B.Yes ↔ A.Solvable p q := by
  constructor
  · rintro ⟨u, hfeas, hpair⟩
    refine ⟨fun j => u ((jobEquiv ν).symm j), feasible_comp_symm (numbering ν) hfeas,
      fun i => ?_⟩
    obtain ⟨i', rfl⟩ : ∃ i' : Fin B.N, Fin.cast ν.hN i' = i :=
      ⟨Fin.cast ν.hN.symm i, by simp⟩
    rcases hpair i' with h | h
    · left
      show u ((jobEquiv ν).symm (A.longJob p q _)) + (p : ℤ) ≤ _
      rw [← jobEquiv_longJob, Equiv.symm_apply_apply, ν.dp'_eq]; exact h
    · right
      show u ((jobEquiv ν).symm (A.shortJob p q _)) + (q : ℤ) ≤ _
      rw [← jobEquiv_shortJob, Equiv.symm_apply_apply, ν.dq'_eq]; exact h
  · rintro ⟨t, hfeas, hpair⟩
    refine ⟨fun x => t (jobEquiv ν x), feasible_comp (numbering ν) hfeas, fun i => ?_⟩
    rcases hpair (Fin.cast ν.hN i) with h | h
    · left
      show t (jobEquiv ν (Sum.inr (Sum.inl i))) + (p : ℤ) ≤ B.dp' i
      rw [jobEquiv_longJob, ← ν.dp'_eq]; exact h
    · right
      show t (jobEquiv ν (Sum.inr (Sum.inr i))) + (q : ℤ) ≤ B.dq' i
      rw [jobEquiv_shortJob, ← ν.dq'_eq]; exact h

end Lax391470Proofs.AuxNumbering
