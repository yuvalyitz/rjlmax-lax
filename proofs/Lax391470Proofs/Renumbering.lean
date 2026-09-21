import Lax391470.Scheduling
import Lax391470Proofs.TypedDefs

/-!
Transport of feasibility between an instance whose jobs are named structurally and an
instance whose jobs are numbered, along a bijection that preserves the data.
-/

namespace Lax391470Proofs.Renumbering

open Lax391470 Lax391470Proofs.RjLmax

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A numbering of the jobs of `I` that turns it into `J`. -/
structure Numbering (I : RjLmax.Instance) (J : Scheduling.Instance) where
  /-- The numbering. -/
  e : I.Job ≃ Fin J.jobs
  /-- Release times agree. -/
  r_eq : ∀ x, J.r (e x) = I.r x
  /-- Deadlines agree. -/
  d_eq : ∀ x, J.d (e x) = I.d x
  /-- Processing times agree. -/
  p_eq : ∀ x, J.p (e x) = I.p x

variable {I : RjLmax.Instance} {J : Scheduling.Instance} (ν : Numbering I J)

/-- A feasible schedule of the numbered instance, read along the numbering. -/
lemma feasible_comp {t : J.Schedule} (h : Scheduling.Instance.Feasible t) :
    RjLmax.Instance.Feasible (I := I) (fun x => t (ν.e x)) := by
  obtain ⟨hav, hsep⟩ := h
  refine ⟨fun x => ?_, fun x y hxy => ?_⟩
  · have := hav (ν.e x)
    rw [ν.r_eq, ν.d_eq, ν.p_eq] at this
    exact this
  · have := hsep (ν.e x) (ν.e y) (fun h => hxy (ν.e.injective h))
    rw [ν.p_eq, ν.p_eq] at this
    exact this

/-- A feasible schedule of the named instance, read along the inverse numbering. -/
lemma feasible_comp_symm {u : I.Schedule} (h : RjLmax.Instance.Feasible u) :
    Scheduling.Instance.Feasible (I := J) (fun j => u (ν.e.symm j)) := by
  obtain ⟨hav, hsep⟩ := h
  refine ⟨fun j => ?_, fun j k hjk => ?_⟩
  · have := hav (ν.e.symm j)
    unfold RjLmax.Instance.completion at this
    rw [← ν.r_eq, ← ν.d_eq, ← ν.p_eq, Equiv.apply_symm_apply] at this
    exact this
  · have := hsep (ν.e.symm j) (ν.e.symm k) (fun h => hjk (ν.e.symm.injective h))
    unfold RjLmax.Instance.completion at this
    rw [← ν.p_eq, ← ν.p_eq, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    exact this

/-- The two instances are schedulable together. -/
theorem schedulable_iff (ν : Numbering I J) : I.IsYes ↔ J.Schedulable :=
  ⟨fun ⟨_, hu⟩ => ⟨_, feasible_comp_symm ν hu⟩, fun ⟨_, ht⟩ => ⟨_, feasible_comp ν ht⟩⟩

end Lax391470Proofs.Renumbering
