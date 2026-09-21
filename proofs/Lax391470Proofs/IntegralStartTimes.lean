import Lax391470.IntegralStartTimes
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring

namespace Lax391470Proofs.IntegralStartTimes

open Lax391470.Scheduling Lax391470.Scheduling.Instance

/--
---
conclusion: Lax391470.IntegralStartTimes.realSchedulable_iff
---
Round every start time up. Rounding up is monotone and commutes with adding an integer,
and all data are integers, so every inequality of feasibility survives.
-/
theorem realSchedulable_iff (I : Instance) : I.RealSchedulable ↔ I.Schedulable := by
  constructor
  · rintro ⟨t, havail, hsep⟩
    have key : ∀ i, ⌈t i + (I.p i : ℝ)⌉ = ⌈t i⌉ + (I.p i : ℤ) := fun i => by
      have : t i + (I.p i : ℝ) = t i + ((I.p i : ℤ) : ℝ) := by push_cast; rfl
      rw [this, Int.ceil_add_intCast]
    refine ⟨fun i => ⌈t i⌉, fun i => ⟨?_, ?_⟩, fun i j hij => ?_⟩
    · have := Int.ceil_mono (havail i).1
      rwa [Int.ceil_intCast] at this
    · have := Int.ceil_mono (havail i).2
      rwa [key i, Int.ceil_intCast] at this
    · rcases hsep i j hij with h | h
      · left
        have := Int.ceil_mono h
        rwa [key i] at this
      · right
        have := Int.ceil_mono h
        rwa [key j] at this
  · rintro ⟨t, havail, hsep⟩
    refine ⟨fun i => (t i : ℝ), fun i => ⟨?_, ?_⟩, fun i j hij => ?_⟩
    · show (I.r i : ℝ) ≤ (t i : ℝ)
      exact_mod_cast (havail i).1
    · show (t i : ℝ) + (I.p i : ℝ) ≤ (I.d i : ℝ)
      exact_mod_cast (havail i).2
    · rcases hsep i j hij with h | h
      · left
        show (t i : ℝ) + (I.p i : ℝ) ≤ (t j : ℝ)
        exact_mod_cast h
      · right
        show (t j : ℝ) + (I.p j : ℝ) ≤ (t i : ℝ)
        exact_mod_cast h

end Lax391470Proofs.IntegralStartTimes
