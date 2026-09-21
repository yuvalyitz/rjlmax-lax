import Mathlib.Data.List.Range
import Mathlib.Data.List.GetD

/-!
Lists made of records of a fixed length.
-/

namespace Lax391470Proofs.RecList

variable {α : Type}

lemma length_flatMap_const (f : ℕ → List α) (c : ℕ) (hf : ∀ k, (f k).length = c) (N : ℕ) :
    ((List.range N).flatMap f).length = c * N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp [hf, Nat.mul_succ]

lemma getD_flatMap_const (f : ℕ → List α) (c : ℕ) (hf : ∀ k, (f k).length = c) (N k r : ℕ)
    (hk : k < N) (hr : r < c) (d : α) :
    ((List.range N).flatMap f).getD (c * k + r) d = (f k).getD r d := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append]
    have hlen := length_flatMap_const f c hf N
    rcases Nat.lt_or_ge k N with h | h
    · have hlt : c * k + r < c * N := by
        have := Nat.mul_le_mul_left c (show k + 1 ≤ N by omega)
        rw [Nat.mul_succ] at this; omega
      rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hlt)]
      exact ih h
    · have : k = N := by omega
      subst this
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
      simp

end Lax391470Proofs.RecList
