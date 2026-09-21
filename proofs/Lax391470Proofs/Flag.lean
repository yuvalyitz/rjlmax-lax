import Mathlib

/-!
A flag that survives a loop exactly if every round was fine.
-/

namespace Lax391470Proofs.Flag

/-- The flag after `k` rounds. -/
def flagTo (P : ℕ → Prop) [DecidablePred P] (okin k : ℕ) : ℕ :=
  if okin = 1 ∧ ∀ j < k, P j then 1 else 0

variable (P : ℕ → Prop) [DecidablePred P]

lemma flagTo_le (okin k : ℕ) : flagTo P okin k ≤ 1 := by unfold flagTo; split <;> omega

lemma flagTo_zero (okin : ℕ) (h : okin ≤ 1) : flagTo P okin 0 = okin := by
  unfold flagTo; split_ifs with h1 <;> simp at h1 <;> omega

lemma forall_lt_succ {Q : ℕ → Prop} (j : ℕ) : (∀ k < j + 1, Q k) ↔ (∀ k < j, Q k) ∧ Q j :=
  ⟨fun h => ⟨fun k hk => h k (by omega), h j (by omega)⟩, fun h k hk => by
    rcases Nat.lt_or_ge k j with h1 | h1
    · exact h.1 k h1
    · have : k = j := by omega
      rw [this]; exact h.2⟩

lemma flagTo_succ (okin k : ℕ) :
    flagTo P okin (k + 1) = if flagTo P okin k = 1 ∧ P k then 1 else 0 := by
  unfold flagTo
  have e := @forall_lt_succ P k
  by_cases hA : okin = 1 ∧ ∀ j < k + 1, P j
  · have h := e.mp hA.2
    rw [if_pos hA, if_pos ⟨by rw [if_pos ⟨hA.1, h.1⟩], h.2⟩]
  · rw [if_neg hA]
    symm; apply if_neg
    rintro ⟨h1, h2⟩
    by_cases hC : okin = 1 ∧ ∀ j < k, P j
    · exact hA ⟨hC.1, e.mpr ⟨hC.2, h2⟩⟩
    · rw [if_neg hC] at h1; omega

lemma flagTo_eq_one {okin k : ℕ} : flagTo P okin k = 1 ↔ okin = 1 ∧ ∀ j < k, P j := by
  unfold flagTo; split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h0 => absurd h0 (by decide), fun h1 => absurd h1 h⟩

end Lax391470Proofs.Flag
