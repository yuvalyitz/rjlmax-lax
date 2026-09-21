import Lax391470Proofs.L1Ordered
import Lax391470Proofs.L1Check

/-!
What the program reads from the token array agrees with the list of tokens: every index
it uses lies below the token count.
-/

namespace Lax391470Proofs.L1Agree

open Lax391470Proofs.L1Model Lax391470Proofs.L1Ordered Lax391470Proofs.L1Check

variable (p q : ℕ) (arr : List ℕ) (n N T : ℕ)

lemma getD_take {k : ℕ} (hk : k < T) : (arr.take T).getD k 0 = arr.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, hk]

lemma ordRow_agree (hT : T = 2 + 3 * n + 4 * N) {i : ℕ} (hi : i < n) :
    ordRow p q (arr.take T) i = ordRow p q arr i := by
  unfold ordRow
  rw [getD_take arr T (by omega), getD_take arr T (by omega), getD_take arr T (by omega)]

lemma quadRow_agree (hT : T = 2 + 3 * n + 4 * N) {i : ℕ} (hi : i < N) :
    quadRow p q (arr.take T) n i = quadRow p q arr n i := by
  unfold quadRow
  rw [getD_take arr T (by omega), getD_take arr T (by omega), getD_take arr T (by omega),
    getD_take arr T (by omega)]

lemma pairOK_agree (hT : T = 2 + 3 * n + 4 * N) {i : ℕ} (hi : i < N) :
    PairOK (arr.take T) n N i ↔ PairOK arr n N i := by
  unfold PairOK ev
  rw [getD_take arr T (by omega), getD_take arr T (by omega), getD_take arr T (by omega),
    getD_take arr T (by omega)]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
  refine forall_congr' fun hnext => ?_
  rw [getD_take arr T (by omega), getD_take arr T (by omega)]

/-- The flag of the check loop says whether the conditions hold. -/
theorem okv_iff (hT : T = 2 + 3 * n + 4 * N) (h0 : (arr.take T).getD 0 0 = n)
    (h1 : (arr.take T).getD 1 0 = N) :
    okv arr (2 + 3 * n) N N = 1 ↔ OrdOK (arr.take T) := by
  unfold okv OrdOK
  rw [h0, h1]
  constructor
  · intro h i hi
    have hall : ∀ i' < N, PairOK' arr (2 + 3 * n) N i' := by
      by_contra hc; rw [if_neg hc] at h; omega
    exact (pairOK_agree arr n N T hT hi).mpr ((pairOK'_iff arr n N i).mp (hall i hi))
  · intro h
    rw [if_pos]
    intro i hi
    exact (pairOK'_iff arr n N i).mpr ((pairOK_agree arr n N T hT hi).mp (h i hi))

end Lax391470Proofs.L1Agree
