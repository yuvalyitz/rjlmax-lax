import Lax391470Proofs.SatPairs

/-!
Every time of the constructed instance lies on the time line of length `2nS`.
-/

namespace Lax391470Proofs.SatTimes

open Lax391470 Lax391470.SatConstruction Lax429075
open Lax391470Proofs.SatOrdinary Lax391470Proofs.SatOrdinaryData Lax391470Proofs.SatPairs

variable (p q : ℕ) (F : CNF.Formula)

lemma sec_le (s x : ℕ) (hs : s < 2 * numVars F) (hx : x ≤ sectionLength p q F) :
    sectionStart p q F s + x ≤ 2 * numVars F * sectionLength p q F := by
  have h := Nat.mul_le_mul_left (sectionLength p q F) (show s + 1 ≤ 2 * numVars F by omega)
  rw [Nat.mul_succ] at h
  have e : 2 * numVars F * sectionLength p q F = sectionLength p q F * (2 * numVars F) :=
    Nat.mul_comm _ _
  unfold sectionStart
  omega

lemma clause_le (s j : ℕ) (hs : s < 2 * numVars F) (hj : j < numClauses F) :
    clauseEarly p q F s j ≤ 2 * numVars F * sectionLength p q F ∧
      clauseDue p q F s j ≤ 2 * numVars F * sectionLength p q F := by
  have hmul := Nat.mul_le_mul_right (p + q) (show j + 1 ≤ numClauses F by omega)
  rw [Nat.succ_mul] at hmul
  have hx : p + 2 * q + j * (p + q) + p + q + 1 ≤ sectionLength p q F := by
    unfold sectionLength; omega
  have := sec_le p q F s _ hs hx
  unfold clauseEarly clauseDue clauseStart
  constructor
  · split <;> omega
  · omega

lemma S_facts : 2 * q + 1 ≤ sectionLength p q F ∧ p + 2 * q + 1 ≤ sectionLength p q F := by
  unfold sectionLength; omega

/--
---
conclusion: Lax391470.SatConstruction.times_le
---
-/
theorem times_le (p q : ℕ) (F : CNF.Formula) :
    (∀ o, (inst p q F).r o ≤ 2 * numVars F * sectionLength p q F ∧
      (inst p q F).d o ≤ 2 * numVars F * sectionLength p q F) ∧
    (∀ i, (inst p q F).longDue i ≤ 2 * numVars F * sectionLength p q F ∧
      (inst p q F).shortDue i ≤ 2 * numVars F * sectionLength p q F) := by
  obtain ⟨hS1, hS2⟩ := S_facts p q F
  constructor
  · rintro ⟨o, ho⟩
    show ordRelease p q F o ≤ _ ∧ SatConstruction.ordDue p q F o ≤ _
    have ho' : o < 6 * numVars F + 2 * numClauses F := ho
    by_cases h : o < 6 * numVars F
    · have hs : o / 3 < 2 * numVars F := by omega
      have hc : o % 3 < 3 := by omega
      have e : o = 3 * (o / 3) + o % 3 := by omega
      rw [e, ordRelease_sec p q F _ _ hs hc, ordDue_sec p q F _ _ hs hc]
      have b0 := sec_le p q F (o / 3) 0 hs (by omega)
      have b1 := sec_le p q F (o / 3) (sectionLength p q F) hs le_rfl
      have b2 := sec_le p q F (o / 3) (p + 2 * q + 1) hs hS2
      have b3 := sec_le p q F (o / 3) (2 * q + 1) hs hS1
      have b4 := sec_le p q F (o / 3) (p + q) hs (by omega)
      constructor <;> split_ifs <;> omega
    · have hn := numVars_pos F
      constructor
      · simp [ordRelease, h]
      · unfold SatConstruction.ordDue
        rw [if_neg h]
        split
        · exact (clause_le p q F _ _ (by omega) (by omega)).1
        · exact (clause_le p q F _ _ (by omega) (by omega)).1
  · rintro ⟨i, hi⟩
    show SatConstruction.longDue p q F i ≤ _ ∧ SatConstruction.shortDue p q F i ≤ _
    obtain ⟨hg, -⟩ := group_bounds F i hi
    unfold SatConstruction.longDue SatConstruction.shortDue
    by_cases h : posOf F i = 0
    · rw [if_pos h, if_pos h]
      have b1 := sec_le p q F (2 * groupOf F i) (p + 2 * q) (by omega) (by omega)
      have b2 := sec_le p q F (2 * groupOf F i + 1) (p + 2 * q) (by omega) (by omega)
      omega
    · rw [if_neg h, if_neg h]
      have hs := pairSection_lt F i hi h
      have hj := pairClause_lt F i h
      exact ⟨(clause_le p q F _ _ (by omega) hj).2, (clause_le p q F _ _ (by omega) hj).2⟩

end Lax391470Proofs.SatTimes
