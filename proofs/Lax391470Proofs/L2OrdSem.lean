import Lax391470Proofs.L2Ord
import Lax391470Proofs.L2Active

/-!
The mirror functions of the ordinary-job calculator are the concept's functions.
-/

namespace Lax391470Proofs.L2OrdSem

open Lax429075.CNF Lax391470.SatConstruction Lax391470Proofs.L2Ord Lax391470Proofs.L2Active

variable (p q : ℕ) (F : Formula)

lemma mod3 (o : ℕ) : o - 3 * (o / 3) = o % 3 := by omega
lemma mod2 (s : ℕ) : s - s / 2 * 2 = s % 2 := by omega

theorem rVal_eq (o : ℕ) :
    rVal q (numVars F) (sectionLength p q F) o = ordRelease p q F o := by
  unfold rVal ordRelease sectionStart
  simp only [mod3, mod2]
  split
  · have h3 : o % 3 < 3 := Nat.mod_lt _ (by omega)
    rcases h : o % 3 with _ | _ | _ | k
    · simp; split <;> rfl
    · simp
    · simp
    · omega
  · rfl

theorem lgVal_eq (o : ℕ) :
    lgVal (numVars F) (numClauses F) o = if ordLong F o then 1 else 0 := by
  unfold lgVal ordLong
  simp only [mod3, mod2]
  split
  · have h2 : o / 3 % 2 < 2 := Nat.mod_lt _ (by omega)
    by_cases h : o % 3 = 1
    · rcases h' : o / 3 % 2 with _ | _ | k <;> simp [h] ; omega
    · simp [h]
  · split <;> simp [*]

theorem dVal_eq (o : ℕ) (ho : o < numOrdinary F) :
    dVal p q (numVars F) (numClauses F) (sectionLength p q F) (table F) o =
      Lax391470.SatConstruction.ordDue p q F o := by
  unfold dVal Lax391470.SatConstruction.ordDue sectionStart
  unfold numOrdinary at ho
  simp only [mod3, mod2]
  split
  · have h3 : o % 3 < 3 := Nat.mod_lt _ (by omega)
    rcases h : o % 3 with _ | _ | _ | k
    · simp; split <;> rfl
    · simp; omega
    · simp
    · omega
  · split
    · next h1 h2 =>
      have hj : o - 6 * numVars F < F.length := by unfold numClauses at h2; omega
      have := table_eq F (2 * numVars F - 1) (o - 6 * numVars F) hj
      unfold numClauses
      rw [this]
      unfold clauseEarly clauseStart sectionStart
      cases active F (2 * numVars F - 1) (o - 6 * numVars F) <;> simp <;> ring
    · next h1 h2 =>
      have hj : o - 6 * numVars F - numClauses F < F.length := by
        unfold numClauses at h2 ho ⊢; omega
      have := table_eq F 0 (o - 6 * numVars F - numClauses F) hj
      simp only [Nat.zero_mul, Nat.zero_add] at this
      rw [this]
      unfold clauseEarly clauseStart sectionStart
      cases active F 0 (o - 6 * numVars F - numClauses F) <;> simp

end Lax391470Proofs.L2OrdSem
