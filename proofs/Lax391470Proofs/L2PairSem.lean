import Lax391470Proofs.L2Pair
import Lax391470Proofs.L2Active
import Lax391470Proofs.SatPairs

/-!
The mirror functions of the pair calculator are the concept's functions.
-/

namespace Lax391470Proofs.L2PairSem

open Lax429075.CNF Lax391470.SatConstruction Lax391470Proofs.L2Pair Lax391470Proofs.L2Active

variable (p q : ℕ) (F : Formula)

lemma sub_div_mul (x m : ℕ) : x - x / m * m = x % m := by
  have := Nat.div_add_mod x m
  have h2 : x / m * m = m * (x / m) := Nat.mul_comm _ _
  omega

lemma pp_eq (i : ℕ) : pp (1 + 2 * numClauses F) i = posOf F i := sub_div_mul _ _

lemma pj_eq (i : ℕ) : pj (1 + 2 * numClauses F) (numClauses F) i = pairClause F i := by
  unfold pj pairClause
  rw [pp_eq, sub_div_mul]

lemma psec_eq (i : ℕ) : psec (1 + 2 * numClauses F) (numClauses F) i = pairSection F i := by
  unfold psec pairSection groupOf
  rw [pp_eq]

theorem e2Val_eq (i : ℕ) :
    e2Val p q (1 + 2 * numClauses F) (numClauses F) (sectionLength p q F) i = longDue p q F i := by
  unfold e2Val longDue
  rw [pp_eq, psec_eq, pj_eq]
  unfold clauseDue clauseStart sectionStart groupOf
  split <;> ring

theorem e4Val_eq (i : ℕ) :
    e4Val p q (1 + 2 * numClauses F) (numClauses F) (sectionLength p q F) i = shortDue p q F i := by
  unfold e4Val shortDue
  rw [pp_eq, psec_eq, pj_eq]
  unfold clauseDue clauseStart sectionStart groupOf
  split <;> ring

theorem e1Val_eq (i : ℕ) (_hi : i < Lax391470.SatConstruction.numPairs F) :
    e1Val p q (1 + 2 * numClauses F) (numClauses F) (sectionLength p q F) (table F) i =
      longEarly p q F i := by
  unfold e1Val longEarly
  rw [pp_eq, psec_eq, pj_eq]
  by_cases h : posOf F i = 0
  · rw [if_pos h, if_pos h]; unfold sectionStart groupOf; ring
  · rw [if_neg h, if_neg h]
    have hj : pairClause F i < F.length := SatPairs.pairClause_lt F i h
    have := table_eq F (pairSection F i) (pairClause F i) hj
    unfold numClauses at *
    rw [this]
    unfold clauseEarly clauseStart sectionStart
    cases active F (pairSection F i) (pairClause F i) <;> simp <;> ring

theorem e3Val_eq (i : ℕ) (_hi : i < Lax391470.SatConstruction.numPairs F) :
    e3Val p q (1 + 2 * numClauses F) (numClauses F) (sectionLength p q F) (table F) i =
      shortEarly p q F i := by
  unfold e3Val shortEarly
  rw [pp_eq, psec_eq, pj_eq]
  by_cases h : posOf F i = 0
  · rw [if_pos h, if_pos h]; unfold sectionStart groupOf; ring
  · rw [if_neg h, if_neg h]
    have hj : pairClause F i < F.length := SatPairs.pairClause_lt F i h
    have := table_eq F (pairSection F i + 1) (pairClause F i) hj
    unfold numClauses at *
    rw [this]
    unfold clauseEarly clauseStart sectionStart
    cases active F (pairSection F i + 1) (pairClause F i) <;> simp <;> ring

end Lax391470Proofs.L2PairSem
