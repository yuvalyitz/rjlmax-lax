import Lax391470Proofs.SatPairs
import Lax391470Proofs.AuxNumbering

/-!
The instance built from a formula is the typed construction, numbered; its correctness
follows.
-/

namespace Lax391470Proofs.SatNumbering

open Lax391470 Lax391470.SatConstruction Lax429075
open Lax391470Proofs.SatBridge Lax391470Proofs.RjLmax Lax391470Proofs.RjLmax.FromSat
open Lax391470Proofs.Sat Lax391470Proofs.SatOrdinary Lax391470Proofs.SatOrdinaryData
open Lax391470Proofs.SatPairs Lax391470Proofs.AuxNumbering

variable (p q : ℕ) (F : CNF.Formula)

section pairs
variable (hq : 1 < q) (i : Fin (FromSat.numPairs (toCnf F)))
include hq

lemma longEarly_eq :
    ((SatConstruction.longEarly p q F i : ℕ) : ℤ) = dpOf' p q (toCnf F) (pairOfIdx F i) := by
  unfold pairOfIdx SatConstruction.longEarly
  by_cases h : posOf F i = 0
  · rw [dif_pos h, if_pos h]
    simp [dpOf', litOffset, secOffset, secIndex, Blocks.litEarly, sectionStart, secLen_eq]
    ring_nf
  · rw [dif_neg h, if_neg h]
    exact (congrArg (fun s => ((clauseEarly p q F s (pairClause F i) : ℕ) : ℤ))
      (secIndex_litOfIndex _ _)).symm.trans (clauseEarly_eq p q F hq _ ⟨_, pairClause_lt F i h⟩)

omit hq in
lemma longDue_eq :
    ((SatConstruction.longDue p q F i : ℕ) : ℤ) = dpOf p q (toCnf F) (pairOfIdx F i) := by
  unfold pairOfIdx SatConstruction.longDue
  by_cases h : posOf F i = 0
  · rw [dif_pos h, if_pos h]
    simp [dpOf, litOffset, secOffset, secIndex, Blocks.LitJob.due, sectionStart, secLen_eq]
    ring_nf
  · rw [dif_neg h, if_neg h]
    exact (congrArg (fun s => ((clauseDue p q F s (pairClause F i) : ℕ) : ℤ))
      (secIndex_litOfIndex _ _)).symm.trans (clauseDue_eq p q F _ ⟨_, pairClause_lt F i h⟩)

lemma shortEarly_eq :
    ((SatConstruction.shortEarly p q F i : ℕ) : ℤ) = dqOf' p q (toCnf F) (pairOfIdx F i) := by
  unfold pairOfIdx SatConstruction.shortEarly
  by_cases h : posOf F i = 0
  · rw [dif_pos h, if_pos h]
    simp [dqOf', litOffset, secOffset, secIndex, Blocks.litEarly, sectionStart, secLen_eq]
  · rw [dif_neg h, if_neg h]
    exact (congrArg (fun s => ((clauseEarly p q F s (pairClause F i) : ℕ) : ℤ))
      (secIndex_litOfIndex _ _)).symm.trans (clauseEarly_eq p q F hq _ ⟨_, pairClause_lt F i h⟩)

omit hq in
lemma shortDue_eq :
    ((SatConstruction.shortDue p q F i : ℕ) : ℤ) = dqOf p q (toCnf F) (pairOfIdx F i) := by
  unfold pairOfIdx SatConstruction.shortDue
  by_cases h : posOf F i = 0
  · rw [dif_pos h, if_pos h]
    simp [dqOf, litOffset, secOffset, secIndex, Blocks.LitJob.due, sectionStart, secLen_eq]
    ring_nf
  · rw [dif_neg h, if_neg h]
    exact (congrArg (fun s => ((clauseDue p q F s (pairClause F i) : ℕ) : ℤ))
      (secIndex_litOfIndex _ _)).symm.trans (clauseDue_eq p q F _ ⟨_, pairClause_lt F i h⟩)

end pairs

variable (hq : 1 < q) (hqp : q < p)

/-- The constructed instance is the typed construction, numbered. -/
noncomputable def satNum : AuxNum (toAux p q (toCnf F) hq hqp) (inst p q F) where
  eo := ordEquiv F
  hN := rfl
  r_eq o := ord_r p q F o
  d_eq o := ord_d p q F hq o
  len_eq o := ord_len p q F o
  dp'_eq i := (longEarly_eq p q F hq i).trans (congrArg _ (pairEquiv_eq F i).symm)
  dp_eq i := (longDue_eq p q F i).trans (congrArg _ (pairEquiv_eq F i).symm)
  dq'_eq i := (shortEarly_eq p q F hq i).trans (congrArg _ (pairEquiv_eq F i).symm)
  dq_eq i := (shortDue_eq p q F i).trans (congrArg _ (pairEquiv_eq F i).symm)

/--
---
conclusion: Lax391470.SatConstruction.ordered
---
The deadlines are those of the typed construction, whose chains are verified there.
-/
theorem ordered (p q : ℕ) (F : CNF.Formula) (hq : 1 < q) (hqp : q < p) :
    (inst p q F).Ordered :=
  AuxNumbering.ordered (satNum p q F hq hqp)

lemma map_eq : FromSat.map p q hqp hq (toCnf F) = toAux p q (toCnf F) hq hqp := by
  have hn : ¬ ((toCnf F).n = 0 ∧ 0 < (toCnf F).m) := fun h => by
    have : 0 < numVars F := numVars_pos F
    exact absurd h.1 (by show numVars F ≠ 0; omega)
  rw [FromSat.map, if_neg hn]

theorem solvable_iff (hq : 1 < q) (hqp : q < p) :
    CNF.Satisfiable F ↔ (inst p q F).Solvable p q := by
  rw [satisfiable_iff F, ← yes_iff (satNum p q F hq hqp), ← map_eq p q F hq hqp]
  exact FromSat.map_correct p q hqp hq (toCnf F)

/--
---
conclusion: Lax391470.SatConstruction.solvable_of_satisfiable
---
-/
theorem solvable_of_satisfiable (p q : ℕ) (F : CNF.Formula) (hq : 1 < q) (hqp : q < p) :
    CNF.Satisfiable F → (inst p q F).Solvable p q :=
  (solvable_iff p q F hq hqp).mp

/--
---
conclusion: Lax391470.SatConstruction.satisfiable_of_solvable
---
-/
theorem satisfiable_of_solvable (p q : ℕ) (F : CNF.Formula) (hq : 1 < q) (hqp : q < p) :
    (inst p q F).Solvable p q → CNF.Satisfiable F :=
  (solvable_iff p q F hq hqp).mpr

end Lax391470Proofs.SatNumbering
