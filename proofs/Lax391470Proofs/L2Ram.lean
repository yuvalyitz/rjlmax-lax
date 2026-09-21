import Lax391470Proofs.L2Main
import Lax391470Proofs.L2Nums
import Lax391470Proofs.RamBridge

/-!
The reduction of Lemma 2 runs in polynomial time on a word RAM.
-/

namespace Lax391470Proofs.L2Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax391470Proofs.L2Main Lax391470Proofs.L2Nums

variable (p q : ℕ)

def layout : Layout :=
  ⟨["L", "rt", "rv", "mx", "ph", "n", "C", "k", "p", "c", "m", "nn", "S", "n6", "n6m", "NO", "g",
    "NP", "i", "t", "o", "s", "par", "base", "lg", "r", "d", "j", "sec", "cs", "v", "pos", "x",
    "h", "cs1", "cs2", "e1", "e2", "e3", "e4", "u", "i2"],
   ["a", "vr", "sg", "cl", "act", "R", "D", "LG", "E1", "E2", "E3", "E4"], 12⟩

theorem com_ok : Com.Ok layout (main p q) := by
  simp [main, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, L2Scan.scanLoop,
    L2Scan.scanBody, L2Scan.dispatch, L2Scan.phase3, L2Accept.accept, L2Parts.setupA,
    L2Parts.setupB, L2Fill.fillLoop, L2Fill.fillBody, L2OrdLoop.ordLoop, L2OrdLoop.ordBody,
    L2OrdLoop.calcO, L2Ord.calcSec, L2Ord.calcTail, L2PairLoop.pairLoop, L2PairLoop.pairBody,
    L2Pair.calcP, L2Pair.headP, L2Pair.litPart, L2Pair.clA, L2Pair.clB, L2Pair.clC,
    L2Parts.emitVar, L2Parts.emitLit, L2Print.recO, L2Print.recP, L2Print.emitAt,
    L2Print.rawStep, L2Print.bumpStep, L2Reject.reject, EmitNat.emitNat, EmitNat.sizeLoop,
    EmitNat.sizeBody, EmitNat.onesLoop, EmitNat.onesBody, EmitNat.digLoop, EmitNat.digBody,
    layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

open Lax391470Proofs.CnfScan Lax391470Proofs.L2ScanModel Lax391470Proofs.Bits
open Lax391470.SatConstruction

/-- The largest entry. -/
def Mx (y : List ℕ) : ℕ := y.foldr max 0

lemma le_Mx {y : List ℕ} {v : ℕ} (hv : v ∈ y) : v ≤ Mx y := by
  induction y with
  | nil => cases hv
  | cons a t ih =>
    simp only [Mx, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp hv with rfl | h
    · omega
    · have := ih h; omega

/-- The value bound of an input. -/
def Bd (y : List ℕ) : ℕ := bnd p q (y.length + 4) (Mx y)

lemma dim_of_accept (y : List ℕ) (h4 : (run init (bitsOf y)).ph = 4) :
    Dim (run init (bitsOf y)).done (y.length + 4) := by
  have hc := cur_nil h4
  have hflat : flat (run init (bitsOf y)) = lits (run init (bitsOf y)).done := by
    simp [flat, hc]
  have h := size_run (bitsOf y)
  have hl : (bitsOf y).length = y.length := by simp [bitsOf]
  rw [hl] at h
  simp only [L2ScanModel.size, hflat] at h
  have hnv : numVars (run init (bitsOf y)).done = mxOf (lits (run init (bitsOf y)).done) := rfl
  exact ⟨by rw [hnv]; omega, by omega, by omega⟩

/-- The cost of the program on an input. -/
def Kfull (y : List ℕ) : ℕ :=
  Kmain y (y.length + 4) (8 * (y.length + 4))
    ((y.length + 4) + 2 * ((y.length + 4) * (y.length + 4))) (Bd p q y).size

theorem run_main (y : List ℕ) :
    ∃ σ', Run (Bd p q y) (main p q)
        (initEnv (ext y.length (2 * ((y.length + 4) * (y.length + 4)))
          (4 * ((y.length + 4) * (y.length + 4)))) (y.length :: y)) σ' (Kfull p q y) ∧
      σ'.out = L2Model.red p q y := by
  have hX : y.length + 4 ≤ (y.length + 4) * (y.length + 4) := Nat.le_mul_of_pos_left _ (by omega)
  have hU : (y.length + 4) * (y.length + 4) ≤ (p + q + 1) * ((y.length + 4) * (y.length + 4)) :=
    Nat.le_mul_of_pos_left _ (by omega)
  refine main_spec (B := Bd p q y) p q y _ _ _ _ _ (fun v hv => ?_) ?_
    (fun h4 => nums p q _ _ _ (dim_of_accept y h4)) (fun h4 => ?_)
  · have := le_Mx hv; unfold Bd bnd; omega
  · unfold Bd bnd; omega
  · obtain ⟨d1, d2, d3⟩ := dim_of_accept y h4
    have hP := (prods p q _ _ ⟨d1, d2, d3⟩).hnm
    refine ⟨by omega, by unfold numOrdinary numClauses; omega, ?_⟩
    unfold Lax391470.SatConstruction.numPairs numClauses
    have : (2 * numVars (run init (bitsOf y)).done - 1) * (run init (bitsOf y)).done.length ≤
        2 * numVars (run init (bitsOf y)).done * (run init (bitsOf y)).done.length :=
      Nat.mul_le_mul_right _ (by omega)
    omega

end Lax391470Proofs.L2Ram
