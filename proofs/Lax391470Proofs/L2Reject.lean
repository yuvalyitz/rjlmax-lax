import Lax391470Proofs.L2Parts
import Lax391470Proofs.L2Model

/-!
The rejecting branch: the zeros and ones of the fixed unsolvable instance.
-/

namespace Lax391470Proofs.L2Reject

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.Bits Lax391470Proofs.L2Parts

def reject : Com :=
  .seq (emitLit 1) (.seq (emitLit 0) (.seq (emitLit 0) (.seq (emitLit 0) (.write (.lit 0)))))

variable {B : ℕ}

theorem reject_spec (hB : 8 < B) :
    Spec B (fun σ => σ.out = []) reject (fun _ σ' => σ'.out = L2Model.blockedBits) 400 := by
  intro σ0 h0
  have s1 : (1 : ℕ).size ≤ 1 := by decide
  have s0 : (0 : ℕ).size ≤ 1 := by decide
  obtain ⟨σ1, r1, o1, -, -⟩ := emitLit_spec (B := B) 1 1 (by omega) s1 σ0 trivial
  obtain ⟨σ2, r2, o2, -, -⟩ := emitLit_spec (B := B) 0 1 (by omega) s0 σ1 trivial
  obtain ⟨σ3, r3, o3, -, -⟩ := emitLit_spec (B := B) 0 1 (by omega) s0 σ2 trivial
  obtain ⟨σ4, r4, o4, -, -⟩ := emitLit_spec (B := B) 0 1 (by omega) s0 σ3 trivial
  have r5 := Run.write (B := B) (σ := σ4) (e := .lit 0) (v := 0) (evalB_lit (by omega))
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono (by simp [Expr.size]), ?_⟩
  show σ4.out ++ [0] = L2Model.blockedBits
  rw [o4, o3, o2, o1, h0]
  simp [L2Model.blockedBits]

end Lax391470Proofs.L2Reject
