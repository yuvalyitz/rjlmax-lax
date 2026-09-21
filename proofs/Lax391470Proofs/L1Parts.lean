import Lax391470Proofs.OutSteps
import Lax391470Proofs.L1Red

/-!
The small commands of Lemma 1's reduction.
-/

namespace Lax391470Proofs.L1Parts

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.Bits Lax391470Proofs.OutSteps Lax391470Proofs.L2Parts

variable {B : ℕ} (p : ℕ)

/-- Hand the input length to the tokenizer and put its scalars in their initial state. -/
def initS : Com :=
  .seq (.assign "Ln" (V "L")) (.seq (.assign "L" (.lit 0)) (.assign "pw" (.lit 1)))

theorem initS_spec (hB : 2 < B) :
    Spec B (fun σ => σ.vars "L" < B) initS
      (fun σ σ' => σ'.vars "Ln" = σ.vars "L" ∧ σ'.vars "L" = 0 ∧ σ'.vars "pw" = 1 ∧
        (∀ y ∉ ["Ln", "L", "pw"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
        σ'.inp = σ.inp) 8 := by
  run_vcg
  · refine ⟨by simp [Env.setVar], by simp [Env.setVar], by simp [Env.setVar], fun y hy => ?_,
      by simp [Env.setVar], by simp [Env.setVar], by simp [Env.setVar]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [Env.setVar, hy.1, hy.2.1, hy.2.2]

/-- Read the two counts, the base of the pairs, and raise the flag. -/
def setup1 : Com :=
  .seq (.assign "n" (.get "TK" (.lit 0))) (.seq (.assign "N" (.get "TK" (.lit 1)))
    (.seq (.assign "b3" (.bin .add (.lit 2) (.bin .mul (.lit 3) (V "n"))))
      (.seq (.assign "ok" (.lit 1))
        (.assign "jobs" (.bin .add (V "n") (.bin .mul (.lit 5) (V "N")))))))

theorem setup1_spec (arr : List ℕ) (hlen : 2 ≤ arr.length)
    (hB : 3 * arr.getD 0 0 + 5 * arr.getD 1 0 + 8 < B) :
    Spec B (fun σ => σ.arrs "TK" = arr) setup1
      (fun σ σ' => σ'.vars "n" = arr.getD 0 0 ∧ σ'.vars "N" = arr.getD 1 0 ∧
        σ'.vars "b3" = 2 + 3 * arr.getD 0 0 ∧ σ'.vars "ok" = 1 ∧
        σ'.vars "jobs" = arr.getD 0 0 + 5 * arr.getD 1 0 ∧
        (∀ y ∉ ["n", "N", "b3", "ok", "jobs"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧
        σ'.out = σ.out) 30 := by
  run_vcg
  all_goals have hT := ‹σ.arrs "TK" = arr›
  all_goals try simp [Env.setVar, hT] at *
  all_goals first
    | omega
    | (intro y h1 h2 h3 h4 h5; simp [h1, h2, h3, h4, h5])

/-- The zeros and ones of the fixed infeasible instance. -/
def rejectCom : Com :=
  .seq (emitLit 1) (.seq (.write (.lit 0)) (.seq (emitLit 0) (.seq (.write (.lit 0))
    (.seq (emitLit 0) (emitLit p)))))

theorem rejectCom_spec (Sz : ℕ) (hp : p + 8 < B) (hs : ∀ v, v + 4 < B → v.size ≤ Sz) :
    Spec B (fun _ => True) (rejectCom p)
      (fun σ σ' => σ'.out = σ.out ++ L1Red.blockedBits p) (4 * (48 * Sz + 50) + 4) := by
  have h := ((oEmitLit (B := B) 1 Sz (by omega) (hs 1 (by omega))).seq
    ((oWrite (B := B) 0 (by omega)).seq ((oEmitLit (B := B) 0 Sz (by omega) (hs 0 (by omega))).seq
    ((oWrite (B := B) 0 (by omega)).seq ((oEmitLit (B := B) 0 Sz (by omega) (hs 0 (by omega))).seq
    (oEmitLit (B := B) p Sz (by omega) (hs p (by omega))))))))
  intro σ _
  obtain ⟨σ', r, o, -⟩ := h σ ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  refine ⟨σ', r.mono (by omega), ?_⟩
  show σ'.out = σ.out ++ L1Red.blockedBits p
  rw [o]; simp [L1Red.blockedBits, List.append_assoc]

end Lax391470Proofs.L1Parts
