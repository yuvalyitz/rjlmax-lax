import Lax391470Proofs.V1Accept
import Lax391470Proofs.V1Nk
import Lax391470Proofs.TokRun
import Lax391470Proofs.VUnpair

/-!
The small commands of the verifier of `TwoLengths p q` between its loops.
-/

namespace Lax391470Proofs.V1Parts

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.L1Check (V add)
open Lax391470Proofs.AuxNk (mul)

variable {B : ℕ}

def initU : Com :=
  .seq (.assign "Ln" (V "L")) (.seq (.assign "st" (.lit 0))
    (.seq (.assign "nx" (.lit 0)) (.assign "nw" (.lit 0))))

theorem initU_spec (l : ℕ) (hB : l + 2 < B) :
    Spec B (fun σ => σ.vars "L" = l) initU
      (fun σ σ' => σ'.vars "Ln" = l ∧ σ'.vars "st" = 0 ∧ σ'.vars "nx" = 0 ∧ σ'.vars "nw" = 0 ∧
        σ'.arrs = σ.arrs ∧ σ'.out = σ.out) 10 := by
  run_vcg
  all_goals try simp_all [Env.setVar]

/-- Did the first scan stop exactly at the end of an instance? -/
def bcheck : Com :=
  .seq (.assign "okx" (.lit 0))
    (.ite (.eq (V "ph") (.lit 0))
      (.ite (.eq (V "L") (.lit 0))
        (.ite (.eq (V "T") (.lit 0)) .skip
          (.ite (.eq (V "T") (add (.lit 1) (mul (.lit 5) (.get "TK" (.lit 0)))))
            (.assign "okx" (.lit 1)) .skip)) .skip) .skip)

theorem bcheck_flat (n : ℕ) (hB : 5 * n + 8 < B) :
    Spec B (fun σ => σ.vars "ph" < B ∧ σ.vars "L" < B ∧ σ.vars "T" < B ∧
        (σ.arrs "TK").getD 0 0 = n ∧ 1 ≤ (σ.arrs "TK").length) bcheck
      (fun σ σ' => σ'.vars "okx" = (if σ.vars "ph" = 0 ∧ σ.vars "L" = 0 ∧
          σ.vars "T" = 1 + 5 * n then 1 else 0) ∧
        (∀ z, z ≠ "okx" → σ'.vars z = σ.vars z) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out) 40 := by
  run_vcg
  all_goals have e0 := ‹(σ.arrs "TK").getD 0 0 = n›
  all_goals try simp [Env.setVar] at *
  all_goals try simp only [e0] at *
  all_goals first
    | omega
    | (refine ⟨?_, fun z hz => by simp [hz]⟩; simp_all; done)
    | (refine ⟨?_, fun z hz => by simp [hz]⟩; simp_all; omega)

theorem bcheck_zero (hB : 8 < B) :
    Spec B (fun σ => σ.vars "ph" < B ∧ σ.vars "L" < B ∧ σ.vars "T" = 0) bcheck
      (fun σ σ' => σ'.vars "okx" = 0 ∧
        (∀ z, z ≠ "okx" → σ'.vars z = σ.vars z) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out) 40 := by
  run_vcg
  all_goals have e0 := ‹σ.vars "T" = 0›
  all_goals try simp [Env.setVar] at *
  all_goals first
    | omega
    | (intro z hz; simp [hz])

/-- All the conditions before the arithmetic, in one flag. -/
def gate : Com :=
  .seq (.assign "g" (.lit 0))
    (.ite (.eq (V "st") (.lit 2))
      (.ite (.eq (V "ph") (.lit 0))
        (.ite (.eq (V "L") (.lit 0))
          (.ite (.eq (V "kind") (.lit 2))
            (.ite (.eq (V "okx") (.lit 1)) (.assign "g" (.lit 1)) .skip) .skip) .skip) .skip)
      .skip)

theorem gate_spec (hB : 8 < B) :
    Spec B (fun σ => σ.vars "st" < B ∧ σ.vars "ph" < B ∧ σ.vars "L" < B ∧ σ.vars "kind" < B ∧
        σ.vars "okx" < B) gate
      (fun σ σ' => σ'.vars "g" = (if σ.vars "st" = 2 ∧ σ.vars "ph" = 0 ∧ σ.vars "L" = 0 ∧
          σ.vars "kind" = 2 ∧ σ.vars "okx" = 1 then 1 else 0) ∧
        (∀ z, z ≠ "g" → σ'.vars z = σ.vars z) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out) 40 := by
  run_vcg
  all_goals try simp [Env.setVar] at *
  all_goals first
    | omega
    | (refine ⟨?_, fun z hz => by simp [hz]⟩; simp_all)

end Lax391470Proofs.V1Parts
