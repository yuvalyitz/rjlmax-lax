import Lax391470Proofs.V1Parts

/-!
The boundary test of the verifier of `AUX p q`.
-/

namespace Lax391470Proofs.V2Parts

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.L1Check (V add)
open Lax391470Proofs.AuxNk (mul)

variable {B : ℕ}

/-- Did the first scan stop exactly at the end of an instance? -/
def bcheck : Com :=
  .seq (.assign "okx" (.lit 0))
    (.ite (.eq (V "ph") (.lit 0))
      (.ite (.eq (V "L") (.lit 0))
        (.ite (.lt (V "T") (.lit 2)) .skip
          (.ite (.eq (V "T") (add (add (.lit 2) (mul (.lit 3) (.get "TK" (.lit 0))))
              (mul (.lit 4) (.get "TK" (.lit 1)))))
            (.assign "okx" (.lit 1)) .skip)) .skip) .skip)

theorem bcheck_flat (n N : ℕ) (hB : 3 * n + 4 * N + 8 < B) :
    Spec B (fun σ => σ.vars "ph" < B ∧ σ.vars "L" < B ∧ σ.vars "T" < B ∧
        (σ.arrs "TK").getD 0 0 = n ∧ (σ.arrs "TK").getD 1 0 = N ∧
        2 ≤ (σ.arrs "TK").length) bcheck
      (fun σ σ' => σ'.vars "okx" = (if σ.vars "ph" = 0 ∧ σ.vars "L" = 0 ∧
          σ.vars "T" = 2 + 3 * n + 4 * N then 1 else 0) ∧
        (∀ z, z ≠ "okx" → σ'.vars z = σ.vars z) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out) 50 := by
  run_vcg
  all_goals have e0 := ‹(σ.arrs "TK").getD 0 0 = n›
  all_goals have e1 := ‹(σ.arrs "TK").getD 1 0 = N›
  all_goals try simp [Env.setVar] at *
  all_goals try simp only [e0, e1] at *
  all_goals first
    | omega
    | (intro z hz)
    | ((repeat' constructor) <;> first
        | trivial
        | omega
        | (intro z hz; simp [hz])
       )

theorem bcheck_small (hB : 8 < B) :
    Spec B (fun σ => σ.vars "ph" < B ∧ σ.vars "L" < B ∧ σ.vars "T" < 2) bcheck
      (fun σ σ' => σ'.vars "okx" = 0 ∧
        (∀ z, z ≠ "okx" → σ'.vars z = σ.vars z) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out) 50 := by
  run_vcg
  all_goals try simp [Env.setVar] at *
  all_goals first
    | omega
    | (intro z hz; simp [hz])

end Lax391470Proofs.V2Parts
