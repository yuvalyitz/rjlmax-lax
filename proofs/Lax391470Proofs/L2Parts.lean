import Lax391470Proofs.L2Print

/-!
The small commands of the reduction: the dimensions of the construction, and the codes of
a scalar and of a constant.
-/

namespace Lax391470Proofs.L2Parts

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.Bits Lax391470Proofs.EmitNat Lax391470Proofs.L2Print

abbrev add (e f : Expr) : Expr := .bin .add e f
abbrev sub (e f : Expr) : Expr := .bin .sub e f
abbrev mul (e f : Expr) : Expr := .bin .mul e f

variable {B : ℕ}

/-- Write the code of the scalar `x`. -/
def emitVar (x : String) : Com := .seq (.assign "v" (.var x)) emitNat

theorem emitVar_spec (x : String) (Sz : ℕ) :
    Spec B (fun σ => σ.vars x + 4 < B ∧ (σ.vars x).size ≤ Sz) (emitVar x)
      (fun σ σ' => σ'.out = σ.out ++ bitsNat (σ.vars x) ∧
        (∀ y ∉ ["v", "s", "u", "i2"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs)
      (48 * Sz + 50) := by
  run_vcg [(emitNat_spec (B := B) Sz).frame]
  · obtain ⟨hout, hfv, hfa, -, -⟩ := ‹_ ∧ (∀ y ∉ emitNat.wvars, _) ∧ _›
    refine ⟨by simpa [Env.setVar] using hout, fun y hy => ?_, ?_⟩
    · have h1 := hfv y (by
        rw [wvars_emitNat]; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy ⊢
        tauto)
      have hyv : y ≠ "v" := fun h => hy (by simp [h])
      simpa [Env.setVar, hyv] using h1
    · funext b
      have := hfa b (by simp [warrs_emitNat])
      simpa [Env.setVar] using this
  all_goals first
    | omega
    | (simp only [Env.setVar, if_true]; exact ⟨‹_›, ‹_›⟩)

/-- Write the code of the constant `n`. -/
def emitLit (n : ℕ) : Com := .seq (.assign "v" (.lit n)) emitNat

theorem emitLit_spec (n Sz : ℕ) (hn : n + 4 < B) (hs : n.size ≤ Sz) :
    Spec B (fun _ => True) (emitLit n)
      (fun σ σ' => σ'.out = σ.out ++ bitsNat n ∧
        (∀ y ∉ ["v", "s", "u", "i2"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs)
      (48 * Sz + 50) := by
  run_vcg [(emitNat_spec (B := B) Sz).frame]
  · obtain ⟨hout, hfv, hfa, -, -⟩ := ‹_ ∧ (∀ y ∉ emitNat.wvars, _) ∧ _›
    refine ⟨by simpa [Env.setVar] using hout, fun y hy => ?_, ?_⟩
    · have h1 := hfv y (by
        rw [wvars_emitNat]; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy ⊢
        tauto)
      have hyv : y ≠ "v" := fun h => hy (by simp [h])
      simpa [Env.setVar, hyv] using h1
    · funext b
      have := hfa b (by simp [warrs_emitNat])
      simpa [Env.setVar] using this
  all_goals first
    | omega
    | (simp only [Env.setVar, if_true]; exact ⟨hn, hs⟩)

variable (p q : ℕ)

def setupA : Com :=
  .seq (.assign "m" (.var "C"))
  (.seq (.assign "nn" (.var "mx"))
  (.seq (.assign "S" (add (add (add (.lit (p + 2 * q)) (mul (.var "m") (.lit (p + q)))) (.lit 1))
      (.lit q)))
    (.assign "n6" (mul (.lit 6) (.var "nn")))))

theorem setupA_spec :
    Spec B (fun σ => p + 2 * q + σ.vars "C" * (p + q) + 1 + q + 6 * σ.vars "mx" +
        σ.vars "C" + 8 < B) (setupA p q)
      (fun σ σ' => σ'.vars "m" = σ.vars "C" ∧ σ'.vars "nn" = σ.vars "mx" ∧
        σ'.vars "S" = p + 2 * q + σ.vars "C" * (p + q) + 1 + q ∧
        σ'.vars "n6" = 6 * σ.vars "mx") 40 := by
  run_vcg
  all_goals simp [Env.setVar] at *

def setupB : Com :=
  .seq (.assign "n6m" (add (.var "n6") (.var "m")))
  (.seq (.assign "NO" (add (.var "n6m") (.var "m")))
  (.seq (.assign "g" (add (.lit 1) (mul (.lit 2) (.var "m"))))
    (.assign "NP" (add (.var "nn") (mul (sub (mul (.lit 2) (.var "nn")) (.lit 1)) (.var "m"))))))

theorem setupB_spec :
    Spec B (fun σ => σ.vars "n6" + 2 * σ.vars "m" + 8 < B ∧
        σ.vars "nn" + (2 * σ.vars "nn" - 1) * σ.vars "m" + 2 * σ.vars "nn" + 8 < B) setupB
      (fun σ σ' => σ'.vars "n6m" = σ.vars "n6" + σ.vars "m" ∧
        σ'.vars "NO" = σ.vars "n6" + σ.vars "m" + σ.vars "m" ∧
        σ'.vars "g" = 1 + 2 * σ.vars "m" ∧
        σ'.vars "NP" = σ.vars "nn" + (2 * σ.vars "nn" - 1) * σ.vars "m") 40 := by
  run_vcg
  all_goals simp [Env.setVar] at *

end Lax391470Proofs.L2Parts
