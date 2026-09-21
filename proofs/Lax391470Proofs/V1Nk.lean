import Lax391470Proofs.AuxNk
import Lax391470Proofs.V1Format

/-!
The format of an instance followed by a schedule, as a command of the tokenizer.
-/

namespace Lax391470Proofs.V1Nk

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.TokModel Lax391470Proofs.TokScan Lax391470Proofs.TokProg
open Lax391470Proofs.V1Format
open Lax391470Proofs.AuxNk (sub mul div)

def nk2 : Com :=
  .ite (.lt (V "T") (.lit 1)) (set "kind" 0)
    (.seq (.assign "j" (sub (V "T") (.lit 1)))
      (.seq (.assign "n5" (mul (.lit 5) (.get "TK" (.lit 0))))
        (.ite (.lt (V "j") (V "n5"))
          (.seq (.assign "mm" (sub (V "j") (mul (div (V "j") (.lit 5)) (.lit 5))))
            (.ite (.eq (V "mm") (.lit 0)) (set "kind" 1)
              (.ite (.eq (V "mm") (.lit 2)) (set "kind" 1) (set "kind" 0))))
          (.ite (.lt (V "j") (add (V "n5") (mul (.lit 2) (.get "TK" (.lit 0)))))
            (.seq (.assign "mm" (sub (V "j") (V "n5")))
              (.ite (.eq (sub (V "mm") (mul (div (V "mm") (.lit 2)) (.lit 2))) (.lit 0))
                (set "kind" 1) (set "kind" 0)))
            (set "kind" 2)))))

/-- The code of what is expected after `Tn` tokens, the count being `n`. -/
def kindCode (Tn n : ℕ) : ℕ := if Tn < 1 then 0 else kcode (kind2 n (Tn - 1))

variable {B : ℕ}

theorem nk2_flat (Tn n : ℕ) (hB : 7 * n + Tn + 8 < B) :
    Spec B (fun σ => σ.vars "T" = Tn ∧ (σ.arrs "TK").getD 0 0 = n ∧
        (1 ≤ Tn → 1 ≤ (σ.arrs "TK").length)) nk2
      (fun σ σ' => σ'.vars "kind" = kindCode Tn n ∧
        (∀ y ∉ ["kind", "j", "n5", "mm"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧
        σ'.out = σ.out ∧ σ'.inp = σ.inp) 90 := by
  run_vcg
  all_goals have hT := ‹σ.vars "T" = Tn›
  all_goals have h0 := ‹(σ.arrs "TK").getD 0 0 = n›
  all_goals have hl := ‹1 ≤ Tn → 1 ≤ (σ.arrs "TK").length›
  all_goals try simp [Env.setVar] at *
  all_goals try simp only [h0, hT] at *
  all_goals first
    | omega
    | (refine ⟨?_, fun y a b c d => by simp [a, b, c, d]⟩
       have k0 : kcode .num = 0 := rfl
       have k1 : kcode .bit = 1 := rfl
       have k2 : kcode .done = 2 := rfl
       unfold kindCode kind2
       split_ifs <;> omega)

theorem setKind0_spec (hB : 2 < B) :
    Spec B (fun _ => True) (set "kind" 0)
      (fun σ σ' => σ'.vars "kind" = 0 ∧
        (∀ y ∉ ["kind", "j", "n5", "mm"], σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp) 2 := by
  run_vcg
  · refine ⟨by simp [Env.setVar], fun y hy => ?_, by simp [Env.setVar], by simp [Env.setVar],
      by simp [Env.setVar]⟩
    have : y ≠ "kind" := fun h => hy (by simp [h])
    simp [Env.setVar, this]

/-- **The command meets the contract of the tokenizer.** -/
theorem nk2_spec (Bt cap : ℕ) (hB : 8 * Bt + cap + 8 < B) : NkSpec B Bt E2 cap nk2 90 := by
  intro toks hfol hcap
  have frame : ∀ {σ σ' : Env}, (∀ y ∉ ["kind", "j", "n5", "mm"], σ'.vars y = σ.vars y) →
      ∀ y ∈ scanVars, σ'.vars y = σ.vars y := fun h y hy => h y (by
    simp only [scanVars, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  rcases toks with _ | ⟨a, rest⟩
  · rintro σ ⟨⟨hT, -⟩, -⟩
    obtain ⟨σ', r, q1, q2, q3, q4, q5⟩ :=
      (ite_true_spec (B := B) (P := fun σ => σ.vars "T" = 0)
        (b := .lt (V "T") (.lit 1)) (d := _)
        (fun σ h => by
          rw [evalB_condLt (evalB_var (by rw [h]; omega)) (evalB_lit (by omega)), h]
          simp)
        ((setKind0_spec (B := B) (by omega)).pre (fun _ _ => trivial))) σ (by simpa using hT)
    exact ⟨σ', r.mono (by simp [Cond.size, Expr.size]), by rw [q1]; rfl, frame q2, q3, q4, q5⟩
  · have ha : a.kind = .num := by simpa [E2] using hfol 0 (by simp)
    obtain ⟨n, rfl⟩ : ∃ n, a = .num n := ⟨_, AuxFormat.tok_of_num ha⟩
    intro σ ⟨⟨hT, hTK⟩, hsm⟩
    have hn : n < Bt := hsm (.num n) (by simp)
    have hlen : 1 ≤ (σ.arrs "TK").length := by
      have := congrArg List.length hTK
      simp at this; omega
    have g0 : (σ.arrs "TK").getD 0 0 = n := by
      have := congrArg (fun l => l.getD 0 0) hTK
      simpa [List.getD_eq_getElem?_getD, List.getElem?_take, Tok.val] using this
    simp only [List.length_cons] at hcap hT
    obtain ⟨σ', r, q1, q2, q3, q4, q5⟩ := nk2_flat (B := B) (rest.length + 1) n (by omega) σ
      ⟨by rw [hT], g0, fun _ => hlen⟩
    refine ⟨σ', r, ?_, frame q2, q3, q4, q5⟩
    rw [q1, E2_cons]
    simp [kindCode]

end Lax391470Proofs.V1Nk
