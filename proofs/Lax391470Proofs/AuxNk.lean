import Lax391470Proofs.TokLoop
import Lax391470Proofs.AuxFormat

/-!
What the format of the auxiliary problem expects next, as a command.
-/

namespace Lax391470Proofs.AuxNk

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.TokModel Lax391470Proofs.TokScan Lax391470Proofs.TokProg
open Lax391470Proofs.AuxFormat

abbrev sub (e f : Expr) : Expr := .bin .sub e f
abbrev mul (e f : Expr) : Expr := .bin .mul e f
abbrev div (e f : Expr) : Expr := .bin .div e f

def nkA : Com :=
  .ite (.lt (V "T") (.lit 2)) (set "kind" 0)
    (.seq (.assign "j" (sub (V "T") (.lit 2)))
      (.seq (.assign "n3" (mul (.lit 3) (.get "TK" (.lit 0))))
        (.ite (.lt (V "j") (V "n3"))
          (.ite (.eq (sub (V "j") (mul (div (V "j") (.lit 3)) (.lit 3))) (.lit 2))
            (set "kind" 1) (set "kind" 0))
          (.ite (.lt (V "j") (add (V "n3") (mul (.lit 4) (.get "TK" (.lit 1)))))
            (set "kind" 0) (set "kind" 2)))))

/-- The code of what is expected after `Tn` tokens, the counts being `n` and `N`. -/
def kindCode (Tn n N : ℕ) : ℕ := if Tn < 2 then 0 else kcode (kindAt n N (Tn - 2))

variable {B : ℕ}

theorem nkA_flat (Tn n N : ℕ) (hB : 3 * n + 4 * N + Tn + 8 < B) :
    Spec B (fun σ => σ.vars "T" = Tn ∧ (σ.arrs "TK").getD 0 0 = n ∧
        (σ.arrs "TK").getD 1 0 = N ∧ (2 ≤ Tn → 2 ≤ (σ.arrs "TK").length)) nkA
      (fun σ σ' => σ'.vars "kind" = kindCode Tn n N ∧
        (∀ y ∉ ["kind", "j", "n3"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧
        σ'.out = σ.out ∧ σ'.inp = σ.inp) 60 := by
  run_vcg
  all_goals have hT := ‹σ.vars "T" = Tn›
  all_goals have h0 := ‹(σ.arrs "TK").getD 0 0 = n›
  all_goals have h1 := ‹(σ.arrs "TK").getD 1 0 = N›
  all_goals have hl := ‹2 ≤ Tn → 2 ≤ (σ.arrs "TK").length›
  all_goals try simp [Env.setVar] at *
  all_goals try simp only [h0, h1, hT] at *
  all_goals first
    | omega
    | (refine ⟨?_, fun y a b c => by simp [a, b, c]⟩
       have k0 : kcode .num = 0 := rfl
       have k1 : kcode .bit = 1 := rfl
       have k2 : kcode .done = 2 := rfl
       unfold kindCode kindAt
       split_ifs <;> omega)

theorem setKind0_spec (hB : 2 < B) :
    Spec B (fun _ => True) (set "kind" 0)
      (fun σ σ' => σ'.vars "kind" = 0 ∧ (∀ y ∉ ["kind", "j", "n3"], σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp) 2 := by
  run_vcg
  · refine ⟨by simp [Env.setVar], fun y hy => ?_, by simp [Env.setVar], by simp [Env.setVar],
      by simp [Env.setVar]⟩
    have : y ≠ "kind" := fun h => hy (by simp [h])
    simp [Env.setVar, this]

/-- **The command meets the contract of the tokenizer.** -/
theorem nkA_spec (Bt cap : ℕ) (hB : 8 * Bt + cap + 8 < B) : NkSpec B Bt EA cap nkA 60 := by
  intro toks hfol hcap
  have frame : ∀ {σ σ' : Env}, (∀ y ∉ ["kind", "j", "n3"], σ'.vars y = σ.vars y) →
      ∀ y ∈ scanVars, σ'.vars y = σ.vars y := fun h y hy => h y (by
    simp only [scanVars, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  by_cases h2 : toks.length < 2
  · -- fewer than two tokens: a count is expected
    have hE : EA toks = .num := by
      rcases toks with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · rfl
      · cases a <;> rfl
      · simp at h2
    rintro σ ⟨⟨hT, -⟩, -⟩
    obtain ⟨σ', r, q1, q2, q3, q4, q5⟩ :=
      (ite_true_spec (B := B) (P := fun σ => σ.vars "T" = toks.length)
        (b := .lt (V "T") (.lit 2)) (d := _)
        (fun σ h => by
          rw [evalB_condLt (evalB_var (by rw [h]; omega)) (evalB_lit (by omega)), h]
          simp [h2])
        ((setKind0_spec (B := B) (by omega)).pre (fun _ _ => trivial))) σ hT
    exact ⟨σ', r.mono (by simp [Cond.size, Expr.size]), by rw [q1, hE]; rfl, frame q2, q3, q4, q5⟩
  · -- the counts are known
    rcases toks with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at h2
    · simp at h2
    have ha : a.kind = .num := by simpa [EA] using hfol 0 (by simp)
    have hb : b.kind = .num := by
      have := hfol 1 (by simp)
      simpa [EA] using this
    obtain ⟨n, rfl⟩ : ∃ n, a = .num n := ⟨_, tok_of_num ha⟩
    obtain ⟨N, rfl⟩ : ∃ N, b = .num N := ⟨_, tok_of_num hb⟩
    intro σ ⟨⟨hT, hTK⟩, hsm⟩
    have hn : n < Bt := hsm (.num n) (by simp)
    have hN : N < Bt := hsm (.num N) (by simp)
    have hlen : 2 ≤ (σ.arrs "TK").length := by
      have := congrArg List.length hTK
      simp at this; omega
    have g0 : (σ.arrs "TK").getD 0 0 = n := by
      have := congrArg (fun l => l.getD 0 0) hTK
      simpa [List.getD_eq_getElem?_getD, List.getElem?_take, Tok.val] using this
    have g1 : (σ.arrs "TK").getD 1 0 = N := by
      have := congrArg (fun l => l.getD 1 0) hTK
      simpa [List.getD_eq_getElem?_getD, List.getElem?_take, Tok.val] using this
    simp only [List.length_cons] at hcap hT
    obtain ⟨σ', r, q1, q2, q3, q4, q5⟩ := nkA_flat (B := B) (rest.length + 2) n N (by omega) σ
      ⟨by rw [hT], g0, g1, fun _ => hlen⟩
    refine ⟨σ', r, ?_, frame q2, q3, q4, q5⟩
    rw [q1, EA_cons]
    simp [kindCode]

end Lax391470Proofs.AuxNk
