import Lax391470Proofs.L1Print
import Lax391470Proofs.L1Agree

/-!
The accepting branch of Lemma 1's reduction: from the tokens to the output.
-/

namespace Lax391470Proofs.L1Accept

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.Bits Lax391470Proofs.TokModel Lax391470Proofs.TokProg
open Lax391470Proofs.AuxFormat Lax391470Proofs.L1Model Lax391470Proofs.L1Ordered
open Lax391470Proofs.L1Check Lax391470Proofs.L1Parts Lax391470Proofs.L1Print
open Lax391470Proofs.L1Agree Lax391470Proofs.L1Rows

variable {B : ℕ} (p q : ℕ)

def acceptCom : Com :=
  .seq setup1 (.seq checkLoop
    (.ite (.eq (.var "ok") (.lit 1)) (printPart p q) (rejectCom p)))

/-- The shape of a conforming stream: its length in terms of its two counts. -/
lemma conf_length {toks : List Tok} (hc : Conforms EA toks) :
    toks.length = 2 + 3 * (toks.map Tok.val).getD 0 0 + 4 * (toks.map Tok.val).getD 1 0 := by
  have h := toksOf_ofToks hc
  have e : toks.map Tok.val = tkOf (ofToks toks) := by unfold tkOf; rw [h]
  rw [e, tk_zero, tk_one, ← toksOf_length, h]

lemma wvars_check : checkLoop.wvars =
    ["i", "e0", "e1", "e2", "e3", "ok", "ok", "ok", "f0", "f2", "ok", "ok", "i"] := by
  simp [checkLoop, checkBody, load, load2, chk, Com.wvars]

lemma warrs_check : checkLoop.warrs = [] := by
  simp [checkLoop, checkBody, load, load2, chk, Com.warrs]

/-- The cost of the accepting branch. -/
def Kacc1 (Sz n N : ℕ) : ℕ :=
  30 + (124 * N + 6) + 4 + Kprint Sz n N + (4 * (48 * Sz + 50) + 4)

theorem accept_spec (toks : List Tok) (hconf : Conforms EA toks) (Bt Sz : ℕ)
    (hsmall : ∀ t ∈ toks, Tok.val t < Bt) (hBt : Bt + 4 ≤ B)
    (hB : 4 * toks.length + (p + 2 * q) * ((toks.map Tok.val).getD 1 0 + 2) + 16 < B)
    (hp : p + 8 < B) (hs : ∀ v, v + 4 < B → v.size ≤ Sz) :
    Spec B (fun σ => TokRefl toks σ ∧ toks.length ≤ (σ.arrs "TK").length ∧ σ.out = [])
      (acceptCom p q)
      (fun _ σ' => σ'.out = if OrdOK (toks.map Tok.val) then outBits p q (toks.map Tok.val)
        else L1Red.blockedBits p)
      (Kacc1 Sz ((toks.map Tok.val).getD 0 0) ((toks.map Tok.val).getD 1 0)) := by
  intro σ ⟨⟨hTv, hTK⟩, hlen, hout⟩
  set tk := toks.map Tok.val with htk
  set n := tk.getD 0 0 with hn
  set N := tk.getD 1 0 with hN
  have hT : toks.length = 2 + 3 * n + 4 * N := conf_length hconf
  set arr := σ.arrs "TK" with harr
  have g : ∀ k < toks.length, arr.getD k 0 = tk.getD k 0 := fun k hk => by
    rw [← hTK, getD_take arr toks.length hk]
  have tkB : ∀ k < toks.length, tk.getD k 0 < Bt := fun k hk => by
    have hk' : k < tk.length := by simpa [htk] using hk
    rw [List.getD_eq_getElem _ _ hk']
    simp only [htk, List.getElem_map]
    exact hsmall _ (List.getElem_mem _)
  have a0 : arr.getD 0 0 = n := g 0 (by omega)
  have a1 : arr.getD 1 0 = N := g 1 (by omega)
  have hnB : n < Bt := tkB 0 (by omega)
  -- the counts
  obtain ⟨σ1, r1, s1, s2, s3, s4, s5, sv, sa, so⟩ := setup1_spec (B := B) arr (by omega)
    (by rw [a0, a1]; omega) σ rfl
  rw [a0] at s1 s3 s5; rw [a1] at s2 s5
  -- the conditions
  obtain ⟨σ2, r2, ⟨⟨c1, c2, c3, -, c5, c6⟩, ci⟩, fv, fa, -, -⟩ :=
    (checkLoop_spec (B := B) arr (2 + 3 * n) N [] (by omega) (by omega)
      (fun k hk => by have := tkB k (by omega); rw [g k (by omega)]; omega)).frame σ1
    ⟨by simp only [Env.setVar]; rw [sa], by simpa [Env.setVar] using s3,
      by simpa [Env.setVar] using s2, by simp [Env.setVar],
      by simp [Env.setVar, okv, s4], by simp only [Env.setVar]; rw [so, hout]⟩
  rw [ci] at c5
  have hev : (Cond.eq (.var "ok") (.lit 1)).evalB B σ2 = some (σ2.vars "ok" == 1) :=
    evalB_condEq (evalB_var (by rw [c5]; have := okv_le arr (2 + 3 * n) N N; omega))
      (evalB_lit (by omega))
  have hiff := okv_iff arr n N toks.length hT (by rw [hTK]) (by rw [hTK])
  rw [hTK] at hiff
  by_cases hord : OrdOK tk
  · -- print the instance
    have hok1 : σ2.vars "ok" = 1 := by rw [c5]; exact hiff.mpr hord
    obtain ⟨σ3, r3, o3⟩ := printPart_spec (B := B) p q arr n N toks.length Sz [] hT
      ⟨hlen, fun k hk => by
        have := tkB k hk
        rw [g k hk]; exact ⟨by omega, hs _ (by omega)⟩⟩ a0 (by omega) hs σ2
      ⟨c1, by rw [fv "n" (by simp [wvars_check])]; exact s1, c3, c2,
        by rw [fv "jobs" (by simp [wvars_check])]; exact s5, c6⟩
    have rite := Run.ite_true (d := rejectCom p) (by rw [hev, hok1]; rfl) r3
    refine ⟨σ3, (r1.seq (r2.seq rite)).mono (by unfold Kacc1; simp [Cond.size, Expr.size]; omega),
      ?_⟩
    show σ3.out = _
    rw [o3, if_pos hord]
    have e1 : (List.range n).flatMap (ordRow p q arr) =
        (List.range n).flatMap (ordRow p q tk) := List.flatMap_congr fun i hi => by
      rw [← hTK]
      exact (ordRow_agree p q arr n N toks.length hT (List.mem_range.mp hi)).symm
    have e2 : (List.range N).flatMap (quadRow p q arr n) =
        (List.range N).flatMap (quadRow p q tk n) := List.flatMap_congr fun i hi => by
      rw [← hTK]
      exact (quadRow_agree p q arr n N toks.length hT (List.mem_range.mp hi)).symm
    rw [e1, e2, List.nil_append]
    rfl
  · -- the fixed infeasible instance
    have hok0 : σ2.vars "ok" ≠ 1 := by rw [c5]; exact fun h => hord (hiff.mp h)
    obtain ⟨σ3, r3, o3⟩ := rejectCom_spec (B := B) p Sz hp hs σ2 trivial
    have rite := Run.ite_false (c := printPart p q) (by rw [hev]; simp [hok0]) r3
    refine ⟨σ3, (r1.seq (r2.seq rite)).mono (by unfold Kacc1; simp [Cond.size, Expr.size]; omega),
      ?_⟩
    show σ3.out = _
    rw [o3, c6, if_neg hord, List.nil_append]

end Lax391470Proofs.L1Accept
