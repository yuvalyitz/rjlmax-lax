import Lax391470Proofs.V1Link
import Lax391470Proofs.VSum

/-!
The accepting branch of the verifier of `TwoLengths p q`: from conforming tokens to the
answer.
-/

namespace Lax391470Proofs.V1Accept

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.L1Check (V add)
open Lax391470Proofs.AuxNk (mul)
open Lax391470Proofs.V1Front Lax391470Proofs.VPairs Lax391470Proofs.VSum
open Lax391470Proofs.V1Sem Lax391470Proofs.V1Link Lax391470Proofs.Flag

def setupF : Com :=
  .seq (.assign "O" (.lit 0)) (.seq (.assign "nj" (.get "TK" (.lit 0)))
    (.seq (.assign "m5" (mul (.lit 5) (.get "TK" (.lit 0)))) (.assign "ok" (.lit 1))))

variable {B : ℕ}

open Classical

theorem setupF_spec (n : ℕ) (hB : 5 * n + 8 < B) :
    Spec B (fun σ => (σ.arrs "TK").getD 0 0 = n ∧ 1 ≤ (σ.arrs "TK").length) setupF
      (fun σ σ' => σ'.vars "O" = 0 ∧ σ'.vars "nj" = n ∧ σ'.vars "m5" = 5 * n ∧
        σ'.vars "ok" = 1 ∧ (∀ z ∉ ["O", "nj", "m5", "ok"], σ'.vars z = σ.vars z) ∧
        σ'.arrs = σ.arrs ∧ σ'.out = σ.out) 20 := by
  run_vcg
  all_goals have e0 := ‹(σ.arrs "TK").getD 0 0 = n›
  all_goals have e1 := ‹1 ≤ (σ.arrs "TK").length›
  all_goals try simp [Env.setVar] at *
  all_goals try simp only [e0] at *
  all_goals first
    | omega
    | (intro z h0 h1 h2 h3)
    | (refine ⟨by omega, fun z h0 h1 h2 h3 => by simp [h0, h1, h2, h3]⟩)

def acceptPart (p q : ℕ) : Com :=
  .seq setupF (.seq sumLoop (.seq (frontLoop p q) (.seq pairsLoop (.write (V "ok")))))

lemma sumTo_le (t : List ℕ) (Bt : ℕ) : ∀ Tn, Tn ≤ t.length → (∀ k < Tn, t.getD k 0 < Bt) →
    sumTo t Tn ≤ Tn * Bt
  | 0, _, _ => by simp [sumTo_zero]
  | Tn + 1, h, hb => by
    have ih := sumTo_le t Bt Tn (by omega) (fun k hk => hb k (by omega))
    have := hb Tn (by omega)
    rw [sumTo_succ (by omega), Nat.succ_mul]; omega

lemma flagTo_one (P : ℕ → Prop) [DecidablePred P] (k : ℕ) :
    flagTo P 1 k = if ∀ j < k, P j then 1 else 0 := by
  unfold flagTo; simp

/-- The cost of the accepting branch on `Tn` tokens and `n` jobs. -/
def Kacc (Tn n : ℕ) : ℕ :=
  20 + ((10 + 4) * Tn + 6) + ((210 + 4) * n + 6) + (((70 + 4) * n + 6 + 4 + 4) * n + 6) + 2

theorem accept_spec (p q : ℕ) (t : List ℕ) (Tn n Bt : ℕ) (h0 : t.getD 0 0 = n)
    (hTn : Tn = 1 + 7 * n) (hTl : Tn ≤ t.length) (htB : ∀ k < Tn, t.getD k 0 < Bt)
    (hB : Tn * Bt + 2 * Bt + 10 * Tn + 8 < B) (hp : p < B) (hq : q < B) :
    Spec B (fun σ => σ.arrs "TK" = t ∧ σ.vars "T" = Tn ∧ n ≤ (σ.arrs "TT").length ∧
        n ≤ (σ.arrs "PP").length ∧ σ.out = []) (acceptPart p q)
      (fun _ σ' => σ'.out = [if NZ t ∧ AV p q t ∧ OV t then 1 else 0]) (Kacc Tn n) := by
  intro σ ⟨hTK, hT, hlt, hlp, hout⟩
  have hsum := sumTo_le t Bt Tn hTl htB
  set Ov := sumTo t Tn with hOv
  -- set up
  obtain ⟨σ1, r1, s1, s2, s3, s4, k1, a1, o1⟩ := setupF_spec (B := B) n (by omega) σ
    ⟨by rw [hTK]; exact h0, by rw [hTK]; omega⟩
  have k1' : ∀ z, z ∉ ["O", "nj", "m5", "ok"] → σ1.vars z = σ.vars z := k1
  -- the offset
  obtain ⟨σ2, r2, ⟨⟨u1, u2, u3, u4, u5⟩, u6⟩, fv2, fa2, -, -⟩ :=
    (sumLoop_spec (B := B) t Tn [] hTl (by omega)).frame σ1
      ⟨by simp only [Env.setVar]; rw [a1]; exact hTK,
        by simp only [Env.setVar]; rw [if_neg (by decide), k1' _ (by decide)]; exact hT,
        by simp [Env.setVar],
        by simp only [Env.setVar, if_true]; rw [if_neg (by decide), s1, sumTo_zero],
        by simp only [Env.setVar]; rw [o1]; exact hout⟩
  rw [u6] at u4
  have w2 : ∀ z, z ∉ ["sk", "O"] → σ2.vars z = σ1.vars z := fun z hz => fv2 z (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    simp [sumLoop, sumBody, Com.wvars]; tauto)
  have arr2 : σ2.arrs = σ.arrs := by
    funext b
    rw [fa2 b (by simp [sumLoop, sumBody, Com.warrs]), a1]
  -- the jobs
  obtain ⟨σ3, r3, I3, f3⟩ := frontLoop_spec (B := B) p q t n Ov 1 Bt [] (by omega)
    (fun k hk => htB k (by omega)) (by omega) hp hq σ2
    ⟨by simp only [Env.setVar]; exact u1,
      by simp only [Env.setVar]; rw [if_neg (by decide), w2 _ (by decide)]; exact s2,
      by simp only [Env.setVar]; rw [if_neg (by decide), w2 _ (by decide)]; exact s3,
      by simp only [Env.setVar]; rw [if_neg (by decide)]; exact u4,
      by simp [Env.setVar],
      by simp only [Env.setVar, if_true]; rw [if_neg (by decide), w2 _ (by decide), s4,
        flagTo_zero _ _ (le_refl 1)],
      by simp only [Env.setVar]; rw [arr2]; exact hlt,
      by simp only [Env.setVar]; rw [arr2]; exact hlp,
      fun j' hj' => by simp [Env.setVar] at hj',
      by simp only [Env.setVar]; exact u5⟩
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ := I3
  rw [f3] at g6 g9
  -- the pairs
  have hval : ∀ k < n, (σ3.arrs "TT").getD k 0 + (σ3.arrs "PP").getD k 0 < B := fun k hk => by
    rw [(g9 k hk).1, (g9 k hk).2]
    have h1 := sh_le Ov (t.getD (1 + (5 * n + (2 * k + 0))) 0) (t.getD (1 + (5 * n + (2 * k + 1))) 0)
    have h2 := htB (1 + (5 * n + (2 * k + 1))) (by omega)
    have h3 := htB (1 + (5 * k + 4)) (by omega)
    unfold ttv ppv; omega
  obtain ⟨σ4, r4, ⟨c1, c2, c3, c4, c5, c6⟩, c7⟩ := pairsLoop_spec (B := B) (σ3.arrs "TT")
    (σ3.arrs "PP") n (σ3.vars "ok") [] g7 g8 (by omega) hval σ3
    ⟨by simp [Env.setVar], by simp [Env.setVar],
      by simp only [Env.setVar]; rw [if_neg (by decide)]; exact g2, by simp [Env.setVar],
      by simp only [Env.setVar, if_true]; rw [if_neg (by decide),
        okO_zero _ _ _ _ (by rw [g6]; exact flagTo_le _ _ _)],
      by simp only [Env.setVar]; exact g10⟩
  rw [c7, g6, flagTo_one, okO_flag] at c5
  -- the answer
  have r5 := Run.write (B := B) (σ := σ4) (e := V "ok") (v := σ4.vars "ok")
    (evalB_var (by rw [c5]; split <;> omega))
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono (by
    unfold Kacc; simp only [Expr.size]; omega), ?_⟩
  show σ4.out ++ [σ4.vars "ok"] = _
  rw [c6, c5, List.nil_append]
  congr 1
  exact if_congr (link p q t (σ3.arrs "TT") (σ3.arrs "PP") Ov n h0
    (fun k hk => getD_le_sumTo t (by omega) hTl) g9) rfl rfl

end Lax391470Proofs.V1Accept
