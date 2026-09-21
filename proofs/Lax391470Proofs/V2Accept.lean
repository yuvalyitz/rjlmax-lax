import Lax391470Proofs.V2Link
import Lax391470Proofs.L1Accept

/-!
The accepting branch of the verifier of `AUX p q`: from conforming tokens to the answer.
-/

namespace Lax391470Proofs.V2Accept

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.L1Check (V add checkLoop checkLoop_spec okv okv_le PairOK' pairOK'_iff)
open Lax391470Proofs.AuxNk (mul)
open Lax391470Proofs.V2Ord Lax391470Proofs.V2Pair Lax391470Proofs.VPairs
open Lax391470Proofs.V2Sem Lax391470Proofs.V2Link Lax391470Proofs.Flag
open Lax391470Proofs.L1Ordered

variable {B : ℕ}

open Classical

def setA : Com :=
  .seq (.assign "ok" (.lit 1)) (.seq (.assign "nn" (.get "TK" (.lit 0)))
    (.seq (.assign "N" (.get "TK" (.lit 1)))
      (.assign "b3" (add (.lit 2) (mul (.lit 3) (V "nn"))))))

theorem setA_spec (n N : ℕ) (hB : 3 * n + N + 8 < B) :
    Spec B (fun σ => (σ.arrs "TK").getD 0 0 = n ∧ (σ.arrs "TK").getD 1 0 = N ∧
        2 ≤ (σ.arrs "TK").length) setA
      (fun σ σ' => σ'.vars "ok" = 1 ∧ σ'.vars "nn" = n ∧ σ'.vars "N" = N ∧
        σ'.vars "b3" = 2 + 3 * n ∧ (∀ z ∉ ["ok", "nn", "N", "b3"], σ'.vars z = σ.vars z) ∧
        σ'.arrs = σ.arrs ∧ σ'.out = σ.out) 20 := by
  run_vcg
  all_goals have e0 := ‹(σ.arrs "TK").getD 0 0 = n›
  all_goals have e1 := ‹(σ.arrs "TK").getD 1 0 = N›
  all_goals try simp [Env.setVar] at *
  all_goals try simp only [e0, e1] at *
  all_goals first
    | omega
    | (intro z h0 h1 h2 h3)
    | ((repeat' constructor); first
        | trivial
        | omega
        | (intro z h0 h1 h2 h3; simp [h0, h1, h2, h3]))

def setB : Com :=
  .seq (.assign "bS" (add (V "b3") (mul (.lit 4) (V "N"))))
    (.seq (.assign "nN" (add (V "nn") (V "N")))
      (.assign "nj" (add (V "nn") (mul (.lit 2) (V "N")))))

theorem setB_spec (n N b : ℕ) (hB : b + 4 * N + 2 * n + 8 < B) :
    Spec B (fun σ => σ.vars "nn" = n ∧ σ.vars "N" = N ∧ σ.vars "b3" = b) setB
      (fun σ σ' => σ'.vars "bS" = b + 4 * N ∧ σ'.vars "nN" = n + N ∧
        σ'.vars "nj" = n + 2 * N ∧ (∀ z ∉ ["bS", "nN", "nj"], σ'.vars z = σ.vars z) ∧
        σ'.arrs = σ.arrs ∧ σ'.out = σ.out) 20 := by
  run_vcg
  all_goals have e0 := ‹σ.vars "nn" = n›
  all_goals have e1 := ‹σ.vars "N" = N›
  all_goals have e2 := ‹σ.vars "b3" = b›
  all_goals try simp [Env.setVar, e0, e1, e2] at *
  all_goals first
    | omega
    | (intro z h0 h1 h2; simp [h0, h1, h2])

def acceptPart (p q : ℕ) : Com :=
  .seq setA (.seq setB (.seq checkLoop (.seq (ordLoop p q) (.seq (pairLoop p q)
    (.seq pairsLoop (.write (V "ok")))))))

lemma okv_zero (t : List ℕ) (b N : ℕ) : okv t b N 0 = 1 := by unfold okv; simp

lemma okv_eq_one (t : List ℕ) (n N : ℕ) (hn : t.getD 0 0 = n) (hN : t.getD 1 0 = N) :
    okv t (2 + 3 * n) N N = 1 ↔ OrdOK t := by
  unfold okv OrdOK
  rw [hn, hN]
  constructor
  · intro h i hi
    have hall : ∀ i' < N, PairOK' t (2 + 3 * n) N i' := by
      by_contra hc; rw [if_neg hc] at h; omega
    exact (pairOK'_iff t n N i).mp (hall i hi)
  · intro h
    rw [if_pos fun i hi => (pairOK'_iff t n N i).mpr (h i hi)]

/-- The cost of the accepting branch with `n` ordinary jobs and `N` pairs. -/
def Kacc (n N : ℕ) : ℕ :=
  20 + 20 + ((120 + 4) * N + 6) + ((110 + 4) * n + 6) + ((170 + 4) * N + 6) +
    (((70 + 4) * (n + 2 * N) + 6 + 4 + 4) * (n + 2 * N) + 6) + 2

theorem accept_spec (p q : ℕ) (t : List ℕ) (n N Tn Bt : ℕ) (h0 : t.getD 0 0 = n)
    (h1 : t.getD 1 0 = N) (hTn : Tn = 2 + (3 * n + 4 * N + (n + 2 * N))) (hTl : Tn ≤ t.length)
    (htB : ∀ k < Tn, t.getD k 0 < Bt) (hB : 2 * Bt + p + q + 6 * Tn + 16 < B) :
    Spec B (fun σ => σ.arrs "TK" = t ∧ n + 2 * N ≤ (σ.arrs "TT").length ∧
        n + 2 * N ≤ (σ.arrs "PP").length ∧ σ.out = []) (acceptPart p q)
      (fun _ σ' => σ'.out = [if Sem p q t then 1 else 0]) (Kacc n N) := by
  intro σ ⟨hTK, hlt, hlp, hout⟩
  have hn : n < Bt := by rw [← h0]; exact htB 0 (by omega)
  have hN : N < Bt := by rw [← h1]; exact htB 1 (by omega)
  -- set up
  obtain ⟨σ1, r1, s1, s2, s3, s4, k1, a1, o1⟩ := setA_spec (B := B) n N (by omega) σ
    ⟨by rw [hTK]; exact h0, by rw [hTK]; exact h1, by rw [hTK]; omega⟩
  obtain ⟨σ2, r2, u1, u2, u3, k2, a2, o2⟩ := setB_spec (B := B) n N (2 + 3 * n) (by omega) σ1
    ⟨s2, s3, s4⟩
  have k2' : ∀ z, z ∉ ["bS", "nN", "nj"] → σ2.vars z = σ1.vars z := k2
  have arr2 : σ2.arrs = σ.arrs := by rw [a2, a1]
  -- the order of the deadlines
  obtain ⟨σ3, r3, ⟨⟨c1, c2, c3, -, c5, c6⟩, ci⟩, fv3, fa3, -, -⟩ :=
    (checkLoop_spec (B := B) t (2 + 3 * n) N [] (by omega) (by omega)
      (fun k hk => by have := htB k (by omega); omega)).frame σ2
    ⟨by simp only [Env.setVar]; rw [arr2]; exact hTK,
      by simp only [Env.setVar]; rw [if_neg (by decide), k2' _ (by decide)]; exact s4,
      by simp only [Env.setVar]; rw [if_neg (by decide), k2' _ (by decide)]; exact s3,
      by simp [Env.setVar],
      by simp only [Env.setVar, if_true]; rw [if_neg (by decide), k2' _ (by decide), s1,
        okv_zero],
      by simp only [Env.setVar]; rw [o2, o1]; exact hout⟩
  rw [ci] at c5
  have w3 : ∀ z, z ∈ ["nn", "bS", "nN", "nj"] → σ3.vars z = σ2.vars z := fun z hz =>
    fv3 z (by
      rw [L1Accept.wvars_check]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> decide)
  have arr3 : σ3.arrs = σ.arrs := by
    funext x; rw [fa3 x (by rw [L1Accept.warrs_check]; simp), arr2]
  have nn3 : σ3.vars "nn" = n := by rw [w3 _ (by simp), k2' _ (by decide)]; exact s2
  have bS3 : σ3.vars "bS" = 2 + 3 * n + 4 * N := by rw [w3 _ (by simp)]; exact u1
  have nN3 : σ3.vars "nN" = n + N := by rw [w3 _ (by simp)]; exact u2
  have nj3 : σ3.vars "nj" = n + 2 * N := by rw [w3 _ (by simp)]; exact u3
  -- the ordinary jobs
  obtain ⟨σ4, r4, I4, f4⟩ := ordLoop_spec (B := B) p q t n (2 + 3 * n + 4 * N)
    (okv t (2 + 3 * n) N N) Bt Tn (σ3.arrs "TT").length (σ3.arrs "PP").length (σ3.vars)
    hTl (by omega) (by omega) htB (by omega) (by rw [arr3]; omega) (by rw [arr3]; omega) σ3
    ⟨by simp only [Env.setVar]; exact c1,
      by simp only [Env.setVar]; rw [if_neg (by decide)]; exact nn3,
      by simp only [Env.setVar]; rw [if_neg (by decide)]; exact bS3,
      by simp [Env.setVar],
      by simp only [Env.setVar, if_true]; rw [if_neg (by decide), c5,
        flagTo_zero _ _ (okv_le _ _ _ _)],
      by simp [Env.setVar], by simp [Env.setVar],
      fun o ho => by simp [Env.setVar] at ho,
      fun z hz => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
        simp only [Env.setVar]; rw [if_neg (by tauto)],
      by simp only [Env.setVar]; exact c6⟩
  obtain ⟨g1, -, -, -, g5, g6, g7, g8, g9, g10⟩ := I4
  rw [f4] at g5 g8
  -- the pairs
  obtain ⟨σ5, r5, I5, f5⟩ := pairLoop_spec (B := B) p q t (σ4.arrs "TT") (σ4.arrs "PP") N
    (2 + 3 * n) (2 + 3 * n + 4 * N) n (n + N) (σ4.vars "ok") Bt Tn (σ4.vars) rfl hTl (by omega)
    (by omega) htB (by omega) (by rw [g6, arr3]; omega) (by rw [g7, arr3]; omega)
    (by rw [g9 _ (by decide)]; exact c2) (by rw [g9 _ (by decide)]; exact bS3)
    (by rw [g9 _ (by decide)]; exact nn3) (by rw [g9 _ (by decide)]; exact nN3) σ4
    ⟨by simp only [Env.setVar]; exact g1,
      by simp only [Env.setVar]; rw [if_neg (by decide), g9 _ (by decide)]; exact c3,
      by simp [Env.setVar],
      by simp only [Env.setVar, if_true]; rw [if_neg (by decide),
        flagTo_zero _ _ (by rw [g5]; exact flagTo_le _ _ _)],
      by simp [Env.setVar], by simp [Env.setVar],
      fun o _ => by simp [Env.setVar],
      fun i' hi' => by simp [Env.setVar] at hi',
      fun z hz => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
        simp only [Env.setVar]; rw [if_neg (by tauto)],
      by simp only [Env.setVar]; exact g10⟩
  obtain ⟨-, -, -, m4, m5, m6, m7, m8, m9, m10⟩ := I5
  rw [f5] at m4 m8
  -- the values in the arrays
  have hv := values p q t n N (σ5.arrs "TT") (σ5.arrs "PP") h0 h1
    (fun o ho => by rw [(m7 o ho).1, (m7 o ho).2]; exact g8 o ho) m8
  have hval : ∀ k < n + 2 * N, (σ5.arrs "TT").getD k 0 + (σ5.arrs "PP").getD k 0 < B :=
    fun k hk => by
      rw [(hv k hk).1, (hv k hk).2]
      have e1 : tOf t k < Bt := by
        unfold tOf; rw [h0, h1]; exact htB _ (by unfold iS; omega)
      have e2 : pOf p q t k ≤ p + q := by unfold pOf; split_ifs <;> omega
      omega
  -- no overlap
  obtain ⟨σ6, r6, ⟨-, -, -, -, d5, d6⟩, d7⟩ := pairsLoop_spec (B := B) (σ5.arrs "TT")
    (σ5.arrs "PP") (n + 2 * N) (σ5.vars "ok") [] (by rw [m5, g6, arr3]; exact hlt)
    (by rw [m6, g7, arr3]; exact hlp) (by omega) hval σ5
    ⟨by simp [Env.setVar], by simp [Env.setVar],
      by simp only [Env.setVar]; rw [if_neg (by decide), m9 _ (by decide), g9 _ (by decide)]
         exact nj3,
      by simp [Env.setVar],
      by simp only [Env.setVar, if_true]; rw [if_neg (by decide),
        okO_zero _ _ _ _ (by rw [m4]; exact flagTo_le _ _ _)],
      by simp only [Env.setVar]; exact m10⟩
  rw [d7] at d5
  -- the answer
  have hle : σ6.vars "ok" ≤ 1 := by rw [d5]; exact okO_le _ _ _ _ _
  have hiff : σ6.vars "ok" = 1 ↔ Sem p q t := by
    rw [d5, okO_eq_one, m4, flagTo_eq_one, g5, flagTo_eq_one, okv_eq_one t n N h0 h1]
    unfold Sem
    have l1 := link_fe p q t n N h0 h1
    have l2 := link_ov p q t n N (σ5.arrs "TT") (σ5.arrs "PP") h0 h1 hv
    constructor
    · rintro ⟨⟨⟨a, b⟩, c⟩, d⟩
      have := l1.mp ⟨b, c⟩
      exact ⟨a, this.1, l2.mp d, this.2⟩
    · rintro ⟨a, b, c, d⟩
      have := l1.mpr ⟨b, d⟩
      exact ⟨⟨⟨a, this.1⟩, this.2⟩, l2.mpr c⟩
  have r7 := Run.write (B := B) (σ := σ6) (e := V "ok") (v := σ6.vars "ok")
    (evalB_var (by omega))
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))).mono (by
    unfold Kacc; simp only [Expr.size]; omega), ?_⟩
  show σ6.out ++ [σ6.vars "ok"] = _
  rw [d6, List.nil_append]
  by_cases hS : Sem p q t
  · rw [if_pos hS, hiff.mpr hS]
  · rw [if_neg hS]
    have : σ6.vars "ok" ≠ 1 := fun h => hS (hiff.mp h)
    congr 1; omega

end Lax391470Proofs.V2Accept
