import Lax391470Proofs.L1Ordered
import Lax391470Proofs.ReadAll

/-!
Checking the conditions on the deadlines: one pass over the pairs, clearing a flag.
-/

namespace Lax391470Proofs.L1Check

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.L1Ordered

abbrev V (s : String) : Expr := .var s
abbrev add (e f : Expr) : Expr := .bin .add e f
abbrev mul (e f : Expr) : Expr := .bin .mul e f

/-- Token `b3 + 4 i + c`. -/
abbrev tkAt (c : ℕ) : Expr := .get "TK" (add (V "b3") (add (mul (.lit 4) (V "i")) (.lit c)))

def load : Com :=
  .seq (.assign "e0" (tkAt 0)) (.seq (.assign "e1" (tkAt 1))
    (.seq (.assign "e2" (tkAt 2)) (.assign "e3" (tkAt 3))))

def load2 : Com := .seq (.assign "f0" (tkAt 4)) (.assign "f2" (tkAt 6))

/-- Clear the flag if `x < y`. -/
def chk (x y : String) : Com := .ite (.lt (V x) (V y)) (.assign "ok" (.lit 0)) .skip

variable {B : ℕ}

theorem chk_spec (x y : String) (hB : 1 < B) :
    Spec B (fun σ => σ.vars x < B ∧ σ.vars y < B) (chk x y)
      (fun σ σ' => σ'.vars "ok" = (if σ.vars x < σ.vars y then 0 else σ.vars "ok") ∧
        (∀ z, z ≠ "ok" → σ'.vars z = σ.vars z) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out) 6 := by
  run_vcg
  all_goals try simp_all [Env.setVar]

theorem load_spec (t : List ℕ) (i0 b : ℕ) (hlen : b + 4 * i0 + 3 < t.length)
    (hB : b + 4 * i0 + 8 < B) (htB : ∀ k, k ≤ b + 4 * i0 + 3 → t.getD k 0 < B) :
    Spec B (fun σ => σ.arrs "TK" = t ∧ σ.vars "i" = i0 ∧ σ.vars "b3" = b) load
      (fun σ σ' => σ'.vars "e0" = t.getD (b + (4 * i0 + 0)) 0 ∧
        σ'.vars "e1" = t.getD (b + (4 * i0 + 1)) 0 ∧ σ'.vars "e2" = t.getD (b + (4 * i0 + 2)) 0 ∧
        σ'.vars "e3" = t.getD (b + (4 * i0 + 3)) 0 ∧
        (∀ z ∉ ["e0", "e1", "e2", "e3"], σ'.vars z = σ.vars z) ∧ σ'.arrs = σ.arrs ∧
        σ'.out = σ.out) 40 := by
  run_vcg
  all_goals have hT := ‹σ.arrs "TK" = t›
  all_goals have hi := ‹σ.vars "i" = i0›
  all_goals have hb := ‹σ.vars "b3" = b›
  all_goals try simp [Env.setVar, hT, hi, hb] at *
  all_goals first
    | omega
    | (simpa using htB _ (by omega))
    | (intro z h0 h1 h2 h3; simp [h0, h1, h2, h3])

theorem load2_spec (t : List ℕ) (i0 b : ℕ) (hlen : b + 4 * i0 + 6 < t.length)
    (hB : b + 4 * i0 + 8 < B) (htB : ∀ k, k ≤ b + 4 * i0 + 6 → t.getD k 0 < B) :
    Spec B (fun σ => σ.arrs "TK" = t ∧ σ.vars "i" = i0 ∧ σ.vars "b3" = b) load2
      (fun σ σ' => σ'.vars "f0" = t.getD (b + (4 * i0 + 4)) 0 ∧
        σ'.vars "f2" = t.getD (b + (4 * i0 + 6)) 0 ∧
        (∀ z ∉ ["f0", "f2"], σ'.vars z = σ.vars z) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out) 20 := by
  run_vcg
  all_goals have hT := ‹σ.arrs "TK" = t›
  all_goals have hi := ‹σ.vars "i" = i0›
  all_goals have hb := ‹σ.vars "b3" = b›
  all_goals try simp [Env.setVar, hT, hi, hb] at *
  all_goals first
    | omega
    | (simpa using htB _ (by omega))
    | (intro z h0 h1; simp [h0, h1])

/-- Pair `i` meets the conditions, the pairs starting at token `b`. -/
def PairOK' (t : List ℕ) (b N i : ℕ) : Prop :=
  t.getD (b + (4 * i + 0)) 0 ≤ t.getD (b + (4 * i + 1)) 0 ∧
  t.getD (b + (4 * i + 2)) 0 ≤ t.getD (b + (4 * i + 3)) 0 ∧
  t.getD (b + (4 * i + 1)) 0 ≤ t.getD (b + (4 * i + 2)) 0 ∧
  (i + 1 < N → t.getD (b + (4 * i + 1)) 0 ≤ t.getD (b + (4 * i + 4)) 0 ∧
    t.getD (b + (4 * i + 3)) 0 ≤ t.getD (b + (4 * i + 6)) 0)

instance (t : List ℕ) (b N i : ℕ) : Decidable (PairOK' t b N i) := by
  unfold PairOK'; infer_instance

lemma pairOK'_iff (t : List ℕ) (n N i : ℕ) : PairOK' t (2 + 3 * n) N i ↔ PairOK t n N i := by
  unfold PairOK' PairOK ev
  have e4 : 2 + 3 * n + (4 * i + 4) = 2 + (3 * n + (4 * (i + 1) + 0)) := by omega
  have e6 : 2 + 3 * n + (4 * i + 6) = 2 + (3 * n + (4 * (i + 1) + 2)) := by omega
  have e : ∀ c, 2 + 3 * n + (4 * i + c) = 2 + (3 * n + (4 * i + c)) := fun c => by omega
  rw [e4, e6, e 0, e 1, e 2, e 3]

lemma flag5 (okin e0 e1 e2 e3 f0 f2 : ℕ) (hok : okin ≤ 1) :
    (if f2 < e3 then 0 else if f0 < e1 then 0 else
      (if e2 < e1 then 0 else if e3 < e2 then 0 else if e1 < e0 then 0 else okin)) =
    if okin = 1 ∧ (e0 ≤ e1 ∧ e2 ≤ e3 ∧ e1 ≤ e2 ∧ (e1 ≤ f0 ∧ e3 ≤ f2)) then 1 else 0 := by
  split_ifs <;> omega

lemma flag3 (okin e0 e1 e2 e3 : ℕ) (hok : okin ≤ 1) :
    (if e2 < e1 then 0 else if e3 < e2 then 0 else if e1 < e0 then 0 else okin) =
    if okin = 1 ∧ (e0 ≤ e1 ∧ e2 ≤ e3 ∧ e1 ≤ e2) then 1 else 0 := by
  split_ifs <;> omega

def checkBody : Com :=
  .seq load (.seq (chk "e1" "e0") (.seq (chk "e3" "e2") (.seq (chk "e2" "e1")
    (.seq (.ite (.lt (add (V "i") (.lit 1)) (V "N"))
        (.seq load2 (.seq (chk "f0" "e1") (chk "f2" "e3"))) .skip)
      (.assign "i" (add (V "i") (.lit 1)))))))

theorem checkBody_spec (t : List ℕ) (i0 b N okin : ℕ) (hi : i0 < N) (hok : okin ≤ 1)
    (hlen : b + 4 * i0 + 3 < t.length) (hlen2 : i0 + 1 < N → b + 4 * i0 + 6 < t.length)
    (hB : b + 4 * i0 + 8 < B) (hNB : N + 2 < B) (htB : ∀ k, k < b + 4 * N → t.getD k 0 < B) :
    Spec B (fun σ => σ.arrs "TK" = t ∧ σ.vars "i" = i0 ∧ σ.vars "b3" = b ∧ σ.vars "N" = N ∧
        σ.vars "ok" = okin) checkBody
      (fun σ σ' => σ'.vars "ok" = (if okin = 1 ∧ PairOK' t b N i0 then 1 else 0) ∧
        σ'.vars "i" = i0 + 1 ∧ σ'.arrs = σ.arrs ∧ σ'.vars "b3" = b ∧ σ'.vars "N" = N ∧
        σ'.out = σ.out) 120 := by
  intro σ ⟨hT, hiv, hbv, hNv, hokv⟩
  obtain ⟨σ1, r1, l0, l1, l2, l3, lv, la, lo⟩ := load_spec (B := B) t i0 b hlen hB (fun k hk => htB k (by omega)) σ
    ⟨hT, hiv, hbv⟩
  have k1 : ∀ z, z ∉ ["e0", "e1", "e2", "e3"] → σ1.vars z = σ.vars z := lv
  obtain ⟨σ2, r2, c2, v2, a2, o2⟩ := chk_spec (B := B) "e1" "e0" (by omega) σ1
    ⟨by rw [l1]; exact htB _ (by omega), by rw [l0]; exact htB _ (by omega)⟩
  obtain ⟨σ3, r3, c3, v3, a3, o3⟩ := chk_spec (B := B) "e3" "e2" (by omega) σ2
    ⟨by rw [v2 _ (by decide), l3]; exact htB _ (by omega), by rw [v2 _ (by decide), l2]; exact htB _ (by omega)⟩
  obtain ⟨σ4, r4, c4, v4, a4, o4⟩ := chk_spec (B := B) "e2" "e1" (by omega) σ3
    ⟨by rw [v3 _ (by decide), v2 _ (by decide), l2]; exact htB _ (by omega),
      by rw [v3 _ (by decide), v2 _ (by decide), l1]; exact htB _ (by omega)⟩
  have var4 : ∀ z, z ≠ "ok" → σ4.vars z = σ1.vars z := fun z hz => by
    rw [v4 z hz, v3 z hz, v2 z hz]
  have arr4 : σ4.arrs = σ.arrs := by rw [a4, a3, a2, la]
  have out4 : σ4.out = σ.out := by rw [o4, o3, o2, lo]
  have i4 : σ4.vars "i" = i0 := by rw [var4 _ (by decide), k1 _ (by decide), hiv]
  have N4 : σ4.vars "N" = N := by rw [var4 _ (by decide), k1 _ (by decide), hNv]
  have b4 : σ4.vars "b3" = b := by rw [var4 _ (by decide), k1 _ (by decide), hbv]
  have ok4 : σ4.vars "ok" = if σ1.vars "e2" < σ1.vars "e1" then 0 else
      if σ1.vars "e3" < σ1.vars "e2" then 0 else if σ1.vars "e1" < σ1.vars "e0" then 0 else okin := by
    rw [c4, c3, c2, v3 "e2" (by decide), v2 "e2" (by decide), v3 "e1" (by decide),
      v2 "e1" (by decide), v2 "e3" (by decide), k1 "ok" (by decide), hokv]
  have hcond : (Cond.lt (add (V "i") (.lit 1)) (V "N")).evalB B σ4 = some (decide (i0 + 1 < N)) := by
    have e1 := evalB_bin (op := .add) (evalB_var (B := B) (σ := σ4) (x := "i") (by rw [i4]; omega))
      (evalB_lit (n := 1) (by omega)) (by simp [i4]; omega)
    rw [evalB_condLt e1 (evalB_var (by rw [N4]; omega))]
    simp [i4, N4]
  have bumpRun : ∀ τ : Env, τ.vars "i" = i0 →
      Run B (.assign "i" (add (V "i") (.lit 1))) τ (τ.setVar "i" (i0 + 1))
        (1 + (add (V "i") (.lit 1)).size) := fun τ hτ => by
    have := Run.assign (B := B) (σ := τ) (x := "i") (e := add (V "i") (.lit 1)) (v := i0 + 1)
      (by
        have h := evalB_bin (op := .add) (evalB_var (B := B) (σ := τ) (x := "i")
          (by rw [hτ]; omega)) (evalB_lit (n := 1) (by omega)) (by simp [hτ]; omega)
        simpa [hτ] using h)
    exact this
  by_cases hnext : i0 + 1 < N
  · obtain ⟨σ5, r5, m0, m2, mv, ma, mo⟩ := load2_spec (B := B) t i0 b (hlen2 hnext) hB (fun k hk => htB k (by omega)) σ4
      ⟨by rw [arr4]; exact hT, i4, b4⟩
    have e1_5 : σ5.vars "e1" = σ1.vars "e1" := by rw [mv _ (by decide), var4 _ (by decide)]
    have e3_5 : σ5.vars "e3" = σ1.vars "e3" := by rw [mv _ (by decide), var4 _ (by decide)]
    obtain ⟨σ6, r6, c6, v6, a6, o6⟩ := chk_spec (B := B) "f0" "e1" (by omega) σ5
      ⟨by rw [m0]; exact htB _ (by omega), by rw [e1_5, l1]; exact htB _ (by omega)⟩
    obtain ⟨σ7, r7, c7, v7, a7, o7⟩ := chk_spec (B := B) "f2" "e3" (by omega) σ6
      ⟨by rw [v6 _ (by decide), m2]; exact htB _ (by omega),
        by rw [v6 _ (by decide), e3_5, l3]; exact htB _ (by omega)⟩
    have i7 : σ7.vars "i" = i0 := by
      rw [v7 _ (by decide), v6 _ (by decide), mv _ (by decide), i4]
    have rite := Run.ite_true (d := Com.skip) (by rw [hcond]; simp [hnext]) (r5.seq (r6.seq r7))
    refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (rite.seq (bumpRun σ7 i7)))))).mono
      (by simp [Cond.size, Expr.size]), ?_, by simp [Env.setVar], ?_, ?_, ?_, ?_⟩
    · simp only [Env.setVar, if_neg (show ¬ "ok" = "i" by decide)]
      rw [c7, c6, v6 "f2" (by decide), v6 "e3" (by decide), m2, m0, e3_5, e1_5,
        mv "ok" (by decide), ok4, l0, l1, l2, l3, flag5 _ _ _ _ _ _ _ hok]
      simp only [PairOK', hnext, true_imp_iff]
    · simp only [Env.setVar]; rw [a7, a6, ma, arr4]
    · simp only [Env.setVar, if_neg (show ¬ "b3" = "i" by decide)]
      rw [v7 _ (by decide), v6 _ (by decide), mv _ (by decide), b4]
    · simp only [Env.setVar, if_neg (show ¬ "N" = "i" by decide)]
      rw [v7 _ (by decide), v6 _ (by decide), mv _ (by decide), N4]
    · simp only [Env.setVar]; rw [o7, o6, mo, out4]
  · have rite := Run.ite_false (c := Com.seq load2 (.seq (chk "f0" "e1") (chk "f2" "e3")))
      (by rw [hcond]; simp [hnext]) (Run.skip (B := B) (σ := σ4))
    refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (rite.seq (bumpRun σ4 i4)))))).mono
      (by simp [Cond.size, Expr.size]), ?_, by simp [Env.setVar], ?_, ?_, ?_, ?_⟩
    · simp only [Env.setVar, if_neg (show ¬ "ok" = "i" by decide)]
      rw [ok4, l0, l1, l2, l3, flag3 _ _ _ _ _ hok]
      simp only [PairOK', hnext, false_imp_iff, and_true]
    · simp only [Env.setVar]; exact arr4
    · simp only [Env.setVar, if_neg (show ¬ "b3" = "i" by decide)]; exact b4
    · simp only [Env.setVar, if_neg (show ¬ "N" = "i" by decide)]; exact N4
    · simp only [Env.setVar]; exact out4

/-- The flag after `i` pairs. -/
def okv (t : List ℕ) (b N i : ℕ) : ℕ := if ∀ i' < i, PairOK' t b N i' then 1 else 0

lemma okv_le (t : List ℕ) (b N i : ℕ) : okv t b N i ≤ 1 := by unfold okv; split <;> omega

lemma okv_succ (t : List ℕ) (b N i : ℕ) :
    okv t b N (i + 1) = if okv t b N i = 1 ∧ PairOK' t b N i then 1 else 0 := by
  unfold okv
  by_cases h : ∀ i' < i, PairOK' t b N i'
  · by_cases hp : PairOK' t b N i
    · rw [if_pos (fun i' hi' => by
        rcases Nat.lt_or_ge i' i with h1 | h1
        · exact h i' h1
        · have : i' = i := by omega
          rw [this]; exact hp), if_pos h, if_pos ⟨rfl, hp⟩]
    · rw [if_neg (fun hall => hp (hall i (by omega))), if_pos h, if_neg (fun hc => hp hc.2)]
  · rw [if_neg (fun hall => h (fun i' hi' => hall i' (by omega))), if_neg h,
      if_neg (fun hc => by simp at hc)]

def checkLoop : Com := .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "N")) checkBody)

def CInv (t : List ℕ) (b N : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.arrs "TK" = t ∧ σ.vars "b3" = b ∧ σ.vars "N" = N ∧ σ.vars "i" ≤ N ∧
    σ.vars "ok" = okv t b N (σ.vars "i") ∧ σ.out = out0

theorem checkLoop_spec (t : List ℕ) (b N : ℕ) (out0 : List ℕ)
    (hlen : b + 4 * N ≤ t.length) (hB : b + 4 * N + 8 < B)
    (htB : ∀ k, k < b + 4 * N → t.getD k 0 < B) :
    Spec B (fun σ => CInv t b N out0 (σ.setVar "i" 0)) checkLoop
      (fun _ σ' => CInv t b N out0 σ' ∧ σ'.vars "i" = N) ((120 + 4) * N + 6) := by
  refine Spec.forRangeZero "i" "N" (CInv t b N out0) N 120 (by omega) (fun _ h => h.2.2.2.1)
    (fun _ h => h.2.2.1) ?_
  intro σ ⟨⟨hT, hb, hN, hle, hok, hout⟩, hlt⟩
  obtain ⟨σ', r, q1, q2, q3, q4, q5, q6⟩ := checkBody_spec (B := B) t (σ.vars "i") b N
    (okv t b N (σ.vars "i")) hlt (okv_le _ _ _ _) (by omega) (fun _ => by omega) (by omega)
    (by omega) htB σ ⟨hT, rfl, hb, hN, hok⟩
  exact ⟨σ', r, ⟨by rw [q3]; exact hT, q4, q5, by omega, by rw [q1, q2, okv_succ],
    by rw [q6]; exact hout⟩, q2⟩

end Lax391470Proofs.L1Check
