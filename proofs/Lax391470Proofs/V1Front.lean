import Lax391470Proofs.L1Check
import Lax391470Proofs.AuxNk
import Lax391470Proofs.Flag

/-!
The first pass of the verifier over the jobs: shift all times to natural numbers, check
every job against its interval, and leave start times and lengths in the arrays `TT`, `PP`.
-/

namespace Lax391470Proofs.V1Front

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.L1Check (V add)
open Lax391470Proofs.AuxNk (sub mul)

/-- Token `1 + (5 fj + c)`. -/
abbrev tkJ (c : ℕ) : Expr := .get "TK" (add (.lit 1) (add (mul (.lit 5) (V "fj")) (.lit c)))
/-- Token `1 + (m5 + (2 fj + c))`. -/
abbrev tkT (c : ℕ) : Expr :=
  .get "TK" (add (.lit 1) (add (V "m5") (add (mul (.lit 2) (V "fj")) (.lit c))))

def loadA : Com :=
  .seq (.assign "s0" (tkJ 0)) (.seq (.assign "a1" (tkJ 1))
    (.seq (.assign "s2" (tkJ 2)) (.assign "a3" (tkJ 3))))

def loadB : Com :=
  .seq (.assign "P" (tkJ 4)) (.seq (.assign "ts" (tkT 0)) (.assign "ta" (tkT 1)))

variable {B : ℕ}

theorem loadA_spec (t : List ℕ) (j : ℕ) (hlen : 1 + (5 * j + 4) < t.length)
    (hB : 5 * j + 8 < B) (htB : ∀ k, k ≤ 1 + (5 * j + 4) → t.getD k 0 < B) :
    Spec B (fun σ => σ.arrs "TK" = t ∧ σ.vars "fj" = j) loadA
      (fun σ σ' => σ'.vars "s0" = t.getD (1 + (5 * j + 0)) 0 ∧
        σ'.vars "a1" = t.getD (1 + (5 * j + 1)) 0 ∧ σ'.vars "s2" = t.getD (1 + (5 * j + 2)) 0 ∧
        σ'.vars "a3" = t.getD (1 + (5 * j + 3)) 0 ∧
        (∀ z ∉ ["s0", "a1", "s2", "a3"], σ'.vars z = σ.vars z) ∧ σ'.arrs = σ.arrs ∧
        σ'.out = σ.out) 50 := by
  run_vcg
  all_goals have hT := ‹σ.arrs "TK" = t›
  all_goals have hj := ‹σ.vars "fj" = j›
  all_goals try simp [Env.setVar, hT, hj] at *
  all_goals first
    | omega
    | (simpa using htB _ (by omega))
    | (intro z h0 h1 h2 h3; simp [h0, h1, h2, h3])

theorem loadB_spec (t : List ℕ) (j m : ℕ) (hlen : 1 + (m + (2 * j + 1)) < t.length)
    (hlen' : 1 + (5 * j + 4) < t.length)
    (hB : m + 5 * j + 8 < B) (htB : ∀ k, k ≤ 1 + (m + (2 * j + 1)) → t.getD k 0 < B)
    (htB' : t.getD (1 + (5 * j + 4)) 0 < B) :
    Spec B (fun σ => σ.arrs "TK" = t ∧ σ.vars "fj" = j ∧ σ.vars "m5" = m) loadB
      (fun σ σ' => σ'.vars "P" = t.getD (1 + (5 * j + 4)) 0 ∧
        σ'.vars "ts" = t.getD (1 + (m + (2 * j + 0))) 0 ∧
        σ'.vars "ta" = t.getD (1 + (m + (2 * j + 1))) 0 ∧
        (∀ z ∉ ["P", "ts", "ta"], σ'.vars z = σ.vars z) ∧ σ'.arrs = σ.arrs ∧
        σ'.out = σ.out) 50 := by
  run_vcg
  all_goals have hT := ‹σ.arrs "TK" = t›
  all_goals have hj := ‹σ.vars "fj" = j›
  all_goals have hm := ‹σ.vars "m5" = m›
  all_goals try simp [Env.setVar, hT, hj, hm] at *
  all_goals first
    | omega
    | (simpa using htB _ (by omega))
    | (simpa using htB')
    | (intro z h0 h1 h2; simp [h0, h1, h2])

/-- The number `O + z` for the integer `z` with sign `s` and absolute value `a`. -/
def sh (O s a : ℕ) : ℕ := if s = 0 then O + a else O - a

def shift (r s a : String) : Com :=
  .ite (.eq (V s) (.lit 0)) (.assign r (add (V "O") (V a))) (.assign r (sub (V "O") (V a)))

/-- Clear the flag for a `-0`. -/
def nzc (s a : String) : Com :=
  .ite (.eq (V s) (.lit 0)) .skip (.ite (.eq (V a) (.lit 0)) (.assign "ok" (.lit 0)) .skip)

theorem nzc_spec (s a : String) (hB : 1 < B) :
    Spec B (fun σ => σ.vars s < B ∧ σ.vars a < B) (nzc s a)
      (fun σ σ' => σ'.vars "ok" = (if σ.vars s ≠ 0 ∧ σ.vars a = 0 then 0 else σ.vars "ok") ∧
        (∀ z, z ≠ "ok" → σ'.vars z = σ.vars z) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out) 10 := by
  run_vcg
  all_goals try simp_all [Env.setVar]

/-- Clear the flag for a length other than `p` and `q`. -/
def lenc (p q : ℕ) : Com :=
  .ite (.eq (V "P") (.lit p)) .skip (.ite (.eq (V "P") (.lit q)) .skip (.assign "ok" (.lit 0)))

theorem lenc_spec (p q : ℕ) (hB : 1 < B) (hp : p < B) (hq : q < B) :
    Spec B (fun σ => σ.vars "P" < B) (lenc p q)
      (fun σ σ' => σ'.vars "ok" = (if σ.vars "P" = p ∨ σ.vars "P" = q then σ.vars "ok" else 0) ∧
        (∀ z, z ≠ "ok" → σ'.vars z = σ.vars z) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out) 10 := by
  run_vcg
  all_goals try simp_all [Env.setVar]

open Lax391470Proofs.L1Check (chk chk_spec)

/-- The checks of one job. -/
def checks (p q : ℕ) : Com :=
  .seq (nzc "s0" "a1") (.seq (nzc "s2" "a3") (.seq (lenc p q) (.seq (chk "Tt" "R")
    (.seq (.assign "Ee" (add (V "Tt") (V "P"))) (chk "D" "Ee")))))

theorem checks_spec (p q s0 a1 s2 a3 P R D Tt okc : ℕ) (hp : p < B) (hq : q < B) (hB : 1 < B)
    (h0 : s0 < B) (h1 : a1 < B) (h2 : s2 < B) (h3 : a3 < B) (hR : R < B) (hD : D < B)
    (hE : Tt + P < B) :
    Spec B (fun σ => σ.vars "s0" = s0 ∧ σ.vars "a1" = a1 ∧ σ.vars "s2" = s2 ∧ σ.vars "a3" = a3 ∧
        σ.vars "P" = P ∧ σ.vars "R" = R ∧ σ.vars "D" = D ∧ σ.vars "Tt" = Tt ∧
        σ.vars "ok" = okc) (checks p q)
      (fun σ σ' => σ'.vars "ok" =
          (if D < Tt + P then 0 else if Tt < R then 0 else
            if P = p ∨ P = q then
              (if s2 ≠ 0 ∧ a3 = 0 then 0 else if s0 ≠ 0 ∧ a1 = 0 then 0 else okc)
            else 0) ∧
        (∀ z, z ≠ "ok" → z ≠ "Ee" → σ'.vars z = σ.vars z) ∧ σ'.arrs = σ.arrs ∧
        σ'.out = σ.out) 60 := by
  intro σ ⟨e0, e1, e2, e3, eP, eR, eD, eT, eok⟩
  obtain ⟨σ1, r1, c1, v1, a1', o1⟩ := nzc_spec (B := B) "s0" "a1" hB σ
    ⟨by rw [e0]; exact h0, by rw [e1]; exact h1⟩
  obtain ⟨σ2, r2, c2, v2, a2', o2⟩ := nzc_spec (B := B) "s2" "a3" hB σ1
    ⟨by rw [v1 _ (by decide), e2]; exact h2, by rw [v1 _ (by decide), e3]; exact h3⟩
  obtain ⟨σ3, r3, c3, v3, a3', o3⟩ := lenc_spec (B := B) p q hB hp hq σ2
    (by show σ2.vars "P" < B; rw [v2 _ (by decide), v1 _ (by decide), eP]; omega)
  have k3 : ∀ z, z ≠ "ok" → σ3.vars z = σ.vars z := fun z hz => by
    rw [v3 z hz, v2 z hz, v1 z hz]
  obtain ⟨σ4, r4, c4, v4, a4', o4⟩ := chk_spec (B := B) "Tt" "R" hB σ3
    ⟨by rw [k3 _ (by decide), eT]; omega, by rw [k3 _ (by decide), eR]; exact hR⟩
  have k4 : ∀ z, z ≠ "ok" → σ4.vars z = σ.vars z := fun z hz => by rw [v4 z hz, k3 z hz]
  have r5 : Run B (.assign "Ee" (add (V "Tt") (V "P"))) σ4
      (σ4.setVar "Ee" (σ4.vars "Tt" + σ4.vars "P")) (1 + (add (V "Tt") (V "P")).size) :=
    Run.assign (evalB_bin (evalB_var (by rw [k4 _ (by decide), eT]; omega))
      (evalB_var (by rw [k4 _ (by decide), eP]; omega))
      (by simp [k4 "Tt" (by decide), k4 "P" (by decide), eT, eP]; omega))
  rw [k4 "Tt" (by decide), k4 "P" (by decide), eT, eP] at r5
  set σ5 := σ4.setVar "Ee" (Tt + P) with h5
  have d5 : σ5.vars "D" = D := by simp [h5, Env.setVar, k4 "D" (by decide), eD]
  have e5 : σ5.vars "Ee" = Tt + P := by simp [h5, Env.setVar]
  have ok5 : σ5.vars "ok" = σ4.vars "ok" := by simp [h5, Env.setVar]
  obtain ⟨σ6, r6, c6, v6, a6', o6⟩ := chk_spec (B := B) "D" "Ee" hB σ5
    ⟨by rw [d5]; exact hD, by rw [e5]; exact hE⟩
  refine ⟨σ6, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))).mono (by simp [Expr.size]), ?_,
    fun z hz hz' => ?_, ?_, ?_⟩
  · rw [c6, d5, e5, ok5, c4, k3 "Tt" (by decide),
      k3 "R" (by decide), eT, eR, c3, v2 "P" (by decide), v1 "P" (by decide), eP, c2,
      v1 "s2" (by decide), v1 "a3" (by decide), e2, e3, c1, e0, e1, eok]
  · rw [v6 z hz]; simp only [h5, Env.setVar]; rw [if_neg hz', k4 z hz]
  · rw [a6']; simp only [h5, Env.setVar]; rw [a4', a3', a2', a1']
  · rw [o6]; simp only [h5, Env.setVar]; rw [o4, o3, o2, o1]

def shifts : Com :=
  .seq (shift "R" "s0" "a1") (.seq (shift "D" "s2" "a3") (shift "Tt" "ts" "ta"))

theorem shifts_spec (Ov s0 a1 s2 a3 ts ta : ℕ) (hB : 1 < B) (h0 : s0 < B) (h2 : s2 < B)
    (h4 : ts < B) (h1 : Ov + a1 < B) (h3 : Ov + a3 < B) (h5 : Ov + ta < B) :
    Spec B (fun σ => σ.vars "O" = Ov ∧ σ.vars "s0" = s0 ∧ σ.vars "a1" = a1 ∧ σ.vars "s2" = s2 ∧
        σ.vars "a3" = a3 ∧ σ.vars "ts" = ts ∧ σ.vars "ta" = ta) shifts
      (fun σ σ' => σ'.vars "R" = sh Ov s0 a1 ∧ σ'.vars "D" = sh Ov s2 a3 ∧
        σ'.vars "Tt" = sh Ov ts ta ∧ (∀ z ∉ ["R", "D", "Tt"], σ'.vars z = σ.vars z) ∧
        σ'.arrs = σ.arrs ∧ σ'.out = σ.out) 30 := by
  run_vcg
  all_goals have e0 := ‹σ.vars "O" = Ov›
  all_goals have e1 := ‹σ.vars "s0" = s0›
  all_goals have e2 := ‹σ.vars "a1" = a1›
  all_goals have e3 := ‹σ.vars "s2" = s2›
  all_goals have e4 := ‹σ.vars "a3" = a3›
  all_goals have e5 := ‹σ.vars "ts" = ts›
  all_goals have e6 := ‹σ.vars "ta" = ta›
  all_goals try simp [Env.setVar, e0, e1, e2, e3, e4, e5, e6] at *
  all_goals try simp_all [sh]

def stores : Com :=
  .seq (.store "TT" (V "fj") (V "Tt")) (.seq (.store "PP" (V "fj") (V "P"))
    (.assign "fj" (add (V "fj") (.lit 1))))

theorem stores_spec (tt pp : List ℕ) (j a b : ℕ) (hj : j < tt.length) (hj' : j < pp.length)
    (hjB : j + 1 < B) (ha : a < B) (hb : b < B) :
    Spec B (fun σ => σ.arrs "TT" = tt ∧ σ.arrs "PP" = pp ∧ σ.vars "fj" = j ∧ σ.vars "Tt" = a ∧
        σ.vars "P" = b) stores
      (fun σ σ' => σ'.arrs "TT" = tt.set j a ∧ σ'.arrs "PP" = pp.set j b ∧
        (∀ c, c ≠ "TT" → c ≠ "PP" → σ'.arrs c = σ.arrs c) ∧ σ'.vars "fj" = j + 1 ∧
        (∀ z, z ≠ "fj" → σ'.vars z = σ.vars z) ∧ σ'.out = σ.out) 12 := by
  run_vcg
  all_goals have e0 := ‹σ.arrs "TT" = tt›
  all_goals have e1 := ‹σ.arrs "PP" = pp›
  all_goals have e2 := ‹σ.vars "fj" = j›
  all_goals have e3 := ‹σ.vars "Tt" = a›
  all_goals have e4 := ‹σ.vars "P" = b›
  all_goals try simp [Env.setVar, Env.setArr, e0, e1, e2, e3, e4] at *
  all_goals first
    | omega
    | (refine ⟨fun c h1 h2 => by simp [h1, h2], fun z hz => by simp [hz]⟩)

/-- The conditions on job `j`, on shifted numbers. -/
def FOK (p q Ov : ℕ) (t : List ℕ) (n j : ℕ) : Prop :=
  ¬ (t.getD (1 + (5 * j + 0)) 0 ≠ 0 ∧ t.getD (1 + (5 * j + 1)) 0 = 0) ∧
  ¬ (t.getD (1 + (5 * j + 2)) 0 ≠ 0 ∧ t.getD (1 + (5 * j + 3)) 0 = 0) ∧
  (t.getD (1 + (5 * j + 4)) 0 = p ∨ t.getD (1 + (5 * j + 4)) 0 = q) ∧
  sh Ov (t.getD (1 + (5 * j + 0)) 0) (t.getD (1 + (5 * j + 1)) 0) ≤
    sh Ov (t.getD (1 + (5 * n + (2 * j + 0))) 0) (t.getD (1 + (5 * n + (2 * j + 1))) 0) ∧
  sh Ov (t.getD (1 + (5 * n + (2 * j + 0))) 0) (t.getD (1 + (5 * n + (2 * j + 1))) 0) +
    t.getD (1 + (5 * j + 4)) 0 ≤
    sh Ov (t.getD (1 + (5 * j + 2)) 0) (t.getD (1 + (5 * j + 3)) 0)

instance (p q Ov : ℕ) (t : List ℕ) (n j : ℕ) : Decidable (FOK p q Ov t n j) := by
  unfold FOK; infer_instance

lemma flag_front (p q s0 a1 s2 a3 P R D Tt okc : ℕ) (h : okc ≤ 1) :
    (if D < Tt + P then 0 else if Tt < R then 0 else
      if P = p ∨ P = q then
        (if s2 ≠ 0 ∧ a3 = 0 then 0 else if s0 ≠ 0 ∧ a1 = 0 then 0 else okc)
      else 0) =
    if okc = 1 ∧ (¬ (s0 ≠ 0 ∧ a1 = 0) ∧ ¬ (s2 ≠ 0 ∧ a3 = 0) ∧ (P = p ∨ P = q) ∧ R ≤ Tt ∧
      Tt + P ≤ D) then 1 else 0 := by
  split_ifs <;> omega

lemma sh_le (O s a : ℕ) : sh O s a ≤ O + a := by unfold sh; split <;> omega

def frontBody (p q : ℕ) : Com :=
  .seq loadA (.seq loadB (.seq shifts (.seq (checks p q) stores)))

theorem frontBody_spec (p q : ℕ) (t tt pp : List ℕ) (j n Ov okc Bt : ℕ) (hok : okc ≤ 1)
    (hj : j < n) (hlen : 1 + 7 * n ≤ t.length) (htB : ∀ k < 1 + 7 * n, t.getD k 0 < Bt)
    (hBig : Ov + 2 * Bt + 10 * n + 8 < B) (hp : p < B) (hq : q < B)
    (hjt : j < tt.length) (hjp : j < pp.length) :
    Spec B (fun σ => σ.arrs "TK" = t ∧ σ.arrs "TT" = tt ∧ σ.arrs "PP" = pp ∧ σ.vars "fj" = j ∧
        σ.vars "m5" = 5 * n ∧ σ.vars "O" = Ov ∧ σ.vars "ok" = okc) (frontBody p q)
      (fun σ σ' => σ'.vars "ok" = (if okc = 1 ∧ FOK p q Ov t n j then 1 else 0) ∧
        σ'.arrs "TT" = tt.set j (sh Ov (t.getD (1 + (5 * n + (2 * j + 0))) 0)
          (t.getD (1 + (5 * n + (2 * j + 1))) 0)) ∧
        σ'.arrs "PP" = pp.set j (t.getD (1 + (5 * j + 4)) 0) ∧ σ'.arrs "TK" = t ∧
        σ'.vars "fj" = j + 1 ∧ σ'.vars "m5" = 5 * n ∧ σ'.vars "O" = Ov ∧
        σ'.vars "nj" = σ.vars "nj" ∧ σ'.out = σ.out) 210 := by
  intro σ ⟨hTK, hTT, hPP, hfj, hm5, hO, hokv⟩
  have b : ∀ k < 1 + 7 * n, t.getD k 0 < B := fun k hk => by have := htB k hk; omega
  have b0 := htB (1 + (5 * j + 0)) (by omega)
  have b1 := htB (1 + (5 * j + 1)) (by omega)
  have b2 := htB (1 + (5 * j + 2)) (by omega)
  have b3 := htB (1 + (5 * j + 3)) (by omega)
  have b4 := htB (1 + (5 * j + 4)) (by omega)
  have b5 := htB (1 + (5 * n + (2 * j + 0))) (by omega)
  have b6 := htB (1 + (5 * n + (2 * j + 1))) (by omega)
  obtain ⟨σ1, r1, l0, l1, l2, l3, k1, a1, o1⟩ := loadA_spec (B := B) t j (by omega) (by omega)
    (fun k hk => b k (by omega)) σ ⟨hTK, hfj⟩
  have k1' : ∀ z, z ∉ ["s0", "a1", "s2", "a3"] → σ1.vars z = σ.vars z := k1
  obtain ⟨σ2, r2, l4, l5, l6, k2, a2, o2⟩ := loadB_spec (B := B) t j (5 * n) (by omega) (by omega)
    (by omega) (fun k hk => b k (by omega)) (b _ (by omega)) σ1
    ⟨by rw [a1]; exact hTK, by rw [k1' _ (by decide)]; exact hfj,
      by rw [k1' _ (by decide)]; exact hm5⟩
  have k2' : ∀ z, z ∉ ["P", "ts", "ta"] → σ2.vars z = σ1.vars z := k2
  obtain ⟨σ3, r3, s1, s2, s3, k3, a3, o3⟩ := shifts_spec (B := B) Ov (t.getD (1 + (5 * j + 0)) 0) (t.getD (1 + (5 * j + 1)) 0)
    (t.getD (1 + (5 * j + 2)) 0) (t.getD (1 + (5 * j + 3)) 0)
    (t.getD (1 + (5 * n + (2 * j + 0))) 0) (t.getD (1 + (5 * n + (2 * j + 1))) 0) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) σ2
    ⟨by rw [k2' _ (by decide), k1' _ (by decide)]; exact hO, by rw [k2' _ (by decide)]; exact l0,
      by rw [k2' _ (by decide)]; exact l1, by rw [k2' _ (by decide)]; exact l2,
      by rw [k2' _ (by decide)]; exact l3, l5, l6⟩
  have k3' : ∀ z, z ∉ ["R", "D", "Tt"] → σ3.vars z = σ2.vars z := k3
  have hR := sh_le Ov (t.getD (1 + (5 * j + 0)) 0) (t.getD (1 + (5 * j + 1)) 0)
  have hD := sh_le Ov (t.getD (1 + (5 * j + 2)) 0) (t.getD (1 + (5 * j + 3)) 0)
  have hT := sh_le Ov (t.getD (1 + (5 * n + (2 * j + 0))) 0) (t.getD (1 + (5 * n + (2 * j + 1))) 0)
  obtain ⟨σ4, r4, c4, k4, a4, o4⟩ := checks_spec (B := B) p q (t.getD (1 + (5 * j + 0)) 0) (t.getD (1 + (5 * j + 1)) 0)
    (t.getD (1 + (5 * j + 2)) 0) (t.getD (1 + (5 * j + 3)) 0) (t.getD (1 + (5 * j + 4)) 0)
    (sh Ov (t.getD (1 + (5 * j + 0)) 0) (t.getD (1 + (5 * j + 1)) 0)) (sh Ov (t.getD (1 + (5 * j + 2)) 0) (t.getD (1 + (5 * j + 3)) 0))
    (sh Ov (t.getD (1 + (5 * n + (2 * j + 0))) 0) (t.getD (1 + (5 * n + (2 * j + 1))) 0)) okc hp hq (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) σ3
    ⟨by rw [k3' _ (by decide), k2' _ (by decide)]; exact l0,
      by rw [k3' _ (by decide), k2' _ (by decide)]; exact l1,
      by rw [k3' _ (by decide), k2' _ (by decide)]; exact l2,
      by rw [k3' _ (by decide), k2' _ (by decide)]; exact l3,
      by rw [k3' _ (by decide)]; exact l4, s1, s2, s3,
      by rw [k3' _ (by decide), k2' _ (by decide), k1' _ (by decide)]; exact hokv⟩
  obtain ⟨σ5, r5, t5, p5, f5, j5, k5, o5⟩ := stores_spec (B := B) tt pp j (sh Ov (t.getD (1 + (5 * n + (2 * j + 0))) 0) (t.getD (1 + (5 * n + (2 * j + 1))) 0))
    (t.getD (1 + (5 * j + 4)) 0) hjt hjp (by omega)
    (show sh Ov (t.getD (1 + (5 * n + (2 * j + 0))) 0) (t.getD (1 + (5 * n + (2 * j + 1))) 0) < B
      by omega)
    (show t.getD (1 + (5 * j + 4)) 0 < B by omega) σ4
    ⟨by rw [a4, a3, a2, a1]; exact hTT, by rw [a4, a3, a2, a1]; exact hPP,
      by rw [k4 _ (by decide) (by decide), k3' _ (by decide), k2' _ (by decide),
        k1' _ (by decide)]; exact hfj,
      by rw [k4 _ (by decide) (by decide)]; exact s3,
      by rw [k4 _ (by decide) (by decide), k3' _ (by decide)]; exact l4⟩
  have keep : ∀ z, z ∉ ["s0", "a1", "s2", "a3", "P", "ts", "ta", "R", "D", "Tt", "ok", "Ee", "fj"] →
      σ5.vars z = σ.vars z := fun z hz => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [k5 z (by tauto), k4 z (by tauto) (by tauto), k3' z (by simp; tauto),
      k2' z (by simp; tauto), k1' z (by simp; tauto)]
  refine ⟨σ5, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono (by omega), ?_, t5, p5, ?_, j5, ?_, ?_,
    keep _ (by decide), ?_⟩
  · rw [k5 _ (by decide), c4, flag_front p q _ _ _ _ _ _ _ _ okc hok]; rfl
  · rw [f5 _ (by decide) (by decide), a4, a3, a2, a1]; exact hTK
  · rw [keep _ (by decide)]; exact hm5
  · rw [keep _ (by decide)]; exact hO
  · rw [o5, o4, o3, o2, o1]

open Lax391470Proofs.Flag

/-- The shifted start time of job `j`. -/
def ttv (Ov : ℕ) (t : List ℕ) (n j : ℕ) : ℕ :=
  sh Ov (t.getD (1 + (5 * n + (2 * j + 0))) 0) (t.getD (1 + (5 * n + (2 * j + 1))) 0)
/-- The length of job `j`. -/
def ppv (t : List ℕ) (j : ℕ) : ℕ := t.getD (1 + (5 * j + 4)) 0

lemma getD_set_eq (l : List ℕ) (j a : ℕ) (hj : j < l.length) : (l.set j a).getD j 0 = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hj]; rfl

lemma getD_set_ne (l : List ℕ) {j k : ℕ} (a : ℕ) (h : j ≠ k) :
    (l.set j a).getD k 0 = l.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

def frontLoop (p q : ℕ) : Com :=
  .seq (.assign "fj" (.lit 0)) (.while (.lt (V "fj") (V "nj")) (frontBody p q))

inductive FrInv (p q : ℕ) (t : List ℕ) (n Ov okin : ℕ) (out0 : List ℕ) (σ : Env) : Prop where
  | mk
    (hTK : σ.arrs "TK" = t)
    (hnj : σ.vars "nj" = n)
    (hm5 : σ.vars "m5" = 5 * n)
    (hO : σ.vars "O" = Ov)
    (hfj : σ.vars "fj" ≤ n)
    (hok : σ.vars "ok" = flagTo (FOK p q Ov t n) okin (σ.vars "fj"))
    (hlt : n ≤ (σ.arrs "TT").length)
    (hlp : n ≤ (σ.arrs "PP").length)
    (hval : ∀ j' < σ.vars "fj", (σ.arrs "TT").getD j' 0 = ttv Ov t n j' ∧
      (σ.arrs "PP").getD j' 0 = ppv t j')
    (hout : σ.out = out0)

theorem FrInv.hnj
    {p q : ℕ} {t : List ℕ} {n Ov okin : ℕ} {out0 : List ℕ} {σ : Env}
    (h : FrInv p q t n Ov okin out0 σ) : σ.vars "nj" = n :=
  match h with | ⟨_, x, _, _, _, _, _, _, _, _⟩ => x

theorem FrInv.hfj
    {p q : ℕ} {t : List ℕ} {n Ov okin : ℕ} {out0 : List ℕ} {σ : Env}
    (h : FrInv p q t n Ov okin out0 σ) : σ.vars "fj" ≤ n :=
  match h with | ⟨_, _, _, _, x, _, _, _, _, _⟩ => x

/-- **The pass over the jobs.** -/
theorem frontLoop_spec (p q : ℕ) (t : List ℕ) (n Ov okin Bt : ℕ) (out0 : List ℕ)
    (hlen : 1 + 7 * n ≤ t.length) (htB : ∀ k < 1 + 7 * n, t.getD k 0 < Bt)
    (hBig : Ov + 2 * Bt + 10 * n + 8 < B) (hp : p < B) (hq : q < B) :
    Spec B (fun σ => FrInv p q t n Ov okin out0 (σ.setVar "fj" 0)) (frontLoop p q)
      (fun _ σ' => FrInv p q t n Ov okin out0 σ' ∧ σ'.vars "fj" = n) ((210 + 4) * n + 6) := by
  refine Spec.forRangeZero "fj" "nj" (FrInv p q t n Ov okin out0) n 210 (by omega)
    (fun _ h => h.hfj) (fun _ h => h.hnj) ?_
  intro σ ⟨⟨hTK, hnj, hm5, hO, hfj, hok, hlt, hlp, hval, hout⟩, hlt'⟩
  obtain ⟨σ', r, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ := frontBody_spec (B := B) p q t
    (σ.arrs "TT") (σ.arrs "PP") (σ.vars "fj") n Ov _ Bt (flagTo_le _ okin (σ.vars "fj")) hlt' hlen
    htB hBig hp hq (by omega) (by omega) σ ⟨hTK, rfl, rfl, rfl, hm5, hO, hok⟩
  refine ⟨σ', r, ⟨q4, by rw [q8]; exact hnj, q6, q7, by omega, by rw [q1, q5, flagTo_succ],
    by rw [q2, List.length_set]; exact hlt, by rw [q3, List.length_set]; exact hlp, ?_,
    by rw [q9]; exact hout⟩, q5⟩
  intro j' hj'
  rw [q5] at hj'
  rw [q2, q3]
  rcases Nat.lt_or_ge j' (σ.vars "fj") with h | h
  · rw [getD_set_ne _ _ (by omega), getD_set_ne _ _ (by omega)]
    exact hval j' h
  · have e : j' = σ.vars "fj" := by omega
    rw [e, getD_set_eq _ _ _ (by omega), getD_set_eq _ _ _ (by omega)]
    exact ⟨rfl, rfl⟩

end Lax391470Proofs.V1Front
