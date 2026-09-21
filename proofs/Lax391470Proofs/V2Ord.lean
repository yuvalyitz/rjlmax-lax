import Lax391470Proofs.V1Front

/-!
The pass of the verifier of `AUX p q` over the ordinary jobs.
-/

namespace Lax391470Proofs.V2Ord

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.L1Check (V add chk chk_spec)
open Lax391470Proofs.AuxNk (mul)
open Lax391470Proofs.V1Front (stores stores_spec getD_set_eq getD_set_ne)
open Lax391470Proofs.Flag

variable {B : ℕ}

/-- Token `2 + (3 fj + c)`. -/
abbrev tkO (c : ℕ) : Expr := .get "TK" (add (.lit 2) (add (mul (.lit 3) (V "fj")) (.lit c)))

def loadO : Com :=
  .seq (.assign "R" (tkO 0)) (.seq (.assign "D" (tkO 1))
    (.seq (.assign "lg" (tkO 2)) (.assign "Tt" (.get "TK" (add (V "bS") (V "fj"))))))

theorem loadO_spec (t : List ℕ) (o b : ℕ) (hlen : 2 + (3 * o + 2) < t.length)
    (hlen' : b + o < t.length) (hB : b + 3 * o + 8 < B) (g0 : t.getD (2 + (3 * o + 0)) 0 < B)
    (g1 : t.getD (2 + (3 * o + 1)) 0 < B) (g2 : t.getD (2 + (3 * o + 2)) 0 < B)
    (g3 : t.getD (b + o) 0 < B) :
    Spec B (fun σ => σ.arrs "TK" = t ∧ σ.vars "fj" = o ∧ σ.vars "bS" = b) loadO
      (fun σ σ' => σ'.vars "R" = t.getD (2 + (3 * o + 0)) 0 ∧
        σ'.vars "D" = t.getD (2 + (3 * o + 1)) 0 ∧ σ'.vars "lg" = t.getD (2 + (3 * o + 2)) 0 ∧
        σ'.vars "Tt" = t.getD (b + o) 0 ∧
        (∀ z ∉ ["R", "D", "lg", "Tt"], σ'.vars z = σ.vars z) ∧ σ'.arrs = σ.arrs ∧
        σ'.out = σ.out) 50 := by
  run_vcg
  all_goals have hT := ‹σ.arrs "TK" = t›
  all_goals have hj := ‹σ.vars "fj" = o›
  all_goals have hb := ‹σ.vars "bS" = b›
  all_goals try simp [Env.setVar, hT, hj, hb] at *
  all_goals first
    | omega
    | (simpa using g0)
    | (simpa using g1)
    | (simpa using g2)
    | (simpa using g3)
    | (intro z h0 h1 h2 h3; simp [h0, h1, h2, h3])

def setLen (p q : ℕ) : Com :=
  .ite (.eq (V "lg") (.lit 0)) (.assign "P" (.lit q)) (.assign "P" (.lit p))

theorem setLen_spec (p q : ℕ) (hp : p < B) (hq : q < B) (hB : 1 < B) :
    Spec B (fun σ => σ.vars "lg" < B) (setLen p q)
      (fun σ σ' => σ'.vars "P" = (if σ.vars "lg" ≠ 0 then p else q) ∧
        (∀ z, z ≠ "P" → σ'.vars z = σ.vars z) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out) 10 := by
  run_vcg
  all_goals try simp_all [Env.setVar]

def checks2 : Com :=
  .seq (chk "Tt" "R") (.seq (.assign "Ee" (add (V "Tt") (V "P"))) (chk "D" "Ee"))

theorem checks2_spec (P R D Tt okc : ℕ) (hB : 1 < B) (hR : R < B) (hD : D < B)
    (hE : Tt + P < B) :
    Spec B (fun σ => σ.vars "P" = P ∧ σ.vars "R" = R ∧ σ.vars "D" = D ∧ σ.vars "Tt" = Tt ∧
        σ.vars "ok" = okc) checks2
      (fun σ σ' => σ'.vars "ok" = (if D < Tt + P then 0 else if Tt < R then 0 else okc) ∧
        (∀ z, z ≠ "ok" → z ≠ "Ee" → σ'.vars z = σ.vars z) ∧ σ'.arrs = σ.arrs ∧
        σ'.out = σ.out) 30 := by
  intro σ ⟨eP, eR, eD, eT, eok⟩
  obtain ⟨σ4, r4, c4, v4, a4', o4⟩ := chk_spec (B := B) "Tt" "R" hB σ
    ⟨by rw [eT]; omega, by rw [eR]; exact hR⟩
  have r5 : Run B (.assign "Ee" (add (V "Tt") (V "P"))) σ4
      (σ4.setVar "Ee" (σ4.vars "Tt" + σ4.vars "P")) (1 + (add (V "Tt") (V "P")).size) :=
    Run.assign (evalB_bin (evalB_var (by rw [v4 _ (by decide), eT]; omega))
      (evalB_var (by rw [v4 _ (by decide), eP]; omega))
      (by simp [v4 "Tt" (by decide), v4 "P" (by decide), eT, eP]; omega))
  rw [v4 "Tt" (by decide), v4 "P" (by decide), eT, eP] at r5
  set σ5 := σ4.setVar "Ee" (Tt + P) with h5
  have d5 : σ5.vars "D" = D := by simp [h5, Env.setVar, v4 "D" (by decide), eD]
  have e5 : σ5.vars "Ee" = Tt + P := by simp [h5, Env.setVar]
  have ok5 : σ5.vars "ok" = σ4.vars "ok" := by simp [h5, Env.setVar]
  obtain ⟨σ6, r6, c6, v6, a6', o6⟩ := chk_spec (B := B) "D" "Ee" hB σ5
    ⟨by rw [d5]; exact hD, by rw [e5]; exact hE⟩
  refine ⟨σ6, (r4.seq (r5.seq r6)).mono (by simp [Expr.size]), ?_, fun z hz hz' => ?_, ?_, ?_⟩
  · rw [c6, d5, e5, ok5, c4, eT, eR, eok]
  · rw [v6 z hz]; simp only [h5, Env.setVar]; rw [if_neg hz', v4 z hz]
  · rw [a6']; simp only [h5, Env.setVar]; rw [a4']
  · rw [o6]; simp only [h5, Env.setVar]; rw [o4]

/-- The conditions on the ordinary job `o`, its start time being token `b + o`. -/
def FO (p q : ℕ) (t : List ℕ) (b o : ℕ) : Prop :=
  t.getD (2 + (3 * o + 0)) 0 ≤ t.getD (b + o) 0 ∧
  t.getD (b + o) 0 + (if t.getD (2 + (3 * o + 2)) 0 ≠ 0 then p else q) ≤
    t.getD (2 + (3 * o + 1)) 0

instance (p q : ℕ) (t : List ℕ) (b o : ℕ) : Decidable (FO p q t b o) := by
  unfold FO; infer_instance

lemma flag_ord (P R D Tt okc : ℕ) (h : okc ≤ 1) :
    (if D < Tt + P then 0 else if Tt < R then 0 else okc) =
      if okc = 1 ∧ (R ≤ Tt ∧ Tt + P ≤ D) then 1 else 0 := by
  split_ifs <;> omega

def ordBody (p q : ℕ) : Com := .seq loadO (.seq (setLen p q) (.seq checks2 stores))

theorem ordBody_spec (p q : ℕ) (t tt pp : List ℕ) (o n b okc Bt Tn : ℕ) (hok : okc ≤ 1)
    (ho : o < n) (hTn : Tn ≤ t.length) (hlen : 2 + 3 * n ≤ Tn) (hlen' : b + n ≤ Tn)
    (htB : ∀ k < Tn, t.getD k 0 < Bt)
    (hBig : 2 * Bt + p + q + b + 3 * n + 8 < B) (hjt : o < tt.length) (hjp : o < pp.length) :
    Spec B (fun σ => σ.arrs "TK" = t ∧ σ.arrs "TT" = tt ∧ σ.arrs "PP" = pp ∧ σ.vars "fj" = o ∧
        σ.vars "bS" = b ∧ σ.vars "ok" = okc) (ordBody p q)
      (fun σ σ' => σ'.vars "ok" = (if okc = 1 ∧ FO p q t b o then 1 else 0) ∧
        σ'.arrs "TT" = tt.set o (t.getD (b + o) 0) ∧
        σ'.arrs "PP" = pp.set o (if t.getD (2 + (3 * o + 2)) 0 ≠ 0 then p else q) ∧
        σ'.arrs "TK" = t ∧ σ'.vars "fj" = o + 1 ∧
        (∀ z ∉ ["R", "D", "lg", "Tt", "P", "ok", "Ee", "fj"], σ'.vars z = σ.vars z) ∧
        σ'.out = σ.out) 110 := by
  intro σ ⟨hTK, hTT, hPP, hfj, hbS, hokv⟩
  have b0 := htB (2 + (3 * o + 0)) (by omega)
  have b1 := htB (2 + (3 * o + 1)) (by omega)
  have b2 := htB (2 + (3 * o + 2)) (by omega)
  have b3 := htB (b + o) (by omega)
  obtain ⟨σ1, r1, l0, l1, l2, l3, k1, a1, o1⟩ := loadO_spec (B := B) t o b (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) σ ⟨hTK, hfj, hbS⟩
  have k1' : ∀ z, z ∉ ["R", "D", "lg", "Tt"] → σ1.vars z = σ.vars z := k1
  obtain ⟨σ2, r2, c2, k2, a2, o2⟩ := setLen_spec (B := B) p q (by omega) (by omega) (by omega) σ1
    (by show σ1.vars "lg" < B; rw [l2]; omega)
  rw [l2] at c2
  have hP : (if t.getD (2 + (3 * o + 2)) 0 ≠ 0 then p else q) ≤ p + q := by split <;> omega
  obtain ⟨σ3, r3, c3, k3, a3, o3⟩ := checks2_spec (B := B)
    (if t.getD (2 + (3 * o + 2)) 0 ≠ 0 then p else q) (t.getD (2 + (3 * o + 0)) 0)
    (t.getD (2 + (3 * o + 1)) 0) (t.getD (b + o) 0) okc (by omega) (by omega) (by omega)
    (by omega) σ2
    ⟨c2, by rw [k2 _ (by decide)]; exact l0, by rw [k2 _ (by decide)]; exact l1,
      by rw [k2 _ (by decide)]; exact l3,
      by rw [k2 _ (by decide), k1' _ (by decide)]; exact hokv⟩
  obtain ⟨σ4, r4, t4, p4, f4, j4, k4, o4⟩ := stores_spec (B := B) tt pp o (t.getD (b + o) 0)
    (if t.getD (2 + (3 * o + 2)) 0 ≠ 0 then p else q) hjt hjp (by omega) (by omega) (by omega) σ3
    ⟨by rw [a3, a2, a1]; exact hTT, by rw [a3, a2, a1]; exact hPP,
      by rw [k3 _ (by decide) (by decide), k2 _ (by decide), k1' _ (by decide)]; exact hfj,
      by rw [k3 _ (by decide) (by decide), k2 _ (by decide)]; exact l3,
      by rw [k3 _ (by decide) (by decide)]; exact c2⟩
  refine ⟨σ4, (r1.seq (r2.seq (r3.seq r4))).mono (by omega), ?_, t4, p4, ?_, j4, ?_, ?_⟩
  · rw [k4 _ (by decide), c3, flag_ord _ _ _ _ okc hok]; rfl
  · rw [f4 _ (by decide) (by decide), a3, a2, a1]; exact hTK
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [k4 z (by tauto), k3 z (by tauto) (by tauto), k2 z (by tauto), k1' z (by simp; tauto)]
  · rw [o4, o3, o2, o1]

def ordLoop (p q : ℕ) : Com :=
  .seq (.assign "fj" (.lit 0)) (.while (.lt (V "fj") (V "nn")) (ordBody p q))

/-- The length of the ordinary job `o`. -/
def lenO (p q : ℕ) (t : List ℕ) (o : ℕ) : ℕ := if t.getD (2 + (3 * o + 2)) 0 ≠ 0 then p else q

inductive OInv (p q : ℕ) (t : List ℕ) (n b okin lt lp : ℕ) (keep : String → ℕ) (σ : Env) :
    Prop where
  | mk
    (hTK : σ.arrs "TK" = t)
    (hnn : σ.vars "nn" = n)
    (hbS : σ.vars "bS" = b)
    (hfj : σ.vars "fj" ≤ n)
    (hok : σ.vars "ok" = flagTo (FO p q t b) okin (σ.vars "fj"))
    (hlt : (σ.arrs "TT").length = lt)
    (hlp : (σ.arrs "PP").length = lp)
    (hval : ∀ o < σ.vars "fj", (σ.arrs "TT").getD o 0 = t.getD (b + o) 0 ∧
      (σ.arrs "PP").getD o 0 = lenO p q t o)
    (hkeep : ∀ z ∉ ["R", "D", "lg", "Tt", "P", "ok", "Ee", "fj"], σ.vars z = keep z)
    (hout : σ.out = [])

theorem OInv.hnn
    {p q : ℕ} {t : List ℕ} {n b okin lt lp : ℕ} {keep : String → ℕ} {σ : Env}
    (h : OInv p q t n b okin lt lp keep σ) : σ.vars "nn" = n :=
  match h with | ⟨_, x, _, _, _, _, _, _, _, _⟩ => x

theorem OInv.hfj
    {p q : ℕ} {t : List ℕ} {n b okin lt lp : ℕ} {keep : String → ℕ} {σ : Env}
    (h : OInv p q t n b okin lt lp keep σ) : σ.vars "fj" ≤ n :=
  match h with | ⟨_, _, _, x, _, _, _, _, _, _⟩ => x

/-- **The pass over the ordinary jobs.** -/
theorem ordLoop_spec (p q : ℕ) (t : List ℕ) (n b okin Bt Tn lt lp : ℕ) (keep : String → ℕ)
    (hTn : Tn ≤ t.length) (hlen : 2 + 3 * n ≤ Tn) (hlen' : b + n ≤ Tn)
    (htB : ∀ k < Tn, t.getD k 0 < Bt) (hBig : 2 * Bt + p + q + b + 3 * n + 8 < B)
    (hkt : n ≤ lt) (hkp : n ≤ lp) :
    Spec B (fun σ => OInv p q t n b okin lt lp keep (σ.setVar "fj" 0)) (ordLoop p q)
      (fun _ σ' => OInv p q t n b okin lt lp keep σ' ∧ σ'.vars "fj" = n) ((110 + 4) * n + 6) := by
  refine Spec.forRangeZero "fj" "nn" (OInv p q t n b okin lt lp keep) n 110 (by omega)
    (fun _ h => h.hfj) (fun _ h => h.hnn) ?_
  intro σ ⟨⟨hTK, hnn, hbS, hfj, hok, hlt, hlp, hval, hkeep, hout⟩, hlt'⟩
  obtain ⟨σ', r, q1, q2, q3, q4, q5, q6, q7⟩ := ordBody_spec (B := B) p q t (σ.arrs "TT")
    (σ.arrs "PP") (σ.vars "fj") n b _ Bt Tn (flagTo_le _ okin (σ.vars "fj")) hlt' hTn hlen hlen' htB
    hBig (by omega) (by omega) σ ⟨hTK, rfl, rfl, rfl, hbS, hok⟩
  have q6' : ∀ z, z ∉ ["R", "D", "lg", "Tt", "P", "ok", "Ee", "fj"] → σ'.vars z = σ.vars z := q6
  refine ⟨σ', r, ⟨q4, by rw [q6' _ (by decide)]; exact hnn, by rw [q6' _ (by decide)]; exact hbS,
    by omega, by rw [q1, q5, flagTo_succ],
    by rw [q2, List.length_set]; exact hlt, by rw [q3, List.length_set]; exact hlp, ?_,
    fun z hz => by rw [q6' z hz]; exact hkeep z hz, by rw [q7]; exact hout⟩, q5⟩
  intro o ho
  rw [q5] at ho
  rw [q2, q3]
  rcases Nat.lt_or_ge o (σ.vars "fj") with h | h
  · rw [getD_set_ne _ _ (by omega), getD_set_ne _ _ (by omega)]
    exact hval o h
  · have e : o = σ.vars "fj" := by omega
    rw [e, getD_set_eq _ _ _ (by omega), getD_set_eq _ _ _ (by omega)]
    exact ⟨rfl, rfl⟩

end Lax391470Proofs.V2Ord
