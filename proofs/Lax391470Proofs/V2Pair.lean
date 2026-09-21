import Lax391470Proofs.V2Ord

/-!
The pass of the verifier of `AUX p q` over the connected pairs.
-/

namespace Lax391470Proofs.V2Pair

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.L1Check (V add chk chk_spec load load_spec)
open Lax391470Proofs.V1Front (getD_set_eq getD_set_ne)
open Lax391470Proofs.Flag

variable {B : ℕ}

def loadP2 (p q : ℕ) : Com :=
  .seq (.assign "tL" (.get "TK" (add (V "bS") (add (V "nn") (V "i")))))
    (.seq (.assign "tS" (.get "TK" (add (V "bS") (add (V "nN") (V "i")))))
      (.seq (.assign "EL" (add (V "tL") (.lit p))) (.assign "ES" (add (V "tS") (.lit q)))))

theorem loadP2_spec (p q : ℕ) (t : List ℕ) (i0 b n m : ℕ) (h1 : b + (n + i0) < t.length)
    (h2 : b + (m + i0) < t.length) (hB : b + n + m + i0 + 8 < B)
    (hb1 : t.getD (b + (n + i0)) 0 + p < B) (hb2 : t.getD (b + (m + i0)) 0 + q < B) :
    Spec B (fun σ => σ.arrs "TK" = t ∧ σ.vars "i" = i0 ∧ σ.vars "bS" = b ∧ σ.vars "nn" = n ∧
        σ.vars "nN" = m) (loadP2 p q)
      (fun σ σ' => σ'.vars "tL" = t.getD (b + (n + i0)) 0 ∧
        σ'.vars "tS" = t.getD (b + (m + i0)) 0 ∧
        σ'.vars "EL" = t.getD (b + (n + i0)) 0 + p ∧ σ'.vars "ES" = t.getD (b + (m + i0)) 0 + q ∧
        (∀ z ∉ ["tL", "tS", "EL", "ES"], σ'.vars z = σ.vars z) ∧ σ'.arrs = σ.arrs ∧
        σ'.out = σ.out) 50 := by
  run_vcg
  all_goals have hT := ‹σ.arrs "TK" = t›
  all_goals have e1 := ‹σ.vars "i" = i0›
  all_goals have e2 := ‹σ.vars "bS" = b›
  all_goals have e3 := ‹σ.vars "nn" = n›
  all_goals have e4 := ‹σ.vars "nN" = m›
  all_goals try simp [Env.setVar, hT, e1, e2, e3, e4] at *
  all_goals first
    | omega
    | (intro z h0 h1 h2 h3; simp [h0, h1, h2, h3])

/-- Clear the flag if neither job of the pair is early. -/
def early : Com :=
  .ite (.lt (V "e0") (V "EL")) (.ite (.lt (V "e2") (V "ES")) (.assign "ok" (.lit 0)) .skip) .skip

theorem early_spec (hB : 1 < B) :
    Spec B (fun σ => σ.vars "e0" < B ∧ σ.vars "EL" < B ∧ σ.vars "e2" < B ∧ σ.vars "ES" < B) early
      (fun σ σ' => σ'.vars "ok" = (if σ.vars "e0" < σ.vars "EL" ∧ σ.vars "e2" < σ.vars "ES"
          then 0 else σ.vars "ok") ∧
        (∀ z, z ≠ "ok" → σ'.vars z = σ.vars z) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out) 10 := by
  run_vcg
  all_goals try simp_all [Env.setVar]

def checksP : Com := .seq (chk "e1" "EL") (.seq (chk "e3" "ES") early)

theorem checksP_spec (e0 e1 e2 e3 EL ES okc : ℕ) (hB : 1 < B) (h0 : e0 < B) (h1 : e1 < B)
    (h2 : e2 < B) (h3 : e3 < B) (hL : EL < B) (hS : ES < B) :
    Spec B (fun σ => σ.vars "e0" = e0 ∧ σ.vars "e1" = e1 ∧ σ.vars "e2" = e2 ∧ σ.vars "e3" = e3 ∧
        σ.vars "EL" = EL ∧ σ.vars "ES" = ES ∧ σ.vars "ok" = okc) checksP
      (fun σ σ' => σ'.vars "ok" = (if e0 < EL ∧ e2 < ES then 0 else if e3 < ES then 0 else
          if e1 < EL then 0 else okc) ∧
        (∀ z, z ≠ "ok" → σ'.vars z = σ.vars z) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out) 30 := by
  intro σ ⟨q0, q1, q2, q3, qL, qS, qok⟩
  obtain ⟨σ1, r1, c1, v1, a1, o1⟩ := chk_spec (B := B) "e1" "EL" hB σ
    ⟨by rw [q1]; exact h1, by rw [qL]; exact hL⟩
  obtain ⟨σ2, r2, c2, v2, a2, o2⟩ := chk_spec (B := B) "e3" "ES" hB σ1
    ⟨by rw [v1 _ (by decide), q3]; exact h3, by rw [v1 _ (by decide), qS]; exact hS⟩
  have k2 : ∀ z, z ≠ "ok" → σ2.vars z = σ.vars z := fun z hz => by rw [v2 z hz, v1 z hz]
  obtain ⟨σ3, r3, c3, v3, a3, o3⟩ := early_spec (B := B) hB σ2
    ⟨by rw [k2 _ (by decide), q0]; exact h0, by rw [k2 _ (by decide), qL]; exact hL,
      by rw [k2 _ (by decide), q2]; exact h2, by rw [k2 _ (by decide), qS]; exact hS⟩
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by omega), ?_, fun z hz => by rw [v3 z hz, k2 z hz],
    by rw [a3, a2, a1], by rw [o3, o2, o1]⟩
  rw [c3, k2 "e0" (by decide), k2 "EL" (by decide), k2 "e2" (by decide), k2 "ES" (by decide),
    q0, qL, q2, qS, c2, v1 "e3" (by decide), v1 "ES" (by decide), q3, qS, c1, q1, qL, qok]

lemma flag_pair (e0 e1 e2 e3 EL ES okc : ℕ) (h : okc ≤ 1) :
    (if e0 < EL ∧ e2 < ES then 0 else if e3 < ES then 0 else if e1 < EL then 0 else okc) =
      if okc = 1 ∧ (EL ≤ e1 ∧ ES ≤ e3 ∧ (EL ≤ e0 ∨ ES ≤ e2)) then 1 else 0 := by
  split_ifs <;> omega

def stores4 (p q : ℕ) : Com :=
  .seq (.store "TT" (add (V "nn") (V "i")) (V "tL"))
    (.seq (.store "PP" (add (V "nn") (V "i")) (.lit p))
      (.seq (.store "TT" (add (V "nN") (V "i")) (V "tS"))
        (.seq (.store "PP" (add (V "nN") (V "i")) (.lit q))
          (.assign "i" (add (V "i") (.lit 1))))))

theorem stores4_spec (p q : ℕ) (tt pp : List ℕ) (i0 n m a c : ℕ) (h1 : n + i0 < tt.length)
    (h2 : m + i0 < tt.length) (h1' : n + i0 < pp.length) (h2' : m + i0 < pp.length)
    (hB : n + m + i0 + 2 < B) (ha : a < B) (hc : c < B) (hp : p < B) (hq : q < B) :
    Spec B (fun σ => σ.arrs "TT" = tt ∧ σ.arrs "PP" = pp ∧ σ.vars "i" = i0 ∧ σ.vars "nn" = n ∧
        σ.vars "nN" = m ∧ σ.vars "tL" = a ∧ σ.vars "tS" = c) (stores4 p q)
      (fun σ σ' => σ'.arrs "TT" = (tt.set (n + i0) a).set (m + i0) c ∧
        σ'.arrs "PP" = (pp.set (n + i0) p).set (m + i0) q ∧
        (∀ x, x ≠ "TT" → x ≠ "PP" → σ'.arrs x = σ.arrs x) ∧ σ'.vars "i" = i0 + 1 ∧
        (∀ z, z ≠ "i" → σ'.vars z = σ.vars z) ∧ σ'.out = σ.out) 30 := by
  run_vcg
  all_goals have e0 := ‹σ.arrs "TT" = tt›
  all_goals have e1 := ‹σ.arrs "PP" = pp›
  all_goals have e2 := ‹σ.vars "i" = i0›
  all_goals have e3 := ‹σ.vars "nn" = n›
  all_goals have e4 := ‹σ.vars "nN" = m›
  all_goals have e5 := ‹σ.vars "tL" = a›
  all_goals have e6 := ‹σ.vars "tS" = c›
  all_goals try simp [Env.setVar, Env.setArr, e0, e1, e2, e3, e4, e5, e6] at *
  all_goals first
    | omega
    | (refine ⟨fun x h1 h2 => by simp [h1, h2], fun z hz => by simp [hz]⟩)

/-- The conditions on pair `i`. -/
def FP (p q : ℕ) (t : List ℕ) (b3 bS n m i : ℕ) : Prop :=
  t.getD (bS + (n + i)) 0 + p ≤ t.getD (b3 + (4 * i + 1)) 0 ∧
  t.getD (bS + (m + i)) 0 + q ≤ t.getD (b3 + (4 * i + 3)) 0 ∧
  (t.getD (bS + (n + i)) 0 + p ≤ t.getD (b3 + (4 * i + 0)) 0 ∨
    t.getD (bS + (m + i)) 0 + q ≤ t.getD (b3 + (4 * i + 2)) 0)

instance (p q : ℕ) (t : List ℕ) (b3 bS n m i : ℕ) : Decidable (FP p q t b3 bS n m i) := by
  unfold FP; infer_instance

def pairBody (p q : ℕ) : Com := .seq load (.seq (loadP2 p q) (.seq checksP (stores4 p q)))

theorem pairBody_spec (p q : ℕ) (t tt pp : List ℕ) (i0 N b3 bS n m okc Bt Tn : ℕ)
    (hok : okc ≤ 1) (hTn : Tn ≤ t.length)
    (hi : i0 < N) (hl1 : b3 + 4 * N ≤ Tn) (hl2 : bS + (m + N) ≤ Tn) (hnm : n ≤ m)
    (htB : ∀ k < Tn, t.getD k 0 < Bt)
    (hBig : 2 * Bt + p + q + b3 + bS + 4 * N + n + m + 8 < B)
    (ht : m + N ≤ tt.length) (hp : m + N ≤ pp.length) :
    Spec B (fun σ => σ.arrs "TK" = t ∧ σ.arrs "TT" = tt ∧ σ.arrs "PP" = pp ∧ σ.vars "i" = i0 ∧
        σ.vars "b3" = b3 ∧ σ.vars "bS" = bS ∧ σ.vars "nn" = n ∧ σ.vars "nN" = m ∧
        σ.vars "ok" = okc) (pairBody p q)
      (fun σ σ' => σ'.vars "ok" = (if okc = 1 ∧ FP p q t b3 bS n m i0 then 1 else 0) ∧
        σ'.arrs "TT" = (tt.set (n + i0) (t.getD (bS + (n + i0)) 0)).set (m + i0)
          (t.getD (bS + (m + i0)) 0) ∧
        σ'.arrs "PP" = (pp.set (n + i0) p).set (m + i0) q ∧ σ'.arrs "TK" = t ∧
        σ'.vars "i" = i0 + 1 ∧
        (∀ z ∉ ["e0", "e1", "e2", "e3", "tL", "tS", "EL", "ES", "ok", "i"],
          σ'.vars z = σ.vars z) ∧ σ'.out = σ.out) 170 := by
  intro σ ⟨hTK, hTT, hPP, hiv, hb3, hbS, hnn, hnN, hokv⟩
  have c0 := htB (b3 + (4 * i0 + 0)) (by omega)
  have c1 := htB (b3 + (4 * i0 + 1)) (by omega)
  have c2 := htB (b3 + (4 * i0 + 2)) (by omega)
  have c3 := htB (b3 + (4 * i0 + 3)) (by omega)
  have cL := htB (bS + (n + i0)) (by omega)
  have cS := htB (bS + (m + i0)) (by omega)
  obtain ⟨σ1, r1, l0, l1, l2, l3, k1, a1, o1⟩ := load_spec (B := B) t i0 b3 (by omega) (by omega)
    (fun k hk => by have := htB k (by omega); omega) σ ⟨hTK, hiv, hb3⟩
  have k1' : ∀ z, z ∉ ["e0", "e1", "e2", "e3"] → σ1.vars z = σ.vars z := k1
  obtain ⟨σ2, r2, m0, m1, m2, m3, k2, a2, o2⟩ := loadP2_spec (B := B) p q t i0 bS n m (by omega)
    (by omega) (by omega) (by omega) (by omega) σ1
    ⟨by rw [a1]; exact hTK, by rw [k1' _ (by decide)]; exact hiv,
      by rw [k1' _ (by decide)]; exact hbS, by rw [k1' _ (by decide)]; exact hnn,
      by rw [k1' _ (by decide)]; exact hnN⟩
  have k2' : ∀ z, z ∉ ["tL", "tS", "EL", "ES"] → σ2.vars z = σ1.vars z := k2
  obtain ⟨σ3, r3, c3', k3, a3, o3⟩ := checksP_spec (B := B)
    (t.getD (b3 + (4 * i0 + 0)) 0) (t.getD (b3 + (4 * i0 + 1)) 0) (t.getD (b3 + (4 * i0 + 2)) 0)
    (t.getD (b3 + (4 * i0 + 3)) 0) (t.getD (bS + (n + i0)) 0 + p) (t.getD (bS + (m + i0)) 0 + q)
    okc (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) σ2
    ⟨by rw [k2' _ (by decide)]; exact l0, by rw [k2' _ (by decide)]; exact l1,
      by rw [k2' _ (by decide)]; exact l2, by rw [k2' _ (by decide)]; exact l3, m2, m3,
      by rw [k2' _ (by decide), k1' _ (by decide)]; exact hokv⟩
  obtain ⟨σ4, r4, t4, p4, f4, j4, k4, o4⟩ := stores4_spec (B := B) p q tt pp i0 n m
    (t.getD (bS + (n + i0)) 0) (t.getD (bS + (m + i0)) 0) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) σ3
    ⟨by rw [a3, a2, a1]; exact hTT, by rw [a3, a2, a1]; exact hPP,
      by rw [k3 _ (by decide), k2' _ (by decide), k1' _ (by decide)]; exact hiv,
      by rw [k3 _ (by decide), k2' _ (by decide), k1' _ (by decide)]; exact hnn,
      by rw [k3 _ (by decide), k2' _ (by decide), k1' _ (by decide)]; exact hnN,
      by rw [k3 _ (by decide)]; exact m0, by rw [k3 _ (by decide)]; exact m1⟩
  refine ⟨σ4, (r1.seq (r2.seq (r3.seq r4))).mono (by omega), ?_, t4, p4, ?_, j4, ?_, ?_⟩
  · rw [k4 _ (by decide), c3', flag_pair _ _ _ _ _ _ okc hok]; rfl
  · rw [f4 _ (by decide) (by decide), a3, a2, a1]; exact hTK
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [k4 z (by tauto), k3 z (by tauto), k2' z (by simp; tauto), k1' z (by simp; tauto)]
  · rw [o4, o3, o2, o1]

def pairLoop (p q : ℕ) : Com :=
  .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "N")) (pairBody p q))

inductive PInv (p q : ℕ) (t tt0 pp0 : List ℕ) (N b3 bS n m okin : ℕ) (keep : String → ℕ)
    (σ : Env) : Prop where
  | mk
    (hTK : σ.arrs "TK" = t)
    (hN : σ.vars "N" = N)
    (hi : σ.vars "i" ≤ N)
    (hok : σ.vars "ok" = flagTo (FP p q t b3 bS n m) okin (σ.vars "i"))
    (hlt : (σ.arrs "TT").length = tt0.length)
    (hlp : (σ.arrs "PP").length = pp0.length)
    (hold : ∀ o < n, (σ.arrs "TT").getD o 0 = tt0.getD o 0 ∧ (σ.arrs "PP").getD o 0 = pp0.getD o 0)
    (hval : ∀ i' < σ.vars "i",
      (σ.arrs "TT").getD (n + i') 0 = t.getD (bS + (n + i')) 0 ∧ (σ.arrs "PP").getD (n + i') 0 = p ∧
      (σ.arrs "TT").getD (m + i') 0 = t.getD (bS + (m + i')) 0 ∧ (σ.arrs "PP").getD (m + i') 0 = q)
    (hkeep : ∀ z ∉ ["e0", "e1", "e2", "e3", "tL", "tS", "EL", "ES", "ok", "i"], σ.vars z = keep z)
    (hout : σ.out = [])

theorem PInv.hN
    {p q : ℕ} {t tt0 pp0 : List ℕ} {N b3 bS n m okin : ℕ} {keep : String → ℕ} {σ : Env}
    (h : PInv p q t tt0 pp0 N b3 bS n m okin keep σ) : σ.vars "N" = N :=
  match h with | ⟨_, x, _, _, _, _, _, _, _, _⟩ => x

theorem PInv.hi
    {p q : ℕ} {t tt0 pp0 : List ℕ} {N b3 bS n m okin : ℕ} {keep : String → ℕ} {σ : Env}
    (h : PInv p q t tt0 pp0 N b3 bS n m okin keep σ) : σ.vars "i" ≤ N :=
  match h with | ⟨_, _, x, _, _, _, _, _, _, _⟩ => x

/-- **The pass over the pairs.** -/
theorem pairLoop_spec (p q : ℕ) (t tt0 pp0 : List ℕ) (N b3 bS n m okin Bt Tn : ℕ)
    (keep : String → ℕ) (hm : m = n + N) (hTn : Tn ≤ t.length)
    (hl1 : b3 + 4 * N ≤ Tn) (hl2 : bS + (m + N) ≤ Tn)
    (htB : ∀ k < Tn, t.getD k 0 < Bt)
    (hBig : 2 * Bt + p + q + b3 + bS + 4 * N + n + m + 8 < B)
    (ht : m + N ≤ tt0.length) (hp : m + N ≤ pp0.length)
    (hk1 : keep "b3" = b3) (hk2 : keep "bS" = bS) (hk3 : keep "nn" = n) (hk4 : keep "nN" = m) :
    Spec B (fun σ => PInv p q t tt0 pp0 N b3 bS n m okin keep (σ.setVar "i" 0)) (pairLoop p q)
      (fun _ σ' => PInv p q t tt0 pp0 N b3 bS n m okin keep σ' ∧ σ'.vars "i" = N)
      ((170 + 4) * N + 6) := by
  refine Spec.forRangeZero "i" "N" (PInv p q t tt0 pp0 N b3 bS n m okin keep) N 170 (by omega)
    (fun _ h => h.hi) (fun _ h => h.hN) ?_
  intro σ ⟨⟨hTK, hN, hi, hok, hlt, hlp, hold, hval, hkeep, hout⟩, hlt'⟩
  obtain ⟨σ', r, q1, q2, q3, q4, q5, q6, q7⟩ := pairBody_spec (B := B) p q t (σ.arrs "TT")
    (σ.arrs "PP") (σ.vars "i") N b3 bS n m _ Bt Tn (flagTo_le _ okin (σ.vars "i")) hTn hlt' hl1 hl2
    (by omega) htB hBig (by omega) (by omega) σ
    ⟨hTK, rfl, rfl, rfl, by rw [hkeep _ (by decide), hk1], by rw [hkeep _ (by decide), hk2],
      by rw [hkeep _ (by decide), hk3], by rw [hkeep _ (by decide), hk4], hok⟩
  have q6' : ∀ z, z ∉ ["e0", "e1", "e2", "e3", "tL", "tS", "EL", "ES", "ok", "i"] →
      σ'.vars z = σ.vars z := q6
  have hset : ∀ (l : List ℕ) (a c k : ℕ), m + N ≤ l.length →
      ((l.set (n + σ.vars "i") a).set (m + σ.vars "i") c).getD k 0 =
        if k = m + σ.vars "i" then c else if k = n + σ.vars "i" then a else l.getD k 0 := by
    intro l a c k hl
    by_cases h1 : k = m + σ.vars "i"
    · rw [if_pos h1, h1, getD_set_eq _ _ _ (by rw [List.length_set]; omega)]
    · rw [if_neg h1, getD_set_ne _ _ (fun h => h1 h.symm)]
      by_cases h2 : k = n + σ.vars "i"
      · rw [if_pos h2, h2, getD_set_eq _ _ _ (by omega)]
      · rw [if_neg h2, getD_set_ne _ _ (fun h => h2 h.symm)]
  refine ⟨σ', r, ⟨q4, by rw [q6' _ (by decide)]; exact hN, by omega,
    by rw [q1, q5, flagTo_succ], by rw [q2, List.length_set, List.length_set]; exact hlt,
    by rw [q3, List.length_set, List.length_set]; exact hlp, ?_, ?_,
    fun z hz => by rw [q6' z hz]; exact hkeep z hz, by rw [q7]; exact hout⟩, q5⟩
  · intro o ho
    rw [q2, q3, hset _ _ _ _ (by omega), hset _ _ _ _ (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact hold o ho
  · intro i' hi'
    rw [q5] at hi'
    rw [q2, q3]
    simp only [hset _ _ _ _ (show m + N ≤ (σ.arrs "TT").length by omega),
      hset _ _ _ _ (show m + N ≤ (σ.arrs "PP").length by omega)]
    rcases Nat.lt_or_ge i' (σ.vars "i") with h | h
    · obtain ⟨v1, v2, v3, v4⟩ := hval i' h
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      exact ⟨v1, v2, v3, v4⟩
    · have e : i' = σ.vars "i" := by omega
      rw [e, if_neg (by omega), if_pos rfl, if_neg (by omega), if_pos rfl, if_pos rfl, if_pos rfl]
      exact ⟨rfl, rfl, rfl, rfl⟩

end Lax391470Proofs.V2Pair
