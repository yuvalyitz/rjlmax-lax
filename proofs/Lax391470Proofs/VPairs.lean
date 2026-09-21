import Lax391470Proofs.L1Check

/-!
The quadratic check of a schedule: no two jobs overlap. A double loop over the arrays
`TT` of start times and `PP` of lengths, clearing the flag `ok`.
-/

namespace Lax391470Proofs.VPairs

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.L1Check (V add)

/-- Jobs `i` and `j` do not overlap. -/
def fine (tt pp : List ℕ) (i j : ℕ) : Prop :=
  i = j ∨ tt.getD i 0 + pp.getD i 0 ≤ tt.getD j 0 ∨ tt.getD j 0 + pp.getD j 0 ≤ tt.getD i 0

instance (tt pp : List ℕ) (i j : ℕ) : Decidable (fine tt pp i j) := by
  unfold fine; infer_instance

/-- The flag after `j` rounds of the inner loop. -/
def okI (tt pp : List ℕ) (i okin j : ℕ) : ℕ :=
  if okin = 1 ∧ ∀ j' < j, fine tt pp i j' then 1 else 0

/-- The flag after `i` rounds of the outer loop. -/
def okO (tt pp : List ℕ) (n okin i : ℕ) : ℕ :=
  if okin = 1 ∧ ∀ i' < i, ∀ j' < n, fine tt pp i' j' then 1 else 0

lemma okI_le (tt pp : List ℕ) (i okin j : ℕ) : okI tt pp i okin j ≤ 1 := by
  unfold okI; split <;> omega

lemma okO_le (tt pp : List ℕ) (n okin i : ℕ) : okO tt pp n okin i ≤ 1 := by
  unfold okO; split <;> omega

lemma okI_zero (tt pp : List ℕ) (i okin : ℕ) (h : okin ≤ 1) : okI tt pp i okin 0 = okin := by
  unfold okI; split_ifs with h1 <;> simp at h1 <;> omega

lemma okO_zero (tt pp : List ℕ) (n okin : ℕ) (h : okin ≤ 1) : okO tt pp n okin 0 = okin := by
  unfold okO; split_ifs with h1 <;> simp at h1 <;> omega

lemma forall_lt_succ {P : ℕ → Prop} (j : ℕ) : (∀ k < j + 1, P k) ↔ (∀ k < j, P k) ∧ P j :=
  ⟨fun h => ⟨fun k hk => h k (by omega), h j (by omega)⟩, fun h k hk => by
    rcases Nat.lt_or_ge k j with h1 | h1
    · exact h.1 k h1
    · have : k = j := by omega
      rw [this]; exact h.2⟩

lemma okI_succ (tt pp : List ℕ) (i okin j : ℕ) :
    okI tt pp i okin (j + 1) = if okI tt pp i okin j = 1 ∧ fine tt pp i j then 1 else 0 := by
  unfold okI
  have e := @forall_lt_succ (fun k => fine tt pp i k) j
  by_cases hA : okin = 1 ∧ ∀ j' < j + 1, fine tt pp i j'
  · have h := e.mp hA.2
    rw [if_pos hA, if_pos ⟨by rw [if_pos ⟨hA.1, h.1⟩], h.2⟩]
  · rw [if_neg hA]
    symm; apply if_neg
    rintro ⟨h1, h2⟩
    by_cases hC : okin = 1 ∧ ∀ j' < j, fine tt pp i j'
    · exact hA ⟨hC.1, e.mpr ⟨hC.2, h2⟩⟩
    · rw [if_neg hC] at h1; omega

lemma okO_succ (tt pp : List ℕ) (n okin i : ℕ) :
    okO tt pp n okin (i + 1) = okI tt pp i (okO tt pp n okin i) n := by
  unfold okO okI
  have e := @forall_lt_succ (fun k => ∀ j' < n, fine tt pp k j') i
  by_cases hA : okin = 1 ∧ ∀ i' < i + 1, ∀ j' < n, fine tt pp i' j'
  · have h := e.mp hA.2
    rw [if_pos hA, if_pos ⟨by rw [if_pos ⟨hA.1, h.1⟩], h.2⟩]
  · rw [if_neg hA]
    symm; apply if_neg
    rintro ⟨h1, h2⟩
    by_cases hC : okin = 1 ∧ ∀ i' < i, ∀ j' < n, fine tt pp i' j'
    · exact hA ⟨hC.1, e.mpr ⟨hC.2, h2⟩⟩
    · rw [if_neg hC] at h1; omega

/-- The arithmetic of one round. -/
lemma flag_step (tt pp : List ℕ) (i j okc : ℕ) (h : okc ≤ 1) :
    (if i ≠ j ∧ tt.getD j 0 < tt.getD i 0 + pp.getD i 0 ∧
        tt.getD i 0 < tt.getD j 0 + pp.getD j 0 then 0 else okc) =
    if okc = 1 ∧ fine tt pp i j then 1 else 0 := by
  unfold fine
  split_ifs <;> omega

variable {B : ℕ}

def loadIJ : Com :=
  .seq (.assign "x1" (add (.get "TT" (V "vi")) (.get "PP" (V "vi"))))
    (.seq (.assign "y1" (.get "TT" (V "vj")))
      (.seq (.assign "u1" (add (.get "TT" (V "vj")) (.get "PP" (V "vj"))))
        (.assign "v1" (.get "TT" (V "vi")))))

theorem loadIJ_spec (tt pp : List ℕ) (i j : ℕ) (hi : i < tt.length) (hj : j < tt.length)
    (hi' : i < pp.length) (hj' : j < pp.length) (hiB : i < B) (hjB : j < B)
    (bi : tt.getD i 0 + pp.getD i 0 < B) (bj : tt.getD j 0 + pp.getD j 0 < B) :
    Spec B (fun σ => σ.arrs "TT" = tt ∧ σ.arrs "PP" = pp ∧ σ.vars "vi" = i ∧ σ.vars "vj" = j)
      loadIJ
      (fun σ σ' => σ'.vars "x1" = tt.getD i 0 + pp.getD i 0 ∧ σ'.vars "y1" = tt.getD j 0 ∧
        σ'.vars "u1" = tt.getD j 0 + pp.getD j 0 ∧ σ'.vars "v1" = tt.getD i 0 ∧
        (∀ z ∉ ["x1", "y1", "u1", "v1"], σ'.vars z = σ.vars z) ∧ σ'.arrs = σ.arrs ∧
        σ'.out = σ.out) 40 := by
  run_vcg
  all_goals have hT := ‹σ.arrs "TT" = tt›
  all_goals have hP := ‹σ.arrs "PP" = pp›
  all_goals have hvi := ‹σ.vars "vi" = i›
  all_goals have hvj := ‹σ.vars "vj" = j›
  all_goals try simp [Env.setVar, hT, hP, hvi, hvj] at *
  all_goals first
    | omega
    | (intro z h0 h1 h2 h3; simp [h0, h1, h2, h3])

def ovl : Com :=
  .ite (.eq (V "vi") (V "vj")) .skip
    (.ite (.lt (V "y1") (V "x1"))
      (.ite (.lt (V "v1") (V "u1")) (.assign "ok" (.lit 0)) .skip) .skip)

theorem ovl_spec (hB : 1 < B) :
    Spec B (fun σ => σ.vars "vi" < B ∧ σ.vars "vj" < B ∧ σ.vars "x1" < B ∧ σ.vars "y1" < B ∧
        σ.vars "u1" < B ∧ σ.vars "v1" < B) ovl
      (fun σ σ' => σ'.vars "ok" = (if σ.vars "vi" ≠ σ.vars "vj" ∧ σ.vars "y1" < σ.vars "x1" ∧
          σ.vars "v1" < σ.vars "u1" then 0 else σ.vars "ok") ∧
        (∀ z, z ≠ "ok" → σ'.vars z = σ.vars z) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out) 20 := by
  run_vcg
  all_goals try simp_all [Env.setVar]

def innerBody : Com := .seq loadIJ (.seq ovl (.assign "vj" (add (V "vj") (.lit 1))))

theorem innerBody_spec (tt pp : List ℕ) (i j okc : ℕ) (hok : okc ≤ 1)
    (hi : i < tt.length) (hj : j < tt.length) (hi' : i < pp.length) (hj' : j < pp.length)
    (hiB : i < B) (hjB : j + 2 < B) (bi : tt.getD i 0 + pp.getD i 0 < B)
    (bj : tt.getD j 0 + pp.getD j 0 < B) :
    Spec B (fun σ => σ.arrs "TT" = tt ∧ σ.arrs "PP" = pp ∧ σ.vars "vi" = i ∧ σ.vars "vj" = j ∧
        σ.vars "ok" = okc) innerBody
      (fun σ σ' => σ'.vars "ok" = (if okc = 1 ∧ fine tt pp i j then 1 else 0) ∧
        σ'.vars "vj" = j + 1 ∧ σ'.vars "vi" = i ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
        σ'.vars "nj" = σ.vars "nj") 70 := by
  intro σ ⟨hT, hP, hvi, hvj, hokv⟩
  obtain ⟨σ1, r1, l0, l1, l2, l3, lv, la, lo⟩ :=
    loadIJ_spec (B := B) tt pp i j hi hj hi' hj' hiB (by omega) bi bj σ ⟨hT, hP, hvi, hvj⟩
  have k1 : ∀ z, z ∉ ["x1", "y1", "u1", "v1"] → σ1.vars z = σ.vars z := lv
  obtain ⟨σ2, r2, c2, v2, a2, o2⟩ := ovl_spec (B := B) (by omega) σ1
    ⟨by rw [k1 _ (by decide), hvi]; exact hiB, by rw [k1 _ (by decide), hvj]; omega,
      by rw [l0]; exact bi, by rw [l1]; omega, by rw [l2]; exact bj, by rw [l3]; omega⟩
  have hj2 : σ2.vars "vj" = j := by rw [v2 _ (by decide), k1 _ (by decide), hvj]
  have r3 : Run B (.assign "vj" (add (V "vj") (.lit 1))) σ2 (σ2.setVar "vj" (σ2.vars "vj" + 1))
      (1 + (add (V "vj") (.lit 1)).size) :=
    Run.assign (evalB_bin (evalB_var (by rw [hj2]; omega)) (evalB_lit (by omega))
      (by simp [hj2]; omega))
  rw [hj2] at r3
  refine ⟨_, (r1.seq (r2.seq r3)).mono (by simp [Expr.size]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Env.setVar]
    rw [if_neg (by decide), c2, k1 "vi" (by decide), k1 "vj" (by decide), k1 "ok" (by decide),
      hvi, hvj, hokv, l0, l1, l2, l3]
    exact flag_step tt pp i j okc hok
  · simp [Env.setVar]
  · simp only [Env.setVar]; rw [if_neg (by decide), v2 _ (by decide), k1 _ (by decide), hvi]
  · simp only [Env.setVar]; rw [a2, la]
  · simp only [Env.setVar]; rw [o2, lo]
  · simp only [Env.setVar]; rw [if_neg (by decide), v2 _ (by decide), k1 _ (by decide)]

def innerLoop : Com :=
  .seq (.assign "vj" (.lit 0)) (.while (.lt (V "vj") (V "nj")) innerBody)

def IInv (tt pp : List ℕ) (n i okin : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.arrs "TT" = tt ∧ σ.arrs "PP" = pp ∧ σ.vars "nj" = n ∧ σ.vars "vi" = i ∧ σ.vars "vj" ≤ n ∧
    σ.vars "ok" = okI tt pp i okin (σ.vars "vj") ∧ σ.out = out0

theorem innerLoop_spec (tt pp : List ℕ) (n i okin : ℕ) (out0 : List ℕ) (hi : i < n)
    (hn : n ≤ tt.length) (hn' : n ≤ pp.length) (hnB : n + 2 < B)
    (hB : ∀ k < n, tt.getD k 0 + pp.getD k 0 < B) :
    Spec B (fun σ => IInv tt pp n i okin out0 (σ.setVar "vj" 0)) innerLoop
      (fun _ σ' => IInv tt pp n i okin out0 σ' ∧ σ'.vars "vj" = n) ((70 + 4) * n + 6) := by
  refine Spec.forRangeZero "vj" "nj" (IInv tt pp n i okin out0) n 70 (by omega)
    (fun _ h => h.2.2.2.2.1) (fun _ h => h.2.2.1) ?_
  intro σ ⟨⟨hT, hP, hN, hvi, hle, hok, hout⟩, hlt⟩
  obtain ⟨σ', r, q1, q2, q3, q4, q5, q6⟩ := innerBody_spec (B := B) tt pp i (σ.vars "vj")
    (okI tt pp i okin (σ.vars "vj")) (okI_le _ _ _ _ _) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (hB i hi) (hB _ hlt) σ ⟨hT, hP, hvi, rfl, hok⟩
  exact ⟨σ', r, ⟨by rw [q4]; exact hT, by rw [q4]; exact hP, by rw [q6]; exact hN, q3,
    by omega, by rw [q1, q2, okI_succ], by rw [q5]; exact hout⟩, q2⟩

def outerBody : Com := .seq innerLoop (.assign "vi" (add (V "vi") (.lit 1)))

def pairsLoop : Com :=
  .seq (.assign "vi" (.lit 0)) (.while (.lt (V "vi") (V "nj")) outerBody)

def PInv (tt pp : List ℕ) (n okin : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.arrs "TT" = tt ∧ σ.arrs "PP" = pp ∧ σ.vars "nj" = n ∧ σ.vars "vi" ≤ n ∧
    σ.vars "ok" = okO tt pp n okin (σ.vars "vi") ∧ σ.out = out0

/-- **The double loop**: the flag survives exactly if no two of the `n` jobs overlap. -/
theorem pairsLoop_spec (tt pp : List ℕ) (n okin : ℕ) (out0 : List ℕ)
    (hn : n ≤ tt.length) (hn' : n ≤ pp.length) (hnB : n + 2 < B)
    (hB : ∀ k < n, tt.getD k 0 + pp.getD k 0 < B) :
    Spec B (fun σ => PInv tt pp n okin out0 (σ.setVar "vi" 0)) pairsLoop
      (fun _ σ' => PInv tt pp n okin out0 σ' ∧ σ'.vars "vi" = n)
      (((70 + 4) * n + 6 + 4 + 4) * n + 6) := by
  refine Spec.forRangeZero "vi" "nj" (PInv tt pp n okin out0) n ((70 + 4) * n + 6 + 4) (by omega)
    (fun _ h => h.2.2.2.1) (fun _ h => h.2.2.1) ?_
  intro σ ⟨⟨hT, hP, hN, hle, hok, hout⟩, hlt⟩
  obtain ⟨σ1, r1, ⟨⟨i1, i2, i3, i4, i5, i6, i7⟩, i8⟩⟩ :=
    innerLoop_spec (B := B) tt pp n (σ.vars "vi") (okO tt pp n okin (σ.vars "vi")) out0 hlt hn hn'
      hnB hB σ ⟨by simpa [Env.setVar] using hT, by simpa [Env.setVar] using hP,
        by simpa [Env.setVar] using hN, by simp [Env.setVar], by simp [Env.setVar],
        by simp [Env.setVar, okI_zero _ _ _ _ (okO_le _ _ _ _ _), hok],
        by simpa [Env.setVar] using hout⟩
  have r2 : Run B (.assign "vi" (add (V "vi") (.lit 1))) σ1 (σ1.setVar "vi" (σ1.vars "vi" + 1))
      (1 + (add (V "vi") (.lit 1)).size) :=
    Run.assign (evalB_bin (evalB_var (by rw [i4]; omega)) (evalB_lit (by omega))
      (by simp [i4]; omega))
  rw [i4] at r2
  refine ⟨_, (r1.seq r2).mono (by simp [Expr.size]), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa [Env.setVar] using i1
  · simpa [Env.setVar] using i2
  · simpa [Env.setVar] using i3
  · simp [Env.setVar]; omega
  · simp only [Env.setVar, if_true]; rw [if_neg (by decide), i6, i8, okO_succ]
  · simpa [Env.setVar] using i7
  · simp [Env.setVar]

lemma okO_eq_one (tt pp : List ℕ) (n okin i : ℕ) :
    okO tt pp n okin i = 1 ↔ okin = 1 ∧ ∀ i' < i, ∀ j' < n, fine tt pp i' j' := by
  unfold okO; split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h0 => absurd h0 (by decide), fun h1 => absurd h1 h⟩

/-- The flag at the end, started from the flag of another loop. -/
lemma okO_flag (tt pp : List ℕ) (n : ℕ) (F : ℕ → Prop) [DecidablePred F] :
    okO tt pp n (if ∀ j < n, F j then 1 else 0) n =
      if (∀ j < n, F j) ∧ ∀ i < n, ∀ j < n, fine tt pp i j then 1 else 0 := by
  unfold okO
  by_cases h1 : ∀ j < n, F j
  · rw [if_pos h1]
    by_cases h2 : ∀ i < n, ∀ j < n, fine tt pp i j
    · rw [if_pos ⟨rfl, h2⟩, if_pos ⟨h1, h2⟩]
    · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 h.2)]
  · rw [if_neg h1, if_neg (fun h => absurd h.1 (by decide)), if_neg (fun h => h1 h.1)]

end Lax391470Proofs.VPairs
