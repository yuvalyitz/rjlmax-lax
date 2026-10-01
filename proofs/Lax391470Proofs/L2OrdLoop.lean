import Lax391470Proofs.L2Ord

/-!
The loop over the ordinary jobs: compute the three numbers of each and store them.
-/

namespace Lax391470Proofs.L2OrdLoop

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.L2Ord

variable (p q : ℕ)

def calcO : Com := .ite (.lt (V "o") (V "n6")) (calcSec p q) (calcTail p q)

variable {B : ℕ} (nn m S : ℕ) (act : ℕ → ℕ)

/-- What the calculators need of the environment. -/
structure CPre (σ : Env) : Prop where
  hS : σ.vars "S" = S
  hnn : σ.vars "nn" = nn
  hm : σ.vars "m" = m
  h6 : σ.vars "n6" = 6 * nn
  h6m : σ.vars "n6m" = 6 * nn + m
  ho : σ.vars "o" < 6 * nn + 2 * m
  hlen : (2 * nn - 1) * m + m ≤ (σ.arrs "act").length
  hact : ∀ t, (σ.arrs "act").getD t 0 = act t
  hact1 : ∀ t, act t ≤ 1
  hbig : S * (2 * nn) + S + (p + 2 * q) + 2 * (m * (p + q)) + (p + q) + 6 * nn + 2 * m + 8 < B
  hbig2 : (2 * nn - 1) * m + m < B

lemma CPre.act_lt {σ : Env} (h : CPre p q (B := B) nn m S act σ) (t : ℕ) :
    (σ.arrs "act").getD t 0 < B := by
  have hb := h.hbig
  rw [h.hact t]; have := h.hact1 t; omega

theorem calc_spec :
    Spec B (CPre p q (B := B) nn m S act) (calcO p q)
      (fun σ σ' => σ'.vars "r" = rVal q nn S (σ.vars "o") ∧
        σ'.vars "d" = dVal p q nn m S act (σ.vars "o") ∧ σ'.vars "lg" = lgVal nn m (σ.vars "o"))
      70 := by
  have hev : ∀ σ, CPre p q (B := B) nn m S act σ →
      (Cond.lt (V "o") (V "n6")).evalB B σ = some (decide (σ.vars "o" < σ.vars "n6")) :=
    fun σ h => evalB_condLt (evalB_var (by have := h.ho; have := h.hbig; omega))
      (evalB_var (by rw [h.h6]; have := h.hbig; omega))
  refine (Spec.ite (K := 60) (Q := fun σ σ' => σ'.vars "r" = rVal q nn S (σ.vars "o") ∧
        σ'.vars "d" = dVal p q nn m S act (σ.vars "o") ∧ σ'.vars "lg" = lgVal nn m (σ.vars "o")) (fun σ h => ⟨_, hev σ h⟩) ?_ ?_).mono (by simp [Cond.size, Expr.size])
  · refine Spec.pre (calcSec_spec p q nn m S act) ?_
    rintro σ ⟨h, hc⟩
    rw [hev σ h] at hc
    have ho : σ.vars "o" < 6 * nn := by rw [← h.h6]; simpa using hc
    have hmul := Nat.mul_le_mul_left S (show σ.vars "o" / 3 ≤ 2 * nn by omega)
    have := h.hbig
    exact ⟨h.hS, ho, by omega, by omega, by omega, by omega⟩
  · refine Spec.pre (calcTail_spec p q nn m S act) ?_
    rintro σ ⟨h, hc⟩
    rw [hev σ h] at hc
    have ho : ¬ σ.vars "o" < 6 * nn := by rw [← h.h6]; simpa using hc
    have ho2 := h.ho
    have hb := h.hbig
    have hmul := Nat.mul_le_mul_left S (show 2 * nn - 1 ≤ 2 * nn by omega)
    have hlen := h.hlen
    refine ⟨h.hS, h.hnn, h.hm, h.h6, h.h6m, ho, ho2, hlen, h.hact _, h.hact _, by omega,
      ?_, ?_, by omega, h.hbig2,
      by omega, h.act_lt p q nn m S act⟩
    · have := Nat.mul_le_mul_right (p + q) (show σ.vars "o" - 6 * nn ≤ 2 * m by omega)
      rw [Nat.mul_assoc] at this; exact this
    · have := Nat.mul_le_mul_right (p + q) (show σ.vars "o" - 6 * nn - m ≤ 2 * m by omega)
      rw [Nat.mul_assoc] at this; exact this

/-! ### The Values Are Small -/

lemma rVal_le (o : ℕ) : rVal q nn S o ≤ S * (2 * nn) + S + q + 1 := by
  unfold rVal
  by_cases ho : o < 6 * nn
  · have hmul := Nat.mul_le_mul_left S (show o / 3 ≤ 2 * nn by omega)
    rw [if_pos ho]
    split_ifs <;> omega
  · rw [if_neg ho]; omega

lemma dVal_le (o : ℕ) (ho : o < 6 * nn + 2 * m) :
    dVal p q nn m S act o ≤ S * (2 * nn) + S + (p + 2 * q) + 2 * (m * (p + q)) + (p + q) + 1 := by
  unfold dVal
  by_cases h6 : o < 6 * nn
  · have hmul := Nat.mul_le_mul_left S (show o / 3 ≤ 2 * nn by omega)
    rw [if_pos h6]
    split_ifs <;> omega
  · have hmul2 := Nat.mul_le_mul_left S (show 2 * nn - 1 ≤ 2 * nn by omega)
    have h1 := Nat.mul_le_mul_right (p + q) (show o - 6 * nn ≤ 2 * m by omega)
    have h2 := Nat.mul_le_mul_right (p + q) (show o - 6 * nn - m ≤ 2 * m by omega)
    rw [Nat.mul_assoc] at h1 h2
    rw [if_neg h6]
    split_ifs <;> omega

lemma lgVal_le (o : ℕ) : lgVal nn m o ≤ 1 := by
  unfold lgVal
  split_ifs <;> omega

/-- Writing the next entry extends a correctly filled prefix. -/
lemma set_step (l : List ℕ) (o v : ℕ) (f : ℕ → ℕ) (hl : o < l.length)
    (h : ∀ o' < o, l.getD o' 0 = f o') (hv : v = f o) :
    ∀ o' ≤ o, (l.set o v)[o']?.getD 0 = f o' := by
  intro o' ho'
  rw [List.getElem?_set]
  by_cases he : o = o'
  · subst he; simp [hl, hv]
  · rw [if_neg he, ← h o' (by omega), List.getD_eq_getElem?_getD]

/-! ### The Loop -/

def ordBody : Com :=
  .seq (calcO p q)
    (.seq (.store "R" (V "o") (V "r"))
      (.seq (.store "D" (V "o") (V "d"))
        (.seq (.store "LG" (V "o") (V "lg")) (.assign "o" (add (V "o") (.lit 1))))))

def ordLoop : Com := .seq (.assign "o" (.lit 0)) (.while (.lt (V "o") (V "NO")) (ordBody p q))

lemma wvars_calcO : (calcO p q).wvars =
    ["s", "c", "par", "base", "lg", "r", "d", "r", "d", "lg", "r", "d", "lg", "r", "d",
      "r", "j", "sec", "lg", "j", "sec", "lg", "cs", "d", "d"] := by
  simp [calcO, calcSec, calcTail, Com.wvars]

lemma warrs_calcO : (calcO p q).warrs = [] := by
  simp [calcO, calcSec, calcTail, Com.warrs]

/-- The invariant of the loop: the constants, the table, and the entries written so far. -/
structure OInv (σ : Env) : Prop where
  hS : σ.vars "S" = S
  hnn : σ.vars "nn" = nn
  hm : σ.vars "m" = m
  h6 : σ.vars "n6" = 6 * nn
  h6m : σ.vars "n6m" = 6 * nn + m
  hNO : σ.vars "NO" = 6 * nn + 2 * m
  ho : σ.vars "o" ≤ 6 * nn + 2 * m
  hlen : (2 * nn - 1) * m + m ≤ (σ.arrs "act").length
  hact : ∀ t, (σ.arrs "act").getD t 0 = act t
  hR : 6 * nn + 2 * m ≤ (σ.arrs "R").length
  hD : 6 * nn + 2 * m ≤ (σ.arrs "D").length
  hLG : 6 * nn + 2 * m ≤ (σ.arrs "LG").length
  hr : ∀ o' < σ.vars "o", (σ.arrs "R").getD o' 0 = rVal q nn S o'
  hd : ∀ o' < σ.vars "o", (σ.arrs "D").getD o' 0 = dVal p q nn m S act o'
  hl : ∀ o' < σ.vars "o", (σ.arrs "LG").getD o' 0 = lgVal nn m o'
  hout : σ.out = []

theorem ordBody_spec (hact1 : ∀ t, act t ≤ 1)
    (hbig : S * (2 * nn) + S + (p + 2 * q) + 2 * (m * (p + q)) + (p + q) + 6 * nn + 2 * m + 8 < B)
    (hbig2 : (2 * nn - 1) * m + m < B) :
    Spec B (fun σ => OInv p q nn m S act σ ∧ σ.vars "o" < 6 * nn + 2 * m) (ordBody p q)
      (fun σ σ' => OInv p q nn m S act σ' ∧ σ'.vars "o" = σ.vars "o" + 1) 100 := by
  refine Spec.pre (P := fun σ => OInv p q nn m S act σ ∧ σ.vars "o" < 6 * nn + 2 * m ∧
      CPre p q (B := B) nn m S act σ) ?_ ?_
  · run_vcg [(calc_spec p q nn m S act).frame]
    all_goals try assumption
    all_goals obtain ⟨⟨er, ed, el⟩, hfv, hfa, -, hfo⟩ :=
      ‹_ ∧ (∀ y ∉ (calcO p q).wvars, _) ∧ _›
    all_goals have hI := ‹OInv p q nn m S act σ›
    all_goals have hlt := ‹σ.vars "o" < 6 * nn + 2 * m›
    all_goals have ho' := hfv "o" (by simp [wvars_calcO])
    all_goals have aR := hfa "R" (by simp [warrs_calcO])
    all_goals have aD := hfa "D" (by simp [warrs_calcO])
    all_goals have aL := hfa "LG" (by simp [warrs_calcO])
    all_goals have lR := congrArg List.length aR
    all_goals have lD := congrArg List.length aD
    all_goals have lL := congrArg List.length aL
    all_goals have br := rVal_le q nn S (σ.vars "o")
    all_goals have bd := dVal_le p q nn m S act (σ.vars "o") hlt
    all_goals have bl := lgVal_le nn m (σ.vars "o")
    all_goals have hR := hI.hR
    all_goals have hD := hI.hD
    all_goals have hLG := hI.hLG
    · have eS := hfv "S" (by simp [wvars_calcO])
      have enn := hfv "nn" (by simp [wvars_calcO])
      have em := hfv "m" (by simp [wvars_calcO])
      have e6 := hfv "n6" (by simp [wvars_calcO])
      have e6m := hfv "n6m" (by simp [wvars_calcO])
      have eNO := hfv "NO" (by simp [wvars_calcO])
      have aA := hfa "act" (by simp [warrs_calcO])
      have hout' := hfo (by simp [calcO, calcSec, calcTail, Com.NoWrite])
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      all_goals simp [Env.setVar, Env.setArr, eS, enn, em, e6, e6m, eNO, ho', aR, aD, aL, aA, hout',
        hI.hS, hI.hnn, hI.hm, hI.h6, hI.h6m, hI.hNO, hI.hout]
      · omega
      · exact hI.hlen
      · simpa using hI.hact
      · exact hR
      · exact hD
      · exact hLG
      · exact set_step _ _ _ _ (by omega) hI.hr er
      · exact set_step _ _ _ _ (by omega) hI.hd ed
      · exact set_step _ _ _ _ (by omega) hI.hl el
    all_goals simp [Env.setArr]
    all_goals omega
  · rintro σ ⟨hI, ho⟩
    exact ⟨hI, ho, ⟨hI.hS, hI.hnn, hI.hm, hI.h6, hI.h6m, ho, hI.hlen, hI.hact, hact1, hbig, hbig2⟩⟩

theorem ordLoop_spec (hact1 : ∀ t, act t ≤ 1)
    (hbig : S * (2 * nn) + S + (p + 2 * q) + 2 * (m * (p + q)) + (p + q) + 6 * nn + 2 * m + 8 < B)
    (hbig2 : (2 * nn - 1) * m + m < B) :
    Spec B (fun σ => OInv p q nn m S act (σ.setVar "o" 0)) (ordLoop p q)
      (fun _ σ' => OInv p q nn m S act σ' ∧ σ'.vars "o" = 6 * nn + 2 * m)
      (104 * (6 * nn + 2 * m) + 6) :=
  Spec.forRangeZero "o" "NO" (OInv p q nn m S act) (6 * nn + 2 * m) 100 (by omega)
    (fun _ h => h.ho) (fun _ h => h.hNO) (ordBody_spec p q nn m S act hact1 hbig hbig2)

end Lax391470Proofs.L2OrdLoop
