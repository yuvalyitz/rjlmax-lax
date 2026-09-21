import Lax391470Proofs.L2Accept
import Lax391470Proofs.L2Reject
import Lax391470Proofs.L2Scan

/-!
The whole reduction of Lemma 2 as one IMP+ program, and what it computes.
-/

namespace Lax391470Proofs.L2Main

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax429075.CNF Lax391470.SatConstruction
open Lax391470Proofs.CnfScan Lax391470Proofs.L2ScanModel Lax391470Proofs.L2Scan
open Lax391470Proofs.L2Dims Lax391470Proofs.L2Accept Lax391470Proofs.Bits

variable (p q : ℕ)

def main : Com :=
  .seq ReadAll.readAll (.seq (.assign "mx" (.lit 1)) (.seq scanLoop
    (.ite (.eq (.var "ph") (.lit 4)) (accept p q) L2Reject.reject)))

/-- The declared array lengths. -/
def ext (n Lact big : ℕ) (a : String) : ℕ :=
  if a ∈ ["a", "vr", "sg", "cl"] then n else if a = "act" then Lact else big

lemma wvars_readAll : ReadAll.readAll.wvars = ["L", "rt", "rv", "rt"] := by
  simp [ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, Com.wvars]
lemma warrs_readAll : ReadAll.readAll.warrs = ["a"] := by
  simp [ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, Com.warrs]
lemma warrs_scan : scanLoop.warrs = ["vr", "sg", "sg", "cl"] := by
  simp [scanLoop, scanBody, dispatch, phase3, Com.warrs]

/-- The accepted state has no pending literal. -/
lemma cur_nil {w : Lax434930.PolynomialTime.Word} (h : (run init w).ph = 4) :
    (run init w).cur = [] := (run_inv w (by omega)).1 (Or.inr h)

lemma getD_of_take (l : List ℕ) (K i : ℕ) (hi : i < K) : l.getD i 0 = (l.take K).getD i 0 := by
  simp [List.getD_eq_getElem?_getD, hi]

lemma getD_map {α : Type} (l : List α) (f : α → ℕ) (d : α) (i : ℕ) (hi : i < l.length) :
    (l.map f).getD i 0 = f (l.getD i d) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]

variable {B : ℕ} (y : List ℕ) (Lact big : ℕ)

/-- The cost of the whole program. -/
def Kmain (K NO NP Sz : ℕ) : ℕ :=
  (12 * y.length + 10) + 2 + (64 * y.length + 6) + (4 + (Kacc K NO NP Sz + 400))

theorem main_spec (K' NO' NP' : ℕ) (hyB : ∀ v ∈ y, v < B) (hB : y.length + 8 < B)
    (hn : (run init (bitsOf y)).ph = 4 →
      Nums (B := B) p q (run init (bitsOf y)).done Lact big)
    (hk : (run init (bitsOf y)).ph = 4 →
      (lits (run init (bitsOf y)).done).length ≤ K' ∧
      numOrdinary (run init (bitsOf y)).done ≤ NO' ∧
      Lax391470.SatConstruction.numPairs (run init (bitsOf y)).done ≤ NP') :
    ∃ σ', Run B (main p q) (initEnv (ext y.length Lact big) (y.length :: y)) σ'
        (Kmain y K' NO' NP' B.size) ∧
      σ'.out = L2Model.red p q y := by
  set σ0 := initEnv (ext y.length Lact big) (y.length :: y) with hσ0
  -- read
  obtain ⟨σ1, r1, ⟨hL1, ha1, ho1, -⟩, fv1, fa1, -, -⟩ :=
    (ReadAll.readAll_spec (B := B) (y := y) hyB (by omega)).frame σ0
      ⟨rfl, rfl, by simp [hσ0, initEnv, ext]⟩
  have z1 : ∀ x, x ∉ ["L", "rt", "rv"] → σ1.vars x = 0 := fun x hx => by
    rw [fv1 x (by rw [wvars_readAll]; simp only [List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hx ⊢; tauto)]
    rfl
  have ar1 : ∀ a, a ≠ "a" → σ1.arrs a = List.replicate (ext y.length Lact big a) 0 :=
    fun a ha => by rw [fa1 a (by simp [warrs_readAll, ha])]; rfl
  -- mx := 1
  have r2 : Run B (.assign "mx" (.lit 1)) σ1 (σ1.setVar "mx" 1) (1 + (Expr.lit 1).size) :=
    Run.assign (evalB_lit (by omega))
  -- scan
  obtain ⟨σ3, r3, ⟨I3, p3⟩, -, fa3, -, -⟩ := (scanLoop_spec (B := B) (y := y) hB hyB).frame
    (σ1.setVar "mx" 1) (by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [Env.setVar]
    all_goals try simp [stAt, bitsOf, init, flat, lits, nums, cn, mxOf]
    · exact z1 "ph" (by decide)
    · exact z1 "n" (by decide)
    · exact z1 "C" (by decide)
    · exact z1 "k" (by decide)
    · exact ha1
    · exact hL1
    · rw [ar1 "vr" (by decide)]; simp [ext]
    · rw [ar1 "sg" (by decide)]; simp [ext]
    · rw [ar1 "cl" (by decide)]; simp [ext]
    · exact ho1)
  obtain ⟨hR, -, -, -, lvr, lsg, lcl, out3⟩ := I3
  have hst : stAt y (σ3.vars "p") = run init (bitsOf y) := by
    rw [p3]; unfold stAt; rw [List.take_length]
  rw [hst] at hR
  have hphB : σ3.vars "ph" < B := by
    rw [hR.ph]; have := ph_run_le (bitsOf y); omega
  have hev : (Cond.eq (.var "ph") (.lit 4)).evalB B σ3 = some (σ3.vars "ph" == 4) :=
    evalB_condEq (evalB_var hphB) (evalB_lit (by omega))
  have ar3 : ∀ a, a ∉ ["a", "vr", "sg", "cl"] →
      σ3.arrs a = List.replicate (ext y.length Lact big a) 0 := fun a ha => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
    rw [fa3 a (by rw [warrs_scan]; simp; tauto)]
    exact ar1 a ha.1
  have hseq : ∀ {σ' K}, Run B (.ite (.eq (.var "ph") (.lit 4)) (accept p q) L2Reject.reject)
      σ3 σ' K → Run B (main p q) σ0 σ' ((12 * y.length + 10) + ((1 + (Expr.lit 1).size) +
        ((64 * y.length + 6) + K))) := fun h => r1.seq (r2.seq (r3.seq h))
  by_cases h4 : (run init (bitsOf y)).ph = 4
  · -- accept
    have hc := cur_nil h4
    have hflat : flat (run init (bitsOf y)) = lits (run init (bitsOf y)).done := by
      simp [flat, hc]
    have hnums : nums (run init (bitsOf y)) = cn (run init (bitsOf y)).done := by
      simp [nums, hc]
    have hpre : AccPre (run init (bitsOf y)).done Lact big σ3 := by
      have e1 := hR.vr; have e2 := hR.sg; have e3 := hR.cl
      rw [hflat] at e1 e2 e3; rw [hnums] at e3
      have hk := hR.k; rw [hflat] at hk
      have hKy : (lits (run init (bitsOf y)).done).length ≤ y.length := by
        have h := size_run (bitsOf y)
        have hl : (bitsOf y).length = y.length := by simp [bitsOf]
        rw [hl] at h
        simp only [L2ScanModel.size, hflat] at h
        omega
      have hmx := hR.mx; rw [hflat] at hmx
      refine ⟨hR.C, hmx, hk, by omega, by omega, by omega, fun i hi => ?_, fun i hi => ?_,
        fun i hi => ?_, ?_, fun a ha => ?_, out3⟩
      · rw [getD_of_take _ _ _ hi, e1, getD_map _ _ dflt _ hi]; rfl
      · rw [getD_of_take _ _ _ hi, e2, getD_map _ _ dflt _ hi]; rfl
      · rw [getD_of_take _ _ _ hi, e3]; rfl
      · rw [ar3 "act" (by decide)]; simp [ext]
      · have hne : a ∉ ["a", "vr", "sg", "cl"] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        rw [ar3 a hne]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ext]
    obtain ⟨σ', ra, oa⟩ := accept_spec (B := B) p q _ Lact big (hn h4) σ3 hpre
    have hc4 : σ3.vars "ph" = 4 := by rw [hR.ph, h4]
    have rite := Run.ite_true (d := L2Reject.reject) (by rw [hev, hc4]; rfl) ra
    obtain ⟨k1, k2, k3⟩ := hk h4
    have hmono := Kacc_mono B.size k1 k2 k3
    refine ⟨σ', (hseq rite).mono (by unfold Kmain; simp [Cond.size, Expr.size]; omega), ?_⟩
    rw [oa]; unfold L2Model.red; simp [h4]
  · obtain ⟨σ', rr, orj⟩ := L2Reject.reject_spec (B := B) (by omega) σ3 out3
    have hc4 : ¬ σ3.vars "ph" = 4 := by rw [hR.ph]; exact h4
    have rite := Run.ite_false (c := accept p q) (by rw [hev]; simp [hc4]) rr
    refine ⟨σ', (hseq rite).mono (by unfold Kmain; simp [Cond.size, Expr.size]; omega), ?_⟩
    rw [orj]; unfold L2Model.red; simp [h4]

end Lax391470Proofs.L2Main
