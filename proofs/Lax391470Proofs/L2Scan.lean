import Lax391470Proofs.L2ScanModel
import Lax391470Proofs.ReadAll

/-!
The scan of a formula's encoding, as an IMP+ loop: one bit a step, the state of `CnfScan`
in five scalars and three arrays.
-/

namespace Lax391470Proofs.L2Scan

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax429075.CNF Lax434930.PolynomialTime
open Lax391470Proofs.CnfScan Lax391470Proofs.L2ScanModel Lax391470Proofs.Bits

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.bin .add (V s) (.lit 1))
abbrev set (s : String) (n : ℕ) : Com := .assign s (.lit n)

/-- The environment reflects a state of the scan. -/
structure Refl (s : St) (σ : Env) : Prop where
  ph : σ.vars "ph" = s.ph
  n : σ.vars "n" = s.n
  C : σ.vars "C" = s.done.length
  k : σ.vars "k" = (flat s).length
  mx : σ.vars "mx" = mxOf (flat s)
  vr : (σ.arrs "vr").take (flat s).length = (flat s).map Literal.index
  sg : (σ.arrs "sg").take (flat s).length = (flat s).map fun l => if l.positive then 1 else 0
  cl : (σ.arrs "cl").take (flat s).length = nums s

def phase3 : Com :=
  .seq (.store "vr" (V "k") (V "n"))
    (.seq (.ite (.eq (V "c") (.lit 0)) (.store "sg" (V "k") (.lit 0)) (.store "sg" (V "k") (.lit 1)))
      (.seq (.store "cl" (V "k") (V "C"))
        (.seq (.ite (.lt (V "n") (V "mx")) .skip (.assign "mx" (.bin .add (V "n") (.lit 1))))
          (.seq (bump "k") (set "ph" 1)))))

def dispatch : Com :=
  .ite (.eq (V "ph") (.lit 0)) (.ite (.eq (V "c") (.lit 0)) (set "ph" 4) (set "ph" 1))
    (.ite (.eq (V "ph") (.lit 1))
      (.ite (.eq (V "c") (.lit 0)) (.seq (bump "C") (set "ph" 0)) (.seq (set "ph" 2) (set "n" 0)))
      (.ite (.eq (V "ph") (.lit 2)) (.ite (.eq (V "c") (.lit 0)) (set "ph" 3) (bump "n"))
        (.ite (.eq (V "ph") (.lit 3)) phase3 (set "ph" 5))))

def scanBody : Com := .seq (.assign "c" (.get "a" (V "p"))) (.seq dispatch (bump "p"))

def scanLoop : Com := .seq (set "p" 0) (.while (.lt (V "p") (V "L")) scanBody)

variable {B : ℕ} {y : List ℕ}

/-- The state after the first `t` bits. -/
def stAt (y : List ℕ) (t : ℕ) : St := run init (bitsOf (y.take t))

def SInv (y : List ℕ) (σ : Env) : Prop :=
  Refl (stAt y (σ.vars "p")) σ ∧ σ.arrs "a" = y ∧ σ.vars "L" = y.length ∧
    σ.vars "p" ≤ y.length ∧ (σ.arrs "vr").length = y.length ∧
    (σ.arrs "sg").length = y.length ∧ (σ.arrs "cl").length = y.length ∧ σ.out = []

lemma stAt_succ {t : ℕ} (ht : t < y.length) :
    stAt y (t + 1) = step (stAt y t) (decide (y.getD t 0 ≠ 0)) := by
  unfold stAt
  rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some]
  simp only [bitsOf, List.map_append, List.map_cons, List.map_nil]
  rw [run_append, run_cons, run_nil, List.getD_eq_getElem _ _ ht]

lemma take_set_succ (l : List ℕ) (k v : ℕ) (hk : k < l.length) :
    (l.set k v).take (k + 1) = l.take k ++ [v] := by
  rw [List.take_add_one, List.take_set_of_le (le_refl k)]
  simp [hk]

/-- The step of the scan, from what the program did. -/
theorem sinv_of (σ σ' : Env) (hI : SInv y σ) (hp : σ.vars "p" < y.length)
    (hp' : σ'.vars "p" = σ.vars "p" + 1)
    (hR : Refl (step (stAt y (σ.vars "p")) (decide (y.getD (σ.vars "p") 0 ≠ 0))) σ')
    (ha : σ'.arrs "a" = σ.arrs "a") (hL : σ'.vars "L" = σ.vars "L")
    (h1 : (σ'.arrs "vr").length = (σ.arrs "vr").length)
    (h2 : (σ'.arrs "sg").length = (σ.arrs "sg").length)
    (h3 : (σ'.arrs "cl").length = (σ.arrs "cl").length) (ho : σ'.out = σ.out) :
    SInv y σ' := by
  obtain ⟨-, ha0, hL0, -, hvr, hsg, hcl, hout⟩ := hI
  refine ⟨?_, ha.trans ha0, hL.trans hL0, by omega, h1.trans hvr, h2.trans hsg, h3.trans hcl,
    ho.trans hout⟩
  rw [hp', stAt_succ hp]; exact hR

set_option maxHeartbeats 4000000 in
theorem scanBody_flat (hB : y.length + 8 < B) (_hy : ∀ v ∈ y, v < B) :
    Spec B (fun σ => SInv y σ ∧ σ.vars "p" < y.length ∧
        σ.vars "p" < (σ.arrs "a").length ∧ (σ.arrs "a").getD (σ.vars "p") 0 < B ∧
        σ.vars "ph" < B ∧ σ.vars "n" + 1 < B ∧ σ.vars "C" + 1 < B ∧ σ.vars "k" + 1 < B ∧
        σ.vars "mx" < B ∧ σ.vars "p" + 1 < B ∧
        σ.vars "k" < (σ.arrs "vr").length ∧ σ.vars "k" < (σ.arrs "sg").length ∧
        σ.vars "k" < (σ.arrs "cl").length) scanBody
      (fun σ σ' => SInv y σ' ∧ σ'.vars "p" = σ.vars "p" + 1) 60 := by
  run_vcg
  all_goals try (simp only [Env.setVar]; exact ‹(σ.arrs "a").getD (σ.vars "p") 0 < B›)
  all_goals (
    have hI := ‹SInv y σ›
    have hR := hI.1
    have hya : σ.arrs "a" = y := hI.2.1
    refine ⟨sinv_of σ _ hI ‹σ.vars "p" < y.length› (by simp [Env.setVar]) ?_
      (by simp [Env.setVar, Env.setArr]) (by simp [Env.setVar, Env.setArr])
      (by simp [Env.setVar, Env.setArr]) (by simp [Env.setVar, Env.setArr])
      (by simp [Env.setVar, Env.setArr]) (by simp [Env.setVar, Env.setArr]),
      by simp [Env.setVar]⟩
    simp only [Env.setVar, hya] at *
    generalize stAt y (σ.vars "p") = s at hR ⊢
    obtain ⟨ph, n, d, c⟩ := s
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := hR
    simp only at r1 r2 r3 r4 r5 r6 r7 r8
    constructor <;> simp_all [step, flat, nums, Env.setArr, lits_append, cn_append])
  all_goals first
    | omega
    | (rw [← List.append_assoc, mxOf_append]; simp only []; omega)
    | (rw [← Nat.add_assoc, take_set_succ _ _ _ (by assumption)]
       simp_all [List.replicate_succ'])

lemma ph_step_le (s : St) (b : Bool) (h : s.ph ≤ 5) : (step s b).ph ≤ 5 := by
  obtain ⟨ph, n, d, c⟩ := s
  match ph with
  | 0 => cases b <;> simp [step]
  | 1 => cases b <;> simp [step]
  | 2 => cases b <;> simp [step]
  | 3 => simp [step]
  | k + 4 => simp [step]

lemma ph_run_le (w : Word) : (run init w).ph ≤ 5 := by
  induction w using List.reverseRecOn with
  | nil => simp [init]
  | append_singleton u b ih => rw [run_append]; exact ph_step_le _ _ ih

lemma size_stAt (t : ℕ) (ht : t ≤ y.length) : L2ScanModel.size (stAt y t) ≤ t := by
  have := size_run (bitsOf (y.take t))
  have hl : (bitsOf (y.take t)).length = t := by
    simp [bitsOf, List.length_take, Nat.min_eq_left ht]
  rw [hl] at this
  exact this

theorem scanBody_spec (hB : y.length + 8 < B) (hy : ∀ v ∈ y, v < B) :
    Spec B (fun σ => SInv y σ ∧ σ.vars "p" < y.length) scanBody
      (fun σ σ' => SInv y σ' ∧ σ'.vars "p" = σ.vars "p" + 1) 60 := by
  refine Spec.pre (scanBody_flat hB hy) ?_
  rintro σ ⟨hI, hp⟩
  obtain ⟨hR, ha, hL, hple, hvr, hsg, hcl, hout⟩ := hI
  have hsz := size_stAt (y := y) (σ.vars "p") hple
  have hph := ph_run_le (bitsOf (y.take (σ.vars "p")))
  have hmx := mxOf_pos (flat (stAt y (σ.vars "p")))
  simp only [L2ScanModel.size] at hsz
  have e1 := hR.ph; have e2 := hR.n; have e3 := hR.C; have e4 := hR.k; have e5 := hR.mx
  change (stAt y (σ.vars "p")).ph ≤ 5 at hph
  refine ⟨⟨hR, ha, hL, hple, hvr, hsg, hcl, hout⟩, hp, by rw [ha]; exact hp, ?_,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  rw [ha, List.getD_eq_getElem _ _ hp]
  exact hy _ (List.getElem_mem hp)

theorem scanLoop_spec (hB : y.length + 8 < B) (hy : ∀ v ∈ y, v < B) :
    Spec B (fun σ => SInv y (σ.setVar "p" 0)) scanLoop
      (fun _ σ' => SInv y σ' ∧ σ'.vars "p" = y.length) (64 * y.length + 6) :=
  Spec.forRangeZero "p" "L" (SInv y) y.length 60 (by omega)
    (fun _ h => h.2.2.2.1) (fun _ h => h.2.2.1) (scanBody_spec hB hy)

end Lax391470Proofs.L2Scan
