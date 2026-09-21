import Lax391470Proofs.L2Pair
import Lax391470Proofs.L2OrdLoop

/-!
The loop over the connected pairs: compute the four deadlines of each and store them.
-/

namespace Lax391470Proofs.L2PairLoop

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.L2Ord Lax391470Proofs.L2Pair Lax391470Proofs.L2OrdLoop

variable (p q : ℕ) {B : ℕ} (g m S Lact NP : ℕ) (act : ℕ → ℕ) (R0 D0 L0 : List ℕ)

/-- The calculator, for whatever pair the counter points at. -/
theorem calcP_spec (hPB : ∀ i0 < NP, PB (B := B) p q g m S Lact act i0) :
    Spec B (fun σ => σ.vars "S" = S ∧ σ.vars "m" = m ∧ σ.vars "g" = g ∧ σ.vars "i" < NP ∧
        (∀ t, (σ.arrs "act").getD t 0 = act t) ∧ Lact ≤ (σ.arrs "act").length) (calcP p q)
      (fun σ σ' => σ'.vars "e1" = e1Val p q g m S act (σ.vars "i") ∧
        σ'.vars "e2" = e2Val p q g m S (σ.vars "i") ∧
        σ'.vars "e3" = e3Val p q g m S act (σ.vars "i") ∧
        σ'.vars "e4" = e4Val p q g m S (σ.vars "i")) 250 := by
  intro σ ⟨h1, h2, h3, h4, h5, h6⟩
  exact calcP_fixed p q g m S Lact act (σ.vars "i") (hPB _ h4) σ ⟨h1, h2, h3, rfl, h5, h6⟩

def pairBody : Com :=
  .seq (calcP p q)
    (.seq (.store "E1" (V "i") (V "e1"))
      (.seq (.store "E2" (V "i") (V "e2"))
        (.seq (.store "E3" (V "i") (V "e3"))
          (.seq (.store "E4" (V "i") (V "e4")) (.assign "i" (add (V "i") (.lit 1)))))))

def pairLoop : Com := .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "NP")) (pairBody p q))

lemma wvars_calcP : (calcP p q).wvars =
    ["v", "pos", "e1", "e2", "e3", "e4", "x", "h", "j", "sec", "cs1", "cs2", "e2", "e4",
      "e1", "e1", "e3", "e3"] := by
  simp [calcP, headP, litPart, clA, clB, clC, Com.wvars]

lemma warrs_calcP : (calcP p q).warrs = [] := by
  simp [calcP, headP, litPart, clA, clB, clC, Com.warrs]

structure PInv (σ : Env) : Prop where
  hS : σ.vars "S" = S
  hm : σ.vars "m" = m
  hg : σ.vars "g" = g
  hNP : σ.vars "NP" = NP
  hi : σ.vars "i" ≤ NP
  hact : ∀ t, (σ.arrs "act").getD t 0 = act t
  hlen : Lact ≤ (σ.arrs "act").length
  h1 : NP ≤ (σ.arrs "E1").length
  h2 : NP ≤ (σ.arrs "E2").length
  h3 : NP ≤ (σ.arrs "E3").length
  h4 : NP ≤ (σ.arrs "E4").length
  e1 : ∀ i' < σ.vars "i", (σ.arrs "E1").getD i' 0 = e1Val p q g m S act i'
  e2 : ∀ i' < σ.vars "i", (σ.arrs "E2").getD i' 0 = e2Val p q g m S i'
  e3 : ∀ i' < σ.vars "i", (σ.arrs "E3").getD i' 0 = e3Val p q g m S act i'
  e4 : ∀ i' < σ.vars "i", (σ.arrs "E4").getD i' 0 = e4Val p q g m S i'
  hR : σ.arrs "R" = R0
  hD : σ.arrs "D" = D0
  hL : σ.arrs "LG" = L0
  hout : σ.out = []

theorem pairBody_spec (hPB : ∀ i0 < NP, PB (B := B) p q g m S Lact act i0)
    (hval : ∀ i0 < NP, e1Val p q g m S act i0 < B ∧ e2Val p q g m S i0 < B ∧
      e3Val p q g m S act i0 < B ∧ e4Val p q g m S i0 < B) (hNPB : NP + 1 < B) :
    Spec B (fun σ => PInv p q g m S Lact NP act R0 D0 L0 σ ∧ σ.vars "i" < NP) (pairBody p q)
      (fun σ σ' => PInv p q g m S Lact NP act R0 D0 L0 σ' ∧ σ'.vars "i" = σ.vars "i" + 1)
      300 := by
  refine Spec.pre (P := fun σ => PInv p q g m S Lact NP act R0 D0 L0 σ ∧ σ.vars "i" < NP ∧
      (σ.vars "S" = S ∧ σ.vars "m" = m ∧ σ.vars "g" = g ∧ σ.vars "i" < NP ∧
        (∀ t, (σ.arrs "act").getD t 0 = act t) ∧ Lact ≤ (σ.arrs "act").length)) ?_
    (fun σ h => ⟨h.1, h.2, h.1.hS, h.1.hm, h.1.hg, h.2, h.1.hact, h.1.hlen⟩)
  run_vcg [(calcP_spec p q g m S Lact NP act hPB).frame]
  all_goals try (exact ⟨‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩)
  all_goals obtain ⟨⟨q1, q2, q3, q4⟩, hfv, hfa, -, hfo⟩ :=
    ‹_ ∧ (∀ y ∉ (calcP p q).wvars, _) ∧ _›
  all_goals have hI := ‹PInv p q g m S Lact NP act R0 D0 L0 σ›
  all_goals have hlt := ‹σ.vars "i" < NP›
  all_goals have hi' := hfv "i" (by simp [wvars_calcP])
  all_goals have a1 := hfa "E1" (by simp [warrs_calcP])
  all_goals have a2 := hfa "E2" (by simp [warrs_calcP])
  all_goals have a3 := hfa "E3" (by simp [warrs_calcP])
  all_goals have a4 := hfa "E4" (by simp [warrs_calcP])
  all_goals have l1 := congrArg List.length a1
  all_goals have l2 := congrArg List.length a2
  all_goals have l3 := congrArg List.length a3
  all_goals have l4 := congrArg List.length a4
  all_goals obtain ⟨b1, b2, b3, b4⟩ := hval _ hlt
  all_goals have g1 := hI.h1
  all_goals have g2 := hI.h2
  all_goals have g3 := hI.h3
  all_goals have g4 := hI.h4
  · have eS := hfv "S" (by simp [wvars_calcP])
    have em := hfv "m" (by simp [wvars_calcP])
    have eg := hfv "g" (by simp [wvars_calcP])
    have eNP := hfv "NP" (by simp [wvars_calcP])
    have aA := hfa "act" (by simp [warrs_calcP])
    have aR := hfa "R" (by simp [warrs_calcP])
    have aD := hfa "D" (by simp [warrs_calcP])
    have aL := hfa "LG" (by simp [warrs_calcP])
    have hout' := hfo (by simp [calcP, headP, litPart, clA, clB, clC, Com.NoWrite])
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals simp [Env.setVar, Env.setArr, eS, em, eg, eNP, hi', a1, a2, a3, a4, aA, aR, aD, aL,
      hout', hI.hS, hI.hm, hI.hg, hI.hNP, hI.hout, hI.hR, hI.hD, hI.hL]
    · exact hlt
    · simpa using hI.hact
    · exact hI.hlen
    · exact g1
    · exact g2
    · exact g3
    · exact g4
    · exact set_step _ _ _ _ (by omega) hI.e1 q1
    · exact set_step _ _ _ _ (by omega) hI.e2 q2
    · exact set_step _ _ _ _ (by omega) hI.e3 q3
    · exact set_step _ _ _ _ (by omega) hI.e4 q4
  all_goals simp [Env.setArr]
  all_goals omega

theorem pairLoop_spec (hPB : ∀ i0 < NP, PB (B := B) p q g m S Lact act i0)
    (hval : ∀ i0 < NP, e1Val p q g m S act i0 < B ∧ e2Val p q g m S i0 < B ∧
      e3Val p q g m S act i0 < B ∧ e4Val p q g m S i0 < B) (hNPB : NP + 1 < B) :
    Spec B (fun σ => PInv p q g m S Lact NP act R0 D0 L0 (σ.setVar "i" 0)) (pairLoop p q)
      (fun _ σ' => PInv p q g m S Lact NP act R0 D0 L0 σ' ∧ σ'.vars "i" = NP)
      (304 * NP + 6) :=
  Spec.forRangeZero "i" "NP" (PInv p q g m S Lact NP act R0 D0 L0) NP 300 (by omega)
    (fun _ h => h.hi) (fun _ h => h.hNP)
    (pairBody_spec p q g m S Lact NP act R0 D0 L0 hPB hval hNPB)

end Lax391470Proofs.L2PairLoop
