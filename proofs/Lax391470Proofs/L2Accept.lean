import Lax391470Proofs.L2Parts
import Lax391470Proofs.L2Dims
import Lax391470Proofs.L2OrdSem
import Lax391470Proofs.L2PairSem
import Lax391470Proofs.L2PairLoop
import Lax391470Proofs.L2Model

/-!
The accepting branch of the reduction: from the scanned formula to the zeros and ones of
the constructed instance.
-/

namespace Lax391470Proofs.L2Accept

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax429075.CNF Lax391470.SatConstruction
open Lax391470Proofs.L2ScanModel Lax391470Proofs.L2Active Lax391470Proofs.L2Dims
open Lax391470Proofs.L2Parts Lax391470Proofs.L2Print Lax391470Proofs.Bits

variable (p q : ℕ)

def accept : Com :=
  .seq (setupA p q) (.seq setupB (.seq L2Fill.fillLoop (.seq (L2OrdLoop.ordLoop p q)
    (.seq (L2PairLoop.pairLoop p q) (.seq (emitVar "NO") (.seq (emitVar "NP")
      (.seq (.seq (.assign "o" (.lit 0)) (.while (.lt (.var "o") (.var "NO")) recO))
        (.seq (.assign "i" (.lit 0)) (.while (.lt (.var "i") (.var "NP")) recP)))))))))

variable {B : ℕ} (F : Formula) (Lact big : ℕ)

/-- What the scan leaves for the accepting branch. -/
structure AccPre (σ : Env) : Prop where
  hC : σ.vars "C" = F.length
  hmx : σ.vars "mx" = numVars F
  hk : σ.vars "k" = (lits F).length
  lvr : (lits F).length ≤ (σ.arrs "vr").length
  lsg : (lits F).length ≤ (σ.arrs "sg").length
  lcl : (lits F).length ≤ (σ.arrs "cl").length
  hvr : ∀ i < (lits F).length, (σ.arrs "vr").getD i 0 = ivF F i
  hsg : ∀ i < (lits F).length, (σ.arrs "sg").getD i 0 = svF F i
  hcl : ∀ i < (lits F).length, (σ.arrs "cl").getD i 0 = cvF F i
  hact : σ.arrs "act" = List.replicate Lact 0
  hbigA : ∀ a ∈ ["R", "D", "LG", "E1", "E2", "E3", "E4"], (σ.arrs a).length = big
  hout : σ.out = []

lemma wvars_setupA : (setupA p q).wvars = ["m", "nn", "S", "n6"] := by
  simp [setupA, Com.wvars]
lemma wvars_setupB : setupB.wvars = ["n6m", "NO", "g", "NP"] := by simp [setupB, Com.wvars]
lemma warrs_setupA : (setupA p q).warrs = [] := by simp [setupA, Com.warrs]
lemma warrs_setupB : setupB.warrs = [] := by simp [setupB, Com.warrs]
lemma wvars_fill : L2Fill.fillLoop.wvars = ["i", "t", "i"] := by
  simp [L2Fill.fillLoop, L2Fill.fillBody, Com.wvars]
lemma warrs_fill : L2Fill.fillLoop.warrs = ["act"] := by
  simp [L2Fill.fillLoop, L2Fill.fillBody, Com.warrs]
lemma wvars_ord : (L2OrdLoop.ordLoop p q).wvars = "o" :: ((L2OrdLoop.calcO p q).wvars ++ ["o"]) := by
  simp [L2OrdLoop.ordLoop, L2OrdLoop.ordBody, Com.wvars]
lemma warrs_ord : (L2OrdLoop.ordLoop p q).warrs = ["R", "D", "LG"] := by
  simp [L2OrdLoop.ordLoop, L2OrdLoop.ordBody, Com.warrs, L2OrdLoop.warrs_calcO]
lemma wvars_pair : (L2PairLoop.pairLoop p q).wvars = "i" :: ((L2Pair.calcP p q).wvars ++ ["i"]) := by
  simp [L2PairLoop.pairLoop, L2PairLoop.pairBody, Com.wvars]

/-- The numeric side conditions, all of the form "this quantity is below the bound". -/
structure Nums : Prop where
  hLact : 2 * numVars F * F.length ≤ Lact
  hLact2 : (2 * numVars F - 1) * F.length + F.length ≤ Lact
  hLactB : Lact + 2 < B
  hKB : (lits F).length + 1 < B
  hfill : ∀ i < (lits F).length, 2 * ivF F i + 1 < B ∧ svF F i < B ∧ cvF F i < B ∧
    (2 * ivF F i + 1 - svF F i) * F.length < B
  hsetB : numVars F + (2 * numVars F - 1) * F.length + 2 * numVars F + 8 < B
  hbig : sectionLength p q F * (2 * numVars F) + sectionLength p q F + (p + 2 * q) +
    2 * (F.length * (p + q)) + (p + q) + 6 * numVars F + 2 * F.length + 8 < B
  hPB : ∀ i0 < Lax391470.SatConstruction.numPairs F,
    L2Pair.PB (B := B) p q (1 + 2 * F.length) F.length (sectionLength p q F) Lact (table F) i0
  heval : ∀ i0 < Lax391470.SatConstruction.numPairs F,
    L2Pair.e1Val p q (1 + 2 * F.length) F.length (sectionLength p q F) (table F) i0 + 4 < B ∧
    L2Pair.e2Val p q (1 + 2 * F.length) F.length (sectionLength p q F) i0 + 4 < B ∧
    L2Pair.e3Val p q (1 + 2 * F.length) F.length (sectionLength p q F) (table F) i0 + 4 < B ∧
    L2Pair.e4Val p q (1 + 2 * F.length) F.length (sectionLength p q F) i0 + 4 < B
  hNO : numOrdinary F ≤ big
  hNP : Lax391470.SatConstruction.numPairs F ≤ big
  hNPB : Lax391470.SatConstruction.numPairs F + 4 < B

/-- The cost of the accepting branch. -/
def Kacc (K NO NP Sz : ℕ) : ℕ :=
  40 + 40 + (44 * K + 6) + (104 * NO + 6) + (304 * NP + 6) + 2 * (48 * Sz + 50) +
    ((2 * (48 * Sz + 50) + 20 + 4) * NO + 6) + ((4 * (48 * Sz + 50) + 10 + 4) * NP + 6)

lemma Kacc_eq (K NO NP Sz : ℕ) :
    Kacc K NO NP Sz = 210 + 44 * K + 228 * NO + 518 * NP + 96 * Sz + 96 * (Sz * NO) +
      192 * (Sz * NP) := by
  unfold Kacc; ring

lemma Kacc_mono {K NO NP K' NO' NP' : ℕ} (Sz : ℕ) (h1 : K ≤ K') (h2 : NO ≤ NO') (h3 : NP ≤ NP') :
    Kacc K NO NP Sz ≤ Kacc K' NO' NP' Sz := by
  rw [Kacc_eq, Kacc_eq]
  have := Nat.mul_le_mul_left Sz h2
  have := Nat.mul_le_mul_left Sz h3
  omega

theorem accept_spec (hn : Nums (B := B) p q F Lact big) :
    Spec B (AccPre F Lact big) (accept p q)
      (fun _ σ' => σ'.out = L2Model.outBits p q F)
      (Kacc (lits F).length (numOrdinary F) (Lax391470.SatConstruction.numPairs F) B.size) := by
  intro σ0 h0
  have hbig := hn.hbig
  have hm_eq : numClauses F = F.length := rfl
  -- setup A
  obtain ⟨σ1, r1, ⟨a1, a2, a3, a4⟩, fv1, fa1, -, fo1⟩ := (setupA_spec (B := B) p q).frame σ0 (by
    show p + 2 * q + σ0.vars "C" * (p + q) + 1 + q + 6 * σ0.vars "mx" + σ0.vars "C" + 8 < B
    rw [h0.hC, h0.hmx]; unfold sectionLength at hbig; rw [hm_eq] at hbig; omega)
  rw [h0.hC] at a1 a3; rw [h0.hmx] at a2 a4
  -- setup B
  have hsetB := hn.hsetB
  obtain ⟨σ2, r2, ⟨b1, b2, b3, b4⟩, fv2, fa2, -, fo2⟩ := (setupB_spec (B := B)).frame σ1 (by
    show σ1.vars "n6" + 2 * σ1.vars "m" + 8 < B ∧
      σ1.vars "nn" + (2 * σ1.vars "nn" - 1) * σ1.vars "m" + 2 * σ1.vars "nn" + 8 < B
    rw [a1, a2, a4]; exact ⟨by omega, hsetB⟩)
  rw [a1, a4] at b1 b2; rw [a1] at b3; rw [a1, a2] at b4
  have vm2 : σ2.vars "m" = F.length := by rw [fv2 "m" (by simp [wvars_setupB]), a1]
  have vnn2 : σ2.vars "nn" = numVars F := by rw [fv2 "nn" (by simp [wvars_setupB]), a2]
  have vS2 : σ2.vars "S" = sectionLength p q F := by
    rw [fv2 "S" (by simp [wvars_setupB]), a3]; rfl
  have v62 : σ2.vars "n6" = 6 * numVars F := by rw [fv2 "n6" (by simp [wvars_setupB]), a4]
  have vk2 : σ2.vars "k" = (lits F).length := by
    rw [fv2 "k" (by simp [wvars_setupB]), fv1 "k" (by simp [wvars_setupA]), h0.hk]
  have ar2 : σ2.arrs = σ0.arrs := by
    funext a
    rw [fa2 a (by simp [warrs_setupB]), fa1 a (by simp [warrs_setupA])]
  have out2 : σ2.out = [] := by
    rw [fo2 (by simp [setupB, Com.NoWrite]), fo1 (by simp [setupA, Com.NoWrite]), h0.hout]
  -- the table
  have hLactB := hn.hLactB
  obtain ⟨σ3, r3, ⟨I3, i3⟩, fv3, fa3, -, fo3⟩ :=
    (L2Fill.fillLoop_spec (B := B) (lits F).length F.length Lact (ivF F) (svF F) (cvF F)
      (fun i hi => lt_of_lt_of_le (cell_lt F i hi) hn.hLact) hn.hfill hLactB hn.hKB
      (by omega)).frame σ2 (by
    refine ⟨by simpa [Env.setVar] using vm2, by simpa [Env.setVar] using vk2, by simp [Env.setVar],
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simpa [Env.setVar] using out2⟩
    all_goals simp only [Env.setVar, ar2]
    · exact h0.lvr
    · exact h0.lsg
    · exact h0.lcl
    · exact h0.hvr
    · exact h0.hsg
    · exact h0.hcl
    · rw [h0.hact]; simp
    · intro t ht
      rw [h0.hact]
      classical
      simp [L2Fill.pre, List.getD_eq_getElem?_getD, ht])
  obtain ⟨-, -, -, -, -, -, -, -, -, len3, tab3, -⟩ := I3
  have hact3 : ∀ t, (σ3.arrs "act").getD t 0 = table F t := fun t => by
    rcases Nat.lt_or_ge t Lact with ht | ht
    · rw [tab3 t ht, i3, pre_eq_table]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), table_zero F t
        (le_trans hn.hLact ht)]
      rfl
  have vf3 : ∀ y, y ≠ "i" → y ≠ "t" → σ3.vars y = σ2.vars y := fun y h1 h2 =>
    fv3 y (by simp [wvars_fill, h1, h2])
  have ar3 : ∀ a, a ≠ "act" → σ3.arrs a = σ0.arrs a := fun a ha => by
    rw [fa3 a (by simp [warrs_fill, ha]), ar2]
  have out3 : σ3.out = [] := by
    rw [fo3 (by simp [L2Fill.fillLoop, L2Fill.fillBody, Com.NoWrite]), out2]
  -- the ordinary jobs
  have hNO := hn.hNO
  have hbigA := h0.hbigA
  obtain ⟨σ4, r4, ⟨I4, o4⟩, fv4, fa4, -, fo4⟩ :=
    (L2OrdLoop.ordLoop_spec (B := B) p q (numVars F) F.length (sectionLength p q F) (table F)
      (table_le_one F) hbig (by have := hn.hLact2; omega)).frame σ3 (by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [Env.setVar]
    · simpa using (vf3 "S" (by decide) (by decide)).trans vS2
    · simpa using (vf3 "nn" (by decide) (by decide)).trans vnn2
    · simpa using (vf3 "m" (by decide) (by decide)).trans vm2
    · simpa using (vf3 "n6" (by decide) (by decide)).trans v62
    · simpa using (vf3 "n6m" (by decide) (by decide)).trans b1
    · have := (vf3 "NO" (by decide) (by decide)).trans b2
      simp; omega
    · simp
    · rw [len3]; exact hn.hLact2
    · exact hact3
    · rw [ar3 "R" (by decide), hbigA "R" (by simp)]; exact hNO
    · rw [ar3 "D" (by decide), hbigA "D" (by simp)]; exact hNO
    · rw [ar3 "LG" (by decide), hbigA "LG" (by simp)]; exact hNO
    · intro o' ho'; simp at ho'
    · intro o' ho'; simp at ho'
    · intro o' ho'; simp at ho'
    · exact out3)
  have vf4 : ∀ y, y ∉ (L2OrdLoop.ordLoop p q).wvars → y ≠ "i" → y ≠ "t" →
      σ4.vars y = σ2.vars y := fun y hy h1 h2 => by rw [fv4 y hy, vf3 y h1 h2]
  have nw : ∀ y, y ∈ ["S", "m", "g", "NP", "NO", "nn"] → y ∉ (L2OrdLoop.ordLoop p q).wvars := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [wvars_ord, L2OrdLoop.wvars_calcO]
  have vS4 : σ4.vars "S" = sectionLength p q F :=
    (vf4 "S" (nw _ (by simp)) (by decide) (by decide)).trans vS2
  have vm4 : σ4.vars "m" = F.length :=
    (vf4 "m" (nw _ (by simp)) (by decide) (by decide)).trans vm2
  have vg4 : σ4.vars "g" = 1 + 2 * F.length :=
    (vf4 "g" (nw _ (by simp)) (by decide) (by decide)).trans b3
  have vNP4 : σ4.vars "NP" = Lax391470.SatConstruction.numPairs F :=
    (vf4 "NP" (nw _ (by simp)) (by decide) (by decide)).trans b4
  have vNO4 : σ4.vars "NO" = numOrdinary F := by
    rw [vf4 "NO" (nw _ (by simp)) (by decide) (by decide), b2]
    unfold numOrdinary numClauses; omega
  have act4 : σ4.arrs "act" = σ3.arrs "act" := fa4 "act" (by simp [warrs_ord])
  have arE4 : ∀ a ∈ ["E1", "E2", "E3", "E4"], (σ4.arrs a).length = big := fun a ha => by
    have h1 : a ∉ (L2OrdLoop.ordLoop p q).warrs := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> simp [warrs_ord]
    have h2 : a ≠ "act" := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> decide
    rw [fa4 a h1, ar3 a h2]
    exact hbigA a (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha ⊢; tauto)
  have out4 : σ4.out = [] := by
    rw [fo4 (by simp [L2OrdLoop.ordLoop, L2OrdLoop.ordBody, L2OrdLoop.calcO, L2Ord.calcSec,
      L2Ord.calcTail, Com.NoWrite]), out3]
  -- the pairs
  have hNP := hn.hNP
  obtain ⟨σ5, r5, ⟨I5, i5⟩, fv5, fa5, -, fo5⟩ :=
    (L2PairLoop.pairLoop_spec (B := B) p q (1 + 2 * F.length) F.length (sectionLength p q F) Lact
      (Lax391470.SatConstruction.numPairs F) (table F) (σ4.arrs "R") (σ4.arrs "D")
      (σ4.arrs "LG") hn.hPB
      (fun i0 hi => by obtain ⟨h1, h2, h3, h4⟩ := hn.heval i0 hi; exact ⟨by omega, by omega,
        by omega, by omega⟩) (by have := hn.hNPB; omega)).frame σ4 (by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [Env.setVar]
    · simpa using vS4
    · simpa using vm4
    · simpa using vg4
    · simpa using vNP4
    · simp
    · rw [act4]; exact hact3
    · rw [act4, len3]
    · rw [arE4 "E1" (by simp)]; exact hNP
    · rw [arE4 "E2" (by simp)]; exact hNP
    · rw [arE4 "E3" (by simp)]; exact hNP
    · rw [arE4 "E4" (by simp)]; exact hNP
    · intro o' ho'; simp at ho'
    · intro o' ho'; simp at ho'
    · intro o' ho'; simp at ho'
    · intro o' ho'; simp at ho'
    all_goals first | rfl | exact out4)
  -- the header
  have hsz : ∀ v, v + 4 < B → v.size ≤ B.size := fun v hv => Nat.size_le_size (by omega)
  have nwp : ∀ y, y ∈ ["NO", "NP"] → y ∉ (L2PairLoop.pairLoop p q).wvars := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl <;> simp [wvars_pair, L2PairLoop.wvars_calcP]
  have vNO5 : σ5.vars "NO" = numOrdinary F := (fv5 "NO" (nwp _ (by simp))).trans vNO4
  have hNOB : numOrdinary F + 4 < B := by unfold numOrdinary numClauses; omega
  have out5 : σ5.out = [] := I5.hout
  obtain ⟨σ6, r6, o6, v6, a6⟩ := emitVar_spec (B := B) "NO" B.size σ5
    ⟨by rw [vNO5]; exact hNOB, by rw [vNO5]; exact hsz _ hNOB⟩
  have vNP6 : σ6.vars "NP" = Lax391470.SatConstruction.numPairs F :=
    (v6 "NP" (by decide)).trans I5.hNP
  obtain ⟨σ7, r7, o7, v7, a7⟩ := emitVar_spec (B := B) "NP" B.size σ6
    ⟨by rw [vNP6]; exact hn.hNPB, by rw [vNP6]; exact hsz _ hn.hNPB⟩
  have ar7 : σ7.arrs = σ5.arrs := a7.trans a6
  have vNO7 : σ7.vars "NO" = numOrdinary F :=
    ((v7 "NO" (by decide)).trans (v6 "NO" (by decide))).trans vNO5
  have vNP7 : σ7.vars "NP" = Lax391470.SatConstruction.numPairs F :=
    (v7 "NP" (by decide)).trans vNP6
  have out7 : σ7.out = bitsNat (numOrdinary F) ++
      bitsNat (Lax391470.SatConstruction.numPairs F) := by
    rw [o7, o6, out5, vNO5, vNP6]; rfl
  -- the ordinary records
  have o4' : σ4.vars "o" = numOrdinary F := by
    rw [o4]; unfold numOrdinary numClauses; rfl
  have hR7 : σ7.arrs "R" = σ4.arrs "R" := by rw [ar7]; exact I5.hR
  have hD7 : σ7.arrs "D" = σ4.arrs "D" := by rw [ar7]; exact I5.hD
  have hL7 : σ7.arrs "LG" = σ4.arrs "LG" := by rw [ar7]; exact I5.hL
  have rowO_eq : ∀ o < numOrdinary F, rowO σ7.arrs o = L2Model.ordBits p q F o := fun o ho => by
    have hd := L2OrdSem.dVal_eq p q F o ho
    have hl := L2OrdSem.lgVal_eq F o
    simp only [numClauses] at hd hl
    unfold rowO L2Model.ordBits
    rw [hR7, hD7, hL7, I4.hr o (by omega), I4.hd o (by omega), I4.hl o (by omega),
      L2OrdSem.rVal_eq, hd, hl]
  obtain ⟨σ8, r8, ⟨⟨a8, v8, -, o8⟩, x8⟩⟩ :=
    printLoop_spec (B := B) "o" "NO" recO (okO (B := B) B.size) rowO _ (recO_spec (B := B) B.size)
      σ7.arrs σ7.vars (numOrdinary F) σ7.out (by decide) vNO7 (by omega)
      (fun σ ha ho => by
        have e1 := I4.hr _ (by omega : σ.vars "o" < σ4.vars "o")
        have e2 := I4.hd _ (by omega : σ.vars "o" < σ4.vars "o")
        have e3 := I4.hl _ (by omega : σ.vars "o" < σ4.vars "o")
        have b1 := L2OrdLoop.rVal_le q (numVars F) (sectionLength p q F) (σ.vars "o")
        have b2 := L2OrdLoop.dVal_le p q (numVars F) F.length (sectionLength p q F) (table F)
          (σ.vars "o") (by unfold numOrdinary numClauses at ho; exact ho)
        have b3 := L2OrdLoop.lgVal_le (numVars F) F.length (σ.vars "o")
        have g1 := I4.hR
        have g2 := I4.hD
        have g3 := I4.hLG
        have ho' : σ.vars "o" < 6 * numVars F + 2 * F.length := by
          unfold numOrdinary numClauses at ho; exact ho
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals try simp only [ha, hR7, hD7, hL7, e1, e2, e3]
        all_goals first | omega | exact hsz _ (by omega)) σ7 ⟨rfl, fun y hy => by simp [Env.setVar]; intro h; simp [h] at hy, by simp [Env.setVar],
        by simp [Env.setVar]⟩
  -- the pair records
  have ar8 : σ8.arrs = σ5.arrs := a8.trans ar7
  have vNP8 : σ8.vars "NP" = Lax391470.SatConstruction.numPairs F :=
    (v8 "NP" (by decide)).trans vNP7
  have he1 := fun i (hi : i < Lax391470.SatConstruction.numPairs F) => I5.e1 i (by omega)
  have he2 := fun i (hi : i < Lax391470.SatConstruction.numPairs F) => I5.e2 i (by omega)
  have he3 := fun i (hi : i < Lax391470.SatConstruction.numPairs F) => I5.e3 i (by omega)
  have he4 := fun i (hi : i < Lax391470.SatConstruction.numPairs F) => I5.e4 i (by omega)
  have rowP_eq : ∀ i < Lax391470.SatConstruction.numPairs F,
      rowP σ8.arrs i = L2Model.pairBits p q F i := fun i hi => by
    have q1 := L2PairSem.e1Val_eq p q F i hi
    have q2 := L2PairSem.e2Val_eq p q F i
    have q3 := L2PairSem.e3Val_eq p q F i hi
    have q4 := L2PairSem.e4Val_eq p q F i
    simp only [numClauses] at q1 q2 q3 q4
    unfold rowP L2Model.pairBits
    rw [ar8, he1 i hi, he2 i hi, he3 i hi, he4 i hi, q1, q2, q3, q4]
  obtain ⟨σ9, r9, ⟨⟨-, -, -, o9⟩, x9⟩⟩ :=
    printLoop_spec (B := B) "i" "NP" recP (okP (B := B) B.size) rowP _ (recP_spec (B := B) B.size)
      σ8.arrs σ8.vars (Lax391470.SatConstruction.numPairs F) σ8.out (by decide) vNP8
      (by have := hn.hNPB; omega)
      (fun σ ha hi => by
        obtain ⟨w1, w2, w3, w4⟩ := hn.heval _ hi
        have g1 := I5.h1
        have g2 := I5.h2
        have g3 := I5.h3
        have g4 := I5.h4
        refine ⟨by have := hn.hNPB; omega, fun a hmem => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl | rfl
        · rw [ha, ar8, he1 _ hi]; exact ⟨by omega, w1, hsz _ w1⟩
        · rw [ha, ar8, he2 _ hi]; exact ⟨by omega, w2, hsz _ w2⟩
        · rw [ha, ar8, he3 _ hi]; exact ⟨by omega, w3, hsz _ w3⟩
        · rw [ha, ar8, he4 _ hi]; exact ⟨by omega, w4, hsz _ w4⟩) σ8
      ⟨rfl, fun y hy => by simp [Env.setVar]; intro h; simp [h] at hy, by simp [Env.setVar],
        by simp [Env.setVar]⟩
  refine ⟨σ9, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq r9)))))))).mono
    (by unfold Kacc; omega), ?_⟩
  show σ9.out = L2Model.outBits p q F
  rw [o9, x9, o8, x8, out7]
  unfold L2Model.outBits
  rw [List.flatMap_congr (fun o ho => rowO_eq o (List.mem_range.mp ho)),
    List.flatMap_congr (fun i hi => rowP_eq i (List.mem_range.mp hi))]

end Lax391470Proofs.L2Accept
