import Lax391470Proofs.EmitNat

/-!
Printing a table of records: for every row, the codes of its number columns and then its
raw bit columns. Stated for arbitrary columns, so that nothing here knows about scheduling.
-/

namespace Lax391470Proofs.L2Print

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.Bits Lax391470Proofs.EmitNat

abbrev V (s : String) : Expr := .var s

/-- Write the code of entry `x` of array `a`. -/
def emitAt (a x : String) : Com := .seq (.assign "v" (.get a (V x))) emitNat

lemma wvars_emitNat : emitNat.wvars = ["s", "u", "u", "s", "i2", "i2", "u", "i2", "u", "i2"] := by
  simp [emitNat, sizeLoop, sizeBody, onesLoop, onesBody, digLoop, digBody, Com.wvars]

lemma warrs_emitNat : emitNat.warrs = [] := by
  simp [emitNat, sizeLoop, sizeBody, onesLoop, onesBody, digLoop, digBody, Com.warrs]

variable {B : ℕ}

/-- **One number.** Everything but the scratch scalars and the output is left alone. -/
theorem emitAt_spec (a x : String) (Sz : ℕ) (_hx : x ∉ ["v", "s", "u", "i2"]) :
    Spec B (fun σ => σ.vars x < (σ.arrs a).length ∧ σ.vars x < B ∧
        (σ.arrs a).getD (σ.vars x) 0 + 4 < B ∧ ((σ.arrs a).getD (σ.vars x) 0).size ≤ Sz)
      (emitAt a x)
      (fun σ σ' => σ'.out = σ.out ++ bitsNat ((σ.arrs a).getD (σ.vars x) 0) ∧
        (∀ y ∉ ["v", "s", "u", "i2"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs)
      (48 * Sz + 50) := by
  run_vcg [(emitNat_spec (B := B) Sz).frame]
  · obtain ⟨hout, hfv, hfa, -, -⟩ := ‹_ ∧ (∀ y ∉ emitNat.wvars, _) ∧ _›
    refine ⟨by simpa [Env.setVar] using hout, fun y hy => ?_, ?_⟩
    · have h1 := hfv y (by
        rw [wvars_emitNat]; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy ⊢
        tauto)
      have hyv : y ≠ "v" := fun h => hy (by simp [h])
      simpa [Env.setVar, hyv] using h1
    · funext b
      have := hfa b (by simp [warrs_emitNat])
      simpa [Env.setVar] using this
  · simp only [Env.setVar, if_true]
    exact ⟨‹_›, ‹_›⟩

/-- Write the raw entry `x` of array `a`, and advance `x`. -/
def rawStep (a x : String) : Com :=
  .seq (.write (.get a (V x))) (.assign x (.bin .add (V x) (.lit 1)))

theorem rawStep_spec (a x : String) :
    Spec B (fun σ => σ.vars x < (σ.arrs a).length ∧ σ.vars x + 1 < B ∧
        (σ.arrs a).getD (σ.vars x) 0 < B) (rawStep a x)
      (fun σ σ' => σ'.out = σ.out ++ [(σ.arrs a).getD (σ.vars x) 0] ∧
        σ'.vars x = σ.vars x + 1 ∧ (∀ y, y ≠ x → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs)
      20 := by
  run_vcg
  · refine ⟨by simp [Env.setVar], by simp [Env.setVar], fun y hy => by simp [Env.setVar, hy], ?_⟩
    simp [Env.setVar]

/-- Advance `x` only. -/
def bumpStep (x : String) : Com := .assign x (.bin .add (V x) (.lit 1))

theorem bumpStep_spec (x : String) :
    Spec B (fun σ => σ.vars x + 1 < B) (bumpStep x)
      (fun σ σ' => σ'.out = σ.out ∧ σ'.vars x = σ.vars x + 1 ∧
        (∀ y, y ≠ x → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs) 10 := by
  run_vcg
  · exact ⟨by simp [Env.setVar], by simp [Env.setVar], fun y hy => by simp [Env.setVar, hy],
      by simp [Env.setVar]⟩

/-! ### One record of an ordinary job -/

def recO : Com := .seq (emitAt "R" "o") (.seq (emitAt "D" "o") (rawStep "LG" "o"))

/-- The zeros and ones of row `o` of the three columns. -/
def rowO (A : String → List ℕ) (o : ℕ) : List ℕ :=
  bitsNat ((A "R").getD o 0) ++ bitsNat ((A "D").getD o 0) ++ [(A "LG").getD o 0]

def okO (Sz : ℕ) (σ : Env) : Prop :=
  σ.vars "o" < (σ.arrs "R").length ∧ σ.vars "o" < (σ.arrs "D").length ∧
    σ.vars "o" < (σ.arrs "LG").length ∧ σ.vars "o" + 1 < B ∧
    (σ.arrs "R").getD (σ.vars "o") 0 + 4 < B ∧ ((σ.arrs "R").getD (σ.vars "o") 0).size ≤ Sz ∧
    (σ.arrs "D").getD (σ.vars "o") 0 + 4 < B ∧ ((σ.arrs "D").getD (σ.vars "o") 0).size ≤ Sz ∧
    (σ.arrs "LG").getD (σ.vars "o") 0 < B

theorem recO_spec (Sz : ℕ) :
    Spec B (okO (B := B) Sz) recO
      (fun σ σ' => σ'.out = σ.out ++ rowO σ.arrs (σ.vars "o") ∧
        σ'.vars "o" = σ.vars "o" + 1 ∧
        (∀ y ∉ ["v", "s", "u", "i2", "o"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs)
      (2 * (48 * Sz + 50) + 20) := by
  intro σ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  obtain ⟨σ1, r1, o1, v1, a1⟩ := emitAt_spec (B := B) "R" "o" Sz (by decide) σ
    ⟨h1, by omega, h5, h6⟩
  have e1 : σ1.vars "o" = σ.vars "o" := v1 "o" (by decide)
  obtain ⟨σ2, r2, o2, v2, a2⟩ := emitAt_spec (B := B) "D" "o" Sz (by decide) σ1
    ⟨by rw [a1, e1]; exact h2, by rw [e1]; omega, by rw [a1, e1]; exact h7,
      by rw [a1, e1]; exact h8⟩
  have e2 : σ2.vars "o" = σ.vars "o" := (v2 "o" (by decide)).trans e1
  obtain ⟨σ3, r3, o3, v3, w3, a3⟩ := rawStep_spec (B := B) "LG" "o" σ2
    ⟨by rw [a2, a1, e2]; exact h3, by rw [e2]; exact h4, by rw [a2, a1, e2]; exact h9⟩
  refine ⟨σ3, ((r1.seq (r2.seq r3))).mono (by omega), ?_, by rw [v3, e2], fun y hy => ?_,
    by rw [a3, a2, a1]⟩
  · rw [o3, o2, o1, a2, a1, e2, e1]
    simp [rowO, List.append_assoc]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [w3 y hy.2.2.2.2, v2 y (by simp; tauto), v1 y (by simp; tauto)]

/-! ### One record of a connected pair -/

def recP : Com :=
  .seq (emitAt "E1" "i") (.seq (emitAt "E2" "i") (.seq (emitAt "E3" "i")
    (.seq (emitAt "E4" "i") (bumpStep "i"))))

def rowP (A : String → List ℕ) (i : ℕ) : List ℕ :=
  bitsNat ((A "E1").getD i 0) ++ bitsNat ((A "E2").getD i 0) ++
    bitsNat ((A "E3").getD i 0) ++ bitsNat ((A "E4").getD i 0)

def okP (Sz : ℕ) (σ : Env) : Prop :=
  σ.vars "i" + 1 < B ∧ ∀ a ∈ ["E1", "E2", "E3", "E4"],
    σ.vars "i" < (σ.arrs a).length ∧ (σ.arrs a).getD (σ.vars "i") 0 + 4 < B ∧
      ((σ.arrs a).getD (σ.vars "i") 0).size ≤ Sz

theorem recP_spec (Sz : ℕ) :
    Spec B (okP (B := B) Sz) recP
      (fun σ σ' => σ'.out = σ.out ++ rowP σ.arrs (σ.vars "i") ∧
        σ'.vars "i" = σ.vars "i" + 1 ∧
        (∀ y ∉ ["v", "s", "u", "i2", "i"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs)
      (4 * (48 * Sz + 50) + 10) := by
  intro σ ⟨hB, h⟩
  obtain ⟨k1, k2, k3⟩ := h "E1" (by simp)
  obtain ⟨σ1, r1, o1, v1, a1⟩ := emitAt_spec (B := B) "E1" "i" Sz (by decide) σ
    ⟨k1, by omega, k2, k3⟩
  have e1 : σ1.vars "i" = σ.vars "i" := v1 "i" (by decide)
  obtain ⟨k1, k2, k3⟩ := h "E2" (by simp)
  obtain ⟨σ2, r2, o2, v2, a2⟩ := emitAt_spec (B := B) "E2" "i" Sz (by decide) σ1
    ⟨by rw [a1, e1]; exact k1, by rw [e1]; omega, by rw [a1, e1]; exact k2,
      by rw [a1, e1]; exact k3⟩
  have e2 : σ2.vars "i" = σ.vars "i" := (v2 "i" (by decide)).trans e1
  obtain ⟨k1, k2, k3⟩ := h "E3" (by simp)
  obtain ⟨σ3, r3, o3, v3, a3⟩ := emitAt_spec (B := B) "E3" "i" Sz (by decide) σ2
    ⟨by rw [a2, a1, e2]; exact k1, by rw [e2]; omega, by rw [a2, a1, e2]; exact k2,
      by rw [a2, a1, e2]; exact k3⟩
  have e3 : σ3.vars "i" = σ.vars "i" := (v3 "i" (by decide)).trans e2
  obtain ⟨k1, k2, k3⟩ := h "E4" (by simp)
  obtain ⟨σ4, r4, o4, v4, a4⟩ := emitAt_spec (B := B) "E4" "i" Sz (by decide) σ3
    ⟨by rw [a3, a2, a1, e3]; exact k1, by rw [e3]; omega, by rw [a3, a2, a1, e3]; exact k2,
      by rw [a3, a2, a1, e3]; exact k3⟩
  have e4 : σ4.vars "i" = σ.vars "i" := (v4 "i" (by decide)).trans e3
  obtain ⟨σ5, r5, o5, v5, w5, a5⟩ := bumpStep_spec (B := B) "i" σ4 (by show σ4.vars "i" + 1 < B; rw [e4]; exact hB)
  refine ⟨σ5, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono (by omega), ?_, by rw [v5, e4],
    fun y hy => ?_, by rw [a5, a4, a3, a2, a1]⟩
  · rw [o5, o4, o3, o2, o1, a3, a2, a1, e3, e2, e1]
    simp [rowP, List.append_assoc]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [w5 y hy.2.2.2.2, v4 y (by simp; tauto), v3 y (by simp; tauto), v2 y (by simp; tauto),
      v1 y (by simp; tauto)]

/-! ### A loop of records -/

/-- The invariant of a printing loop over the counter `x`: the arrays and all scalars but
the scratch ones are fixed, and the rows below the counter have been written. -/
def PrInv (x : String) (A0 : String → List ℕ) (v0 : String → ℕ) (N : ℕ)
    (row : (String → List ℕ) → ℕ → List ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.arrs = A0 ∧ (∀ y ∉ ["v", "s", "u", "i2", x], σ.vars y = v0 y) ∧ σ.vars x ≤ N ∧
    σ.out = out0 ++ (List.range (σ.vars x)).flatMap (row A0)

theorem printLoop_spec (x mv : String) (c : Com) (ok : Env → Prop)
    (row : (String → List ℕ) → ℕ → List ℕ) (K : ℕ)
    (hc : Spec B ok c (fun σ σ' => σ'.out = σ.out ++ row σ.arrs (σ.vars x) ∧
      σ'.vars x = σ.vars x + 1 ∧ (∀ y ∉ ["v", "s", "u", "i2", x], σ'.vars y = σ.vars y) ∧
      σ'.arrs = σ.arrs) K)
    (A0 : String → List ℕ) (v0 : String → ℕ) (N : ℕ) (out0 : List ℕ)
    (hmv : mv ∉ ["v", "s", "u", "i2", x]) (hN : v0 mv = N) (hNB : N < B)
    (hok : ∀ σ, σ.arrs = A0 → σ.vars x < N → ok σ) :
    Spec B (fun σ => PrInv x A0 v0 N row out0 (σ.setVar x 0))
      (.seq (.assign x (.lit 0)) (.while (.lt (.var x) (.var mv)) c))
      (fun _ σ' => PrInv x A0 v0 N row out0 σ' ∧ σ'.vars x = N) ((K + 4) * N + 6) := by
  refine Spec.forRangeZero x mv (PrInv x A0 v0 N row out0) N K hNB (fun _ h => h.2.2.1)
    (fun σ h => (h.2.1 mv hmv).trans hN) ?_
  intro σ ⟨⟨ha, hv, hle, hout⟩, hlt⟩
  obtain ⟨σ', r, o1, x1, v1, a1⟩ := hc σ (hok σ ha hlt)
  refine ⟨σ', r, ⟨a1.trans ha, fun y hy => (v1 y hy).trans (hv y hy), by omega, ?_⟩, x1⟩
  rw [o1, hout, x1, List.range_succ, List.flatMap_append, ha]
  simp

end Lax391470Proofs.L2Print
