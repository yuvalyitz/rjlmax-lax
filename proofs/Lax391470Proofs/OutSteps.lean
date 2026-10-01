import Lax391470Proofs.L2Parts
import Lax391470Proofs.L1Lists

/-!
Output steps: commands that append to the output a list determined by the token array, a
counter and a base index, and otherwise touch only scratch scalars. Such steps compose.
-/

namespace Lax391470Proofs.OutSteps

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.Bits

/-- The scratch scalars of output steps. -/
def SCR : List String := ["v", "s", "u", "i2", "ix", "aa", "M"]

/-- Nothing but scratch scalars changed. -/
def Same (σ σ' : Env) : Prop := (∀ y ∉ SCR, σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs

lemma Same.trans {σ σ' σ'' : Env} (h : Same σ σ') (h' : Same σ' σ'') : Same σ σ'' :=
  ⟨fun y hy => (h'.1 y hy).trans (h.1 y hy), h'.2.trans h.2⟩

variable {B : ℕ}

/-- An output step: under `P` of the token array, the counter `i` and the base `b3`, the
command appends `bits` of the same three. -/
def OStep (B : ℕ) (c : Com) (P : List ℕ → ℕ → ℕ → Prop) (bits : List ℕ → ℕ → ℕ → List ℕ)
    (K : ℕ) : Prop :=
  Spec B (fun σ => P (σ.arrs "TK") (σ.vars "i") (σ.vars "b3")) c
    (fun σ σ' => σ'.out = σ.out ++ bits (σ.arrs "TK") (σ.vars "i") (σ.vars "b3") ∧ Same σ σ') K

lemma key_of_same {σ σ' : Env} (h : Same σ σ') :
    σ'.arrs "TK" = σ.arrs "TK" ∧ σ'.vars "i" = σ.vars "i" ∧ σ'.vars "b3" = σ.vars "b3" :=
  ⟨by rw [h.2], h.1 "i" (by decide), h.1 "b3" (by decide)⟩

/-- **Output steps compose.** -/
theorem OStep.seq {c d : Com} {P Q : List ℕ → ℕ → ℕ → Prop}
    {b e : List ℕ → ℕ → ℕ → List ℕ} {K K' : ℕ} (h : OStep B c P b K) (h' : OStep B d Q e K') :
    OStep B (.seq c d) (fun t i b3 => P t i b3 ∧ Q t i b3) (fun t i b3 => b t i b3 ++ e t i b3)
      (K + K') := by
  intro σ ⟨hP, hQ⟩
  obtain ⟨σ1, r1, o1, s1⟩ := h σ hP
  obtain ⟨k1, k2, k3⟩ := key_of_same s1
  obtain ⟨σ2, r2, o2, s2⟩ := h' σ1 (by
    show Q (σ1.arrs "TK") (σ1.vars "i") (σ1.vars "b3")
    rw [k1, k2, k3]; exact hQ)
  refine ⟨σ2, r1.seq r2, ?_, s1.trans s2⟩
  rw [o2, o1, k1, k2, k3, List.append_assoc]

theorem OStep.weaken {c : Com} {P P' : List ℕ → ℕ → ℕ → Prop}
    {b b' : List ℕ → ℕ → ℕ → List ℕ} {K K' : ℕ} (h : OStep B c P b K)
    (hP : ∀ t i b3, P' t i b3 → P t i b3) (hb : ∀ t i b3, P' t i b3 → b t i b3 = b' t i b3)
    (hK : K ≤ K') : OStep B c P' b' K' := by
  intro σ hσ
  obtain ⟨σ1, r1, o1, s1⟩ := h σ (hP _ _ _ hσ)
  exact ⟨σ1, r1.mono hK, by rw [o1, hb _ _ _ hσ], s1⟩

open Lax391470Proofs.L2Parts Lax391470Proofs.L2Print

lemma same_of_frame {σ σ' : Env} (hv : ∀ y ∉ ["v", "s", "u", "i2"], σ'.vars y = σ.vars y)
    (ha : σ'.arrs = σ.arrs) : Same σ σ' :=
  ⟨fun y hy => hv y (by
    simp only [SCR, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy ⊢; tauto), ha⟩

/-- Write the constant bit `n`. -/
theorem oWrite (n : ℕ) (hn : n < B) :
    OStep B (.write (.lit n)) (fun _ _ _ => True) (fun _ _ _ => [n]) 2 := by
  intro σ _
  exact ⟨_, (Run.write (evalB_lit hn)).mono (by simp [Expr.size]), rfl, fun _ _ => rfl, rfl⟩

/-- Write the code of the constant `n`. -/
theorem oEmitLit (n Sz : ℕ) (hn : n + 4 < B) (hs : n.size ≤ Sz) :
    OStep B (emitLit n) (fun _ _ _ => True) (fun _ _ _ => bitsNat n) (48 * Sz + 50) := by
  intro σ _
  obtain ⟨σ', r, o, v, a⟩ := emitLit_spec (B := B) n Sz hn hs σ trivial
  exact ⟨σ', r, o, same_of_frame v a⟩

/-- Write the code of the token at the index the expression `ie` computes. -/
def emitTK (ie : Expr) : Com := .seq (.assign "ix" ie) (emitAt "TK" "ix")

theorem oEmitTK (ie : Expr) (f : ℕ → ℕ → ℕ) (Sz : ℕ) (P : List ℕ → ℕ → ℕ → Prop)
    (hie : ∀ σ, P (σ.arrs "TK") (σ.vars "i") (σ.vars "b3") →
      ie.evalB B σ = some (f (σ.vars "i") (σ.vars "b3")))
    (hP : ∀ t i b3, P t i b3 → f i b3 < t.length ∧ f i b3 < B ∧ t.getD (f i b3) 0 + 4 < B ∧
      (t.getD (f i b3) 0).size ≤ Sz) :
    OStep B (emitTK ie) P (fun t i b3 => bitsNat (t.getD (f i b3) 0))
      (1 + ie.size + (48 * Sz + 50)) := by
  intro σ hσ
  obtain ⟨h1, h2, h3, h4⟩ := hP _ _ _ hσ
  have r1 : Run B (.assign "ix" ie) σ (σ.setVar "ix" (f (σ.vars "i") (σ.vars "b3")))
      (1 + ie.size) := Run.assign (hie σ hσ)
  obtain ⟨σ2, r2, o2, v2, a2⟩ := emitAt_spec (B := B) "TK" "ix" Sz (by decide)
    (σ.setVar "ix" (f (σ.vars "i") (σ.vars "b3")))
    ⟨by simpa [Env.setVar] using h1, by simpa [Env.setVar] using h2,
      by simpa [Env.setVar] using h3, by simpa [Env.setVar] using h4⟩
  refine ⟨σ2, r1.seq r2, by simpa [Env.setVar] using o2, fun y hy => ?_, by
    rw [a2]; simp [Env.setVar]⟩
  have hix : y ≠ "ix" := fun h => hy (by simp [SCR, h])
  rw [v2 y (by
    simp only [SCR, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy ⊢; tauto)]
  simp [Env.setVar, hix]

open Lax391470Proofs.EmitNat Lax391470Proofs.L1Lists

abbrev V (s : String) : Expr := .var s

variable (p q : ℕ)

/-- Write the integer `a - (p + 2q)(i + 1)`: its sign, then its absolute value. -/
def emitInt (a : ℕ) : Com :=
  .seq (.assign "M" (.bin .mul (.lit (p + 2 * q)) (.bin .add (V "i") (.lit 1))))
    (.seq (.ite (.lt (.lit a) (V "M"))
        (.seq (.write (.lit 1)) (.assign "v" (.bin .sub (V "M") (.lit a))))
        (.seq (.write (.lit 0)) (.assign "v" (.bin .sub (.lit a) (V "M")))))
      emitNat)

theorem emitInt_flat (a Sz i0 : ℕ) (hB : (p + 2 * q) * (i0 + 1) + a + 8 < B)
    (hiB : i0 + 2 < B) (hpq : p + 2 * q < B)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) :
    Spec B (fun σ => σ.vars "i" = i0) (emitInt p q a)
      (fun σ σ' => σ'.out = σ.out ++ intBits a ((p + 2 * q) * (i0 + 1)) ∧
        (∀ y ∉ ["v", "s", "u", "i2", "M"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs)
      (48 * Sz + 70) := by
  run_vcg [(emitNat_spec (B := B) Sz).frame]
  all_goals have hi := ‹σ.vars "i" = i0›
  iterate 2 (
    obtain ⟨ho, hfv, hfa, -, -⟩ := ‹_ ∧ (∀ y ∉ emitNat.wvars, _) ∧ _›
    refine ⟨?_, fun y hy => ?_, ?_⟩
    · simp only [Env.setVar, if_true, hi] at ho
      rw [ho]
      first
        | (simp_all [intBits, Env.setVar]; done)
        | (simp_all [intBits, Env.setVar]; rw [if_neg (by omega)])
    · have hy' : y ∉ emitNat.wvars := by
        rw [L2Print.wvars_emitNat]
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy ⊢; tauto
      have h1 : y ≠ "v" := fun h => hy (by simp [h])
      have h2 : y ≠ "M" := fun h => hy (by simp [h])
      rw [hfv y hy']; simp [Env.setVar, h1, h2]
    · funext b
      rw [hfa b (by simp [L2Print.warrs_emitNat])]; simp [Env.setVar])
  all_goals try simp [Env.setVar] at *
  all_goals try simp only [hi] at *
  all_goals first
    | omega
    | exact ⟨by omega, hs _ (by omega)⟩

theorem oEmitInt (a Sz : ℕ) (hpq : p + 2 * q < B) (hs : ∀ v, v + 4 < B → v.size ≤ Sz) :
    OStep B (emitInt p q a) (fun _ i _ => (p + 2 * q) * (i + 1) + a + 8 < B ∧ i + 2 < B)
      (fun _ i _ => intBits a ((p + 2 * q) * (i + 1))) (48 * Sz + 70) := by
  intro σ ⟨h1, h2⟩
  obtain ⟨σ', r, o, v, a'⟩ := emitInt_flat (B := B) p q a Sz (σ.vars "i") h1 h2 hpq hs σ rfl
  refine ⟨σ', r, o, fun y hy => v y ?_, a'⟩
  simp only [SCR, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy ⊢; tauto

/-- Choose the length by the bit in `TK[ix]`, and write its code. -/
def selLen : Com :=
  .seq (.assign "v" (.lit q))
    (.seq (.ite (.eq (.get "TK" (V "ix")) (.lit 0)) .skip (.assign "v" (.lit p))) emitNat)

theorem selLen_flat (Sz k bit : ℕ) (hp : p + 4 < B) (hq : q + 4 < B)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) :
    Spec B (fun σ => σ.vars "ix" = k ∧ k < (σ.arrs "TK").length ∧ k < B ∧
        (σ.arrs "TK").getD k 0 = bit ∧ bit < B) (selLen p q)
      (fun σ σ' => σ'.out = σ.out ++ bitsNat (if bit = 0 then q else p) ∧
        (∀ y ∉ ["v", "s", "u", "i2"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs)
      (48 * Sz + 60) := by
  run_vcg [(emitNat_spec (B := B) Sz).frame]
  all_goals have hix := ‹σ.vars "ix" = k›
  all_goals have hbit := ‹(σ.arrs "TK").getD k 0 = bit›
  iterate 2 (
    obtain ⟨ho, hfv, hfa, -, -⟩ := ‹_ ∧ (∀ y ∉ emitNat.wvars, _) ∧ _›
    refine ⟨?_, fun y hy => ?_, ?_⟩
    · simp only [Env.setVar, if_true] at ho
      rw [ho]
      simp_all [Env.setVar]
    · have hy' : y ∉ emitNat.wvars := by
        rw [L2Print.wvars_emitNat]
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy ⊢; tauto
      have h1 : y ≠ "v" := fun h => hy (by simp [h])
      rw [hfv y hy']; simp [Env.setVar, h1]
    · funext b
      rw [hfa b (by simp [L2Print.warrs_emitNat])]; simp [Env.setVar])
  all_goals try simp [Env.setVar] at *
  all_goals try simp only [hix, hbit] at *
  all_goals first
    | omega
    | exact ⟨by omega, hs _ (by omega)⟩

/-- Write `p` or `q` according to the token at the index `ie` computes. -/
def emitSel (ie : Expr) : Com := .seq (.assign "ix" ie) (selLen p q)

theorem oEmitSel (ie : Expr) (f : ℕ → ℕ → ℕ) (Sz : ℕ) (P : List ℕ → ℕ → ℕ → Prop)
    (hp : p + 4 < B) (hq : q + 4 < B) (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hie : ∀ σ, P (σ.arrs "TK") (σ.vars "i") (σ.vars "b3") →
      ie.evalB B σ = some (f (σ.vars "i") (σ.vars "b3")))
    (hP : ∀ t i b3, P t i b3 → f i b3 < t.length ∧ f i b3 < B ∧ t.getD (f i b3) 0 < B) :
    OStep B (emitSel p q ie) P
      (fun t i b3 => bitsNat (if t.getD (f i b3) 0 = 0 then q else p))
      (1 + ie.size + (48 * Sz + 60)) := by
  intro σ hσ
  obtain ⟨h1, h2, h3⟩ := hP _ _ _ hσ
  have r1 : Run B (.assign "ix" ie) σ (σ.setVar "ix" (f (σ.vars "i") (σ.vars "b3")))
      (1 + ie.size) := Run.assign (hie σ hσ)
  obtain ⟨σ2, r2, o2, v2, a2⟩ := selLen_flat (B := B) p q Sz (f (σ.vars "i") (σ.vars "b3"))
    ((σ.arrs "TK").getD (f (σ.vars "i") (σ.vars "b3")) 0) hp hq hs
    (σ.setVar "ix" (f (σ.vars "i") (σ.vars "b3")))
    ⟨by simp [Env.setVar], by simpa [Env.setVar] using h1, h2, by simp [Env.setVar], h3⟩
  refine ⟨σ2, r1.seq r2, by simpa [Env.setVar] using o2, fun y hy => ?_, by
    rw [a2]; simp [Env.setVar]⟩
  have hix : y ≠ "ix" := fun h => hy (by simp [SCR, h])
  rw [v2 y (by
    simp only [SCR, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy ⊢; tauto)]
  simp [Env.setVar, hix]

/-! ### A Loop of Output Steps -/

/-- The invariant of a loop printing rows `0, …, i - 1`. -/
def LInv (A0 : String → List ℕ) (v0 : String → ℕ) (N : ℕ)
    (bits : List ℕ → ℕ → ℕ → List ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.arrs = A0 ∧ (∀ y ∉ SCR, y ≠ "i" → σ.vars y = v0 y) ∧ σ.vars "i" ≤ N ∧
    σ.out = out0 ++ (List.range (σ.vars "i")).flatMap fun i => bits (A0 "TK") i (v0 "b3")

theorem oLoop (mv : String) (c : Com) (P : List ℕ → ℕ → ℕ → Prop)
    (bits : List ℕ → ℕ → ℕ → List ℕ) (K : ℕ) (hc : OStep B c P bits K)
    (A0 : String → List ℕ) (v0 : String → ℕ) (N : ℕ) (out0 : List ℕ)
    (hmv : mv ∉ SCR) (hmi : mv ≠ "i") (hN : v0 mv = N) (hNB : N + 1 < B)
    (hP : ∀ i < N, P (A0 "TK") i (v0 "b3")) :
    Spec B (fun σ => LInv A0 v0 N bits out0 (σ.setVar "i" 0))
      (.seq (.assign "i" (.lit 0))
        (.while (.lt (.var "i") (.var mv)) (.seq c (.assign "i" (.bin .add (V "i") (.lit 1))))))
      (fun _ σ' => LInv A0 v0 N bits out0 σ' ∧ σ'.vars "i" = N) ((K + 10 + 4) * N + 6) := by
  refine Spec.forRangeZero "i" mv (LInv A0 v0 N bits out0) N (K + 10) (by omega)
    (fun _ h => h.2.2.1) (fun σ h => (h.2.1 mv hmv hmi).trans hN) ?_
  intro σ ⟨⟨ha, hv, hle, hout⟩, hlt⟩
  have hb3 : σ.vars "b3" = v0 "b3" := hv "b3" (by decide) (by decide)
  obtain ⟨σ1, r1, o1, s1⟩ := hc σ (by
    show P (σ.arrs "TK") (σ.vars "i") (σ.vars "b3")
    rw [ha, hb3]; exact hP _ hlt)
  obtain ⟨k1, k2, k3⟩ := key_of_same s1
  have r2 : Run B (.assign "i" (.bin .add (V "i") (.lit 1))) σ1 (σ1.setVar "i" (σ1.vars "i" + 1))
      (1 + (Expr.bin .add (V "i") (.lit 1)).size) :=
    Run.assign (evalB_bin (evalB_var (by rw [k2]; omega)) (evalB_lit (by omega))
      (by simp [k2]; omega))
  refine ⟨_, (r1.seq r2).mono (by simp [Expr.size]), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [Env.setVar]; rw [s1.2, ha]
  · intro y hy hyi
    simp only [Env.setVar, if_neg hyi]
    rw [s1.1 y hy]; exact hv y hy hyi
  · simp [Env.setVar, k2]; omega
  · simp only [Env.setVar, if_true, k2]
    rw [o1, hout, List.range_succ, List.flatMap_append, ha, hb3]
    simp
  · simp [Env.setVar, k2]

end Lax391470Proofs.OutSteps
