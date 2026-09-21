import Lax391470Proofs.L2Ord

/-!
The four deadlines of one connected pair, computed from the dimensions of the construction
and the table of active blocks. Stated against pure mirror functions of the program.
-/

namespace Lax391470Proofs.L2Pair

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.L2Ord

variable (p q : ℕ)

def pp (g i : ℕ) : ℕ := i - i / g * g
def pj (g m i : ℕ) : ℕ := (pp g i - 1) - (pp g i - 1) / m * m
def psec (g m i : ℕ) : ℕ := 2 * (i / g) + (pp g i - 1) / m

def e1Val (g m S : ℕ) (act : ℕ → ℕ) (i : ℕ) : ℕ :=
  if pp g i = 0 then S * (2 * (i / g)) + (p + q + 1)
  else if act (psec g m i * m + pj g m i) = 0
    then S * psec g m i + (p + 2 * q) + pj g m i * (p + q) + (p + q - 1)
    else S * psec g m i + (p + 2 * q) + pj g m i * (p + q) + (p + q)

def e2Val (g m S : ℕ) (i : ℕ) : ℕ :=
  if pp g i = 0 then S * (2 * (i / g)) + (p + 2 * q)
  else S * psec g m i + (p + 2 * q) + pj g m i * (p + q) + (p + q + 1)

def e3Val (g m S : ℕ) (act : ℕ → ℕ) (i : ℕ) : ℕ :=
  if pp g i = 0 then S * (2 * (i / g) + 1) + q
  else if act ((psec g m i + 1) * m + pj g m i) = 0
    then S * (psec g m i + 1) + (p + 2 * q) + pj g m i * (p + q) + (p + q - 1)
    else S * (psec g m i + 1) + (p + 2 * q) + pj g m i * (p + q) + (p + q)

def e4Val (g m S : ℕ) (i : ℕ) : ℕ :=
  if pp g i = 0 then S * (2 * (i / g) + 1) + (p + 2 * q)
  else S * (psec g m i + 1) + (p + 2 * q) + pj g m i * (p + q) + (p + q + 1)

def headP : Com :=
  .seq (.assign "v" (div (V "i") (V "g"))) (.assign "pos" (sub (V "i") (mul (V "v") (V "g"))))

def litPart : Com :=
  .seq (.assign "e1" (add (mul (V "S") (mul (.lit 2) (V "v"))) (.lit (p + q + 1))))
  (.seq (.assign "e2" (add (mul (V "S") (mul (.lit 2) (V "v"))) (.lit (p + 2 * q))))
  (.seq (.assign "e3" (add (mul (V "S") (add (mul (.lit 2) (V "v")) (.lit 1))) (.lit q)))
    (.assign "e4" (add (mul (V "S") (add (mul (.lit 2) (V "v")) (.lit 1))) (.lit (p + 2 * q))))))

def clA : Com :=
  .seq (.assign "x" (sub (V "pos") (.lit 1)))
  (.seq (.assign "h" (div (V "x") (V "m")))
  (.seq (.assign "j" (sub (V "x") (mul (V "h") (V "m"))))
    (.assign "sec" (add (mul (.lit 2) (V "v")) (V "h")))))

def clB : Com :=
  .seq (.assign "cs1" (add (add (mul (V "S") (V "sec")) (.lit (p + 2 * q)))
      (mul (V "j") (.lit (p + q)))))
  (.seq (.assign "cs2" (add (add (mul (V "S") (add (V "sec") (.lit 1))) (.lit (p + 2 * q)))
      (mul (V "j") (.lit (p + q)))))
  (.seq (.assign "e2" (add (V "cs1") (.lit (p + q + 1))))
    (.assign "e4" (add (V "cs2") (.lit (p + q + 1))))))

def clC : Com :=
  .seq (.ite (.eq (.get "act" (add (mul (V "sec") (V "m")) (V "j"))) (.lit 0))
      (.assign "e1" (add (V "cs1") (.lit (p + q - 1))))
      (.assign "e1" (add (V "cs1") (.lit (p + q)))))
    (.ite (.eq (.get "act" (add (mul (add (V "sec") (.lit 1)) (V "m")) (V "j"))) (.lit 0))
      (.assign "e3" (add (V "cs2") (.lit (p + q - 1))))
      (.assign "e3" (add (V "cs2") (.lit (p + q)))))

def calcP : Com :=
  .seq headP (.ite (.eq (V "pos") (.lit 0)) (litPart p q) (.seq clA (.seq (clB p q) (clC p q))))

variable {B : ℕ} (g m S Lact : ℕ) (act : ℕ → ℕ) (i0 : ℕ)

/-- The constants and the table. -/
structure PC (σ : Env) : Prop where
  hS : σ.vars "S" = S
  hm : σ.vars "m" = m
  hg : σ.vars "g" = g
  hi : σ.vars "i" = i0
  hact : ∀ t, (σ.arrs "act").getD t 0 = act t
  hlen : Lact ≤ (σ.arrs "act").length

/-- What is known of the numbers involved. -/
structure PB : Prop where
  hactB : ∀ t, act t < B
  hSB : S < B
  hmB : m < B
  hgB : g < B
  hiB : i0 < B
  hvB : 2 * (i0 / g) + 4 < B
  hb1 : S * (2 * (i0 / g) + 1) + (p + 2 * q) + (p + q) + 8 < B
  hb2 : S * (psec g m i0 + 1) + (p + 2 * q) + pj g m i0 * (p + q) + (p + q) + 8 < B
  hb3 : (psec g m i0 + 1) * m + pj g m i0 < B
  hb4 : pp g i0 ≠ 0 → (psec g m i0 + 1) * m + pj g m i0 < Lact

def P1 (σ : Env) : Prop :=
  PC g m S Lact act i0 σ ∧ σ.vars "v" = i0 / g ∧ σ.vars "pos" = pp g i0

def P2 (σ : Env) : Prop :=
  P1 g m S Lact act i0 σ ∧ σ.vars "j" = pj g m i0 ∧ σ.vars "sec" = psec g m i0

def P3 (σ : Env) : Prop :=
  P2 g m S Lact act i0 σ ∧
    σ.vars "cs1" = S * psec g m i0 + (p + 2 * q) + pj g m i0 * (p + q) ∧
    σ.vars "cs2" = S * (psec g m i0 + 1) + (p + 2 * q) + pj g m i0 * (p + q) ∧
    σ.vars "e2" = e2Val p q g m S i0 ∧ σ.vars "e4" = e4Val p q g m S i0

def QP (σ : Env) : Prop :=
  σ.vars "e1" = e1Val p q g m S act i0 ∧ σ.vars "e2" = e2Val p q g m S i0 ∧
    σ.vars "e3" = e3Val p q g m S act i0 ∧ σ.vars "e4" = e4Val p q g m S i0

lemma pc_set {g' m' S' L' : ℕ} {act' : ℕ → ℕ} {i' : ℕ} {σ : Env}
    (h : PC g' m' S' L' act' i' σ) (x : String) (v : ℕ)
    (h1 : x ≠ "S") (h2 : x ≠ "m") (h3 : x ≠ "g") (h4 : x ≠ "i") :
    PC g' m' S' L' act' i' (σ.setVar x v) :=
  ⟨by simpa [Env.setVar, Ne.symm h1] using h.hS, by simpa [Env.setVar, Ne.symm h2] using h.hm,
   by simpa [Env.setVar, Ne.symm h3] using h.hg, by simpa [Env.setVar, Ne.symm h4] using h.hi,
   h.hact, h.hlen⟩

theorem headP_spec (hb : PB (B := B) p q g m S Lact act i0) :
    Spec B (PC g m S Lact act i0) headP
      (fun _ σ' => P1 g m S Lact act i0 σ') 20 := by
  have f2 : i0 / g * g ≤ i0 := Nat.div_mul_le_self _ _
  have f1 : i0 / g ≤ i0 := Nat.div_le_self _ _
  have hiB := hb.hiB
  have hgB := hb.hgB
  refine Spec.pre (P := fun σ => PC g m S Lact act i0 σ ∧
      σ.vars "i" = i0 ∧ σ.vars "g" = g) ?_ (fun σ h => ⟨h, h.hi, h.hg⟩)
  run_vcg
  all_goals have hi := ‹σ.vars "i" = i0›
  all_goals have hg := ‹σ.vars "g" = g›
  · refine ⟨pc_set (pc_set ‹PC g m S Lact act i0 σ› _ _ (by decide) (by decide) (by decide)
      (by decide)) _ _ (by decide) (by decide) (by decide) (by decide), ?_, ?_⟩ <;>
      simp [Env.setVar, hi, hg, pp]
  all_goals simp [Env.setVar, hi, hg]
  all_goals omega

theorem litPart_spec (hb : PB (B := B) p q g m S Lact act i0) (hpp : pp g i0 = 0) :
    Spec B (P1 g m S Lact act i0) (litPart p q) (fun _ σ' => QP p q g m S act i0 σ') 60 := by
  have hb1 := hb.hb1
  have hv := hb.hvB
  have hSB := hb.hSB
  have f3 : S * (2 * (i0 / g)) ≤ S * (2 * (i0 / g) + 1) := Nat.mul_le_mul_left _ (by omega)
  refine Spec.pre (P := fun σ => σ.vars "S" = S ∧ σ.vars "v" = i0 / g) ?_
    (fun σ h => ⟨h.1.hS, h.2.1⟩)
  run_vcg
  all_goals have hS := ‹σ.vars "S" = S›
  all_goals have hvv := ‹σ.vars "v" = i0 / g›
  · simp [QP, e1Val, e2Val, e3Val, e4Val, hpp, Env.setVar, hS, hvv]
  all_goals simp [Env.setVar, hS, hvv]
  all_goals omega

theorem clA_spec (hb : PB (B := B) p q g m S Lact act i0) :
    Spec B (P1 g m S Lact act i0) clA (fun _ σ' => P2 g m S Lact act i0 σ') 60 := by
  have hv := hb.hvB
  have hmB := hb.hmB
  have hiB := hb.hiB
  have hb3 := hb.hb3
  have f0 : pp g i0 ≤ i0 := Nat.sub_le _ _
  have f4 : (pp g i0 - 1) / m ≤ pp g i0 - 1 := Nat.div_le_self _ _
  have f5 : (pp g i0 - 1) / m * m ≤ pp g i0 - 1 := Nat.div_mul_le_self _ _
  have f6 : (pp g i0 - 1) / m ≤ psec g m i0 := by unfold psec; omega
  have f7 : psec g m i0 ≤ (psec g m i0 + 1) * m + pj g m i0 ∨ m = 0 := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exact Or.inr h
    · left
      have := Nat.le_mul_of_pos_right (psec g m i0 + 1) h
      omega
  have f8 : m = 0 → (pp g i0 - 1) / m = 0 := fun h => by rw [h, Nat.div_zero]
  have hps : psec g m i0 = 2 * (i0 / g) + (pp g i0 - 1) / m := rfl
  refine Spec.pre (P := fun σ => P1 g m S Lact act i0 σ ∧ σ.vars "m" = m ∧
      σ.vars "v" = i0 / g ∧ σ.vars "pos" = pp g i0) ?_ (fun σ h => ⟨h, h.1.hm, h.2.1, h.2.2⟩)
  run_vcg
  all_goals have hm := ‹σ.vars "m" = m›
  all_goals have hvv := ‹σ.vars "v" = i0 / g›
  all_goals have hpos := ‹σ.vars "pos" = pp g i0›
  · obtain ⟨hpc, h1, h2⟩ := ‹P1 g m S Lact act i0 σ›
    refine ⟨⟨pc_set (pc_set (pc_set (pc_set hpc _ _ (by decide) (by decide) (by decide)
      (by decide)) _ _ (by decide) (by decide) (by decide) (by decide)) _ _ (by decide)
      (by decide) (by decide) (by decide)) _ _ (by decide) (by decide) (by decide) (by decide),
      ?_, ?_⟩, ?_, ?_⟩ <;> simp [Env.setVar, hm, hvv, hpos, pj, psec]
  all_goals simp [Env.setVar, hm, hvv, hpos]
  all_goals omega

theorem clB_spec (hb : PB (B := B) p q g m S Lact act i0) (hpp : pp g i0 ≠ 0) :
    Spec B (P2 g m S Lact act i0) (clB p q) (fun _ σ' => P3 p q g m S Lact act i0 σ') 80 := by
  have hb2 := hb.hb2
  have hSB := hb.hSB
  have f6 : S * psec g m i0 ≤ S * (psec g m i0 + 1) := Nat.mul_le_mul_left _ (by omega)
  have f9 : psec g m i0 + 1 ≤ S * (psec g m i0 + 1) ∨ S = 0 := by
    rcases Nat.eq_zero_or_pos S with h | h
    · exact Or.inr h
    · exact Or.inl (Nat.le_mul_of_pos_left _ h)
  have hv := hb.hvB
  have hb3 := hb.hb3
  have f7 : psec g m i0 ≤ (psec g m i0 + 1) * m + pj g m i0 ∨ m = 0 := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exact Or.inr h
    · left
      have := Nat.le_mul_of_pos_right (psec g m i0 + 1) h
      omega
  have f8 : m = 0 → psec g m i0 = 2 * (i0 / g) := fun h => by
    unfold psec; rw [h, Nat.div_zero]; rfl
  have f12 : psec g m i0 + 1 ≤ (psec g m i0 + 1) * m + pj g m i0 ∨ m = 0 := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exact Or.inr h
    · exact Or.inl (le_trans (Nat.le_mul_of_pos_right _ h) (Nat.le_add_right _ _))
  have f10 : pj g m i0 ≤ pp g i0 - 1 := Nat.sub_le _ _
  have f11 : pp g i0 ≤ i0 := Nat.sub_le _ _
  have hiB := hb.hiB
  refine Spec.pre (P := fun σ => P2 g m S Lact act i0 σ ∧ σ.vars "S" = S ∧
      σ.vars "j" = pj g m i0 ∧ σ.vars "sec" = psec g m i0) ?_
    (fun σ h => ⟨h, h.1.1.hS, h.2.1, h.2.2⟩)
  run_vcg
  all_goals have hS := ‹σ.vars "S" = S›
  all_goals have hj := ‹σ.vars "j" = pj g m i0›
  all_goals have hsec := ‹σ.vars "sec" = psec g m i0›
  · obtain ⟨⟨hpc, h1, h2⟩, h3, h4⟩ := ‹P2 g m S Lact act i0 σ›
    refine ⟨⟨⟨pc_set (pc_set (pc_set (pc_set hpc _ _ (by decide) (by decide) (by decide)
      (by decide)) _ _ (by decide) (by decide) (by decide) (by decide)) _ _ (by decide)
      (by decide) (by decide) (by decide)) _ _ (by decide) (by decide) (by decide) (by decide),
      ?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
      simp [Env.setVar, hS, hj, hsec, h1, h2, e2Val, e4Val, hpp]
  all_goals simp [Env.setVar, hS, hj, hsec]
  all_goals omega

theorem clC_spec (hb : PB (B := B) p q g m S Lact act i0) (hpp : pp g i0 ≠ 0) :
    Spec B (P3 p q g m S Lact act i0) (clC p q) (fun _ σ' => QP p q g m S act i0 σ') 80 := by
  have hb2 := hb.hb2
  have hb3 := hb.hb3
  have hb4 := hb.hb4 hpp
  have f7 : psec g m i0 * m ≤ (psec g m i0 + 1) * m := Nat.mul_le_mul_right _ (by omega)
  have f6 : S * psec g m i0 ≤ S * (psec g m i0 + 1) := Nat.mul_le_mul_left _ (by omega)
  have hmB := hb.hmB
  have f12 : psec g m i0 + 1 ≤ (psec g m i0 + 1) * m + pj g m i0 ∨ m = 0 := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exact Or.inr h
    · exact Or.inl (le_trans (Nat.le_mul_of_pos_right _ h) (Nat.le_add_right _ _))
  have f8 : m = 0 → psec g m i0 = 2 * (i0 / g) := fun h => by
    unfold psec; rw [h, Nat.div_zero]; rfl
  have hv := hb.hvB
  have f10 : pj g m i0 ≤ pp g i0 - 1 := Nat.sub_le _ _
  have f11 : pp g i0 ≤ i0 := Nat.sub_le _ _
  have hiB := hb.hiB
  refine Spec.pre (P := fun σ => P3 p q g m S Lact act i0 σ ∧ σ.vars "m" = m ∧
      σ.vars "j" = pj g m i0 ∧ σ.vars "sec" = psec g m i0 ∧
      σ.vars "cs1" = S * psec g m i0 + (p + 2 * q) + pj g m i0 * (p + q) ∧
      σ.vars "cs2" = S * (psec g m i0 + 1) + (p + 2 * q) + pj g m i0 * (p + q) ∧
      (∀ t, (σ.arrs "act").getD t 0 = act t) ∧ Lact ≤ (σ.arrs "act").length) ?_
    (fun σ h => ⟨h, h.1.1.1.hm, h.1.2.1, h.1.2.2, h.2.1, h.2.2.1, h.1.1.1.hact, h.1.1.1.hlen⟩)
  run_vcg
  all_goals have hm := ‹σ.vars "m" = m›
  all_goals have hj := ‹σ.vars "j" = pj g m i0›
  all_goals have hsec := ‹σ.vars "sec" = psec g m i0›
  all_goals have hc1 := ‹σ.vars "cs1" = _›
  all_goals have hc2 := ‹σ.vars "cs2" = _›
  all_goals have hact := ‹∀ t, (σ.arrs "act").getD t 0 = act t›
  all_goals have hlen := ‹Lact ≤ (σ.arrs "act").length›
  all_goals have hactB := hb.hactB
  all_goals try simp [Env.setVar] at *
  all_goals try simp only [hm, hj, hsec, hc1, hc2] at *
  all_goals try omega
  all_goals try (simpa [hact] using hactB _)
  all_goals (
    obtain ⟨-, -, -, he2, he4⟩ := ‹P3 p q g m S Lact act i0 σ›
    simp_all [QP, e1Val, e3Val])

/-- The clause-pair branch, assembled. -/
theorem clPart_spec (hb : PB (B := B) p q g m S Lact act i0) (hpp : pp g i0 ≠ 0) :
    Spec B (P1 g m S Lact act i0) (.seq clA (.seq (clB p q) (clC p q)))
      (fun _ σ' => QP p q g m S act i0 σ') 220 :=
  (clA_spec p q g m S Lact act i0 hb).seq
    ((clB_spec p q g m S Lact act i0 hb hpp).seq (clC_spec p q g m S Lact act i0 hb hpp)
      (fun _ _ _ h => h) (fun _ _ _ _ _ h => h))
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)

/-- **The four deadlines of pair `i0`.** -/
theorem calcP_fixed (hb : PB (B := B) p q g m S Lact act i0) :
    Spec B (PC g m S Lact act i0) (calcP p q) (fun _ σ' => QP p q g m S act i0 σ') 250 := by
  have hev : ∀ σ, P1 g m S Lact act i0 σ →
      (Cond.eq (V "pos") (.lit 0)).evalB B σ = some (σ.vars "pos" == 0) := fun σ h =>
    evalB_condEq (evalB_var (by
      rw [h.2.2]; have : pp g i0 ≤ i0 := Nat.sub_le _ _; have := hb.hiB; omega))
      (evalB_lit (by have := hb.hiB; omega))
  refine ((headP_spec p q g m S Lact act i0 hb).seq
    ((Spec.ite (K := 220) (Q := fun _ σ' => QP p q g m S act i0 σ')
      (fun σ h => ⟨_, hev σ h⟩) ?_ ?_)) (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)).mono
      (by simp [Cond.size, Expr.size])
  · by_cases hpp : pp g i0 = 0
    · exact ((litPart_spec p q g m S Lact act i0 hb hpp).pre (fun σ h => h.1)).mono (by omega)
    · intro σ ⟨h, hc⟩
      rw [hev σ h, h.2.2] at hc
      simp at hc
      exact absurd hc hpp
  · by_cases hpp : pp g i0 = 0
    · intro σ ⟨h, hc⟩
      rw [hev σ h, h.2.2] at hc
      simp at hc
      exact absurd hpp hc
    · exact (clPart_spec p q g m S Lact act i0 hb hpp).pre (fun σ h => h.1)

end Lax391470Proofs.L2Pair
