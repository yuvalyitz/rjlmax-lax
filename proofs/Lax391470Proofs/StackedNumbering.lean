import Lax391470Proofs.StackedBridge

/-!
The stacked instance of the typed development, numbered as the concept numbers it.
-/

namespace Lax391470Proofs.StackedNumbering

open Lax391470 Lax391470.AuxiliaryProblem Lax391470Proofs.RjLmax Lax391470Proofs.Renumbering
open Lax391470Proofs.StackedBridge

variable {p q : ℕ} (A : AuxiliaryProblem.Instance)

/-- The five jobs of a pair, in the concept's order. -/
def partEquiv : Part ≃ Fin 5 where
  toFun
    | .sep => 0
    | .longIn => 1
    | .longOut => 2
    | .shortIn => 3
    | .shortOut => 4
  invFun i :=
    match i with
    | 0 => .sep
    | 1 => .longIn
    | 2 => .longOut
    | 3 => .shortIn
    | 4 => .shortOut
  left_inv := by intro x; cases x <;> rfl
  right_inv := by decide

/-- Ordinary jobs, then the five jobs of each pair in turn. -/
def stackEquiv : Fin A.ordinary ⊕ Fin A.pairs × Part ≃ Fin (A.ordinary + 5 * A.pairs) :=
  (Equiv.sumCongr (Equiv.refl _)
    ((Equiv.prodCongr (Equiv.refl _) partEquiv).trans finProdFinEquiv)).trans
    (finSumFinEquiv.trans (finCongr (by ring)))

@[simp] lemma stackEquiv_ord (o : Fin A.ordinary) :
    ((stackEquiv A (Sum.inl o) : Fin _) : ℕ) = o := by
  simp [stackEquiv]

@[simp] lemma stackEquiv_quad (i : Fin A.pairs) (part : Part) :
    ((stackEquiv A (Sum.inr (i, part)) : Fin _) : ℕ) =
      A.ordinary + 5 * i + (partEquiv part : ℕ) := by
  simp [stackEquiv]; ring

section read
variable {A} (p q) {j : Fin (StackedConstruction.inst p q A).jobs}

lemma r_of_ord (o : Fin A.ordinary) (h : (j : ℕ) = o) :
    (StackedConstruction.inst p q A).r j = A.r o := by
  have hlt : (j : ℕ) < A.ordinary := h ▸ o.isLt
  have e : (⟨j, hlt⟩ : Fin A.ordinary) = o := Fin.ext h
  simp only [StackedConstruction.inst, dif_pos hlt, e]

lemma d_of_ord (o : Fin A.ordinary) (h : (j : ℕ) = o) :
    (StackedConstruction.inst p q A).d j = A.d o := by
  have hlt : (j : ℕ) < A.ordinary := h ▸ o.isLt
  have e : (⟨j, hlt⟩ : Fin A.ordinary) = o := Fin.ext h
  simp only [StackedConstruction.inst, dif_pos hlt, e]

lemma p_of_ord (o : Fin A.ordinary) (h : (j : ℕ) = o) :
    (StackedConstruction.inst p q A).p j = if A.long o then p else q := by
  have hlt : (j : ℕ) < A.ordinary := h ▸ o.isLt
  have e : (⟨j, hlt⟩ : Fin A.ordinary) = o := Fin.ext h
  simp only [StackedConstruction.inst, dif_pos hlt, e]

lemma pairOf_eq (i : Fin A.pairs) (k : ℕ) (hk : k < 5) (h : (j : ℕ) = A.ordinary + 5 * i + k) :
    StackedConstruction.pairOf A j = i := by
  simp only [StackedConstruction.pairOf]; omega

lemma partOf_eq (i : Fin A.pairs) (k : ℕ) (hk : k < 5) (h : (j : ℕ) = A.ordinary + 5 * i + k) :
    StackedConstruction.partOf A j = k := by
  simp only [StackedConstruction.partOf]; omega

/-- The release time of part `k`, relative to the bin. -/
def relPart (p q k : ℕ) : ℤ :=
  match k with
  | 0 => ((p + q : ℕ) : ℤ)
  | 1 => (q : ℕ)
  | 2 => 0
  | 3 => (p : ℕ)
  | _ => 0

/-- The deadline of part `k` of pair `i`. -/
def duePart (p q : ℕ) (A : AuxiliaryProblem.Instance) (i : Fin A.pairs) (k : ℕ) : ℤ :=
  match k with
  | 0 => StackedConstruction.binStart p q i + ((p + 2 * q : ℕ) : ℤ)
  | 1 => (A.longEarly i : ℤ)
  | 2 => A.longDue i
  | 3 => A.shortEarly i
  | _ => A.shortDue i

/-- The length of part `k`. -/
def lenPart (p q k : ℕ) : ℕ :=
  match k with
  | 1 => p
  | 2 => p
  | _ => q

lemma r_of_quad (i : Fin A.pairs) (k : ℕ) (hk : k < 5) (h : (j : ℕ) = A.ordinary + 5 * i + k) :
    (StackedConstruction.inst p q A).r j = StackedConstruction.binStart p q i + relPart p q k := by
  have hlt : ¬ (j : ℕ) < A.ordinary := by omega
  simp only [StackedConstruction.inst, dif_neg hlt, pairOf_eq p q i k hk h,
    partOf_eq p q i k hk h, relPart]
  rcases k with _ | _ | _ | _ | _ | k
  all_goals first | rfl

lemma d_of_quad (i : Fin A.pairs) (k : ℕ) (hk : k < 5) (h : (j : ℕ) = A.ordinary + 5 * i + k) :
    (StackedConstruction.inst p q A).d j = duePart p q A i k := by
  have hlt : ¬ (j : ℕ) < A.ordinary := by omega
  simp only [StackedConstruction.inst, dif_neg hlt, pairOf_eq p q i k hk h,
    partOf_eq p q i k hk h, Fin.eta, duePart]
  rcases k with _ | _ | _ | _ | _ | k
  all_goals first | rfl

lemma p_of_quad (i : Fin A.pairs) (k : ℕ) (hk : k < 5) (h : (j : ℕ) = A.ordinary + 5 * i + k) :
    (StackedConstruction.inst p q A).p j = lenPart p q k := by
  have hlt : ¬ (j : ℕ) < A.ordinary := by omega
  simp only [StackedConstruction.inst, dif_neg hlt, partOf_eq p q i k hk h, lenPart]
  rcases k with _ | _ | _ | _ | _ | k
  all_goals first | rfl

end read

variable {A} (hq : 0 < q) (hqp : q < p) (hA : A.Ordered)

lemma quad_r (i : Fin A.pairs) (part : Part) :
    (StackedConstruction.inst p q A).r (stackEquiv A (Sum.inr (i, part))) =
      Stacked.quadRel (toTyped A hq hqp hA) (i, part) := by
  rw [r_of_quad p q i (partEquiv part) (partEquiv part).isLt (stackEquiv_quad A i part)]
  cases part <;>
    simp [relPart, partEquiv, Stacked.quadRel, Stacked.binStart, Stacked.width,
      StackedConstruction.binStart, toTyped] <;> ring

lemma quad_d (i : Fin A.pairs) (part : Part) :
    (StackedConstruction.inst p q A).d (stackEquiv A (Sum.inr (i, part))) =
      Stacked.quadDue (toTyped A hq hqp hA) (i, part) := by
  rw [d_of_quad p q i (partEquiv part) (partEquiv part).isLt (stackEquiv_quad A i part)]
  cases part <;>
    simp [duePart, partEquiv, Stacked.quadDue, Stacked.binStart, Stacked.width,
      StackedConstruction.binStart, toTyped]; ring

lemma quad_p (i : Fin A.pairs) (part : Part) :
    (StackedConstruction.inst p q A).p (stackEquiv A (Sum.inr (i, part))) =
      Stacked.quadLen (toTyped A hq hqp hA) p q (i, part) := by
  rw [p_of_quad p q i (partEquiv part) (partEquiv part).isLt (stackEquiv_quad A i part)]
  cases part <;> simp [lenPart, partEquiv, Stacked.quadLen]

/-- The stacked instance of the typed view, numbered. -/
def stackNumbering :
    Numbering (Stacked.inst (toTyped A hq hqp hA)) (StackedConstruction.inst p q A) where
  e := stackEquiv A
  r_eq := by
    rintro (o | ⟨i, part⟩)
    · exact r_of_ord p q o (stackEquiv_ord A o)
    · exact quad_r hq hqp hA i part
  d_eq := by
    rintro (o | ⟨i, part⟩)
    · exact d_of_ord p q o (stackEquiv_ord A o)
    · exact quad_d hq hqp hA i part
  p_eq := by
    rintro (o | ⟨i, part⟩)
    · exact p_of_ord p q o (stackEquiv_ord A o)
    · exact quad_p hq hqp hA i part

/--
---
conclusion: Lax391470.StackedConstruction.correct
---
The numbered auxiliary instance and its stacked instance are renumberings of the typed
ones, for which the exchange argument of the source is carried out.
-/
theorem correct (p q : ℕ) (A : AuxiliaryProblem.Instance) (hq : 0 < q) (hqp : q < p)
    (hA : A.Ordered) : A.Solvable p q ↔ (StackedConstruction.inst p q A).Schedulable :=
  (solvable_iff hq hqp hA).trans
    ((Stacked.correct (toTyped A hq hqp hA)).trans
      (schedulable_iff (stackNumbering hq hqp hA)))

/--
---
conclusion: Lax391470.StackedConstruction.lengthsIn
---
-/
theorem lengthsIn (p q : ℕ) (A : AuxiliaryProblem.Instance) :
    (StackedConstruction.inst p q A).LengthsIn p q := by
  intro j
  simp only [StackedConstruction.inst]
  split
  · split <;> simp
  · split <;> simp

/--
---
conclusion: Lax391470.StackedConstruction.times_le
---
-/
theorem times_le (p q : ℕ) (A : AuxiliaryProblem.Instance) (hA : A.Ordered) (T : ℕ)
    (hT : (∀ o, A.r o ≤ T ∧ A.d o ≤ T) ∧
      (∀ i, A.longDue i ≤ T ∧ A.shortDue i ≤ T)) :
    ∀ j, |(StackedConstruction.inst p q A).r j| ≤ ((T + (p + 2 * q) * A.pairs : ℕ) : ℤ) ∧
      |(StackedConstruction.inst p q A).d j| ≤ ((T + (p + 2 * q) * A.pairs : ℕ) : ℤ) := by
  intro j
  have hle : ∀ i : Fin A.pairs, A.longEarly i ≤ T ∧ A.longDue i ≤ T ∧
      A.shortEarly i ≤ T ∧ A.shortDue i ≤ T := fun i =>
    ⟨(hA.longEarly_le i).trans (hT.2 i).1, (hT.2 i).1,
      (hA.shortEarly_le i).trans (hT.2 i).2, (hT.2 i).2⟩
  simp only [StackedConstruction.inst]
  split
  · rename_i h
    have := hT.1 ⟨j, h⟩
    have g0 : (0 : ℤ) ≤ (p + 2 * q) * A.pairs := by positivity
    constructor <;> rw [abs_of_nonneg (by positivity)] <;> push_cast <;> omega
  · rename_i h
    have hi : StackedConstruction.pairOf A j < A.pairs := by
      have := j.isLt
      simp only [StackedConstruction.pairOf, StackedConstruction.numJobs] at *
      omega
    have hb : (p + 2 * q) * (StackedConstruction.pairOf A j + 1) ≤
        (p + 2 * q) * A.pairs := Nat.mul_le_mul_left _ hi
    have e := hle ⟨StackedConstruction.pairOf A j, hi⟩
    simp only [StackedConstruction.binStart]
    generalize StackedConstruction.partOf A j = m
    push_cast at hb ⊢
    rcases m with _ | _ | _ | _ | _ | m <;> simp only [] <;>
      constructor <;> rw [abs_le] <;> constructor <;> nlinarith

end Lax391470Proofs.StackedNumbering
