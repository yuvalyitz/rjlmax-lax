import Lax391470.StackedConstruction
import Lax391470Proofs.TypedStacked
import Lax391470Proofs.Renumbering
import Mathlib.Logic.Equiv.Fin.Basic

/-!
The numbered instance of the auxiliary problem read as the structurally named one of the
typed development, and the two numberings that connect them: of the underlying
scheduling instance, and of the stacked instance.
-/

namespace Lax391470Proofs.StackedBridge

open Lax391470 Lax391470.AuxiliaryProblem Lax391470Proofs.RjLmax Lax391470Proofs.Renumbering

variable {p q : ℕ}

/-- The numbered instance `A` as an instance of the typed development. -/
def toTyped (A : AuxiliaryProblem.Instance) (hq : 0 < q) (hqp : q < p) (hA : A.Ordered) :
    RjLmax.Aux p q where
  Ord := Fin A.ordinary
  ordFintype := inferInstance
  ordDecEq := inferInstance
  r o := A.r o
  d o := A.d o
  len o := if A.long o then p else q
  r_nonneg _ := Int.natCast_nonneg _
  len_eq o := by cases A.long o <;> simp
  q_pos := hq
  q_lt_p := hqp
  N := A.pairs
  dp' i := A.longEarly i
  dp i := A.longDue i
  dq' i := A.shortEarly i
  dq i := A.shortDue i
  dp'_le_dp i := by exact_mod_cast hA.longEarly_le i
  dp_le_dp'_succ i j h := by exact_mod_cast hA.longDue_le i j h
  dq'_le_dq i := by exact_mod_cast hA.shortEarly_le i
  dq_le_dq'_succ i j h := by exact_mod_cast hA.shortDue_le i j h
  dp_le_dq' i := by exact_mod_cast hA.longDue_le_shortEarly i
  dp'_nonneg _ := Int.natCast_nonneg _
  dq'_nonneg _ := Int.natCast_nonneg _

variable (A : AuxiliaryProblem.Instance)

/-! ## The underlying instance -/

/-- Ordinary jobs, then long pending jobs, then short pending jobs. -/
def auxEquiv : Fin A.ordinary ⊕ Fin A.pairs ⊕ Fin A.pairs ≃
    Fin (A.ordinary + A.pairs + A.pairs) :=
  (Equiv.sumAssoc _ _ _).symm.trans
    ((Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv)

@[simp] lemma auxEquiv_ord (o : Fin A.ordinary) :
    ((auxEquiv A (Sum.inl o) : Fin _) : ℕ) = o := by
  simp [auxEquiv]

@[simp] lemma auxEquiv_long (i : Fin A.pairs) :
    ((auxEquiv A (Sum.inr (Sum.inl i)) : Fin _) : ℕ) = A.ordinary + i := by
  simp [auxEquiv]

@[simp] lemma auxEquiv_short (i : Fin A.pairs) :
    ((auxEquiv A (Sum.inr (Sum.inr i)) : Fin _) : ℕ) = A.ordinary + A.pairs + i := by
  simp [auxEquiv]

/-! The data of the underlying instance, read at a job whose number is known. -/

section read
variable {A} (p q) {j : Fin (A.toInstance p q).jobs}

lemma r_of_ord (o : Fin A.ordinary) (h : (j : ℕ) = o) : (A.toInstance p q).r j = A.r o := by
  have hlt : (j : ℕ) < A.ordinary := h ▸ o.isLt
  have e : (⟨j, hlt⟩ : Fin A.ordinary) = o := Fin.ext h
  simp only [Instance.toInstance, dif_pos hlt, e]

lemma r_of_pending (h : A.ordinary ≤ (j : ℕ)) : (A.toInstance p q).r j = 0 := by
  have hlt : ¬ (j : ℕ) < A.ordinary := by omega
  simp only [Instance.toInstance, dif_neg hlt]

lemma d_of_ord (o : Fin A.ordinary) (h : (j : ℕ) = o) : (A.toInstance p q).d j = A.d o := by
  have hlt : (j : ℕ) < A.ordinary := h ▸ o.isLt
  have e : (⟨j, hlt⟩ : Fin A.ordinary) = o := Fin.ext h
  simp only [Instance.toInstance, dif_pos hlt, e]

lemma d_of_long (i : Fin A.pairs) (h : (j : ℕ) = A.ordinary + i) :
    (A.toInstance p q).d j = A.longDue i := by
  have h1 : ¬ (j : ℕ) < A.ordinary := by omega
  have h2 : (j : ℕ) < A.ordinary + A.pairs := by have := i.isLt; omega
  have e : (⟨(j : ℕ) - A.ordinary, by omega⟩ : Fin A.pairs) = i :=
    Fin.ext (by show (j : ℕ) - A.ordinary = i; omega)
  simp only [Instance.toInstance, dif_neg h1, dif_pos h2, e]

lemma d_of_short (i : Fin A.pairs) (h : (j : ℕ) = A.ordinary + A.pairs + i) :
    (A.toInstance p q).d j = A.shortDue i := by
  have h1 : ¬ (j : ℕ) < A.ordinary := by omega
  have h2 : ¬ (j : ℕ) < A.ordinary + A.pairs := by omega
  have e : (⟨(j : ℕ) - A.ordinary - A.pairs, by have := i.isLt; omega⟩ : Fin A.pairs) = i :=
    Fin.ext (by show (j : ℕ) - A.ordinary - A.pairs = i; omega)
  simp only [Instance.toInstance, dif_neg h1, dif_neg h2, e]

lemma p_of_ord (o : Fin A.ordinary) (h : (j : ℕ) = o) :
    (A.toInstance p q).p j = if A.long o then p else q := by
  have hlt : (j : ℕ) < A.ordinary := h ▸ o.isLt
  have e : (⟨j, hlt⟩ : Fin A.ordinary) = o := Fin.ext h
  simp only [Instance.toInstance, dif_pos hlt, e]

lemma p_of_long (i : Fin A.pairs) (h : (j : ℕ) = A.ordinary + i) :
    (A.toInstance p q).p j = p := by
  have h1 : ¬ (j : ℕ) < A.ordinary := by omega
  have h2 : (j : ℕ) < A.ordinary + A.pairs := by have := i.isLt; omega
  simp only [Instance.toInstance, dif_neg h1, if_pos h2]

lemma p_of_short (i : Fin A.pairs) (h : (j : ℕ) = A.ordinary + A.pairs + i) :
    (A.toInstance p q).p j = q := by
  have h1 : ¬ (j : ℕ) < A.ordinary := by omega
  have h2 : ¬ (j : ℕ) < A.ordinary + A.pairs := by omega
  simp only [Instance.toInstance, dif_neg h1, if_neg h2]

end read

variable {A} (hq : 0 < q) (hqp : q < p) (hA : A.Ordered)

/-- The underlying scheduling instance of the typed view, numbered. -/
def auxNumbering : Numbering (toTyped A hq hqp hA).toInstance (A.toInstance p q) where
  e := auxEquiv A
  r_eq := by
    rintro (o | i | i)
    · exact r_of_ord p q o (auxEquiv_ord A o)
    · exact r_of_pending p q (le_of_le_of_eq (Nat.le_add_right _ _) (auxEquiv_long A i).symm)
    · exact r_of_pending p q (le_of_le_of_eq (by omega) (auxEquiv_short A i).symm)
  d_eq := by
    rintro (o | i | i)
    · exact d_of_ord p q o (auxEquiv_ord A o)
    · exact d_of_long p q i (auxEquiv_long A i)
    · exact d_of_short p q i (auxEquiv_short A i)
  p_eq := by
    rintro (o | i | i)
    · exact p_of_ord p q o (auxEquiv_ord A o)
    · exact p_of_long p q i (auxEquiv_long A i)
    · exact p_of_short p q i (auxEquiv_short A i)

lemma auxEquiv_longJob (i : Fin A.pairs) :
    auxEquiv A (Sum.inr (Sum.inl i)) = A.longJob p q i := Fin.ext (by simp [Instance.longJob])

lemma auxEquiv_shortJob (i : Fin A.pairs) :
    auxEquiv A (Sum.inr (Sum.inr i)) = A.shortJob p q i := Fin.ext (by simp [Instance.shortJob])

/-- **The numbered and the typed auxiliary problem agree.** -/
theorem solvable_iff : A.Solvable p q ↔ (toTyped A hq hqp hA).Yes := by
  constructor
  · rintro ⟨t, hfeas, hpair⟩
    refine ⟨fun x => t (auxEquiv A x), feasible_comp (auxNumbering hq hqp hA) hfeas,
      fun (i : Fin A.pairs) => ?_⟩
    have e1 := auxEquiv_longJob (p := p) (q := q) i
    have e2 := auxEquiv_shortJob (p := p) (q := q) i
    rcases hpair i with h | h
    · left
      show t (auxEquiv A (Sum.inr (Sum.inl i))) + (p : ℤ) ≤ (A.longEarly i : ℤ)
      rw [e1]; exact h
    · right
      show t (auxEquiv A (Sum.inr (Sum.inr i))) + (q : ℤ) ≤ (A.shortEarly i : ℤ)
      rw [e2]; exact h
  · rintro ⟨u, hfeas, hpair⟩
    refine ⟨fun j => u ((auxEquiv A).symm j),
      feasible_comp_symm (auxNumbering hq hqp hA) hfeas, fun (i : Fin A.pairs) => ?_⟩
    have e1 := auxEquiv_longJob (p := p) (q := q) i
    have e2 := auxEquiv_shortJob (p := p) (q := q) i
    rcases hpair i with h | h
    · left
      show u ((auxEquiv A).symm (A.longJob p q i)) + (p : ℤ) ≤ (A.longEarly i : ℤ)
      rw [← e1, Equiv.symm_apply_apply]; exact h
    · right
      show u ((auxEquiv A).symm (A.shortJob p q i)) + (q : ℤ) ≤ (A.shortEarly i : ℤ)
      rw [← e2, Equiv.symm_apply_apply]; exact h

end Lax391470Proofs.StackedBridge
