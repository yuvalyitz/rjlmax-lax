import Lax391470Proofs.SatOrdinaryData
import Mathlib.Data.Finset.Sort

/-!
The connected pairs of the typed construction, in the explicit order of the concept.
-/

namespace Lax391470Proofs.SatPairs

open Lax391470 Lax391470.SatConstruction Lax429075
open Lax391470Proofs.SatBridge Lax391470Proofs.RjLmax Lax391470Proofs.RjLmax.FromSat
open Lax391470Proofs.Sat Lax391470Proofs.SatOrdinary Lax391470Proofs.SatOrdinaryData

variable (p q : ℕ) (F : CNF.Formula)

lemma half (m x : ℕ) (hx : x < 2 * m) :
    (x < m → x / m = 0 ∧ x % m = x) ∧ (m ≤ x → x / m = 1 ∧ x % m = x - m) := by
  refine ⟨fun h => ⟨Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h⟩, fun h => ?_⟩
  have h1 : x / m = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  refine ⟨h1, ?_⟩
  have := Nat.div_add_mod x m
  rw [h1] at this
  omega

/-- Where a pair index sits: its group is a variable, and the last group is short. -/
lemma group_bounds (i : ℕ) (hi : i < SatConstruction.numPairs F) :
    groupOf F i < numVars F ∧
      (groupOf F i = numVars F - 1 → posOf F i ≤ numClauses F) := by
  obtain ⟨n', hn⟩ : ∃ n', numVars F = n' + 1 := ⟨numVars F - 1, by have := numVars_pos F; omega⟩
  unfold SatConstruction.numPairs at hi
  unfold groupOf posOf
  rw [hn] at hi ⊢
  generalize numClauses F = m at *
  have hdm := Nat.div_add_mod i (1 + 2 * m)
  have hr : i % (1 + 2 * m) < 1 + 2 * m := Nat.mod_lt _ (by omega)
  have hN : n' + 1 + (2 * (n' + 1) - 1) * m = (1 + 2 * m) * n' + m + 1 := by
    have : 2 * (n' + 1) - 1 = 2 * n' + 1 := by omega
    rw [this]; ring
  rw [hN] at hi
  generalize i / (1 + 2 * m) = v at *
  generalize i % (1 + 2 * m) = r at *
  constructor
  · by_contra hv
    have : (1 + 2 * m) * (n' + 1) ≤ (1 + 2 * m) * v := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_succ] at this
    omega
  · intro hv
    have hv' : v = n' := by omega
    subst hv'
    omega

lemma numClauses_pos_of_pos {i : ℕ} (h : posOf F i ≠ 0) : 0 < numClauses F := by
  unfold posOf at h
  by_contra hm
  have : numClauses F = 0 := by omega
  rw [this] at h
  omega

lemma pos_lt (i : ℕ) : posOf F i < 1 + 2 * numClauses F := Nat.mod_lt _ (by omega)

lemma pairSection_lt (i : ℕ) (hi : i < SatConstruction.numPairs F) (h : posOf F i ≠ 0) :
    pairSection F i < 2 * numVars F - 1 := by
  obtain ⟨h1, h2⟩ := group_bounds F i hi
  have hp := pos_lt F i
  have hm := numClauses_pos_of_pos F h
  obtain ⟨ha, hb⟩ := half (numClauses F) (posOf F i - 1) (by omega)
  unfold pairSection
  by_cases hc : posOf F i - 1 < numClauses F
  · rw [(ha hc).1]; omega
  · rw [(hb (by omega)).1]
    have : groupOf F i ≠ numVars F - 1 := fun he => by have := h2 he; omega
    omega

lemma pairClause_lt (i : ℕ) (h : posOf F i ≠ 0) : pairClause F i < numClauses F :=
  Nat.mod_lt _ (numClauses_pos_of_pos F h)

/-- The pair with a given index. -/
def pairOfIdx (i : Fin (FromSat.numPairs (toCnf F))) : Pair (toCnf F) :=
  if h : posOf F i = 0 then Sum.inl ⟨groupOf F i, (group_bounds F i i.isLt).1⟩
  else Sum.inr (⟨pairSection F i, pairSection_lt F i i.isLt h⟩, ⟨pairClause F i, pairClause_lt F i h⟩)

lemma key_pairOfIdx (i : Fin (FromSat.numPairs (toCnf F))) :
    key (toCnf F) (pairOfIdx F i) = (groupOf F i, posOf F i) := by
  unfold pairOfIdx
  split
  · next h => simp only [key, h]
  · next h =>
    have hp := pos_lt F i
    have hm := numClauses_pos_of_pos F h
    obtain ⟨ha, hb⟩ := half (numClauses F) (posOf F i - 1) (by omega)
    have hφ : (toCnf F).m = numClauses F := rfl
    simp only [key, pairSection, pairClause, hφ]
    by_cases hc : posOf F i - 1 < numClauses F
    · rw [(ha hc).1, (ha hc).2]
      have e1 : (2 * groupOf F i + 0) / 2 = groupOf F i := by omega
      have e2 : (2 * groupOf F i + 0) % 2 = 0 := by omega
      rw [e1, e2, if_pos rfl]
      congr 1; omega
    · rw [(hb (by omega)).1, (hb (by omega)).2]
      have e1 : (2 * groupOf F i + 1) / 2 = groupOf F i := by omega
      have e2 : ¬ (2 * groupOf F i + 1) % 2 = 0 := by omega
      rw [e1, if_neg e2]
      congr 1; omega

lemma divmod_lt (g a b : ℕ) (h : a < b) : a / g < b / g ∨ a / g = b / g ∧ a % g < b % g := by
  have h1 := Nat.div_add_mod a g
  have h2 := Nat.div_add_mod b g
  have hle : a / g ≤ b / g := Nat.div_le_div_right h.le
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq, ?_⟩
    rw [heq] at h1
    omega

lemma pairOfIdx_strictMono :
    @StrictMono _ _ _ (instLinearOrderPair (toCnf F)).toPartialOrder.toPreorder (pairOfIdx F) := by
  rintro ⟨i, hi⟩ ⟨i', hi'⟩ hii
  show toLex (key (toCnf F) (pairOfIdx F ⟨i, hi⟩)) <
    toLex (key (toCnf F) (pairOfIdx F ⟨i', hi'⟩))
  rw [key_pairOfIdx, key_pairOfIdx, Prod.Lex.lt_iff]
  exact divmod_lt _ i i' hii

/-- The order isomorphism of the typed construction is the explicit enumeration. -/
lemma pairEquiv_eq (i : Fin (FromSat.numPairs (toCnf F))) :
    pairEquiv (toCnf F) i = pairOfIdx F i := by
  let : Preorder (Pair (toCnf F)) := (instLinearOrderPair (toCnf F)).toPartialOrder.toPreorder
  have hc : (Finset.univ : Finset (Pair (toCnf F))).card = FromSat.numPairs (toCnf F) :=
    Finset.card_univ.trans (card_pair (toCnf F))
  have e1 := Finset.orderEmbOfFin_unique hc (f := pairOfIdx F) (fun _ => Finset.mem_univ _)
    (pairOfIdx_strictMono F)
  have e2 := Finset.orderEmbOfFin_unique hc (f := ⇑(pairEquiv (toCnf F)))
    (fun _ => Finset.mem_univ _) (fun a b h => (pairEquiv (toCnf F)).lt_iff_lt.mpr h)
  exact (congrFun e2 i).trans (congrFun e1 i).symm

end Lax391470Proofs.SatPairs
