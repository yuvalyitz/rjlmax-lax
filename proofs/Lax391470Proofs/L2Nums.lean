import Lax391470Proofs.L2Accept
import Lax391470Proofs.L2PairSem

/-!
The numeric side conditions of the accepting branch hold under a quadratic bound.
-/

namespace Lax391470Proofs.L2Nums

open Lax429075.CNF Lax391470.SatConstruction
open Lax391470Proofs.L2ScanModel Lax391470Proofs.L2Active Lax391470Proofs.L2Dims
open Lax391470Proofs.L2Accept Lax391470Proofs.L2Pair

variable (p q : ℕ) (F : Formula) (W M : ℕ)

/-- The value bound, for an input of length `W - 4` with entries at most `M`. -/
def bnd : ℕ := 16 * ((p + q + 1) * (W * W)) + 64 + M

/-- The dimensions of the formula are bounded by the length of its encoding. -/
inductive Dim : Prop where
  | mk
    (hnn : numVars F + 3 ≤ W)
    (hm : F.length + 4 ≤ W)
    (hK : (lits F).length + 4 ≤ W)
/-- The arithmetic facts everything else is linear in. -/
inductive Prods : Prop where
  | mk
    (hX : W ≤ W * W)
    (h4X : 4 * W ≤ W * W)
    (hXU : W * W ≤ (p + q + 1) * (W * W))
    (hcU : p + q + 1 ≤ (p + q + 1) * (W * W))
    (hmpq : F.length * (p + q) ≤ (p + q + 1) * (W * W))
    (hS : sectionLength p q F ≤ (p + q + 1) * (W * W))
    (hSnn : sectionLength p q F * (2 * numVars F) ≤ 2 * ((p + q + 1) * (W * W)))
    (hnm : 2 * numVars F * F.length ≤ 2 * (W * W))
    (hnm2 : (2 * numVars F - 1) * F.length + F.length = 2 * numVars F * F.length)

variable {p q : ℕ} {F : Formula} {W : ℕ} in
theorem Prods.hnm
    
    (h : Prods p q F W) : 2 * numVars F * F.length ≤ 2 * (W * W) :=
  match h with | ⟨_, _, _, _, _, _, _, x, _⟩ => x

theorem prods (hd : Dim F W) : Prods p q F W := by
  obtain ⟨hnn, hm, hK⟩ := hd
  have hW : 4 ≤ W := by omega
  have hn1 : 1 ≤ numVars F := mxOf_pos _
  have hX : W ≤ W * W := Nat.le_mul_of_pos_left _ (by omega)
  have h4X : 4 * W ≤ W * W := Nat.mul_le_mul_right _ hW
  have hXU : W * W ≤ (p + q + 1) * (W * W) := Nat.le_mul_of_pos_left _ (by omega)
  have hcU : p + q + 1 ≤ (p + q + 1) * (W * W) := Nat.le_mul_of_pos_right _ (by
    have : 0 < W := by omega
    positivity)
  have hcW : (p + q + 1) * W ≤ (p + q + 1) * (W * W) := Nat.mul_le_mul_left _ hX
  have h1 : F.length * (p + q) ≤ F.length * (p + q + 1) := Nat.mul_le_mul_left _ (by omega)
  have h2 : (F.length + 3) * (p + q + 1) ≤ W * (p + q + 1) := Nat.mul_le_mul_right _ (by omega)
  have h3 : (F.length + 3) * (p + q + 1) = F.length * (p + q + 1) + 3 * (p + q + 1) := by ring
  have h4 : W * (p + q + 1) = (p + q + 1) * W := Nat.mul_comm _ _
  have hS' : sectionLength p q F ≤ (p + q + 1) * W := by
    unfold sectionLength numClauses; omega
  have hSnn : sectionLength p q F * (2 * numVars F) ≤ (p + q + 1) * W * (2 * W) :=
    Nat.mul_le_mul hS' (by omega)
  have h5 : (p + q + 1) * W * (2 * W) = 2 * ((p + q + 1) * (W * W)) := by ring
  have hnm : 2 * numVars F * F.length ≤ 2 * W * W := Nat.mul_le_mul (by omega) (by omega)
  have h6 : 2 * W * W = 2 * (W * W) := by ring
  refine ⟨hX, h4X, hXU, hcU, by omega, by omega, by omega, by omega, ?_⟩
  have : 2 * numVars F = (2 * numVars F - 1) + 1 := by omega
  rw [this, Nat.add_mul, Nat.one_mul]; simp

/-- Where pair `i0` sits. -/
lemma pair_pos (i0 : ℕ) (hi : i0 < Lax391470.SatConstruction.numPairs F) :
    i0 / (1 + 2 * F.length) < numVars F ∧
    psec (1 + 2 * F.length) F.length i0 + 1 ≤ 2 * numVars F ∧
    (pp (1 + 2 * F.length) i0 ≠ 0 → psec (1 + 2 * F.length) F.length i0 + 2 ≤ 2 * numVars F) ∧
    pj (1 + 2 * F.length) F.length i0 ≤ F.length ∧
    (pp (1 + 2 * F.length) i0 ≠ 0 → pj (1 + 2 * F.length) F.length i0 < F.length) := by
  have e1 := L2PairSem.pp_eq F i0
  have e2 := L2PairSem.psec_eq F i0
  have e3 := L2PairSem.pj_eq F i0
  simp only [numClauses] at e1 e2 e3
  obtain ⟨hg, -⟩ := SatPairs.group_bounds F i0 hi
  have hg' : i0 / (1 + 2 * F.length) < numVars F := hg
  refine ⟨hg', ?_⟩
  by_cases hp : posOf F i0 = 0
  · have hpp : pp (1 + 2 * F.length) i0 = 0 := by rw [e1, hp]
    have h1 : psec (1 + 2 * F.length) F.length i0 = 2 * (i0 / (1 + 2 * F.length)) := by
      unfold psec; rw [hpp]; simp
    have h2 : pj (1 + 2 * F.length) F.length i0 = 0 := by unfold pj; rw [hpp]; simp
    exact ⟨by omega, fun h => absurd hpp h, by omega, fun h => absurd hpp h⟩
  · have h1 := SatPairs.pairSection_lt F i0 hi hp
    have h2 := SatPairs.pairClause_lt F i0 hp
    rw [← e2] at h1; rw [← e3] at h2
    unfold numClauses at h2
    exact ⟨by omega, fun _ => by omega, by omega, fun _ => h2⟩

/-- The products a pair's numbers are made of. -/
lemma pair_prods (i0 : ℕ) (hi : i0 < Lax391470.SatConstruction.numPairs F) :
    sectionLength p q F * (2 * (i0 / (1 + 2 * F.length)) + 1) ≤
        sectionLength p q F * (2 * numVars F) ∧
    sectionLength p q F * (2 * (i0 / (1 + 2 * F.length))) ≤
        sectionLength p q F * (2 * numVars F) ∧
    sectionLength p q F * (psec (1 + 2 * F.length) F.length i0 + 1) ≤
        sectionLength p q F * (2 * numVars F) ∧
    sectionLength p q F * psec (1 + 2 * F.length) F.length i0 ≤
        sectionLength p q F * (2 * numVars F) ∧
    pj (1 + 2 * F.length) F.length i0 * (p + q) ≤ F.length * (p + q) ∧
    (psec (1 + 2 * F.length) F.length i0 + 1) * F.length ≤ 2 * numVars F * F.length ∧
    (pp (1 + 2 * F.length) i0 ≠ 0 →
      (psec (1 + 2 * F.length) F.length i0 + 1) * F.length + F.length ≤
        2 * numVars F * F.length) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := pair_pos F i0 hi
  refine ⟨Nat.mul_le_mul_left _ (by omega), Nat.mul_le_mul_left _ (by omega),
    Nat.mul_le_mul_left _ (by omega), Nat.mul_le_mul_left _ (by omega),
    Nat.mul_le_mul_right _ h4, Nat.mul_le_mul_right _ h2, fun hp => ?_⟩
  have := Nat.mul_le_mul_right F.length (h3 hp)
  rw [show psec (1 + 2 * F.length) F.length i0 + 2 =
    (psec (1 + 2 * F.length) F.length i0 + 1) + 1 from rfl, Nat.add_mul, Nat.one_mul] at this
  exact this

theorem nums (hd : Dim F W) :
    Nums (B := bnd p q W M) p q F (2 * (W * W)) (4 * (W * W)) := by
  have P := prods p q F W hd
  obtain ⟨hX, h4X, hXU, hcU, hmpq, hS, hSnn, hnm, hnm2⟩ := P
  obtain ⟨hnn, hm, hK⟩ := hd
  have hNPle : Lax391470.SatConstruction.numPairs F ≤ W + 2 * (W * W) := by
    unfold Lax391470.SatConstruction.numPairs numClauses
    have : (2 * numVars F - 1) * F.length ≤ 2 * numVars F * F.length :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  refine ⟨hnm, by omega, by unfold bnd; omega, by unfold bnd; omega, fun i hi => ?_,
    by unfold bnd; omega, by unfold bnd; omega, fun i0 hi => ?_, fun i0 hi => ?_,
    by unfold numOrdinary numClauses; omega, by omega, by unfold bnd; omega⟩
  · -- the fill loop's values
    have hl : (lits F).getD i dflt ∈ lits F := by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
    have hidx : ivF F i < numVars F := SatBridge.index_lt_foldr _ hl
    have hsv : svF F i ≤ 1 := by unfold svF; split <;> omega
    have hcv : cvF F i < F.length := by
      have := snd_lt_of_mem_zip F ((mem_zip_iff F _).mpr ⟨i, hi, rfl⟩)
      exact this
    have hmul : (2 * ivF F i + 1 - svF F i) * F.length ≤ 2 * numVars F * F.length :=
      Nat.mul_le_mul_right _ (by omega)
    unfold bnd
    exact ⟨by omega, by omega, by omega, by omega⟩
  · -- the pair calculator's bounds
    obtain ⟨h1, h2, h3, h4, h5⟩ := pair_pos F i0 hi
    obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := pair_prods p q F i0 hi
    have hdiv : i0 / (1 + 2 * F.length) ≤ i0 := Nat.div_le_self _ _
    have ht := table_le_one F
    refine ⟨fun t => by have := ht t; unfold bnd; omega, by unfold bnd; omega,
      by unfold bnd; omega, by unfold bnd; omega, by unfold bnd; omega, by unfold bnd; omega,
      by unfold bnd; omega, by unfold bnd; omega, by unfold bnd; omega, fun hp => ?_⟩
    have := m7 hp
    have := h5 hp
    omega
  · -- the pair values
    obtain ⟨h1, h2, h3, h4, h5⟩ := pair_pos F i0 hi
    obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := pair_prods p q F i0 hi
    unfold e1Val e2Val e3Val e4Val bnd
    refine ⟨?_, ?_, ?_, ?_⟩ <;> split_ifs <;> omega

end Lax391470Proofs.L2Nums
