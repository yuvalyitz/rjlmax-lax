import Lax391470Proofs.SatBridge
import Lax391470Proofs.TypedFromSat

/-!
The ordinary jobs of the typed construction, numbered as the concept numbers them.
-/

namespace Lax391470Proofs.SatOrdinary

open Lax391470 Lax391470.SatConstruction Lax429075
open Lax391470Proofs.SatBridge Lax391470Proofs.RjLmax Lax391470Proofs.RjLmax.FromSat
open Lax391470Proofs.Sat

variable (p q : ℕ) (F : CNF.Formula)

lemma numVars_pos : 0 < numVars F := by
  unfold numVars
  induction F.flatMap id with
  | nil => simp
  | cons a L _ => simp only [List.foldr_cons]; omega

/-- The number of an ordinary job. -/
def ordIdx : FromSat.Ord (toCnf F) → ℕ
  | Sum.inl (l, b) => 3 * secIndex l + (if b then 0 else 1)
  | Sum.inr (Sum.inl l) => 3 * secIndex l + 2
  | Sum.inr (Sum.inr (Sum.inl (_, j))) => 6 * numVars F + j
  | Sum.inr (Sum.inr (Sum.inr (_, j))) => 6 * numVars F + F.length + j

lemma ordIdx_lt (o : FromSat.Ord (toCnf F)) : ordIdx F o < numOrdinary F := by
  unfold numOrdinary numClauses
  rcases o with ⟨l, b⟩ | l | ⟨l, j⟩ | ⟨l, j⟩
  · have : secIndex l < 2 * numVars F := secIndex_lt l
    simp only [ordIdx]; split <;> omega
  · have : secIndex l < 2 * numVars F := secIndex_lt l
    simp only [ordIdx]; omega
  · have : (j : ℕ) < F.length := j.isLt
    simp only [ordIdx]; omega
  · have : (j : ℕ) < F.length := j.isLt
    simp only [ordIdx]; omega

lemma ordIdx_injective : Function.Injective (ordIdx F) := by
  rintro (⟨l, b⟩ | l | ⟨l, j⟩ | ⟨l, j⟩) (⟨l', b'⟩ | l' | ⟨l', j'⟩ | ⟨l', j'⟩) h <;>
    simp only [ordIdx] at h
  · have hs : secIndex l = secIndex l' := by split at h <;> split at h <;> omega
    have hb : b = b' := by
      cases b <;> cases b' <;> simp_all
    rw [secIndex_injective hs, hb]
  · exfalso; split at h <;> omega
  · exfalso
    have : secIndex l < 2 * numVars F := secIndex_lt l
    split at h <;> omega
  · exfalso
    have : secIndex l < 2 * numVars F := secIndex_lt l
    split at h <;> omega
  · exfalso; split at h <;> omega
  · have hs : secIndex l = secIndex l' := by omega
    rw [secIndex_injective hs]
  · exfalso
    have : secIndex l < 2 * numVars F := secIndex_lt l
    omega
  · exfalso
    have : secIndex l < 2 * numVars F := secIndex_lt l
    omega
  · exfalso
    have : secIndex l' < 2 * numVars F := secIndex_lt l'
    split at h <;> omega
  · exfalso
    have : secIndex l' < 2 * numVars F := secIndex_lt l'
    omega
  · have hl : l = l' := Subtype.ext (secIndex_injective (l.2.trans l'.2.symm))
    have hj : j = j' := Fin.ext (by omega)
    rw [hl, hj]
  · exfalso
    have : (j : ℕ) < F.length := j.isLt
    omega
  · exfalso
    have : secIndex l' < 2 * numVars F := secIndex_lt l'
    split at h <;> omega
  · exfalso
    have : secIndex l' < 2 * numVars F := secIndex_lt l'
    omega
  · exfalso
    have : (j' : ℕ) < F.length := j'.isLt
    omega
  · have hl : l = l' := Subtype.ext (secIndex_injective (l.2.trans l'.2.symm))
    have hj : j = j' := Fin.ext (by omega)
    rw [hl, hj]

lemma ordIdx_surjective (k : ℕ) (hk : k < numOrdinary F) :
    ∃ o, ordIdx F o = k := by
  unfold numOrdinary numClauses at hk
  have hn := numVars_pos F
  by_cases h1 : k < 6 * numVars F
  · have hs : k / 3 < 2 * (toCnf F).n := by show k / 3 < 2 * numVars F; omega
    have hc : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hc with hc | hc | hc
    · exact ⟨Sum.inl (litOfIndex (k / 3) hs, true), by
        simp only [ordIdx, secIndex_litOfIndex]; simp; omega⟩
    · exact ⟨Sum.inl (litOfIndex (k / 3) hs, false), by
        simp only [ordIdx, secIndex_litOfIndex]; simp; omega⟩
    · exact ⟨Sum.inr (Sum.inl (litOfIndex (k / 3) hs)), by
        simp only [ordIdx, secIndex_litOfIndex]; omega⟩
  · by_cases h2 : k < 6 * numVars F + F.length
    · have hs : 2 * numVars F - 1 < 2 * (toCnf F).n := by show _ < 2 * numVars F; omega
      exact ⟨Sum.inr (Sum.inr (Sum.inl
        (⟨litOfIndex _ hs, secIndex_litOfIndex _ hs⟩, ⟨k - 6 * numVars F, by
          show _ < F.length; omega⟩))), by simp only [ordIdx]; omega⟩
    · have hs : 0 < 2 * (toCnf F).n := by show 0 < 2 * numVars F; omega
      exact ⟨Sum.inr (Sum.inr (Sum.inr
        (⟨litOfIndex _ hs, secIndex_litOfIndex _ hs⟩, ⟨k - 6 * numVars F - F.length, by
          show _ < F.length; omega⟩))), by simp only [ordIdx]; omega⟩

/-- The numbering of the ordinary jobs. -/
noncomputable def ordEquiv : FromSat.Ord (toCnf F) ≃ Fin (numOrdinary F) :=
  Equiv.ofBijective (fun o => ⟨ordIdx F o, ordIdx_lt F o⟩)
    ⟨fun _ _ h => ordIdx_injective F (Fin.mk.inj_iff.mp h),
     fun k => by
      obtain ⟨o, ho⟩ := ordIdx_surjective F k k.isLt
      exact ⟨o, Fin.ext ho⟩⟩

end Lax391470Proofs.SatOrdinary
