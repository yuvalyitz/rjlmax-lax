import Lax391470Proofs.SatOrdinary

/-!
The data of the numbered ordinary jobs agree with those of the typed construction.
-/

namespace Lax391470Proofs.SatOrdinaryData

open Lax391470 Lax391470.SatConstruction Lax429075
open Lax391470Proofs.SatBridge Lax391470Proofs.RjLmax Lax391470Proofs.RjLmax.FromSat
open Lax391470Proofs.Sat Lax391470Proofs.SatOrdinary

variable (p q : ℕ) (F : CNF.Formula)

section read
variable (s c : ℕ) (hs : s < 2 * numVars F) (hc : c < 3)
include hs hc

lemma ordRelease_sec : ordRelease p q F (3 * s + c) =
    if c = 0 then sectionStart p q F s + (if s % 2 = 0 then 1 else q + 1)
    else if c = 1 then sectionStart p q F s
    else sectionStart p q F s + sectionLength p q F - q := by
  have h3 : (3 * s + c) % 3 = c := by omega
  have hd : (3 * s + c) / 3 = s := by omega
  unfold ordRelease
  rw [if_pos (by omega), h3, hd]
  rcases c with _ | _ | _ | c
  · rfl
  · rfl
  · rfl
  · omega

lemma ordDue_sec : ordDue p q F (3 * s + c) =
    if c = 0 then sectionStart p q F s + (if s % 2 = 0 then 2 * q else p + q)
    else if c = 1 then sectionStart p q F s + p + 2 * q + 1
    else sectionStart p q F s + sectionLength p q F := by
  have h3 : (3 * s + c) % 3 = c := by omega
  have hd : (3 * s + c) / 3 = s := by omega
  unfold SatConstruction.ordDue
  rw [if_pos (by omega), h3, hd]
  rcases c with _ | _ | _ | c
  · rfl
  · rfl
  · rfl
  · omega

lemma ordLong_sec : ordLong F (3 * s + c) = decide (c = 1 ∧ s % 2 = 1) := by
  have h3 : (3 * s + c) % 3 = c := by omega
  have hd : (3 * s + c) / 3 = s := by omega
  unfold ordLong
  rw [if_pos (by omega), h3, hd]

end read

lemma secIndex_mod {n : ℕ} (l : Literal n) : secIndex l % 2 = if l.pos then 0 else 1 := by
  unfold secIndex; split <;> omega

/- This is proved by `simp` rather than `rfl`: a `rfl` lemma is used by `simp` without
appearing in the proof term, and the archive's usage check would report it as unused. -/
lemma secLen_eq : secLen p q (toCnf F) = sectionLength p q F := by
  simp [secLen, sectionLength, toCnf, numClauses]

lemma literalOf_secIndex (l : Literal (numVars F)) :
    literalOf (secIndex l) = ⟨l.var, l.pos⟩ := by
  obtain ⟨v, pos⟩ := l
  cases pos <;> simp [literalOf, secIndex]; omega

lemma active_eq (l : Literal (numVars F)) (j : Fin F.length) :
    FromSat.active (toCnf F) l j = SatConstruction.active F (secIndex l) j := by
  unfold FromSat.active SatConstruction.active
  rw [literalOf_secIndex]
  congr 1
  exact propext ⟨fun h => (Finset.mem_filter.mp h).2,
    fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

lemma clauseStart_eq (l : Literal (numVars F)) (j : Fin F.length) :
    ((clauseStart p q F (secIndex l) j : ℕ) : ℤ) = clOffset p q (toCnf F) l j := by
  obtain ⟨j, hj⟩ := j
  simp only [clauseStart, sectionStart, clOffset, secOffset, secLen_eq]
  push_cast
  ring_nf
  rfl

lemma clauseEarly_eq (hq : 1 < q) (l : Literal (numVars F)) (j : Fin F.length) :
    ((clauseEarly p q F (secIndex l) j : ℕ) : ℤ) =
      clOffset p q (toCnf F) l j + Blocks.clEarly p q (FromSat.active (toCnf F) l j) := by
  rw [active_eq, ← clauseStart_eq]
  unfold clauseEarly
  cases SatConstruction.active F (secIndex l) j <;> simp [Blocks.clEarly]; omega

lemma clauseDue_eq (l : Literal (numVars F)) (j : Fin F.length) :
    ((clauseDue p q F (secIndex l) j : ℕ) : ℤ) =
      clOffset p q (toCnf F) l j + Blocks.clDue p q := by
  rw [← clauseStart_eq]
  simp only [clauseDue, Blocks.clDue]
  push_cast; ring

lemma ordRelease_sec0 (s : ℕ) (hs : s < 2 * numVars F) : ordRelease p q F (3 * s) =
    sectionStart p q F s + (if s % 2 = 0 then 1 else q + 1) := by
  simpa using ordRelease_sec p q F s 0 hs (by omega)

lemma ordDue_sec0 (s : ℕ) (hs : s < 2 * numVars F) : SatConstruction.ordDue p q F (3 * s) =
    sectionStart p q F s + (if s % 2 = 0 then 2 * q else p + q) := by
  simpa using ordDue_sec p q F s 0 hs (by omega)

lemma ordLong_sec0 (s : ℕ) (hs : s < 2 * numVars F) : ordLong F (3 * s) = false := by
  simpa using ordLong_sec F s 0 hs (by omega)

lemma sectionLength_ge : q ≤ sectionLength p q F := by unfold sectionLength; omega

lemma ord_r (o : FromSat.Ord (toCnf F)) :
    ((ordRelease p q F (ordIdx F o) : ℕ) : ℤ) = ordRel p q (toCnf F) o := by
  rcases o with ⟨l, b⟩ | l | ⟨l, j⟩ | ⟨l, j⟩
  · have hs : secIndex l < 2 * numVars F := secIndex_lt l
    have hm := secIndex_mod l
    obtain ⟨v, pos⟩ := l
    cases b <;> cases pos <;>
      simp [ordIdx, ordRelease_sec p q F _ _ hs, ordRelease_sec0 p q F _ hs, hm, ordRel, litOffset, secOffset,
        Blocks.LitJob.rel, sectionStart, secLen_eq]
  · have hs : secIndex l < 2 * numVars F := secIndex_lt l
    have hge := sectionLength_ge p q F
    simp only [ordIdx, ordRelease_sec p q F _ 2 hs (by omega), ordRel, sepOffset, secOffset,
      sectionStart, secLen_eq]
    rw [if_neg (by omega), if_neg (by omega), Nat.cast_sub (by omega)]
    push_cast
    rfl
  · have : ¬ 6 * numVars F + (j : ℕ) < 6 * numVars F := by omega
    simp [ordIdx, ordRelease, this, ordRel]
  · have : ¬ 6 * numVars F + F.length + (j : ℕ) < 6 * numVars F := by omega
    simp [ordIdx, ordRelease, this, ordRel]

lemma ord_d (hq : 1 < q) (o : FromSat.Ord (toCnf F)) :
    ((SatConstruction.ordDue p q F (ordIdx F o) : ℕ) : ℤ) = FromSat.ordDue p q (toCnf F) o := by
  rcases o with ⟨l, b⟩ | l | ⟨l, j⟩ | ⟨l, j⟩
  · have hs : secIndex l < 2 * numVars F := secIndex_lt l
    have hm := secIndex_mod l
    obtain ⟨v, pos⟩ := l
    cases b <;> cases pos <;>
      simp [ordIdx, ordDue_sec p q F _ _ hs, ordDue_sec0 p q F _ hs, hm, FromSat.ordDue,
        litOffset, secOffset, Blocks.LitJob.due, sectionStart, secLen_eq] <;> ring_nf
  · have hs : secIndex l < 2 * numVars F := secIndex_lt l
    simp only [ordIdx, ordDue_sec p q F _ 2 hs (by omega), FromSat.ordDue, sepOffset,
      secOffset, sectionStart, secLen_eq]
    rw [if_neg (by omega), if_neg (by omega)]
    push_cast
    try ring_nf
    try rfl
  · have h1 : ¬ 6 * numVars F + (j : ℕ) < 6 * numVars F := by omega
    have h2 : 6 * numVars F + (j : ℕ) < 6 * numVars F + numClauses F := by
      have : (j : ℕ) < F.length := j.isLt
      unfold numClauses; omega
    have hl : secIndex l.1 = 2 * numVars F - 1 := l.2
    simp only [ordIdx, SatConstruction.ordDue, if_neg h1, if_pos h2, FromSat.ordDue,
      Nat.add_sub_cancel_left]
    rw [← hl]
    exact clauseEarly_eq p q F hq l.1 j
  · have hj : (j : ℕ) < F.length := j.isLt
    have h1 : ¬ 6 * numVars F + F.length + (j : ℕ) < 6 * numVars F := by omega
    have h2 : ¬ 6 * numVars F + F.length + (j : ℕ) < 6 * numVars F + numClauses F := by
      unfold numClauses; omega
    have h3 : 6 * numVars F + F.length + (j : ℕ) - 6 * numVars F - numClauses F = j := by
      unfold numClauses; omega
    have hl : secIndex l.1 = 0 := l.2
    simp only [ordIdx, SatConstruction.ordDue, if_neg h1, if_neg h2, FromSat.ordDue, h3]
    exact (congrArg (fun s => ((clauseEarly p q F s j : ℕ) : ℤ)) hl).symm.trans
      (clauseEarly_eq p q F hq l.1 j)

lemma ord_len (o : FromSat.Ord (toCnf F)) :
    (if ordLong F (ordIdx F o) then p else q) = ordLen p q (toCnf F) o := by
  rcases o with ⟨l, b⟩ | l | ⟨l, j⟩ | ⟨l, j⟩
  · have hs : secIndex l < 2 * numVars F := secIndex_lt l
    have hm := secIndex_mod l
    obtain ⟨v, pos⟩ := l
    cases b <;> cases pos <;>
      simp [ordIdx, ordLong_sec F _ _ hs, ordLong_sec0 F _ hs, hm, ordLen, Blocks.LitJob.len]
  · have hs : secIndex l < 2 * numVars F := secIndex_lt l
    simp [ordIdx, ordLong_sec F _ 2 hs, ordLen]
  · have h1 : ¬ 6 * numVars F + (j : ℕ) < 6 * numVars F := by omega
    have h2 : 6 * numVars F + (j : ℕ) < 6 * numVars F + numClauses F := by
      have : (j : ℕ) < F.length := j.isLt
      unfold numClauses; omega
    simp [ordIdx, ordLong, h2, ordLen]
  · have hj : (j : ℕ) < F.length := j.isLt
    have h1 : ¬ 6 * numVars F + F.length + (j : ℕ) < 6 * numVars F := by omega
    have h2 : ¬ 6 * numVars F + F.length + (j : ℕ) < 6 * numVars F + numClauses F := by
      unfold numClauses; omega
    simp [ordIdx, ordLong, h1, h2, ordLen]

end Lax391470Proofs.SatOrdinaryData
