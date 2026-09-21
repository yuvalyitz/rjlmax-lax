import Lax391470.Lemma1
import Lax391470.Lemma2
import Lax391470Proofs.Encoding
import Lax391470Proofs.SatNumbering
import Lax391470Proofs.StackedNumbering
import Lax391470Proofs.DecodeSound
import Lax429075.EncodingCorrect

/-!
The two reductions, as maps on words, preserve and reflect membership.
-/

namespace Lax391470Proofs.Reduce

open Lax391470 Lax391470.BinaryEncoding Lax434930.PolynomialTime Lax429075
open Lax391470Proofs.Encoding

lemma blockedAux_not_solvable (p q : ℕ) (hq : 0 < q) : ¬ Lemma2.blocked.Solvable p q := by
  rintro ⟨t, ⟨hav, -⟩, -⟩
  let j : Fin (Lemma2.blocked.toInstance p q).jobs := ⟨0, by simp [Lemma2.blocked,
    AuxiliaryProblem.Instance.toInstance]⟩
  have h := hav j
  rw [StackedBridge.r_of_ord p q (A := Lemma2.blocked) (j := j) (0 : Fin 1) rfl,
    StackedBridge.d_of_ord p q (A := Lemma2.blocked) (j := j) (0 : Fin 1) rfl,
    StackedBridge.p_of_ord p q (A := Lemma2.blocked) (j := j) (0 : Fin 1) rfl] at h
  simp [Lemma2.blocked] at h
  omega

/--
---
conclusion: Lax391470.Lemma2.reduce_correct
---
-/
theorem lemma2_reduce_correct (p q : ℕ) (hq : 1 < q) (hqp : q < p) (w : Word) :
    w ∈ Satisfiability.SAT ↔ Lemma2.reduce p q w ∈ AUX p q := by
  constructor
  · rintro ⟨F, rfl, hF⟩
    have hdec := Lax429075.EncodingCorrect.roundtrip F
    simp only [Lemma2.reduce, hdec]
    exact ⟨_, rfl, SatNumbering.ordered p q F hq hqp,
      SatNumbering.solvable_of_satisfiable p q F hq hqp hF⟩
  · intro h
    unfold Lemma2.reduce at h
    cases hdec : Encoding.decodeCNF w with
    | none =>
      rw [hdec] at h
      obtain ⟨A, hA, -, hsol⟩ := h
      rw [encodeAux_injective hA] at hsol
      exact absurd hsol (blockedAux_not_solvable p q (by omega))
    | some F =>
      rw [hdec] at h
      obtain ⟨A, hA, -, hsol⟩ := h
      rw [encodeAux_injective hA] at hsol
      exact ⟨F, DecodeSound.decodeCNF_sound w F hdec,
        SatNumbering.satisfiable_of_solvable p q F hq hqp hsol⟩

lemma blocked_not_schedulable (p : ℕ) (hp : 0 < p) : ¬ (Lemma1.blocked p).Schedulable := by
  rintro ⟨t, hav, -⟩
  have h := hav (⟨0, by simp [Lemma1.blocked]⟩ : Fin (Lemma1.blocked p).jobs)
  simp [Lemma1.blocked] at h
  omega

/--
---
conclusion: Lax391470.Lemma1.reduce_correct
---
-/
theorem lemma1_reduce_correct (p q : ℕ) (hq : 0 < q) (hqp : q < p) (w : Word) :
    w ∈ AUX p q ↔ Lemma1.reduce p q w ∈ TwoLengths p q := by
  classical
  unfold Lemma1.reduce
  constructor
  · rintro ⟨A, hA, hord, hsol⟩
    have h : ∃ A : AuxiliaryProblem.Instance, encodeAux A = w ∧ A.Ordered := ⟨A, hA, hord⟩
    rw [dif_pos h]
    have hc : h.choose = A := encodeAux_injective (h.choose_spec.1.trans hA.symm)
    rw [hc]
    exact ⟨_, rfl, StackedNumbering.lengthsIn p q A,
      (StackedNumbering.correct p q A hq hqp hord).mp hsol⟩
  · intro hmem
    by_cases h : ∃ A : AuxiliaryProblem.Instance, encodeAux A = w ∧ A.Ordered
    · rw [dif_pos h] at hmem
      obtain ⟨I, hI, -, hs⟩ := hmem
      rw [encodeInstance_injective hI] at hs
      exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2,
        (StackedNumbering.correct p q _ hq hqp h.choose_spec.2).mpr hs⟩
    · rw [dif_neg h] at hmem
      obtain ⟨I, hI, -, hs⟩ := hmem
      rw [encodeInstance_injective hI] at hs
      exact absurd hs (blocked_not_schedulable p (by omega))

end Lax391470Proofs.Reduce
