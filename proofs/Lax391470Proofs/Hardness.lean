import Lax391470.Theorem1
import Lax429075.SATHard
import Lax434930Proofs.PolynomialComposition

namespace Lax391470Proofs.Hardness

open Lax391470.BinaryEncoding Lax434930.PolynomialTime
open Lax434930.NondeterministicPolynomialTime Lax429075.Reductions

/-- Polynomial-time many-one reductions compose. -/
lemma manyOne_trans {A B C : Language} (hAB : ManyOne A B) (hBC : ManyOne B C) :
    ManyOne A C := by
  obtain ⟨f, ⟨hf⟩, hfc⟩ := hAB
  obtain ⟨g, ⟨hg⟩, hgc⟩ := hBC
  refine ⟨g ∘ f, Lax434930Proofs.PolynomialComposition.comp hf hg, fun x => ?_⟩
  rw [hfc x, hgc (f x)]
  rfl

/--
---
conclusion: Lax391470.Lemma1.aux_manyOne_twoLengths
---
The reduction is the map `reduce`; its two properties are the two other statements.
-/
theorem aux_manyOne_twoLengths (p q : ℕ) (hq : 0 < q) (hqp : q < p) :
    ManyOne (AUX p q) (TwoLengths p q) :=
  ⟨Lax391470.Lemma1.reduce p q, Lax391470.Lemma1.reduce_polyTime p q,
    Lax391470.Lemma1.reduce_correct p q hq hqp⟩

/--
---
conclusion: Lax391470.Lemma2.aux_npHard
---
Compose the Cook–Levin reduction to satisfiability with the map `reduce`.
-/
theorem aux_npHard (p q : ℕ) (hq : 1 < q) (hqp : q < p) :
    ∀ A : Language, A ∈ NP → ManyOne A (AUX p q) := fun A hA =>
  manyOne_trans (Lax429075.SATHard.hardness A hA)
    ⟨Lax391470.Lemma2.reduce p q, Lax391470.Lemma2.reduce_polyTime p q,
      Lax391470.Lemma2.reduce_correct p q hq hqp⟩

/--
---
conclusion: Lax391470.Lemma2.aux_npComplete
---
-/
theorem aux_npComplete (p q : ℕ) (hq : 1 < q) (hqp : q < p) : NPComplete (AUX p q) :=
  ⟨Lax391470.Lemma2.aux_mem_NP p q, Lax391470.Lemma2.aux_npHard p q hq hqp⟩

/--
---
conclusion: Lax391470.Theorem1.twoLengths_npHard
---
Compose Lemma 2's hardness with the reduction of Lemma 1.
-/
theorem twoLengths_npHard (p q : ℕ) (hq : 1 < q) (hqp : q < p) :
    ∀ A : Language, A ∈ NP → ManyOne A (TwoLengths p q) := fun A hA =>
  manyOne_trans (Lax391470.Lemma2.aux_npHard p q hq hqp A hA)
    (Lax391470.Lemma1.aux_manyOne_twoLengths p q (by omega) hqp)

/--
---
conclusion: Lax391470.Theorem1.twoLengths_npComplete
---
-/
theorem twoLengths_npComplete (p q : ℕ) (hq : 1 < q) (hqp : q < p) :
    NPComplete (TwoLengths p q) :=
  ⟨Lax391470.Theorem1.twoLengths_mem_NP p q, Lax391470.Theorem1.twoLengths_npHard p q hq hqp⟩

end Lax391470Proofs.Hardness
