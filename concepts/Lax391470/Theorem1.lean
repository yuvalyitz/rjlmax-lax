import Lax391470.Lemma1
import Lax391470.Lemma2

/-!
---
title: Scheduling with Two Non-Unit Job Lengths Is NP-Complete
type: theorem
---
Let $p > q > 1$ be two integer job lengths. Single machine scheduling with release times
and deadlines, restricted to instances whose processing times all lie in $\{p, q\}$, is
NP-complete.

Hardness is obtained by composing the reduction from satisfiability to the auxiliary
problem $\mathrm{AUX}(p, q)$ with the reduction from the auxiliary problem to scheduling
on the lengths $\{p, q\}$. Since $p$ and $q$ are constants, every number of the
constructed instance is bounded by a polynomial in the size of the formula, so the source
concludes that the problem is even strongly NP-complete. The two bounds are stated as
`SatConstruction.times_le` and `StackedConstruction.times_le`; strong NP-completeness
itself, which would need a unary encoding of the instance, is not stated here.

The cases left out are polynomial-time solvable: a single job length, and two job
lengths of which the shorter is $1$.

# Formalization Notes

Membership in NP holds for every pair of lengths and is stated without hypotheses. A
certificate is a schedule with integer start times; feasibility confines every start
time between a release time and a deadline of the instance, so the certificate has size
polynomial in the encoding length of the instance.
-/

namespace Lax391470.Theorem1

open Lax391470.BinaryEncoding Lax434930.PolynomialTime
open Lax434930.NondeterministicPolynomialTime Lax429075.Reductions

/-- Scheduling on the lengths `{p, q}` belongs to NP. -/
axiom twoLengths_mem_NP (p q : ℕ) : TwoLengths p q ∈ NP

/-- For job lengths `p > q > 1`, scheduling on the lengths `{p, q}` is NP-hard. -/
axiom twoLengths_npHard (p q : ℕ) (hq : 1 < q) (hqp : q < p) :
    ∀ A : Language, A ∈ NP → ManyOne A (TwoLengths p q)

/-- **Theorem 1.** For job lengths `p > q > 1`, scheduling on the lengths `{p, q}` is
NP-complete. -/
axiom twoLengths_npComplete (p q : ℕ) (hq : 1 < q) (hqp : q < p) :
    NPComplete (TwoLengths p q)

end Lax391470.Theorem1
