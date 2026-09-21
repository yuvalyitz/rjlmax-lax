import Lax391470.BinaryEncoding
import Lax391470.StackedConstruction
import Lax429075.Reductions

/-!
---
title: The auxiliary problem reduces to scheduling on two job lengths
type: theorem
---
For any two integer job lengths $p > q \ge 1$, the problem $\mathrm{AUX}(p, q)$ is
polynomial-time reducible to single machine scheduling with release times and deadlines
on the job lengths $\{p, q\}$.

The reduction replaces every connected pair of pending jobs by the five jobs of the
stacked construction. Its correctness is proved by an exchange argument: a feasible
schedule of the stacked instance is rearranged, pair by pair in order of urgency, until
every bin holds two jobs of its own pair, and the jobs left after time $0$ are then read
as a solution of the auxiliary instance.

# Formalization notes

A reduction is a function on all words. A word that does not encode an ordered instance
of the auxiliary problem is sent to the encoding of a fixed instance without a feasible
schedule: a single job of length $p$ whose deadline equals its release time.

The three statements separate what is asserted. The first is the combinatorial content:
the map preserves and reflects membership. The second is the running time of that same
map on a Turing machine. The third is the lemma as the source states it, which follows
from the other two.
-/

namespace Lax391470.Lemma1

open Lax391470.BinaryEncoding Lax434930.PolynomialTime Lax429075.Reductions

/-- An instance on the lengths `{p, q}` without a feasible schedule, when `p ≥ 1`: one job
of length `p` that is due when it is released. -/
def blocked (p : ℕ) : Scheduling.Instance where
  jobs := 1
  r _ := 0
  d _ := 0
  p _ := p

/-- **The reduction**, as a map on words: the encoding of an ordered instance `A` is sent
to the encoding of its stacked instance, and every other word to the encoding of
`blocked p`. -/
noncomputable def reduce (p q : ℕ) (w : Word) : Word :=
  open Classical in
  if h : ∃ A : AuxiliaryProblem.Instance, encodeAux A = w ∧ A.Ordered then
    encodeInstance (StackedConstruction.inst p q h.choose)
  else encodeInstance (blocked p)

/-- **The reduction is correct.** -/
axiom reduce_correct (p q : ℕ) (hq : 0 < q) (hqp : q < p) (w : Word) :
    w ∈ AUX p q ↔ reduce p q w ∈ TwoLengths p q

/-- **The reduction runs in polynomial time.** -/
axiom reduce_polyTime (p q : ℕ) :
    Nonempty (Turing.TM2ComputableInPolyTime id id (reduce p q))

/-- **Lemma 1.** For job lengths `p > q ≥ 1`, `AUX(p, q)` is polynomial-time reducible to
scheduling on the lengths `{p, q}`. -/
axiom aux_manyOne_twoLengths (p q : ℕ) (hq : 0 < q) (hqp : q < p) :
    ManyOne (AUX p q) (TwoLengths p q)

end Lax391470.Lemma1
