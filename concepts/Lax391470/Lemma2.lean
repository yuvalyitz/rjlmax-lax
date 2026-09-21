import Lax391470.BinaryEncoding
import Lax391470.SatConstruction
import Lax429075.Reductions
import Lax429075.Satisfiability

/-!
---
title: The auxiliary problem is NP-complete
type: theorem
---
For any two integer job lengths $p > q > 1$, the problem $\mathrm{AUX}(p, q)$ is
NP-complete.

Hardness is by reduction from satisfiability of formulas in conjunctive normal form. A
satisfying assignment yields a solution in which the sections of the false literals are
delayed by one unit: every clause has a true literal, whose section is not delayed and
whose clause block is active, and at that block the chain of connected pairs of the
clause can switch from completing short jobs early to completing long jobs early.
Conversely, in any solution every job runs inside its own block, one of the sections of
$x_i$ and $\neg x_i$ is delayed for every $i$, and a chain of clause blocks can be
scheduled only if it passes an active block in a section that is not delayed; setting
the literals of the delayed sections to false satisfies the formula.

The assumption $q > 1$ is needed: one unit of delay must not leave room for a short job.

# Formalization notes

A reduction is a function on all words. A word that does not encode a formula is sent to
the encoding of a fixed instance without a solution: a single ordinary short job that is
due at time $0$.

The statements separate what is asserted. The first two concern one map on words: that
it preserves and reflects membership, and that a Turing machine computes it in
polynomial time. NP-hardness follows from them and the Cook–Levin theorem, which the
archive proves. Membership in NP is a further statement, and NP-completeness is the
conjunction.
-/

namespace Lax391470.Lemma2

open Lax391470.BinaryEncoding Lax434930.PolynomialTime
open Lax434930.NondeterministicPolynomialTime Lax429075.Reductions

/-- An instance of the auxiliary problem without a solution, when `q ≥ 1`: one ordinary
short job, released and due at time `0`. -/
def blocked : AuxiliaryProblem.Instance where
  ordinary := 1
  r _ := 0
  d _ := 0
  long _ := false
  pairs := 0
  longEarly := Fin.elim0
  longDue := Fin.elim0
  shortEarly := Fin.elim0
  shortDue := Fin.elim0

/-- **The reduction**, as a map on words: the encoding of a formula is sent to the
encoding of the instance built from it, and every other word to the encoding of
`blocked`. -/
def reduce (p q : ℕ) (w : Word) : Word :=
  match Lax429075.Encoding.decodeCNF w with
  | some F => encodeAux (SatConstruction.inst p q F)
  | none => encodeAux blocked

/-- **The reduction is correct.** -/
axiom reduce_correct (p q : ℕ) (hq : 1 < q) (hqp : q < p) (w : Word) :
    w ∈ Lax429075.Satisfiability.SAT ↔ reduce p q w ∈ AUX p q

/-- **The reduction runs in polynomial time.** -/
axiom reduce_polyTime (p q : ℕ) :
    Nonempty (Turing.TM2ComputableInPolyTime id id (reduce p q))

/-- For job lengths `p > q > 1`, `AUX(p, q)` is NP-hard. -/
axiom aux_npHard (p q : ℕ) (hq : 1 < q) (hqp : q < p) :
    ∀ A : Language, A ∈ NP → ManyOne A (AUX p q)

/-- `AUX(p, q)` belongs to NP. -/
axiom aux_mem_NP (p q : ℕ) : AUX p q ∈ NP

/-- **Lemma 2.** For job lengths `p > q > 1`, `AUX(p, q)` is NP-complete. -/
axiom aux_npComplete (p q : ℕ) (hq : 1 < q) (hqp : q < p) : NPComplete (AUX p q)

end Lax391470.Lemma2
