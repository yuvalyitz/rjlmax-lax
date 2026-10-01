import Lax391470.AuxiliaryProblem
import Lax429075.CNF

/-!
---
title: The Instance of AUX(p, Q) Built from a Formula
type: definition
---
The instance of $\mathrm{AUX}(p, q)$ built from a formula in conjunctive normal form
with $n$ variables and $m$ clauses $C_0, \dots, C_{m-1}$.

The time line is cut into $2n$ *sections* of equal length
$S = (p + 2q) + m(p + q) + 1 + q$, one for every literal, in the order
$x_0, \neg x_0, x_1, \neg x_1, \dots$ A section consists of a *literal block* of total job
length $p + 2q$, then one *clause block* of total job length $p + q$ for every clause,
then one unit of idle time, then a *separator*: an ordinary short job whose availability
interval is exactly the last $q$ time units of the section.

Relative to the start of its section, the literal block of a positive literal, of type
$V^+$, consists of the ordinary jobs $([1, 2q],\, q)$ and $([0,\, p + 2q + 1],\, q)$ and
a long pending job with early deadline $p + q + 1$ and late deadline $p + 2q$. The block
of a negative literal, of type $V^-$, consists of the ordinary jobs
$([q + 1,\, p + q],\, q)$ and $([0,\, p + 2q + 1],\, p)$ and a short pending job with
early deadline $q$ and late deadline $p + 2q$. In either block the pending job can
complete early only at the price of one unit of idle time that no other job can fill.

Relative to the point $p + 2q + j(p + q)$ of its section, the clause block of the clause
$C_j$ consists of a long and a short pending job, both with late deadline $p + q + 1$ and
both with early deadline $p + q$ if the literal of the section occurs in $C_j$ — the
block is then *active* — and $p + q - 1$ otherwise. Both jobs of an active block can
complete early if the section has not been delayed; in a delayed section, or in an
inactive block, only one of them can.

Pending jobs are connected as follows. The long pending job of the literal block of $x_i$
is connected with the short pending job of the literal block of $\neg x_i$. For every
clause, the long pending job of its clause block in a section is connected with the short
pending job of its clause block in the next section. This leaves the long pending jobs
of the clause blocks of the last section and the short ones of the first section
unconnected; they are required to meet their early deadline, which makes them ordinary
jobs released at $0$.

A connected pair of literal blocks forces a delay of one unit in the section of $x_i$ or
in that of $\neg x_i$; the literal whose section is not delayed is the one set to true.
The chain of clause blocks of a clause through all sections can be scheduled only if the
clause block is active in some section that is not delayed, that is, if the clause
contains a true literal.

# Formalization Notes

A formula is a list of clauses over variables named by natural numbers, as elsewhere in
the archive. Its variables are taken to be $x_0, \dots, x_{n-1}$ with $n$ one more than
the largest index that occurs, and $n = 1$ when no literal occurs at all, so that the
construction always has at least one variable. Variables that do not occur receive
sections like any other. A clause is a list, in which a repeated literal counts once and
which may be empty; an empty clause has no active block and makes the instance
unsolvable, as it makes the formula unsatisfiable.

Everything is numbered, because an instance is something a machine is handed as a word.
Section $s$ belongs to the variable $\lfloor s/2 \rfloor$ and is positive when $s$ is
even. The ordinary jobs of section $s$ are $3s$, $3s + 1$ and $3s + 2$: the two ordinary
jobs of the literal block and the separator. They are followed by the $m$ unconnected
long jobs of the last section and the $m$ unconnected short jobs of the first. The
connected pairs are listed in the order of their deadlines, in $n$ groups of $1 + 2m$:
pair $(1 + 2m)\,v$ is the literal pair of the variable $v$, the next $m$ pairs connect
the clause blocks of the section of $x_v$ with those of $\neg x_v$, and the following
$m$ connect those of $\neg x_v$ with those of $x_{v+1}$. The last group lacks these
final $m$ pairs, which leaves $N = n + (2n - 1)m$.
-/

namespace Lax391470.SatConstruction

open Lax391470.AuxiliaryProblem Lax429075.CNF

variable (p q : ℕ) (F : Formula)

/-- The number `n` of variables: one more than the largest index occurring in `F`, and
`1` if no literal occurs. -/
def numVars : ℕ := (F.flatMap id).foldr (fun l n => max (l.index + 1) n) 1

/-- The number `m` of clauses. -/
def numClauses : ℕ := F.length

/-- The length `S` of a section. -/
def sectionLength : ℕ := p + 2 * q + numClauses F * (p + q) + 1 + q

/-- The start of section `s`. -/
def sectionStart (s : ℕ) : ℕ := sectionLength p q F * s

/-- The literal of section `s`: the sections run `x₀, ¬x₀, x₁, ¬x₁, …`. -/
def literalOf (s : ℕ) : Literal := ⟨s / 2, decide (s % 2 = 0)⟩

/-- The clause block of clause `j` in section `s` is *active*: the literal of the section
occurs in the clause. -/
def active (s j : ℕ) : Bool := decide (literalOf s ∈ F.getD j [])

/-- The start of the clause block of clause `j` in section `s`. -/
def clauseStart (s j : ℕ) : ℕ := sectionStart p q F s + p + 2 * q + j * (p + q)

/-- The early deadline of both pending jobs of a clause block. -/
def clauseEarly (s j : ℕ) : ℕ :=
  clauseStart p q F s j + (if active F s j then p + q else p + q - 1)

/-- The late deadline of both pending jobs of a clause block. -/
def clauseDue (s j : ℕ) : ℕ := clauseStart p q F s j + p + q + 1

/-- The number of ordinary jobs: three for every section, and the `2m` unconnected
pending jobs. -/
def numOrdinary : ℕ := 6 * numVars F + 2 * numClauses F

/-- The release time of the ordinary job `o`. -/
def ordRelease (o : ℕ) : ℕ :=
  if o < 6 * numVars F then
    match o % 3 with
    | 0 => sectionStart p q F (o / 3) + (if (o / 3) % 2 = 0 then 1 else q + 1)
    | 1 => sectionStart p q F (o / 3)
    | _ => sectionStart p q F (o / 3) + sectionLength p q F - q
  else 0

/-- The deadline of the ordinary job `o`. -/
def ordDue (o : ℕ) : ℕ :=
  if o < 6 * numVars F then
    match o % 3 with
    | 0 => sectionStart p q F (o / 3) + (if (o / 3) % 2 = 0 then 2 * q else p + q)
    | 1 => sectionStart p q F (o / 3) + p + 2 * q + 1
    | _ => sectionStart p q F (o / 3) + sectionLength p q F
  else if o < 6 * numVars F + numClauses F then
    clauseEarly p q F (2 * numVars F - 1) (o - 6 * numVars F)
  else
    clauseEarly p q F 0 (o - 6 * numVars F - numClauses F)

/-- Whether the ordinary job `o` is long: the second ordinary job of a block of type `V⁻`,
and the unconnected long jobs of the last section. -/
def ordLong (o : ℕ) : Bool :=
  if o < 6 * numVars F then decide (o % 3 = 1 ∧ (o / 3) % 2 = 1)
  else decide (o < 6 * numVars F + numClauses F)

/-- The number `N = n + (2n - 1) m` of connected pairs. -/
def numPairs : ℕ := numVars F + (2 * numVars F - 1) * numClauses F

/-- The variable whose group the pair `i` belongs to. -/
def groupOf (i : ℕ) : ℕ := i / (1 + 2 * numClauses F)

/-- The position of the pair `i` in its group: `0` for the literal pair. -/
def posOf (i : ℕ) : ℕ := i % (1 + 2 * numClauses F)

/-- The section holding the long job of the clause pair `i`. -/
def pairSection (i : ℕ) : ℕ := 2 * groupOf F i + (posOf F i - 1) / numClauses F

/-- The clause of the clause pair `i`. -/
def pairClause (i : ℕ) : ℕ := (posOf F i - 1) % numClauses F

/-- The early deadline of the long job of pair `i`. -/
def longEarly (i : ℕ) : ℕ :=
  if posOf F i = 0 then sectionStart p q F (2 * groupOf F i) + p + q + 1
  else clauseEarly p q F (pairSection F i) (pairClause F i)

/-- The late deadline of the long job of pair `i`. -/
def longDue (i : ℕ) : ℕ :=
  if posOf F i = 0 then sectionStart p q F (2 * groupOf F i) + p + 2 * q
  else clauseDue p q F (pairSection F i) (pairClause F i)

/-- The early deadline of the short job of pair `i`, one section after the long job. -/
def shortEarly (i : ℕ) : ℕ :=
  if posOf F i = 0 then sectionStart p q F (2 * groupOf F i + 1) + q
  else clauseEarly p q F (pairSection F i + 1) (pairClause F i)

/-- The late deadline of the short job of pair `i`. -/
def shortDue (i : ℕ) : ℕ :=
  if posOf F i = 0 then sectionStart p q F (2 * groupOf F i + 1) + p + 2 * q
  else clauseDue p q F (pairSection F i + 1) (pairClause F i)

/-- **The instance of `AUX(p, q)`** built from the formula `F`. -/
def inst : AuxiliaryProblem.Instance where
  ordinary := numOrdinary F
  r o := ordRelease p q F o
  d o := ordDue p q F o
  long o := ordLong F o
  pairs := numPairs F
  longEarly i := longEarly p q F i
  longDue i := longDue p q F i
  shortEarly i := shortEarly p q F i
  shortDue i := shortDue p q F i

/-- For job lengths `p > q > 1`, the deadlines of the constructed instance are ordered as
the auxiliary problem requires. -/
axiom ordered (hq : 1 < q) (hqp : q < p) : (inst p q F).Ordered

/-- **From an assignment to a schedule.** If `F` is satisfiable, the constructed instance
has a solution. -/
axiom solvable_of_satisfiable (hq : 1 < q) (hqp : q < p) :
    Satisfiable F → (inst p q F).Solvable p q

/-- **From a schedule to an assignment.** If the constructed instance has a solution, `F`
is satisfiable. -/
axiom satisfiable_of_solvable (hq : 1 < q) (hqp : q < p) :
    (inst p q F).Solvable p q → Satisfiable F

/-- **The numbers of the constructed instance are small**: every release time and every
deadline is at most the length `2nS` of the time line, a polynomial in the size of the
formula. Together with `StackedConstruction.times_le`, this bounds every number of the
composed reduction; it is the ingredient of strong NP-hardness. -/
axiom times_le :
    (∀ o, (inst p q F).r o ≤ 2 * numVars F * sectionLength p q F ∧
      (inst p q F).d o ≤ 2 * numVars F * sectionLength p q F) ∧
    (∀ i, (inst p q F).longDue i ≤ 2 * numVars F * sectionLength p q F ∧
      (inst p q F).shortDue i ≤ 2 * numVars F * sectionLength p q F)

end Lax391470.SatConstruction
