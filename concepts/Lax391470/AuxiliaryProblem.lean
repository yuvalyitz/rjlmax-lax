import Lax391470.Scheduling

/-!
---
title: The Auxiliary Problem AUX(p, q)
type: definition
---
The intermediate problem through which the hardness proof passes. Fix two job lengths
$p > q$. An instance consists of a set $J$ of *ordinary* jobs, each long (of length $p$)
or short (of length $q$), with non-negative release times and deadlines, together with
two sequences $J_p$ and $J_q$ of $N$ *pending* jobs each. The pending jobs of $J_p$ are
long and those of $J_q$ are short. Every pending job is released at time $0$ and carries
two deadlines: an *early* deadline $d'$ and a *late* deadline $d$. The deadlines satisfy
$$d'_{p,1} \le d_{p,1} \le d'_{p,2} \le d_{p,2} \le \dots \le d'_{p,N} \le d_{p,N},$$
$$d'_{q,1} \le d_{q,1} \le d'_{q,2} \le d_{q,2} \le \dots \le d'_{q,N} \le d_{q,N},$$
$$d_{p,i} \le d'_{q,i} \quad\text{for all } i = 1, \dots, N.$$
The pending jobs $J_{p,i}$ and $J_{q,i}$ are *connected*. The question is whether
$J \cup J_p \cup J_q$ has a feasible schedule, every job meeting its late deadline, in
which for every $i$ at least one of $J_{p,i}$ and $J_{q,i}$ completes by its early
deadline.

A connected pair is a disjunction between two jobs that may sit anywhere on the time
line, which is what lets the problem express the clauses of a formula.

# Formalization Notes

An instance is data only; the three chains of inequalities are the separate predicate
`Ordered`. A construction can then be written down without proof obligations, and that
its output is ordered becomes a statement about it.

The job lengths $p$ and $q$ are not part of an instance. An ordinary job records only
whether it is long, and the lengths enter where the instance is read as a scheduling
instance. The problem is thereby one family of instances interpreted at each pair of
lengths, as the notation $\mathrm{AUX}(p, q)$ suggests.

All times of an instance are natural numbers: the source requires the ordinary jobs'
release times and deadlines to be non-negative, and a pending job, released at $0$, could
not meet a negative deadline.

Forgetting the early deadlines gives an ordinary scheduling instance, `toInstance`, whose
jobs are the ordinary jobs, then the long pending jobs, then the short ones. A solution
is a feasible schedule of that instance satisfying the condition on connected pairs.
-/

namespace Lax391470.AuxiliaryProblem

open Lax391470.Scheduling

/-- The data of an instance of `AUX(p, q)`: ordinary jobs, each long or short, and
`pairs` connected pairs of pending jobs with an early and a late deadline each. -/
structure Instance where
  /-- The number of ordinary jobs. -/
  ordinary : ℕ
  /-- The release time of an ordinary job. -/
  r : Fin ordinary → ℕ
  /-- The deadline of an ordinary job. -/
  d : Fin ordinary → ℕ
  /-- Whether an ordinary job is long (of length `p`) rather than short (of length `q`). -/
  long : Fin ordinary → Bool
  /-- The number `N` of connected pairs of pending jobs. -/
  pairs : ℕ
  /-- The early deadline `d'_{p,i}` of the `i`-th long pending job. -/
  longEarly : Fin pairs → ℕ
  /-- The late deadline `d_{p,i}` of the `i`-th long pending job. -/
  longDue : Fin pairs → ℕ
  /-- The early deadline `d'_{q,i}` of the `i`-th short pending job. -/
  shortEarly : Fin pairs → ℕ
  /-- The late deadline `d_{q,i}` of the `i`-th short pending job. -/
  shortDue : Fin pairs → ℕ

namespace Instance

variable (A : Instance)

/-- The conditions on the deadlines of the pending jobs: within each sequence the
intervals between early and late deadline are ordered and do not intersect, and in every
connected pair the long job is the more urgent. -/
structure Ordered : Prop where
  /-- `d'_{p,i} ≤ d_{p,i}`. -/
  longEarly_le : ∀ i, A.longEarly i ≤ A.longDue i
  /-- `d_{p,i} ≤ d'_{p,i+1}`. -/
  longDue_le : ∀ i j : Fin A.pairs, (i : ℕ) + 1 = j → A.longDue i ≤ A.longEarly j
  /-- `d'_{q,i} ≤ d_{q,i}`. -/
  shortEarly_le : ∀ i, A.shortEarly i ≤ A.shortDue i
  /-- `d_{q,i} ≤ d'_{q,i+1}`. -/
  shortDue_le : ∀ i j : Fin A.pairs, (i : ℕ) + 1 = j → A.shortDue i ≤ A.shortEarly j
  /-- `d_{p,i} ≤ d'_{q,i}`. -/
  longDue_le_shortEarly : ∀ i, A.longDue i ≤ A.shortEarly i

/-- The scheduling instance underlying `A` at the job lengths `p` and `q`: the ordinary
jobs, then the long pending jobs, then the short pending jobs, the pending jobs released
at `0` and due at their late deadlines. -/
def toInstance (p q : ℕ) : Scheduling.Instance where
  jobs := A.ordinary + A.pairs + A.pairs
  r j := if h : (j : ℕ) < A.ordinary then A.r ⟨j, h⟩ else 0
  d j :=
    if h : (j : ℕ) < A.ordinary then A.d ⟨j, h⟩
    else if h' : (j : ℕ) < A.ordinary + A.pairs then
      A.longDue ⟨j - A.ordinary, by omega⟩
    else A.shortDue ⟨j - A.ordinary - A.pairs, by have := j.isLt; omega⟩
  p j :=
    if h : (j : ℕ) < A.ordinary then (if A.long ⟨j, h⟩ then p else q)
    else if (j : ℕ) < A.ordinary + A.pairs then p
    else q

/-- The `i`-th long pending job, as a job of the underlying instance. -/
def longJob (p q : ℕ) (i : Fin A.pairs) : Fin (A.toInstance p q).jobs :=
  ⟨A.ordinary + i, by have := i.isLt; simp only [toInstance]; omega⟩

/-- The `i`-th short pending job, as a job of the underlying instance. -/
def shortJob (p q : ℕ) (i : Fin A.pairs) : Fin (A.toInstance p q).jobs :=
  ⟨A.ordinary + A.pairs + i, by have := i.isLt; simp only [toInstance]; omega⟩

variable {A}

/-- A schedule *solves* `A` at the lengths `p` and `q`: it is feasible, and in every
connected pair the long job completes by its early deadline or the short one does. -/
def Solves (p q : ℕ) (t : (A.toInstance p q).Schedule) : Prop :=
  Scheduling.Instance.Feasible t ∧
  ∀ i : Fin A.pairs,
    t (A.longJob p q i) + p ≤ A.longEarly i ∨ t (A.shortJob p q i) + q ≤ A.shortEarly i

variable (A)

/-- `A` has a solution at the lengths `p` and `q`. -/
def Solvable (p q : ℕ) : Prop := ∃ t, A.Solves p q t

end Instance

end Lax391470.AuxiliaryProblem
