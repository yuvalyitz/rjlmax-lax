import Mathlib.Data.Real.Basic

/-!
---
title: Single machine scheduling with release times and deadlines
type: definition
---
An instance consists of $n$ jobs to be run on a single machine. Job $i$ has a release
time $r_i \in \mathbb{Z}$, a deadline $d_i \in \mathbb{Z}$ and a processing time
$p_i \in \mathbb{N}$; the interval $[r_i, d_i]$ is its *availability interval*. A
schedule assigns a start time $t(i)$ to every job. It is *feasible* if
$r_i \le t(i) \le d_i - p_i$ for every job and the execution intervals
$[t(i),\, t(i) + p_i)$ are pairwise disjoint: no job starts before its release time, no
job completes after its deadline, no job is interrupted, and no two jobs run at the same
time. The decision problem, written $1 \mid r_j \mid L_{\max}$ in the three-field
notation, asks whether a feasible schedule exists — equivalently, whether the maximum
lateness can be made non-positive.

The problem is parameterized by the set of processing times its jobs may have. An
instance is *on the lengths $\{p, q\}$* if every processing time is $p$ or $q$.

# Formalization notes

Jobs are `Fin n` rather than an abstract finite type: an instance is something a machine
is handed as a word, and a word presents its jobs in an order.

Start times are integers. The source allows real start times; since all data are
integral this changes nothing, and that it changes nothing is a statement of this
submission rather than a convention of this file. Both readings are therefore defined
here, the real one only so that their equivalence can be stated.

Disjointness of two execution intervals is written as the arithmetic condition that one
job completes before the other starts. For jobs of positive processing time the two
formulations agree, and every statement of this submission concerns lengths
$p > q \ge 1$. A job of processing time zero is not excluded by the structure, because
excluding it would put a proof obligation into every construction; it plays no role.
-/

namespace Lax391470.Scheduling

/-- An instance of single machine scheduling with release times and deadlines: `jobs`
jobs, each with a release time, a deadline and a processing time. -/
structure Instance where
  /-- The number `n` of jobs. -/
  jobs : ℕ
  /-- The release time `r i` of job `i`. -/
  r : Fin jobs → ℤ
  /-- The deadline `d i` of job `i`. -/
  d : Fin jobs → ℤ
  /-- The processing time `p i` of job `i`. -/
  p : Fin jobs → ℕ

namespace Instance

variable (I : Instance)

/-- A schedule assigns a start time to every job. -/
abbrev Schedule := Fin I.jobs → ℤ

variable {I}

/-- A schedule is *feasible* if every job runs inside its availability interval and no two
jobs run at the same time. -/
def Feasible (t : I.Schedule) : Prop :=
  (∀ i, I.r i ≤ t i ∧ t i + I.p i ≤ I.d i) ∧
  (∀ i j, i ≠ j → t i + I.p i ≤ t j ∨ t j + I.p j ≤ t i)

/-- The same condition for a schedule with real start times. -/
def RealFeasible (t : Fin I.jobs → ℝ) : Prop :=
  (∀ i, (I.r i : ℝ) ≤ t i ∧ t i + I.p i ≤ I.d i) ∧
  (∀ i j, i ≠ j → t i + I.p i ≤ t j ∨ t j + I.p j ≤ t i)

variable (I)

/-- `I` admits a feasible schedule. -/
def Schedulable : Prop := ∃ t : I.Schedule, Feasible t

/-- `I` admits a feasible schedule with real start times. -/
def RealSchedulable : Prop := ∃ t : Fin I.jobs → ℝ, RealFeasible t

/-- Every processing time of `I` is `p` or `q`. -/
def LengthsIn (p q : ℕ) : Prop := ∀ i, I.p i = p ∨ I.p i = q

end Instance

end Lax391470.Scheduling
