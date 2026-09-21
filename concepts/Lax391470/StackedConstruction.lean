import Lax391470.AuxiliaryProblem

/-!
---
title: The stacked scheduling instance
type: definition
---
The scheduling instance built from an instance of $\mathrm{AUX}(p, q)$, in which the two
deadlines of a pending job are expressed by ordinary availability intervals. The
construction buys the second deadline with room on the time line before time $0$.

Let $w = q$ and let $t_i = -(p + q + w)\, i$ for $i = 1, \dots, N$. For every connected
pair $i$ the instance contains five jobs:

- a *separator* with availability interval $[t_i + p + q,\; t_i + p + q + w]$ and length
  $w$, which is thereby pinned in place;
- an *inner* long job $([t_i + q,\; d'_{p,i}],\, p)$ and an *outer* long job
  $([t_i,\; d_{p,i}],\, p)$;
- an *inner* short job $([t_i + p,\; d'_{q,i}],\, q)$ and an *outer* short job
  $([t_i,\; d_{q,i}],\, q)$.

The ordinary jobs are kept unchanged. The separators cut the time before $0$ into $N$
*bins* $[t_i,\, t_i + p + q)$, each with room for exactly one long and one short job. The
availability intervals of the four jobs of a pair are nested, the inner ones carrying
the early deadlines. A feasible schedule parks two jobs of each pair in its bin and runs
the other two, one long and one short, after time $0$. The inner long job and the inner
short job of a pair do not fit into its bin together, so one of the two jobs running
after $0$ is an inner job and meets an early deadline — the condition on connected
pairs.

# Formalization notes

The source leaves the separator length $w \in \{p, q\}$ free; it is fixed to $q$ here.

Jobs are numbered: the ordinary jobs keep their numbers, and the five jobs of pair $i$
(counted from $0$) follow at positions $n + 5i, \dots, n + 5i + 4$ in the order
separator, inner long, outer long, inner short, outer short. With pairs counted from $0$
the left end of bin $i$ is $-(p + 2q)(i + 1)$.
-/

namespace Lax391470.StackedConstruction

open Lax391470.Scheduling Lax391470.AuxiliaryProblem

variable (p q : ℕ) (A : AuxiliaryProblem.Instance)

/-- The left end `tᵢ` of the bin of pair `i`, pairs counted from `0`. -/
def binStart (i : ℕ) : ℤ := -(((p + 2 * q) * (i + 1) : ℕ) : ℤ)

/-- The number of jobs: the ordinary ones and five for every connected pair. -/
def numJobs : ℕ := A.ordinary + 5 * A.pairs

/-- The pair a job beyond the ordinary ones belongs to. -/
def pairOf (j : ℕ) : ℕ := (j - A.ordinary) / 5

/-- Which of the five jobs of its pair a job is: `0` the separator, `1` the inner long
job, `2` the outer long job, `3` the inner short job, `4` the outer short job. -/
def partOf (j : ℕ) : ℕ := (j - A.ordinary) % 5

/-- **The stacked instance** built from `A` at the lengths `p` and `q`. -/
def inst : Scheduling.Instance where
  jobs := numJobs A
  r j :=
    if h : (j : ℕ) < A.ordinary then A.r ⟨j, h⟩
    else
      binStart p q (pairOf A j) +
        match partOf A j with
        | 0 => (p + q : ℕ)
        | 1 => (q : ℕ)
        | 2 => 0
        | 3 => (p : ℕ)
        | _ => 0
  d j :=
    if h : (j : ℕ) < A.ordinary then A.d ⟨j, h⟩
    else
      have hi : pairOf A j < A.pairs := by
        have := j.isLt
        simp only [pairOf, numJobs] at *
        omega
      match partOf A j with
      | 0 => binStart p q (pairOf A j) + (p + 2 * q : ℕ)
      | 1 => A.longEarly ⟨pairOf A j, hi⟩
      | 2 => A.longDue ⟨pairOf A j, hi⟩
      | 3 => A.shortEarly ⟨pairOf A j, hi⟩
      | _ => A.shortDue ⟨pairOf A j, hi⟩
  p j :=
    if h : (j : ℕ) < A.ordinary then (if A.long ⟨j, h⟩ then p else q)
    else
      match partOf A j with
      | 1 => p
      | 2 => p
      | _ => q

/-- The stacked instance is on the lengths `{p, q}`. -/
axiom lengthsIn : (inst p q A).LengthsIn p q

/-- **The construction is correct.** For job lengths `p > q ≥ 1`, an ordered instance of
`AUX(p, q)` has a solution exactly when the stacked instance has a feasible schedule. -/
axiom correct (hq : 0 < q) (hqp : q < p) (hA : A.Ordered) :
    A.Solvable p q ↔ (inst p q A).Schedulable

/-- **The numbers of the stacked instance are small**: if every release time and every
deadline of an ordered instance `A` is at most `T`, every release time and deadline of the
stacked instance lies within `T + (p + 2q)N` of `0`, where `N` is the number of pairs.
Together with `SatConstruction.times_le`, this bounds every number of the composed
reduction by a polynomial in the size of the formula. -/
axiom times_le (hA : A.Ordered) (T : ℕ)
    (hT : (∀ o, A.r o ≤ T ∧ A.d o ≤ T) ∧
      (∀ i, A.longDue i ≤ T ∧ A.shortDue i ≤ T)) :
    ∀ j, |(inst p q A).r j| ≤ ((T + (p + 2 * q) * A.pairs : ℕ) : ℤ) ∧
      |(inst p q A).d j| ≤ ((T + (p + 2 * q) * A.pairs : ℕ) : ℤ)

end Lax391470.StackedConstruction
