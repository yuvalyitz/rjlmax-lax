import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Common

namespace Lax391470Proofs

/-!
# Non-Preemptive Single Machine Scheduling with Release Times and Deadlines

The problem `1|rⱼ|Lmax` of Elffers and de Weerdt, *"Scheduling with two non-unit job
lengths is NP-complete"*, arXiv:1412.3095v2, Definition 1.

An instance is a finite set of jobs, each with a release time `r`, a deadline `d`, and a
processing time `p`. A schedule assigns a start time to every job; it is feasible when
each job starts after its release time, finishes by its deadline, and no two jobs run at
the same time. The question is whether a feasible schedule exists — equivalently, whether
the maximum lateness `Lmax` can be made `≤ 0`, which is where the name of the problem
comes from.

## Time Is an Integer Here

Definition 1 lets a schedule assign *real* start times, `t : {1,…,n} → ℝ`, while all the
data `r`, `d`, `p` is integral. The two readings are equivalent, which the submission
proves separately as `IntegralStartTimes.realSchedulable_iff`: `⌈·⌉` applied pointwise to a real feasible schedule is an integer feasible
schedule, because rounding up commutes with adding the integer `p` and is monotone. So
nothing is lost by working over `ℤ`, and a great deal is gained — over `ℤ` an execution
interval is a `Finset`, and "these jobs fit in this window" becomes a cardinality
argument (`TypedPacking.lean`) rather than a measure-theoretic one. Every later file works
over `ℤ`.

## Standing Convention

`p_pos` is assumed of an instance. A job of length `0` occupies no time, is schedulable
anywhere its window is non-empty, and interacts with nothing; the paper's job lengths are
`p > q > 1` throughout.
-/

namespace RjLmax

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- An instance of `1|rⱼ|Lmax` (Definition 1): finitely many jobs, each with a release
time `rᵢ ∈ ℤ`, a deadline `dᵢ ∈ ℤ` and a processing time `pᵢ ∈ ℕ`. The pair `[rᵢ, dᵢ]` is
the job's *availability interval*.

Jobs are a `Fintype` rather than `Fin n` so that a construction can name them
structurally — as sums of the objects they come from — instead of through an ad-hoc
enumeration. -/
structure Instance where
  /-- The jobs. -/
  Job : Type
  /-- Jobs are finite. -/
  jobFintype : Fintype Job
  /-- Jobs have decidable equality. -/
  jobDecEq : DecidableEq Job
  /-- Release time. -/
  r : Job → ℤ
  /-- Deadline. -/
  d : Job → ℤ
  /-- Processing time. -/
  p : Job → ℕ
  /-- Standing convention: jobs take time. -/
  p_pos : ∀ i, 0 < p i

attribute [instance] Instance.jobFintype Instance.jobDecEq

namespace Instance

variable (I : Instance)

/-! ## 1. Schedules -/

/-- A schedule: a start time for every job. -/
abbrev Schedule : Type := I.Job → ℤ

variable {I}

/-- The time at which job `i` finishes under `t`. -/
def completion (t : I.Schedule) (i : I.Job) : ℤ := t i + I.p i

/-- Job `i` starts after its release time and finishes by its deadline. -/
def Available (t : I.Schedule) : Prop := ∀ i, I.r i ≤ t i ∧ completion t i ≤ I.d i

/-- No two distinct jobs run at the same time, stated as the arithmetic condition. -/
def NoOverlap (t : I.Schedule) : Prop :=
  ∀ i j, i ≠ j → completion t i ≤ t j ∨ completion t j ≤ t i

/-- **The feasibility of Definition 1**: every job runs inside its availability interval,
and the execution intervals are pairwise disjoint. -/
def Feasible (t : I.Schedule) : Prop := Available t ∧ NoOverlap t

/-- **The question of Definition 1**: is there a feasible schedule? -/
def IsYes (I : Instance) : Prop := ∃ t : I.Schedule, Feasible t

variable (I)

variable {I}

/-! ## 2. Windows

Two spellings of "job `i` runs inside `[a, b)`", used constantly by the packing arguments
of `TypedPacking.lean`. -/

/-- Job `i` runs entirely within `[a, b)`. -/
def RunsIn (t : I.Schedule) (i : I.Job) (a b : ℤ) : Prop := a ≤ t i ∧ completion t i ≤ b

/-! ## 2b. Rewriting a schedule

The exchange argument of `TypedStacked.lean` proceeds by moving a handful of jobs and
leaving the rest alone. Feasibility of the result then needs three things and nothing else:
the moved jobs land inside their own availability intervals, they do not collide with each
other, and they do not collide with anything that stayed put. Everything among the
untouched jobs is inherited. -/

/-- **Moving any set of jobs**, given by a predicate rather than a `Finset` — the later
cases of the exchange argument displace a set whose size depends on `⌊(p+q)/q⌋` and so
cannot be named job by job. -/
theorem feasible_of_move' {t t' : I.Schedule} (h : Feasible t) (P : I.Job → Prop)
    (hagree : ∀ y, ¬ P y → t' y = t y)
    (havail : ∀ x, P x → I.r x ≤ t' x ∧ completion t' x ≤ I.d x)
    (hnew : ∀ x, P x → ∀ y, P y → x ≠ y →
      completion t' x ≤ t' y ∨ completion t' y ≤ t' x)
    (hmix : ∀ x, P x → ∀ y, ¬ P y → completion t' x ≤ t y ∨ t y + I.p y ≤ t' x) :
    Feasible t' := by
  classical
  refine ⟨fun x => ?_, fun x y hxy => ?_⟩
  · by_cases hx : P x
    · exact havail x hx
    · rw [hagree x hx]
      simpa only [completion, hagree x hx] using h.1 x
  · by_cases hx : P x
    · by_cases hy : P y
      · exact hnew x hx y hy hxy
      · simp only [completion, hagree y hy]
        exact hmix x hx y hy
    · by_cases hy : P y
      · simp only [completion, hagree x hx]
        exact (hmix y hy x hx).symm
      · simpa only [completion, hagree x hx, hagree y hy] using h.2 x y hxy

/-- **Moving a single job.** The new schedule is supplied directly rather than as a
`Function.update`: `I.Job` is a structure projection, and rewriting with the `update`
lemmas under it runs into instance mismatches that no amount of `simp` will clear. Giving
the caller control of the term avoids the problem entirely. -/
theorem feasible_of_move_one {t t' : I.Schedule} (h : Feasible t) (a : I.Job)
    (hagree : ∀ y, y ≠ a → t' y = t y)
    (havail : I.r a ≤ t' a ∧ completion t' a ≤ I.d a)
    (hclear : ∀ y, y ≠ a → completion t' a ≤ t y ∨ t y + I.p y ≤ t' a) :
    Feasible t' := by
  refine ⟨fun x => ?_, fun x y hxy => ?_⟩
  · by_cases hx : x = a
    · subst hx; exact havail
    · simp only [completion, hagree x hx]
      simpa only [completion] using h.1 x
  · by_cases hx : x = a
    · subst hx
      simp only [completion, hagree y (fun hc => hxy hc.symm)]
      exact hclear y (fun hc => hxy hc.symm)
    · by_cases hy : y = a
      · subst hy
        simp only [completion, hagree x hx]
        exact (hclear x hx).symm
      · simpa only [completion, hagree x hx, hagree y hy] using h.2 x y hxy

/-- **Moving two jobs**, the shape a swap takes. -/
theorem feasible_of_move_two {t t' : I.Schedule} (h : Feasible t) {a b : I.Job}
    (hagree : ∀ y, y ≠ a → y ≠ b → t' y = t y)
    (ha : I.r a ≤ t' a ∧ completion t' a ≤ I.d a)
    (hb : I.r b ≤ t' b ∧ completion t' b ≤ I.d b)
    (hnew : completion t' a ≤ t' b ∨ completion t' b ≤ t' a)
    (hca : ∀ y, y ≠ a → y ≠ b → completion t' a ≤ t y ∨ t y + I.p y ≤ t' a)
    (hcb : ∀ y, y ≠ a → y ≠ b → completion t' b ≤ t y ∨ t y + I.p y ≤ t' b) :
    Feasible t' := by
  refine ⟨fun x => ?_, fun x y hxy => ?_⟩
  · by_cases hxa : x = a
    · subst hxa; exact ha
    · by_cases hxb : x = b
      · subst hxb; exact hb
      · simp only [completion, hagree x hxa hxb]
        simpa only [completion] using h.1 x
  · by_cases hxa : x = a
    · subst hxa
      by_cases hyb : y = b
      · subst hyb; exact hnew
      · simp only [completion, hagree y (fun hc => hxy hc.symm) hyb]
        exact hca y (fun hc => hxy hc.symm) hyb
    · by_cases hxb : x = b
      · subst hxb
        by_cases hya : y = a
        · subst hya; exact hnew.symm
        · simp only [completion, hagree y hya (fun hc => hxy hc.symm)]
          exact hcb y hya (fun hc => hxy hc.symm)
      · by_cases hya : y = a
        · subst hya
          simp only [completion, hagree x hxa hxb]
          exact (hca x hxa hxb).symm
        · by_cases hyb : y = b
          · subst hyb
            simp only [completion, hagree x hxa hxb]
            exact (hcb x hxa hxb).symm
          · simpa only [completion, hagree x hxa hxb, hagree y hya hyb] using h.2 x y hxy

/-! ## 3. The parameterization by job lengths

`P(S) = {pᵢ}` is the set of job lengths occurring in the instance. Theorem 1 concerns the
instances whose lengths all lie in a fixed two-element set `{p, q}`. -/

/-- Every job of `I` has length `p` or length `q`. -/
def LengthsIn (I : Instance) (p q : ℕ) : Prop := ∀ i, I.p i = p ∨ I.p i = q

end Instance

end RjLmax

end Lax391470Proofs
