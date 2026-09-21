import Lax391470Proofs.TypedAux

namespace Lax391470Proofs

/-!
# The four blocks, and Proposition 1

Definition 6 of Elffers–de Weerdt, and the analysis of what a block can do.

A *block* is a handful of jobs whose deadlines sit close together, laid out relative to an
offset `o`. The reduction of `TypedFromSat.lean` builds its instance out of `2n`
sections, each a literal block followed by `m` clause blocks and a separator. This file
defines the four block types and proves the local facts the global argument needs; nothing
here mentions the reduction, and every statement is a fact about three (or two) integers.

## The early deadline of `V⁺`

Definition 6 gives the `V⁺` block a long pending job with deadlines
`(d'_p, d_p) = (p+q+1, p+2q)`, and `litEarly` uses exactly that. The value is forced: the
ordinary job `([1, 2q], q)` cannot run after the pending job, so the pending job starts at
`≥ 1+q` and finishes at `≥ p+q+1`; the proof of Proposition 1 places it at `[q+1, p+q+1)`.

Two checks on that value: `p+q+1 ≤ p+2q` needs `1 ≤ q`, and in the *other* schedule
the pending job completes at `p+2q`, which must exceed `p+q+1` — that needs `q > 1`, which
is exactly the hypothesis under which the paper's theorem is stated, and the reason the
`{1, p}` case is not covered by it.

## Proposition 1, as used

The paper states it as "two schedules are possible, one without idle time and completion
time `p+2q`, one with one unit of idle time and completion time `p+2q+1`; only in the
latter can the pending job complete early". What the global proof consumes is the
contrapositive half — earliness *costs* a unit — in the form of `vplus_early_forces` and
`vminus_early_forces`, one for each block type:

> if the pending job of a literal block completes by its early deadline, then some job of
> the block finishes at `o + p + 2q + 1` or later.

That witness is what pushes the rest of the section one unit to the right
(`RjLmax.FromSat`), and it holds for real-valued start times just as it does for integers,
so nothing is lost by having moved to `ℤ`. The converse half — that both schedules exist —
is `litLate_fits` and `litEarly_fits`, which the other direction of the reduction needs in
order to *build* a schedule.
-/

namespace RjLmax
namespace Blocks

/-! ## 1. Literal blocks: `V⁺` and `V⁻`

A literal block has three jobs: two ordinary ones and a pending one. The sign `s` selects
the type — `s = true` is `V⁺`, used for a positive literal `xᵢ`; `s = false` is `V⁻`, used
for `¬xᵢ`. Both have total job length `p + 2q`.

|          | `V⁺` (`s = true`)        | `V⁻` (`s = false`)       |
|----------|--------------------------|--------------------------|
| `ord1`   | `([1, 2q], q)`           | `([q+1, p+q], q)`        |
| `ord2`   | `([0, p+2q+1], q)`       | `([0, p+2q+1], p)`       |
| `pend`   | long, `(p+q+1, p+2q)`    | short, `(q, p+2q)`       |

The pending job's release time is `0` in the `AUX` instance, not `o`; the bound `o ≤ t`
that `LitFits` records for it is supplied by Proposition 2 in the global argument, not by
the job's own availability interval. -/

set_option genSizeOfSpec false in
/-- The three jobs of a literal block. -/
inductive LitJob
  /-- The ordinary job with the tight availability interval. -/
  | ord1
  /-- The ordinary job available for the whole block. -/
  | ord2
  /-- The pending job, the one carrying two deadlines. -/
  | pend
deriving DecidableEq, Repr

instance : Fintype LitJob where
  elems := {.ord1, .ord2, .pend}
  complete := by intro x; cases x <;> decide

namespace LitJob

/-- Processing time. In `V⁺` the pending job is long; in `V⁻` it is `ord2` that is. -/
def len (p q : ℕ) : Bool → LitJob → ℕ
  | true, .ord1 => q
  | true, .ord2 => q
  | true, .pend => p
  | false, .ord1 => q
  | false, .ord2 => p
  | false, .pend => q

/-- Release time, relative to the block offset. -/
def rel (_p q : ℕ) : Bool → LitJob → ℤ
  | true, .ord1 => 1
  | true, .ord2 => 0
  | true, .pend => 0
  | false, .ord1 => (q : ℤ) + 1
  | false, .ord2 => 0
  | false, .pend => 0

/-- Deadline, relative to the block offset. For the pending job this is the *late*
deadline. -/
def due (p q : ℕ) : Bool → LitJob → ℤ
  | true, .ord1 => 2 * (q : ℤ)
  | true, .ord2 => (p : ℤ) + 2 * q + 1
  | true, .pend => (p : ℤ) + 2 * q
  | false, .ord1 => (p : ℤ) + q
  | false, .ord2 => (p : ℤ) + 2 * q + 1
  | false, .pend => (p : ℤ) + 2 * q

end LitJob

/-- The **early** deadline of a literal block's pending job, relative to the offset.

`p + q + 1` for `V⁺` is Definition 6.1's value; see the module doc. -/
def litEarly (p q : ℕ) : Bool → ℤ
  | true => (p : ℤ) + q + 1
  | false => (q : ℤ)

/-- The total job length of a literal block is `p + 2q`, whichever type it is. -/
lemma sum_litLen (p q : ℕ) (s : Bool) :
    ∑ j : LitJob, LitJob.len p q s j = p + 2 * q := by
  change ∑ j ∈ ({LitJob.ord1, LitJob.ord2, LitJob.pend} : Finset LitJob), _ = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  cases s <;> simp [LitJob.len] <;> omega

/-- What the global schedule guarantees about the jobs of one literal block placed at
offset `o`: each runs inside its availability interval (with the pending job's left bound
coming from Proposition 2), and no two of them overlap. -/
structure LitFits (p q : ℕ) (s : Bool) (o : ℤ) (t : LitJob → ℤ) : Prop where
  /-- Each job starts at or after its release time. -/
  lower : ∀ j, o + LitJob.rel p q s j ≤ t j
  /-- Each job finishes by its deadline. -/
  upper : ∀ j, t j + LitJob.len p q s j ≤ o + LitJob.due p q s j
  /-- No two jobs of the block overlap. -/
  sep : ∀ i j, i ≠ j →
    t i + LitJob.len p q s i ≤ t j ∨ t j + LitJob.len p q s j ≤ t i

/-- The pending job of the block completes by its early deadline. -/
def LitPendEarly (p q : ℕ) (s : Bool) (o : ℤ) (t : LitJob → ℤ) : Prop :=
  t .pend + LitJob.len p q s .pend ≤ o + litEarly p q s

/-! ### Proposition 1, the direction the hardness proof uses -/

/-- **Proposition 1 (`V⁺`).** If the long pending job completes early, the block is rigid:
the tight ordinary job starts at `o+1`, the pending job at `o+q+1`, and the remaining
ordinary job cannot start before `o+p+q+1`. In particular `[o, o+1)` is idle. -/
theorem vplus_early_forces {p q : ℕ} {o : ℤ} {t : LitJob → ℤ} (hq : 1 < q) (hqp : q < p)
    (h : LitFits p q true o t) (he : LitPendEarly p q true o t) :
    t .ord1 = o + 1 ∧ t .pend = o + q + 1 ∧ o + (p : ℤ) + q + 1 ≤ t .ord2 := by
  have l1 := h.lower .ord1
  have l2 := h.lower .ord2
  have l3 := h.lower .pend
  have u1 := h.upper .ord1
  have u2 := h.upper .ord2
  have u3 := h.upper .pend
  have s12 := h.sep .ord1 .ord2 (by decide)
  have s13 := h.sep .ord1 .pend (by decide)
  have s23 := h.sep .ord2 .pend (by decide)
  simp only [LitJob.len, LitJob.rel, LitJob.due, litEarly, LitPendEarly] at *
  omega

/-- **Proposition 1 (`V⁻`).** If the short pending job completes early it must start
exactly at `o`, which forces the idle unit `[o+q, o+q+1)` after it: the tight ordinary job
cannot start before `o+q+1`, and the long one not before `o+2q+1`. -/
theorem vminus_early_forces {p q : ℕ} {o : ℤ} {t : LitJob → ℤ} (hq : 1 < q) (_hqp : q < p)
    (h : LitFits p q false o t) (he : LitPendEarly p q false o t) :
    t .pend = o ∧ o + (q : ℤ) + 1 ≤ t .ord1 ∧ o + 2 * (q : ℤ) + 1 ≤ t .ord2 := by
  have l1 := h.lower .ord1
  have l2 := h.lower .ord2
  have l3 := h.lower .pend
  have u1 := h.upper .ord1
  have u2 := h.upper .ord2
  have u3 := h.upper .pend
  have s12 := h.sep .ord1 .ord2 (by decide)
  have s13 := h.sep .ord1 .pend (by decide)
  have s23 := h.sep .ord2 .pend (by decide)
  simp only [LitJob.len, LitJob.rel, LitJob.due, litEarly, LitPendEarly] at *
  omega

/-! ### Proposition 1, the direction that builds a schedule

The two layouts of a literal block. `litLate` packs it tight, finishing at `o + p + 2q`
with the pending job late; `litEarlySched` spends one unit of idle time, finishes at
`o + p + 2q + 1`, and gets the pending job in early. -/

/-- The tight layout: no idle time, pending job late. -/
def litLate (p q : ℕ) (o : ℤ) : Bool → LitJob → ℤ
  | true, .ord1 => o + q
  | true, .ord2 => o
  | true, .pend => o + 2 * (q : ℤ)
  | false, .ord1 => o + p
  | false, .ord2 => o
  | false, .pend => o + (p : ℤ) + q

/-- The delayed layout: one unit of idle time, pending job early. -/
def litEarlySched (p q : ℕ) (o : ℤ) : Bool → LitJob → ℤ
  | true, .ord1 => o + 1
  | true, .ord2 => o + (p : ℤ) + q + 1
  | true, .pend => o + (q : ℤ) + 1
  | false, .ord1 => o + (q : ℤ) + 1
  | false, .ord2 => o + 2 * (q : ℤ) + 1
  | false, .pend => o

theorem litLate_fits {p q : ℕ} (s : Bool) (o : ℤ) (hq : 1 < q) (hqp : q < p) :
    LitFits p q s o (litLate p q o s) := by
  constructor
  · intro j
    cases s <;> cases j <;>
      simp only [litLate, LitJob.rel] <;> omega
  · intro j
    cases s <;> cases j <;>
      simp only [litLate, LitJob.len, LitJob.due] <;> omega
  · intro i j hij
    cases i <;> cases j <;>
      first
        | exact absurd rfl hij
        | (cases s <;> simp only [litLate, LitJob.len] <;> omega)

/-- In the tight layout the pending job is late: it misses its early deadline. Uses
`q > 1` — this is where the `V⁺` deadline `p+q+1` has to sit strictly below
`p+2q`. -/
theorem litLate_pend_late {p q : ℕ} (s : Bool) (o : ℤ) (hq : 1 < q) (hqp : q < p) :
    ¬ LitPendEarly p q s o (litLate p q o s) := by
  cases s <;>
    simp only [LitPendEarly, litLate, LitJob.len, litEarly, not_le] <;> omega

/-- The tight layout finishes the whole block by `o + p + 2q`: no delay. -/
theorem litLate_le {p q : ℕ} (s : Bool) (o : ℤ) (j : LitJob) :
    litLate p q o s j + LitJob.len p q s j ≤ o + (p : ℤ) + 2 * q := by
  cases s <;> cases j <;>
    simp only [litLate, LitJob.len] <;> omega

theorem litEarly_fits {p q : ℕ} (s : Bool) (o : ℤ) (hq : 1 < q) (hqp : q < p) :
    LitFits p q s o (litEarlySched p q o s) := by
  constructor
  · intro j
    cases s <;> cases j <;>
      simp only [litEarlySched, LitJob.rel] <;> omega
  · intro j
    cases s <;> cases j <;>
      simp only [litEarlySched, LitJob.len, LitJob.due] <;> omega
  · intro i j hij
    cases i <;> cases j <;>
      first
        | exact absurd rfl hij
        | (cases s <;> simp only [litEarlySched, LitJob.len] <;> omega)

/-- In the delayed layout the pending job is early. -/
theorem litEarly_pend_early {p q : ℕ} (s : Bool) (o : ℤ) :
    LitPendEarly p q s o (litEarlySched p q o s) := by
  cases s <;>
    simp only [LitPendEarly, litEarlySched, LitJob.len, litEarly] <;> omega

/-- The delayed layout finishes the whole block by `o + p + 2q + 1`: exactly one unit of
delay, no more. -/
theorem litEarly_le {p q : ℕ} (s : Bool) (o : ℤ) (hqp : q < p) (j : LitJob) :
    litEarlySched p q o s j + LitJob.len p q s j ≤ o + (p : ℤ) + 2 * q + 1 := by
  cases s <;> cases j <;>
    simp only [litEarlySched, LitJob.len] <;> omega

/-! ## 2. Clause blocks: `C_active` and `C_inactive`

A clause block is two pending jobs, one long and one short, with no ordinary jobs. Both
carry the same pair of deadlines, late `p+q+1` and early `p+q` (`C_active`, used when the
literal occurs in the clause) or `p+q-1` (`C_inactive`, when it does not). Total job
length `p+q`.

The whole point is the difference between the two: at delay `0` an active block can get
*both* pending jobs in early, and an inactive one cannot. At delay `1` neither can, which
is what Proposition 3 counts. -/

set_option genSizeOfSpec false in
/-- The two jobs of a clause block. -/
inductive ClJob
  /-- The long pending job. -/
  | long
  /-- The short pending job. -/
  | short
deriving DecidableEq, Repr

instance : Fintype ClJob where
  elems := {.long, .short}
  complete := by intro x; cases x <;> decide

/-- Processing time of a clause-block job. -/
def clLen (p q : ℕ) : ClJob → ℕ
  | .long => p
  | .short => q

/-- The total job length of a clause block is `p + q`. -/
lemma sum_clLen (p q : ℕ) : ∑ j : ClJob, clLen p q j = p + q := by
  change ∑ j ∈ ({ClJob.long, ClJob.short} : Finset ClJob), _ = _
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [clLen]

/-- The **early** deadline of both pending jobs of a clause block, relative to the offset:
`p+q` when the literal occurs in the clause, `p+q-1` when it does not. -/
def clEarly (p q : ℕ) : Bool → ℤ
  | true => (p : ℤ) + q
  | false => (p : ℤ) + q - 1

/-- The late deadline of both pending jobs, relative to the offset. -/
def clDue (p q : ℕ) : ℤ := (p : ℤ) + q + 1

/-- What the global schedule guarantees about a clause block at offset `o` running at
delay `δ`: both jobs start at `o + δ` or later, both finish by the late deadline, and they
do not overlap. -/
structure ClFits (p q : ℕ) (o δ : ℤ) (t : ClJob → ℤ) : Prop where
  /-- Both jobs start at `o + δ` or later. Supplied by Proposition 2 and the delay. -/
  lower : ∀ j, o + δ ≤ t j
  /-- Both jobs meet the late deadline. -/
  upper : ∀ j, t j + clLen p q j ≤ o + clDue p q
  /-- The two jobs do not overlap. -/
  sep : t .long + clLen p q .long ≤ t .short ∨ t .short + clLen p q .short ≤ t .long

/-- A clause-block job completes by its early deadline. -/
def ClEarlyAt (p q : ℕ) (active : Bool) (o : ℤ) (t : ClJob → ℤ) (j : ClJob) : Prop :=
  t j + clLen p q j ≤ o + clEarly p q active

/-- **Both pending jobs of a clause block can be early only at delay `0`, and only if the
block is active.** This is the inequality Proposition 3 contradicts: at delay `1` an active
block, and at any delay an inactive one, must leave one of its two pending jobs late. -/
theorem cl_both_early_bound {p q : ℕ} {active : Bool} {o δ : ℤ} {t : ClJob → ℤ}
    (h : ClFits p q o δ t) (hl : ClEarlyAt p q active o t .long)
    (hs : ClEarlyAt p q active o t .short) :
    δ + (p : ℤ) + q ≤ clEarly p q active := by
  have l1 := h.lower .long
  have l2 := h.lower .short
  have hsep := h.sep
  simp only [ClEarlyAt, clLen] at *
  cases active <;> simp only [clEarly] at * <;> omega

/-! ### The two layouts of a clause block

At delay `δ` the block can be scheduled long-first or short-first. Whichever goes first is
early (provided the deadline allows it); the other one is late unless `δ = 0` and the block
is active, in which case both are early. -/

/-- The layout of a clause block at delay `δ`, with the long job first or the short one
first. -/
def clSched (p q : ℕ) (o δ : ℤ) : Bool → ClJob → ℤ
  | true, .long => o + δ
  | true, .short => o + δ + p
  | false, .long => o + δ + q
  | false, .short => o + δ

theorem clSched_fits {p q : ℕ} (longFirst : Bool) (o δ : ℤ) (hδ : δ ≤ 1) :
    ClFits p q o δ (clSched p q o δ longFirst) := by
  constructor
  · intro j
    cases longFirst <;> cases j <;>
      simp only [clSched] <;> omega
  · intro j
    cases longFirst <;> cases j <;>
      simp only [clSched, clLen, clDue] <;> omega
  · cases longFirst <;>
      simp only [clSched, clLen] <;> omega

/-- Scheduled long-first, the long pending job meets the early deadline, at delay `0` or
`1`. Uses `q > 1` for the inactive block at delay `1`. -/
theorem clSched_long_early {p q : ℕ} (active : Bool) (o δ : ℤ) (hq : 1 < q) (_hqp : q < p)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) : ClEarlyAt p q active o (clSched p q o δ true) .long := by
  cases active <;> simp only [ClEarlyAt, clSched, clLen, clEarly] <;> omega

/-- Scheduled short-first, the short pending job meets the early deadline. Uses `p > q`
for the inactive block at delay `1`. -/
theorem clSched_short_early {p q : ℕ} (active : Bool) (o δ : ℤ) (hq : 1 < q) (hqp : q < p)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) : ClEarlyAt p q active o (clSched p q o δ false) .short := by
  cases active <;> simp only [ClEarlyAt, clSched, clLen, clEarly] <;> omega

/-- A clause block scheduled either way finishes by `o + δ + p + q`: it occupies exactly
its own span, displaced by the delay. This is what keeps it clear of the next block. -/
theorem clSched_le {p q : ℕ} (longFirst : Bool) (o δ : ℤ) (c : ClJob) :
    clSched p q o δ longFirst c + clLen p q c ≤ o + δ + (p : ℤ) + q := by
  cases longFirst <;> cases c <;> simp only [clSched, clLen] <;> omega

/-- A clause block never starts before its own offset, displaced by the delay. -/
theorem clSched_ge {p q : ℕ} (longFirst : Bool) (o δ : ℤ) (c : ClJob) :
    o + δ ≤ clSched p q o δ longFirst c := by
  cases longFirst <;> cases c <;> simp only [clSched] <;> omega

/-- At delay `0` an **active** clause block gets both pending jobs in early, in either
order. This is the slack a section with no idle time buys, and it is what makes a satisfied
clause schedulable. -/
theorem clSched_both_early {p q : ℕ} (longFirst : Bool) (o : ℤ) (j : ClJob) :
    ClEarlyAt p q true o (clSched p q o 0 longFirst) j := by
  cases longFirst <;> cases j <;>
    simp only [ClEarlyAt, clSched, clLen, clEarly] <;> omega

end Blocks
end RjLmax

end Lax391470Proofs
