import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Prod
import Lax391470Proofs.TypedProblems

namespace Lax391470Proofs

/-!
# Lemma 1: `AUX(p, q)` Reduces to `1|rⱼ|Lmax` on Two Job Lengths

Definitions 3 and 4 of Elffers–de Weerdt, and the reduction they define.

An `AUX(p, q)` instance has pending jobs carrying *two* deadlines, which `1|rⱼ|Lmax` has
no way to express. The construction buys the second deadline with room on the time line
*before* `0`:

* each pending pair `i` becomes a **quad** of four jobs — an *inner* and an *outer* copy of
  the long pending job, and of the short one. The outer copies carry the late deadlines
  `d_{p,i}`, `d_{q,i}`; the inner ones carry the early deadlines `d'_{p,i}`, `d'_{q,i}`.
  All four are released before `0`, the inner ones later than the outer ones;
* a **separator** job of length `w` with an availability interval exactly its own length
  is pinned in place, and the separators cut `[-(p+q+w)·N, 0)` into `N` **bins** of length
  `p + q`, one per pair.

A bin holds `p + q`, which is one long job and one short job, no more (`2p > p+q`). So a
feasible schedule must park two jobs of each quad in its bin and run the other two after
`0` — and those two are the pending pair. Which two are parked is exactly the choice
"`J_{p,i}` early or `J_{q,i}` early": parking the outer long and inner short leaves the
inner long, whose deadline is `d'_{p,i}`, to run after `0`.

Definition 4 calls `(J^I_{p,i}, J^O_{q,i})` and `(J^O_{p,i}, J^I_{q,i})` the *proper
pairings*: the two ways of splitting a quad that a feasible schedule can realise.

## Choice of `w`

Definition 3 leaves the separator length `w` free, requiring only `w ∈ {p, q}` so that the
instance uses two job lengths. This file takes `w = q`. Nothing depends on the choice.

## Organisation

§1–§3 build the construction and its geometry: where the bins sit, and which bin a job
scheduled before `0` belongs to. §4 bounds what one bin can hold. §5 proves the forward
direction (`isYes_of_yes`), §6 the converse (`yes_of_isYes`) by the paper's exchange
argument.
-/

namespace RjLmax

set_option genSizeOfSpec false in
/-- The five jobs that Definition 3 puts in place of one pending pair. -/
inductive Part
  /-- The separator job, pinned in place, closing off bin `i`. -/
  | sep
  /-- The inner long job, carrying the *early* deadline `d'_{p,i}`. -/
  | longIn
  /-- The outer long job, carrying the late deadline `d_{p,i}`. -/
  | longOut
  /-- The inner short job, carrying the *early* deadline `d'_{q,i}`. -/
  | shortIn
  /-- The outer short job, carrying the late deadline `d_{q,i}`. -/
  | shortOut
deriving DecidableEq

instance : Fintype Part where
  elems := {.sep, .longIn, .longOut, .shortIn, .shortOut}
  complete := by intro x; cases x <;> decide

namespace Stacked

variable {p q : ℕ} (A : Aux p q)

/-! ## 1. The construction (Definition 3) -/

/-- The width of one bin together with its separator, `p + q + w` with `w = q`. -/
def width (p q : ℕ) : ℕ := p + 2 * q

/-- `tᵢ`, the left end of bin `i`. Bin `0` is the one nearest `0`. -/
def binStart (i : Fin A.N) : ℤ := -(width p q : ℤ) * ((i : ℕ) + 1)

/-- Release time of a quad job. -/
def quadRel : Fin A.N × Part → ℤ
  | (i, .sep) => binStart A i + p + q
  | (i, .longIn) => binStart A i + q
  | (i, .longOut) => binStart A i
  | (i, .shortIn) => binStart A i + p
  | (i, .shortOut) => binStart A i

/-- Deadline of a quad job: the *early* deadline for the inner jobs, the late one for the
outer jobs, and its own release plus its length for the pinned separator. -/
def quadDue : Fin A.N × Part → ℤ
  | (i, .sep) => binStart A i + p + 2 * q
  | (i, .longIn) => A.dp' i
  | (i, .longOut) => A.dp i
  | (i, .shortIn) => A.dq' i
  | (i, .shortOut) => A.dq i

/-- Processing time of a quad job. -/
def quadLen (p q : ℕ) : Fin A.N × Part → ℕ
  | (_, .sep) => q
  | (_, .longIn) => p
  | (_, .longOut) => p
  | (_, .shortIn) => q
  | (_, .shortOut) => q

/-- **Definition 3**: the `1|rⱼ|Lmax` instance built from `A`. Its jobs are those of `A`
together with a quad and a separator for each pending pair. -/
def inst : Instance where
  Job := A.Ord ⊕ Fin A.N × Part
  jobFintype := inferInstance
  jobDecEq := inferInstance
  r := Sum.elim A.r (quadRel A)
  d := Sum.elim A.d (quadDue A)
  p := Sum.elim A.len (quadLen A p q)
  p_pos := by
    rintro (o | ⟨i, part⟩)
    · rcases A.len_eq o with h | h <;> simp only [Sum.elim_inl, h] <;>
        [exact lt_trans A.q_pos A.q_lt_p; exact A.q_pos]
    · cases part <;> simp only [Sum.elim_inr, quadLen] <;>
        [exact A.q_pos; exact lt_trans A.q_pos A.q_lt_p;
         exact lt_trans A.q_pos A.q_lt_p; exact A.q_pos; exact A.q_pos]

/- These are proved by `simp` rather than `rfl`: a `rfl` lemma is used by `simp` without
appearing in the proof term, and the archive's usage check would report it as unused. -/
@[simp] lemma inst_r_quad (x : Fin A.N × Part) : (inst A).r (Sum.inr x) = quadRel A x := by
  simp [inst]
@[simp] lemma inst_d_ord (o : A.Ord) : (inst A).d (Sum.inl o) = A.d o := by
  simp [inst]
@[simp] lemma inst_d_quad (x : Fin A.N × Part) : (inst A).d (Sum.inr x) = quadDue A x := by
  simp [inst]
@[simp] lemma inst_p_ord (o : A.Ord) : (inst A).p (Sum.inl o) = A.len o := by
  simp [inst]

@[simp] lemma inst_p_quad (x : Fin A.N × Part) :
    (inst A).p (Sum.inr x) = quadLen A p q x := by
  simp [inst]

/-- Every job of the constructed instance is long or short: the reduction lands in the
two-length problem. -/
lemma inst_lengthsIn : (inst A).LengthsIn p q := by
  rintro (o | ⟨i, part⟩)
  · exact A.len_eq o
  · cases part <;> simp [inst_p_quad, quadLen]
/-! ## 2. The geometry of the bins

The separators tile `[-width·N, 0)` into `N` copies of `[tᵢ, tᵢ + width)`, each a bin
`[tᵢ, tᵢ + p + q)` followed by a separator `[tᵢ + p + q, tᵢ + width)`. Two facts are all
the feasibility proof needs from this: a bin-and-separator block ends at or before `0`,
and blocks with different indices are disjoint. -/

lemma binStart_add_width (i : Fin A.N) :
    binStart A i + width p q = -(width p q : ℤ) * (i : ℕ) := by
  simp only [binStart, width]
  push_cast
  ring

/-- A bin and its separator end at or before time `0`. -/
lemma binStart_add_width_nonpos (i : Fin A.N) : binStart A i + width p q ≤ 0 := by
  rw [binStart_add_width, neg_mul]
  have : (0 : ℤ) ≤ (width p q : ℤ) * (i : ℕ) := by positivity
  omega

/-- Distinct pairs get disjoint bin-and-separator blocks. -/
lemma binStart_disjoint {i j : Fin A.N} (h : i ≠ j) :
    binStart A i + width p q ≤ binStart A j ∨ binStart A j + width p q ≤ binStart A i := by
  have hij : (i : ℕ) ≠ (j : ℕ) := fun hc => h (Fin.ext hc)
  have hw : (0 : ℤ) < width p q := by
    have := A.q_pos
    simp only [width]
    omega
  simp only [binStart]
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · right
    have : ((j : ℕ) : ℤ) ≥ ((i : ℕ) : ℤ) + 1 := by exact_mod_cast hlt
    nlinarith
  · left
    have : ((i : ℕ) : ℤ) ≥ ((j : ℕ) : ℤ) + 1 := by exact_mod_cast hlt
    nlinarith

/-! ## 3. Locating a job in its bin

The separators tile the negative time line, so any job scheduled before `0` sits inside
exactly one bin. Proving that needs the bins addressed by a plain natural number and built
up one at a time — `binStart` as printed, `-(p+q+w)·(i+1)`, multiplies two variables and is
past what `omega` will do. `binAt` is the same sequence defined by steps of `width`. -/

/-- The left end of the `i`'th bin, defined recursively so that the arithmetic stays
linear. -/
def binAt (p q : ℕ) : ℕ → ℤ
  | 0 => -(width p q : ℤ)
  | (i + 1) => binAt p q i - width p q

lemma binAt_eq (p q : ℕ) (i : ℕ) : binAt p q i = -(width p q : ℤ) * ((i : ℤ) + 1) := by
  induction i with
  | zero => simp [binAt]
  | succ i ih =>
    simp only [binAt, ih]
    push_cast
    ring

lemma binStart_eq_binAt (i : Fin A.N) : binStart A i = binAt p q (i : ℕ) := by
  rw [binAt_eq]
  rfl

/-- **Every job scheduled before `0` lies in a bin**, and a job released no earlier than
the `i`'th bin lies in one of the bins `0, …, i` — the bins nearer to `0`. The separators
are what force this: a job cannot straddle one. -/
lemma exists_bin (i : ℕ) {x : ℤ} (hlo : binAt p q i ≤ x) (hneg : x < 0) :
    ∃ k, k ≤ i ∧ binAt p q k ≤ x ∧ x < binAt p q k + width p q := by
  induction i with
  | zero =>
    refine ⟨0, le_refl 0, hlo, ?_⟩
    simp only [binAt]
    omega
  | succ i ih =>
    by_cases h : x < binAt p q (i + 1) + width p q
    · exact ⟨i + 1, le_refl _, hlo, h⟩
    · have hle : binAt p q i ≤ x := by
        simp only [binAt] at h
        omega
      obtain ⟨k, hk, h1, h2⟩ := ih hle
      exact ⟨k, by omega, h1, h2⟩

/-- Bins are strictly ordered: bin `k` ends where bin `k-1` begins. -/
lemma binAt_succ (p q : ℕ) (k : ℕ) : binAt p q (k + 1) + width p q = binAt p q k := by
  simp only [binAt]
  omega

/-- The separator jobs are pinned in place: their availability interval is exactly their
own length, so a feasible schedule has no choice about them. -/
lemma sep_fixed {u : (inst A).Schedule} (h : (inst A).Feasible u) (i : Fin A.N) :
    u (Sum.inr (i, Part.sep)) = binStart A i + p + q := by
  have h1 := (h.1 (Sum.inr (i, Part.sep))).1
  have h2 := (h.1 (Sum.inr (i, Part.sep))).2
  simp only [inst_r_quad, inst_d_quad, inst_p_quad, quadRel, quadDue, quadLen,
    Instance.completion] at h1 h2
  omega

/-- Every job of a quad is released at or after the start of its own bin. -/
lemma binStart_le_quadRel (i : Fin A.N) (part : Part) :
    binStart A i ≤ quadRel A (i, part) := by
  have := A.q_pos
  have := A.q_lt_p
  cases part <;> simp only [quadRel] <;> omega

/-- **A quad job scheduled before time `0` runs entirely inside one bin**, and that bin's
index is at most the job's own — a quad can only reach the bins nearer to `0` than its own,
because its release time forbids the rest. The separator is what stops it from spilling out
of the far end of the bin. -/
lemma quad_in_bin {u : (inst A).Schedule} (h : (inst A).Feasible u) (i : Fin A.N)
    {part : Part} (hpart : part ≠ Part.sep) (hneg : u (Sum.inr (i, part)) < 0) :
    ∃ k : ℕ, k ≤ (i : ℕ) ∧ k < A.N ∧ binAt p q k ≤ u (Sum.inr (i, part)) ∧
      u (Sum.inr (i, part)) + quadLen A p q (i, part) ≤ binAt p q k + p + q := by
  have hrel := (h.1 (Sum.inr (i, part))).1
  simp only [inst_r_quad] at hrel
  have hbin : binAt p q (i : ℕ) ≤ u (Sum.inr (i, part)) := by
    have h0 := binStart_le_quadRel A i part
    rw [binStart_eq_binAt] at h0
    omega
  obtain ⟨k, hk, h1, h2⟩ := exists_bin (p := p) (q := q) (i : ℕ) hbin hneg
  have hkN : k < A.N := lt_of_le_of_lt hk i.isLt
  refine ⟨k, hk, hkN, h1, ?_⟩
  have hsep := sep_fixed A h ⟨k, hkN⟩
  rw [binStart_eq_binAt] at hsep
  have hne : Sum.inr (i, part) ≠ (Sum.inr (⟨k, hkN⟩, Part.sep) : (inst A).Job) := by
    intro hc
    rw [Sum.inr.injEq, Prod.ext_iff] at hc
    exact hpart hc.2
  have hsep' := h.2 _ _ hne
  simp only [Instance.completion, inst_p_quad, quadLen, hsep] at hsep'
  have hw : (width p q : ℤ) = (p : ℤ) + 2 * q := by
    simp only [width]
    push_cast
    ring
  rw [hw] at h2
  rcases hsep' with hc | hc
  · simpa only [quadLen] using hc
  · omega

/-! ## 4. What one bin can hold

The paper's exchange argument turns on the capacity of a single bin, and every case of it
is the same computation: the jobs parked in a bin run inside a window of length `p + q`, so
their lengths sum to at most `p + q` (`Instance.sum_p_le`). Two long jobs, or a long job
and two short ones, exceed it. -/

/-- Three jobs parked in one bin have total length at most `p + q`. -/
lemma three_in_bin_le {u : (inst A).Schedule} (h : (inst A).Feasible u)
    {x y z : (inst A).Job} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {b : ℤ}
    (hx : Instance.RunsIn u x b (b + p + q)) (hy : Instance.RunsIn u y b (b + p + q))
    (hz : Instance.RunsIn u z b (b + p + q)) :
    (inst A).p x + (inst A).p y + (inst A).p z ≤ p + q := by
  classical
  have hmem : ∀ w ∈ ({x, y, z} : Finset (inst A).Job), Instance.RunsIn u w b (b + p + q) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz
  have hsum := Instance.sum_p_le h.2 ({x, y, z} : Finset (inst A).Job) hmem
  rw [Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_insert (by simp [hyz]),
    Finset.sum_singleton] at hsum
  have harith : ((b + (p : ℤ) + q) - b).toNat = p + q := by omega
  omega

/-! ### The nesting: what an inner job can do in its own bin

"The availability intervals per stack are nested, and those jobs are the ones with the
smallest availability interval that can be scheduled at these positions." Concretely: an
inner job parked in its *own* bin has no freedom at all — its release time pins it against
the far end — and the two inner jobs of a pair therefore cannot share that bin. This is
what the relabelling step of the exchange argument uses. -/

/-- The inner long job of pair `i`, parked in pair `i`'s own bin, is forced against the far
end of it. -/
lemma innerLong_forced {u : (inst A).Schedule} (h : (inst A).Feasible u) (i : Fin A.N)
    (hup : u (Sum.inr (i, Part.longIn)) + (p : ℤ) ≤ binStart A i + p + q) :
    u (Sum.inr (i, Part.longIn)) = binStart A i + q := by
  have hrel := (h.1 (Sum.inr (i, Part.longIn))).1
  simp only [inst_r_quad, quadRel] at hrel
  omega

/-- The inner short job of pair `i`, parked in pair `i`'s own bin, is likewise forced. -/
lemma innerShort_forced {u : (inst A).Schedule} (h : (inst A).Feasible u) (i : Fin A.N)
    (hup : u (Sum.inr (i, Part.shortIn)) + (q : ℤ) ≤ binStart A i + p + q) :
    u (Sum.inr (i, Part.shortIn)) = binStart A i + p := by
  have hrel := (h.1 (Sum.inr (i, Part.shortIn))).1
  simp only [inst_r_quad, quadRel] at hrel
  omega

/-! ### Displacement is safe

The exchange argument moves a job out of a bin and into the slot that pair `i`'s outer long
job vacates. For that to preserve feasibility the displaced job must still meet its own
deadline, and it does: a bin only ever holds jobs of pairs at least as late as its own
index, and the deadline chain of Definition 2 then puts every short job parked in bin `i`
no earlier than `d_{p,i}`, which is what the vacated slot guarantees. -/

lemma binAt_antitone {k k' : ℕ} (h : k ≤ k') : binAt p q k' ≤ binAt p q k := by
  induction k' with
  | zero =>
    have : k = 0 := by omega
    subst this
    exact le_refl _
  | succ k' ih =>
    by_cases hk : k ≤ k'
    · have h5 := ih hk
      have h6 := binAt_succ p q k'
      have h7 : (0 : ℤ) ≤ (width p q : ℤ) := by positivity
      omega
    · have : k = k' + 1 := by omega
      subst this
      exact le_refl _

/-- A time lies in only one bin. -/
lemma bin_unique (_hq : 0 < q) {k k' : ℕ} {x : ℤ}
    (h1 : binAt p q k ≤ x) (h2 : x < binAt p q k + width p q)
    (h1' : binAt p q k' ≤ x) (h2' : x < binAt p q k' + width p q) : k = k' := by
  by_contra hne
  rcases Nat.lt_or_ge k k' with hlt | hge
  · have hstep : binAt p q k' + width p q ≤ binAt p q k := by
      have h3 : binAt p q k' ≤ binAt p q (k + 1) := binAt_antitone (by omega)
      have h4 := binAt_succ p q k
      omega
    omega
  · have hlt' : k' < k := by omega
    have hstep : binAt p q k + width p q ≤ binAt p q k' := by
      have h3 : binAt p q k ≤ binAt p q (k' + 1) := binAt_antitone (by omega)
      have h4 := binAt_succ p q k'
      omega
    omega

/-- **A short job parked in bin `i` has a deadline no earlier than `d_{p,i}`.** Bin `i`
holds only jobs of pairs `i` or later, and within a pair the long job is the more urgent
(`Aux.dp_le_dq'`), so a job displaced from bin `i` into the slot pair `i`'s outer long job
vacates still meets its deadline. -/
lemma parked_short_deadline {u : (inst A).Schedule} (h : (inst A).Feasible u) (i j : Fin A.N)
    {part : Part} (hpart : part = Part.shortIn ∨ part = Part.shortOut)
    (hbin1 : binStart A i ≤ u (Sum.inr (j, part)))
    (hbin2 : u (Sum.inr (j, part)) < binStart A i + width p q) :
    A.dp i ≤ (inst A).d (Sum.inr (j, part)) := by
  have hq := A.q_pos
  have hneg : u (Sum.inr (j, part)) < 0 := by
    have h0 := binStart_add_width_nonpos A i
    omega
  have hne : part ≠ Part.sep := by rcases hpart with rfl | rfl <;> simp
  rw [binStart_eq_binAt] at hbin1 hbin2
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := quad_in_bin A h j hne hneg
  -- the bin the job lies in is bin `i`
  have hki : k = (i : ℕ) := by
    refine bin_unique (p := p) (q := q) hq hk3 ?_ ?_ hbin2
    · have hlen : (0 : ℤ) < quadLen A p q (j, part) := by
        rcases hpart with rfl | rfl <;> simp only [quadLen] <;> exact_mod_cast hq
      have : (width p q : ℤ) = (p : ℤ) + 2 * q := by simp only [width]; push_cast; ring
      have hqle : (quadLen A p q (j, part) : ℤ) ≤ q := by
        rcases hpart with rfl | rfl <;> simp only [quadLen] <;> exact le_refl _
      omega
    · exact hbin1
  -- so pair `i` is no later than pair `j`
  have hij : (i : ℕ) ≤ (j : ℕ) := by omega
  have hchain : A.dp i ≤ A.dq' j := Aux.dp_le_dq'_of_le A hij
  rcases hpart with rfl | rfl
  · simp only [inst_d_quad, quadDue]
    exact hchain
  · simp only [inst_d_quad, quadDue]
    exact le_trans hchain (A.dq'_le_dq j)

/-! ## 5. From a solution of `AUX(p, q)` to a feasible schedule

Given a schedule solving `A`, park two jobs of each quad in its bin and run the other two
where the pending pair ran. Which two are parked is decided by the pairing condition: if
the long pending job of pair `i` is early, park the *outer* long job and the *inner* short
one, leaving the inner long job — the one carrying `d'_{p,i}` — to inherit its position,
which it meets precisely because the pending job was early. Otherwise park the mirror
image, and the inner short job inherits `d'_{q,i}`, which it meets because the pairing
condition then makes the short pending job early. -/

/-- The job of `A` a quad job stands in for, when it is one of the two that run after `0`.
`none` marks the two that are parked in the bin. This is Definition 4's proper pairing,
read off the solution being transported. -/
def slotOf (t : A.toInstance.Schedule) : Fin A.N × Part → Option A.Job
  | (_, .sep) => none
  | (i, .longIn) => if Aux.LongEarly t i then some (Aux.longJob i) else none
  | (i, .longOut) => if Aux.LongEarly t i then none else some (Aux.longJob i)
  | (i, .shortIn) => if Aux.LongEarly t i then none else some (Aux.shortJob i)
  | (i, .shortOut) => if Aux.LongEarly t i then some (Aux.shortJob i) else none

/-- Where each job of the constructed instance goes: ordinary jobs and the two jobs of
each quad that run after `0` keep the time the solution of `A` gave them; the parked ones
sit exactly at their release times, which is the start of their slot in the bin. -/
def assign (t : A.toInstance.Schedule) : (inst A).Job → Option A.Job :=
  Sum.elim (fun o => some (Aux.ordJob o)) (slotOf A t)

/-- The transported schedule. -/
def lift (t : A.toInstance.Schedule) : (inst A).Schedule := fun x =>
  (assign A t x).elim ((inst A).r x) t

lemma lift_of_none {t : A.toInstance.Schedule} {x : (inst A).Job} (h : assign A t x = none) :
    lift A t x = (inst A).r x := by simp [lift, h, Option.elim]

lemma lift_of_some {t : A.toInstance.Schedule} {x : (inst A).Job} {y : A.Job}
    (h : assign A t x = some y) : lift A t x = t y := by simp [lift, h, Option.elim]

/-- A parked job sits inside its own bin-and-separator block. -/
lemma parked_within (_t : A.toInstance.Schedule) (i : Fin A.N) (part : Part) :
    binStart A i ≤ quadRel A (i, part) ∧
      quadRel A (i, part) + quadLen A p q (i, part) ≤ binStart A i + width p q := by
  have := A.q_pos
  have := A.q_lt_p
  cases part <;> simp only [quadRel, quadLen, width] <;> push_cast <;> omega

/-- A job that keeps its old time stands in for a job of `A` of exactly its own length,
starts no earlier than its release time, and meets its deadline. The deadline is where the
two-deadline trick is spent: the *inner* jobs carry the early deadlines, and they are used
only in the branch in which the corresponding pending job is early. -/
lemma assign_some_spec {t : A.toInstance.Schedule} (ht : Aux.Solves t) {x : (inst A).Job}
    {y : A.Job} (h : assign A t x = some y) :
    (inst A).p x = A.toInstance.p y ∧ (inst A).r x ≤ t y ∧
      t y + (inst A).p x ≤ (inst A).d x := by
  have hnn : ∀ z : A.Job, 0 ≤ t z := Aux.nonneg_of_feasible ht.feasible
  rcases x with o | ⟨i, part⟩
  · simp only [assign, Sum.elim_inl, Option.some.injEq] at h
    subst h
    exact ⟨rfl, (ht.feasible.1 _).1, (ht.feasible.1 _).2⟩
  have hnp : binStart A i + (p : ℤ) + 2 * q ≤ 0 := by
    have h0 := binStart_add_width_nonpos A i
    simp only [width] at h0
    push_cast at h0
    omega
  have hlong := hnn (Aux.longJob i)
  have hshort := hnn (Aux.shortJob i)
  have hdl := (ht.feasible.1 (Aux.longJob i)).2
  have hds := (ht.feasible.1 (Aux.shortJob i)).2
  have hq := A.q_pos
  have hqp := A.q_lt_p
  cases part <;> simp only [assign, Sum.elim_inr, slotOf] at h
  · exact absurd h (by simp)
  · -- the inner long job: used exactly when the long pending job is early, and its
    -- deadline is the early one, which is why that hypothesis is what pays for it
    by_cases he : Aux.LongEarly t i
    · rw [if_pos he, Option.some_inj] at h
      subst h
      refine ⟨rfl, ?_, ?_⟩
      · simp only [inst_r_quad, quadRel]
        omega
      · simpa [Aux.LongEarly, Instance.completion, quadLen, quadDue] using he
    · rw [if_neg he] at h
      exact absurd h (by simp)
  · -- the outer long job, carrying the late deadline
    by_cases he : Aux.LongEarly t i
    · rw [if_pos he] at h
      exact absurd h (by simp)
    · rw [if_neg he, Option.some_inj] at h
      subst h
      refine ⟨rfl, ?_, ?_⟩
      · simp only [inst_r_quad, quadRel]
        omega
      · simpa [Instance.completion, quadLen, quadDue] using hdl
  · -- the inner short job: here the pairing condition makes the short pending job early
    by_cases he : Aux.LongEarly t i
    · rw [if_pos he] at h
      exact absurd h (by simp)
    · rw [if_neg he, Option.some_inj] at h
      subst h
      refine ⟨rfl, ?_, ?_⟩
      · simp only [inst_r_quad, quadRel]
        omega
      · simpa [Aux.ShortEarly, Instance.completion, quadLen, quadDue] using
          ht.not_both_late i he
  · -- the outer short job, carrying the late deadline
    by_cases he : Aux.LongEarly t i
    · rw [if_pos he, Option.some_inj] at h
      subst h
      refine ⟨rfl, ?_, ?_⟩
      · simp only [inst_r_quad, quadRel]
        omega
      · simpa [Instance.completion, quadLen, quadDue] using hds
    · rw [if_neg he] at h
      exact absurd h (by simp)

/-- The job of the constructed instance that stands in for a given job of `A` — the
inverse of `assign` on the jobs that keep their times. -/
def unassign (t : A.toInstance.Schedule) : A.Job → (inst A).Job
  | Sum.inl o => Sum.inl o
  | Sum.inr (Sum.inl i) => Sum.inr (i, if Aux.LongEarly t i then .longIn else .longOut)
  | Sum.inr (Sum.inr i) => Sum.inr (i, if Aux.LongEarly t i then .shortOut else .shortIn)

lemma eq_unassign {t : A.toInstance.Schedule} {x : (inst A).Job} {y : A.Job}
    (h : assign A t x = some y) : x = unassign A t y := by
  rcases x with o | ⟨i, part⟩
  · simp only [assign, Sum.elim_inl, Option.some.injEq] at h
    subst h
    rfl
  cases part <;> simp only [assign, Sum.elim_inr, slotOf] at h
  · exact absurd h (by simp)
  · by_cases he : Aux.LongEarly t i
    · rw [if_pos he, Option.some_inj] at h
      subst h
      simp only [unassign]
      split
      · exact rfl
      · exact absurd he ‹_›
    · rw [if_neg he] at h
      exact absurd h (by simp)
  · by_cases he : Aux.LongEarly t i
    · rw [if_pos he] at h
      exact absurd h (by simp)
    · rw [if_neg he, Option.some_inj] at h
      subst h
      simp only [unassign]
      split
      · exact absurd ‹_› he
      · exact rfl
  · by_cases he : Aux.LongEarly t i
    · rw [if_pos he] at h
      exact absurd h (by simp)
    · rw [if_neg he, Option.some_inj] at h
      subst h
      simp only [unassign]
      split
      · exact absurd ‹_› he
      · exact rfl
  · by_cases he : Aux.LongEarly t i
    · rw [if_pos he, Option.some_inj] at h
      subst h
      simp only [unassign]
      split
      · exact rfl
      · exact absurd he ‹_›
    · rw [if_neg he] at h
      exact absurd h (by simp)

/-- Two different jobs of the constructed instance never stand in for the same job of `A`:
each quad contributes one long and one short. -/
lemma assign_injective {t : A.toInstance.Schedule} {x x' : (inst A).Job} {y : A.Job}
    (h : assign A t x = some y) (h' : assign A t x' = some y) : x = x' :=
  (eq_unassign A h).trans (eq_unassign A h').symm

/-- Which of the five jobs of a quad are parked in the bin: the separator always, and then
either the outer long and inner short job, or the inner long and outer short one. This is
Definition 4's *proper pairing*. -/
def Parked (t : A.toInstance.Schedule) (i : Fin A.N) : Part → Prop
  | .sep => True
  | .longIn => ¬ Aux.LongEarly t i
  | .longOut => Aux.LongEarly t i
  | .shortIn => Aux.LongEarly t i
  | .shortOut => ¬ Aux.LongEarly t i

lemma parked_of_none {t : A.toInstance.Schedule} {i : Fin A.N} {c : Part}
    (h : slotOf A t (i, c) = none) : Parked A t i c := by
  cases c <;> simp_all [slotOf, Parked]

/-- Two parked jobs of the same quad do not overlap: the bin holds one long and one short
job, and the separator takes the rest of the block. -/
lemma parked_disjoint (t : A.toInstance.Schedule) (i : Fin A.N) {a b : Part}
    (ha : Parked A t i a) (hb : Parked A t i b) (hab : a ≠ b) :
    quadRel A (i, a) + quadLen A p q (i, a) ≤ quadRel A (i, b) ∨
      quadRel A (i, b) + quadLen A p q (i, b) ≤ quadRel A (i, a) := by
  have hq := A.q_pos
  have hqp := A.q_lt_p
  cases a <;> cases b <;> simp only [Parked] at ha hb <;>
    first
      | exact absurd rfl hab
      | exact absurd ha hb
      | exact absurd hb ha
      | (simp only [quadRel, quadLen]; omega)

/-- **Lemma 1, forward direction.** A solution to `AUX(p, q)` yields a feasible schedule
for the constructed instance. -/
theorem feasible_lift {t : A.toInstance.Schedule} (ht : Aux.Solves t) :
    (inst A).Feasible (lift A t) := by
  have hnn : ∀ z : A.Job, 0 ≤ t z := Aux.nonneg_of_feasible ht.feasible
  have hnp : ∀ i : Fin A.N, binStart A i + (p : ℤ) + 2 * q ≤ 0 := by
    intro i
    have h0 := binStart_add_width_nonpos A i
    simp only [width] at h0
    push_cast at h0
    omega
  constructor
  · -- every job runs inside its availability interval
    intro x
    rcases hx : assign A t x with _ | y
    · have hval := lift_of_none A hx
      refine ⟨le_of_eq hval.symm, ?_⟩
      simp only [Instance.completion, hval]
      rcases x with o | ⟨i, part⟩
      · simp only [assign, Sum.elim_inl] at hx
        exact absurd hx (by simp)
      · -- a parked job ends before `0`, and every deadline of `A` is non-negative
        have h1 := A.dp'_nonneg i
        have h2 := A.dq'_nonneg i
        have h3 := Aux.dp_nonneg A i
        have h4 := Aux.dq_nonneg A i
        have h5 := hnp i
        cases part <;>
          simp only [inst_r_quad, inst_p_quad, inst_d_quad, quadRel, quadDue, quadLen] <;>
          omega
    · have hval := lift_of_some A hx
      obtain ⟨-, hr, hd⟩ := assign_some_spec A ht hx
      refine ⟨by rw [hval]; exact hr, ?_⟩
      simp only [Instance.completion, hval]
      exact hd
  · -- no two jobs overlap
    intro x x' hxx'
    simp only [Instance.completion]
    rcases hx : assign A t x with _ | y <;> rcases hx' : assign A t x' with _ | y'
    · -- both parked: same quad, or disjoint blocks
      rw [lift_of_none A hx, lift_of_none A hx']
      rcases x with o | ⟨i, part⟩
      · simp only [assign, Sum.elim_inl] at hx
        exact absurd hx (by simp)
      rcases x' with o' | ⟨i', part'⟩
      · simp only [assign, Sum.elim_inl] at hx'
        exact absurd hx' (by simp)
      simp only [assign, Sum.elim_inr] at hx hx'
      by_cases hii : i = i'
      · subst hii
        have hab : part ≠ part' := by rintro rfl; exact hxx' rfl
        simpa only [inst_r_quad, inst_p_quad] using
          parked_disjoint A t i (parked_of_none A hx) (parked_of_none A hx') hab
      · have h1 := parked_within A t i part
        have h2 := parked_within A t i' part'
        rcases binStart_disjoint A hii with h | h
        · left
          simp only [inst_r_quad, inst_p_quad]
          omega
        · right
          simp only [inst_r_quad, inst_p_quad]
          omega
    · -- `x` parked, `x'` keeps its time: everything parked ends by `0`
      left
      rw [lift_of_none A hx, lift_of_some A hx']
      rcases x with o | ⟨i, part⟩
      · simp only [assign, Sum.elim_inl] at hx
        exact absurd hx (by simp)
      have h1 := parked_within A t i part
      have h2 := binStart_add_width_nonpos A i
      have h3 := hnn y'
      simp only [inst_r_quad, inst_p_quad]
      omega
    · -- symmetric
      right
      rw [lift_of_none A hx', lift_of_some A hx]
      rcases x' with o | ⟨i, part⟩
      · simp only [assign, Sum.elim_inl] at hx'
        exact absurd hx' (by simp)
      have h1 := parked_within A t i part
      have h2 := binStart_add_width_nonpos A i
      have h3 := hnn y
      simp only [inst_r_quad, inst_p_quad]
      omega
    · -- both keep their times: they stand in for different jobs of `A`, so the schedule
      -- of `A` already separates them
      rw [lift_of_some A hx, lift_of_some A hx']
      obtain ⟨hp, -, -⟩ := assign_some_spec A ht hx
      obtain ⟨hp', -, -⟩ := assign_some_spec A ht hx'
      have hyy : y ≠ y' := by
        rintro rfl
        exact hxx' (assign_injective A hx hx')
      rw [hp, hp']
      exact ht.feasible.2 y y' hyy

/-- **Lemma 1, forward direction.** A solution to `AUX(p, q)` yields a feasible schedule for
the constructed instance. -/
theorem isYes_of_yes (h : auxProblem p q A) : (inst A).IsYes := by
  obtain ⟨t, ht⟩ := h
  exact ⟨lift A t, feasible_lift A ht⟩

/-! ## 6. From a feasible schedule back to a solution of `AUX(p, q)`

The paper's exchange argument. This is the one place where the construction needs more than
bookkeeping, and the obstruction is real rather than technical: a feasible schedule need
*not* park a proper pairing in each bin. Since `2q ≤ p + q`, both short jobs of a quad fit
in one bin together — the outer at `[tᵢ, tᵢ+q)`, the inner at `[tᵢ+p, tᵢ+p+q)` — leaving a
hole of length `p - q` that no long job fits into. A quad's jobs may also be parked in any
bin of index at most its own, so a single bin can hold jobs of several different pairs. In
such a schedule no job is left after `0` to play the role of a pending job, and reading off
the existing start times cannot produce a schedule for `A`.

The schedule is therefore rewritten first, by induction on `i`: the `i`'th outer long job is
swapped into bin `i`, pushing the short jobs it displaces into the space that long job
vacated after `0`. Two facts make the swap safe. A bin holds at most one long job, since
`2p > p + q`; and the deadlines of pair `i` are ordered against those of pair `i+1` by
`Aux.dp_le_dp'_succ`, `Aux.dq_le_dq'_succ` and `Aux.dp_le_dq'`, so a displaced job lands
somewhere whose deadline it still meets. §3 supplies the geometry underneath: every job
scheduled before `0` lies inside a bin whose index is at most its own (`quad_in_bin`), and
the jobs parked in one bin have total length at most `p + q` (`three_in_bin_le`). -/

/-- Bin `i` holds a **proper pair** of its own quad, in the canonical positions of
Definition 4: either the outer long job at the head of the bin with the inner short job
after it, or the outer short job at the head with the inner long job after it. The other
two jobs of the quad then run after time `0`, and they are the pending pair. -/
def ProperAt (u : (inst A).Schedule) (i : Fin A.N) : Prop :=
  (u (Sum.inr (i, Part.longOut)) = binStart A i ∧
      u (Sum.inr (i, Part.shortIn)) = binStart A i + p ∧
      0 ≤ u (Sum.inr (i, Part.longIn)) ∧ 0 ≤ u (Sum.inr (i, Part.shortOut))) ∨
    (u (Sum.inr (i, Part.shortOut)) = binStart A i ∧
      u (Sum.inr (i, Part.longIn)) = binStart A i + q ∧
      0 ≤ u (Sum.inr (i, Part.longOut)) ∧ 0 ≤ u (Sum.inr (i, Part.shortIn)))

/-- A schedule is **normalized** when every bin holds a proper pair. -/
def Normalized (u : (inst A).Schedule) : Prop := ∀ i : Fin A.N, ProperAt A u i

/-- The bins `0 … k-1` hold proper pairs — the invariant the exchange argument carries
along as it walks the bins from `0` outwards. -/
def NormalizedUpTo (u : (inst A).Schedule) (k : ℕ) : Prop :=
  ∀ i : Fin A.N, (i : ℕ) < k → ProperAt A u i

/-- A bin holding a proper pair is **full**: its two jobs cover it exactly, so nothing else
can be scheduled there. This is what stops a later quad from reaching back into a bin the
exchange has already settled. -/
lemma no_room_in_proper_bin {u : (inst A).Schedule} (h : (inst A).Feasible u) {i : Fin A.N}
    (hp : ProperAt A u i) {x : (inst A).Job}
    (hx1 : binStart A i ≤ u x) (hx2 : u x + (inst A).p x ≤ binStart A i + p + q)
    (hne1 : x ≠ Sum.inr (i, Part.longOut)) (hne2 : x ≠ Sum.inr (i, Part.shortIn))
    (hne3 : x ≠ Sum.inr (i, Part.shortOut)) (hne4 : x ≠ Sum.inr (i, Part.longIn)) :
    False := by
  have hq := A.q_pos
  have hxpos : 0 < (inst A).p x := (inst A).p_pos x
  rcases hp with ⟨h1, h2, -, -⟩ | ⟨h1, h2, -, -⟩
  · -- outer long at the head, inner short after it
    have hs1 := h.2 x _ hne1
    have hs2 := h.2 x _ hne2
    simp only [Instance.completion, inst_p_quad, quadLen, h1, h2] at hs1 hs2
    omega
  · -- outer short at the head, inner long after it
    have hs1 := h.2 x _ hne3
    have hs2 := h.2 x _ hne4
    simp only [Instance.completion, inst_p_quad, quadLen, h1, h2] at hs1 hs2
    omega

/-- A deeper block ends before a shallower one begins. -/
lemma binAt_lt {m k : ℕ} (h : m < k) : binAt p q k + width p q ≤ binAt p q m := by
  induction k with
  | zero => omega
  | succ k ih =>
    have h1 := binAt_succ p q k
    have h2 : (0 : ℤ) ≤ (width p q : ℤ) := by positivity
    by_cases hmk : m < k
    · have := ih hmk
      omega
    · have hmk' : m = k := by omega
      subst hmk'
      omega

/-- Blocks with different indices are disjoint. -/
lemma binAt_block_disjoint {m k : ℕ} (hne : m ≠ k) :
    binAt p q m + width p q ≤ binAt p q k ∨ binAt p q k + width p q ≤ binAt p q m := by
  rcases Nat.lt_or_ge m k with hlt | hge
  · exact Or.inr (binAt_lt hlt)
  · exact Or.inl (binAt_lt (by omega))

/-- The jobs the schedule parks inside bin `k`. -/
noncomputable def binOcc (u : (inst A).Schedule) (k : Fin A.N) : Finset ((inst A).Job) :=
  Finset.univ.filter (fun x =>
    binStart A k ≤ u x ∧ u x + (inst A).p x ≤ binStart A k + p + q)

/-- **Anything that so much as touches bin `k` is parked inside it.** Ordinary jobs run
after time `0`, separators are pinned outside every bin, and a quad job scheduled before
`0` lies inside a single one. So a job outside `binOcc` is clear of the bin altogether —
which is what lets the exchange put something else there. -/
lemma mem_binOcc_of_meets {u : (inst A).Schedule} (h : (inst A).Feasible u) (k : Fin A.N)
    (x : (inst A).Job) (h1 : u x < binStart A k + p + q)
    (h2 : binStart A k < u x + (inst A).p x) : x ∈ binOcc A u k := by
  classical
  have hq := A.q_pos
  have hqp := A.q_lt_p
  have hwidth : (width p q : ℤ) = (p : ℤ) + 2 * q := by
    simp only [width]
    push_cast
    ring
  have hknp := binStart_add_width_nonpos A k
  rw [binStart_eq_binAt] at h1 h2 hknp
  simp only [binOcc, Finset.mem_filter, Finset.mem_univ, true_and, binStart_eq_binAt]
  rcases x with o | ⟨j, part⟩
  · -- an ordinary job runs after `0`, and the bin is before it
    exfalso
    have h0 : 0 ≤ u (Sum.inl o) := le_trans (A.r_nonneg o) (h.1 (Sum.inl o)).1
    omega
  by_cases hsep : part = Part.sep
  · -- the separator of some block, pinned just past that block's bin
    exfalso
    subst hsep
    have hfix := sep_fixed A h j
    rw [binStart_eq_binAt] at hfix
    have hlen : (inst A).p (Sum.inr (j, Part.sep)) = q := rfl
    rw [hfix] at h1 h2
    rw [hlen] at h2
    by_cases hjk : (j : ℕ) = (k : ℕ)
    · rw [hjk] at h1
      omega
    · rcases binAt_block_disjoint (p := p) (q := q) hjk with hd | hd <;> omega
  · -- a quad job: after `0`, or inside exactly one bin
    by_cases hneg : u (Sum.inr (j, part)) < 0
    · obtain ⟨m, hm1, hm2, hm3, hm4⟩ := quad_in_bin A h j hsep hneg
      have hlen : (inst A).p (Sum.inr (j, part)) = quadLen A p q (j, part) := rfl
      rw [hlen] at h2 ⊢
      by_cases hmk : m = (k : ℕ)
      · subst hmk
        exact ⟨hm3, hm4⟩
      · exfalso
        have hpos : (0 : ℤ) < quadLen A p q (j, part) := by
          cases part <;> simp only [quadLen] <;> first | exact_mod_cast hq | omega
        rcases binAt_block_disjoint (p := p) (q := q) hmk with hd | hd <;> omega
    · exfalso
      omega

/-- **Under the invariant, a job of quad `i ≥ k` is either running after time `0` or parked
in a bin whose index lies between `k` and `i`.** The bins below `k` are settled and full, so
nothing can retreat into them; this is what keeps the exchange from undoing its own work. -/
lemma placement_of_invariant {u : (inst A).Schedule} (h : (inst A).Feasible u) {k : ℕ}
    (hup : NormalizedUpTo A u k) (i : Fin A.N) {part : Part} (hpart : part ≠ Part.sep)
    (hik : k ≤ (i : ℕ)) (hneg : u (Sum.inr (i, part)) < 0) :
    ∃ j : ℕ, k ≤ j ∧ j ≤ (i : ℕ) ∧ j < A.N ∧
      binAt p q j ≤ u (Sum.inr (i, part)) ∧
      u (Sum.inr (i, part)) + quadLen A p q (i, part) ≤ binAt p q j + p + q := by
  obtain ⟨j, hj1, hj2, hj3, hj4⟩ := quad_in_bin A h i hpart hneg
  refine ⟨j, ?_, hj1, hj2, hj3, hj4⟩
  by_contra hjk
  push Not at hjk
  -- bin `j` is already settled, and full
  have hji : j ≠ (i : ℕ) := by omega
  have hprop := hup ⟨j, hj2⟩ (by simpa using hjk)
  refine no_room_in_proper_bin A h hprop (x := Sum.inr (i, part)) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [binStart_eq_binAt]
    exact hj3
  · rw [binStart_eq_binAt]
    simpa only [inst_p_quad] using hj4
  all_goals
    intro hc
    exact hji (congrArg Fin.val (congrArg Prod.fst (Sum.inr.inj hc))).symm

/-- **Two jobs that cover a bin exactly leave no room for a third.** -/
lemma no_room_of_cover {u : (inst A).Schedule} (h : (inst A).Feasible u) (i : Fin A.N)
    {x y : (inst A).Job} (hx : u x = binStart A i)
    (hy : u y = binStart A i + (inst A).p x)
    (hcov : (inst A).p x + (inst A).p y = p + q)
    {z : (inst A).Job} (hzx : z ≠ x) (hzy : z ≠ y) (hz1 : binStart A i ≤ u z)
    (hz2 : u z + (inst A).p z ≤ binStart A i + p + q) : False := by
  have hzpos := (inst A).p_pos z
  have h1 := h.2 z x hzx
  have h2 := h.2 z y hzy
  simp only [Instance.completion, hx, hy] at h1 h2
  omega

/-- Once the outer short job sits at the head of bin `k` and the inner long job after it,
the bin is full, so the other two jobs of the quad run after time `0`: bin `k` holds a
proper pair. This is how the exchange recognises that it is already done. -/
lemma properAt_of_shortOut_head {u : (inst A).Schedule} (h : (inst A).Feasible u) {k : ℕ}
    (hup : NormalizedUpTo A u k) (i : Fin A.N) (hik : (i : ℕ) = k)
    (h1 : u (Sum.inr (i, Part.shortOut)) = binStart A i)
    (h2 : u (Sum.inr (i, Part.longIn)) = binStart A i + q) : ProperAt A u i := by
  have hq := A.q_pos
  have hcov : (inst A).p (Sum.inr (i, Part.shortOut)) +
      (inst A).p (Sum.inr (i, Part.longIn)) = p + q := by
    simp only [inst_p_quad, quadLen]
    omega
  have hlen : (inst A).p (Sum.inr (i, Part.shortOut)) = q := rfl
  have key : ∀ part : Part, part ≠ Part.sep → part ≠ Part.shortOut → part ≠ Part.longIn →
      0 ≤ u (Sum.inr (i, part)) := by
    intro part hsep hne1 hne2
    by_contra hneg
    push Not at hneg
    obtain ⟨j, hj1, hj2, hj3, hj4, hj5⟩ :=
      placement_of_invariant A h hup i hsep (le_of_eq hik.symm) hneg
    have hjk : j = (i : ℕ) := by omega
    refine no_room_of_cover A h i h1 (by rw [hlen]; exact h2) hcov
      (z := Sum.inr (i, part)) ?_ ?_ ?_ ?_
    · intro hc
      exact hne1 (congrArg Prod.snd (Sum.inr.inj hc))
    · intro hc
      exact hne2 (congrArg Prod.snd (Sum.inr.inj hc))
    · rw [binStart_eq_binAt, ← hjk]
      exact hj4
    · rw [binStart_eq_binAt, ← hjk]
      simpa only [inst_p_quad] using hj5
  exact Or.inr ⟨h1, h2, key Part.longOut (by simp) (by simp) (by simp),
    key Part.shortIn (by simp) (by simp) (by simp)⟩

/-- The mirror image: the outer long job at the head with the inner short job after it. -/
lemma properAt_of_longOut_head {u : (inst A).Schedule} (h : (inst A).Feasible u) {k : ℕ}
    (hup : NormalizedUpTo A u k) (i : Fin A.N) (hik : (i : ℕ) = k)
    (h1 : u (Sum.inr (i, Part.longOut)) = binStart A i)
    (h2 : u (Sum.inr (i, Part.shortIn)) = binStart A i + p) : ProperAt A u i := by
  have hq := A.q_pos
  have hcov : (inst A).p (Sum.inr (i, Part.longOut)) +
      (inst A).p (Sum.inr (i, Part.shortIn)) = p + q := by
    simp only [inst_p_quad, quadLen]
  have hlen : (inst A).p (Sum.inr (i, Part.longOut)) = p := rfl
  have key : ∀ part : Part, part ≠ Part.sep → part ≠ Part.longOut → part ≠ Part.shortIn →
      0 ≤ u (Sum.inr (i, part)) := by
    intro part hsep hne1 hne2
    by_contra hneg
    push Not at hneg
    obtain ⟨j, hj1, hj2, hj3, hj4, hj5⟩ :=
      placement_of_invariant A h hup i hsep (le_of_eq hik.symm) hneg
    have hjk : j = (i : ℕ) := by omega
    refine no_room_of_cover A h i h1 (by rw [hlen]; exact h2) hcov
      (z := Sum.inr (i, part)) ?_ ?_ ?_ ?_
    · intro hc
      exact hne1 (congrArg Prod.snd (Sum.inr.inj hc))
    · intro hc
      exact hne2 (congrArg Prod.snd (Sum.inr.inj hc))
    · rw [binStart_eq_binAt, ← hjk]
      exact hj4
    · rw [binStart_eq_binAt, ← hjk]
      simpa only [inst_p_quad] using hj5
  exact Or.inl ⟨h1, h2, key Part.longIn (by simp) (by simp) (by simp),
    key Part.shortOut (by simp) (by simp) (by simp)⟩

/-- **With the inner long job pinned at `b + q`, anything else in bin `k` sits exactly at
its head, and is a short job.** So the head of the bin holds at most one job, and swapping
the outer short job of pair `k` into it moves at most two jobs. -/
lemma blocker_at_head {u : (inst A).Schedule} (h : (inst A).Feasible u) (i : Fin A.N)
    (hpin : u (Sum.inr (i, Part.longIn)) = binStart A i + q)
    {y : (inst A).Job} (hy : y ≠ Sum.inr (i, Part.longIn))
    (h1 : u y < binStart A i + q) (h2 : binStart A i < u y + (inst A).p y) :
    u y = binStart A i ∧ (inst A).p y = q := by
  have hq := A.q_pos
  have hqp := A.q_lt_p
  have hin : y ∈ binOcc A u i := by
    refine mem_binOcc_of_meets A h i y (by omega) h2
  simp only [binOcc, Finset.mem_filter, Finset.mem_univ, true_and] at hin
  have hsep := h.2 y _ hy
  simp only [Instance.completion, inst_p_quad, quadLen, hpin] at hsep
  have hlen := inst_lengthsIn A y
  constructor <;> omega

/-- A separator is never parked inside a bin: it sits in the gap just past its own. -/
lemma sep_not_in_bin {u : (inst A).Schedule} (h : (inst A).Feasible u) (i j : Fin A.N)
    (h1 : binStart A i ≤ u (Sum.inr (j, Part.sep)))
    (h2 : u (Sum.inr (j, Part.sep)) + (inst A).p (Sum.inr (j, Part.sep)) ≤
      binStart A i + p + q) : False := by
  have hq := A.q_pos
  have hfix := sep_fixed A h j
  rw [binStart_eq_binAt] at hfix
  have hlen : (inst A).p (Sum.inr (j, Part.sep)) = q := rfl
  rw [hlen, hfix] at h2
  rw [hfix] at h1
  rw [binStart_eq_binAt] at h1 h2
  have hwidth : (width p q : ℤ) = (p : ℤ) + 2 * q := by
    simp only [width]
    push_cast
    ring
  by_cases hij : (j : ℕ) = (i : ℕ)
  · rw [hij] at h1 h2
    omega
  · rcases binAt_block_disjoint (p := p) (q := q) hij with hd | hd <;> omega

/-- Everything parked in bin `i` belongs to a pair of index at least `i`. -/
lemma parked_index_ge {u : (inst A).Schedule} (h : (inst A).Feasible u) (i j : Fin A.N)
    {part : Part} (hpart : part ≠ Part.sep)
    (h1 : binStart A i ≤ u (Sum.inr (j, part)))
    (h2 : u (Sum.inr (j, part)) + quadLen A p q (j, part) ≤ binStart A i + p + q) :
    (i : ℕ) ≤ (j : ℕ) := by
  have hq := A.q_pos
  have hqp := A.q_lt_p
  have hknp := binStart_add_width_nonpos A i
  have hwidth : (width p q : ℤ) = (p : ℤ) + 2 * q := by
    simp only [width]
    push_cast
    ring
  have hpos : (0 : ℤ) < quadLen A p q (j, part) := by
    cases part <;> simp only [quadLen] <;> first | exact_mod_cast hq | omega
  have hneg : u (Sum.inr (j, part)) < 0 := by
    rw [binStart_eq_binAt] at h2 hknp
    omega
  obtain ⟨m, hm1, hm2, hm3, hm4⟩ := quad_in_bin A h j hpart hneg
  have hmi : m = (i : ℕ) := by
    refine bin_unique (p := p) (q := q) hq hm3 ?_ ?_ ?_
    · omega
    · rw [binStart_eq_binAt] at h1
      exact h1
    · rw [binStart_eq_binAt] at h2
      omega
  omega

/-- `ProperAt` only looks at the jobs of its own quad. -/
lemma properAt_congr {u u' : (inst A).Schedule} (j : Fin A.N)
    (hagree : ∀ part, u' (Sum.inr (j, part)) = u (Sum.inr (j, part)))
    (hp : ProperAt A u j) : ProperAt A u' j := by
  simp only [ProperAt, hagree]
  exact hp

/-- Every quad job is released before time `0`. -/
lemma quadRel_nonpos (j : Fin A.N) (part : Part) : quadRel A (j, part) ≤ 0 := by
  have hq := A.q_pos
  have hqp := A.q_lt_p
  have := binStart_add_width_nonpos A j
  simp only [width] at this
  push_cast at this
  cases part <;> simp only [quadRel] <;> omega

/-- Two quad jobs with different parts are different jobs. Stated because `(inst A).Job`
is a structure projection, so `simp` will not see through it to `Sum.inr`. -/
lemma quadJob_ne {i j : Fin A.N} {a b : Part} (hab : a ≠ b) :
    (Sum.inr (i, a) : (inst A).Job) ≠ Sum.inr (j, b) :=
  fun hc => hab (congrArg Prod.snd (Sum.inr.inj hc))

/-- **Case 1 of the exchange step.** The inner long job of pair `k` is parked in bin `k`.
It is then pinned against the far end of it, so only a short job can sit at the bin's head,
and moving pair `k`'s outer short job there settles the bin — displacing at most one job,
which belongs to a later pair and so still meets its deadline in the slot that opens up. -/
lemma exchange_innerLong {u : (inst A).Schedule} (h : (inst A).Feasible u) {k : ℕ}
    (hup : NormalizedUpTo A u k) (i : Fin A.N) (hik : (i : ℕ) = k)
    (hneg : u (Sum.inr (i, Part.longIn)) < 0) :
    ∃ u' : (inst A).Schedule, (inst A).Feasible u' ∧ ProperAt A u' i ∧
      (∀ j : Fin A.N, (j : ℕ) < k → ProperAt A u' j) := by
  classical
  have hq := A.q_pos
  have hqp := A.q_lt_p
  have hbneg : binStart A i + (p : ℤ) + q < 0 := by
    have := binStart_add_width_nonpos A i
    simp only [width] at this
    push_cast at this
    omega
  obtain ⟨m, hm1, hm2, hm3, hm4, hm5⟩ :=
    placement_of_invariant A h hup i (by decide) (le_of_eq hik.symm) hneg
  have hmk : m = (i : ℕ) := by omega
  subst hmk
  rw [← binStart_eq_binAt] at hm4 hm5
  have hpin : u (Sum.inr (i, Part.longIn)) = binStart A i + q :=
    innerLong_forced A h i (by simpa only [quadLen] using hm5)
  by_cases hqo : u (Sum.inr (i, Part.shortOut)) = binStart A i
  · exact ⟨u, h, properAt_of_shortOut_head A h hup i hik hqo hpin, fun j hj => hup j hj⟩
  have hqopos : 0 ≤ u (Sum.inr (i, Part.shortOut)) := by
    by_contra hc
    push Not at hc
    obtain ⟨m', hm1', hm2', hm3', hm4', hm5'⟩ :=
      placement_of_invariant A h hup i (by decide) (le_of_eq hik.symm) hc
    have hmk' : m' = (i : ℕ) := by omega
    subst hmk'
    rw [← binStart_eq_binAt] at hm4' hm5'
    have hsep := h.2 (Sum.inr (i, Part.shortOut)) (Sum.inr (i, Part.longIn))
      (quadJob_ne A (by decide))
    simp only [Instance.completion, inst_p_quad, quadLen, hpin] at hsep
    simp only [quadLen] at hm5'
    exact hqo (by omega)
  have hqodue := (h.1 (Sum.inr (i, Part.shortOut))).2
  simp only [Instance.completion, inst_p_quad, inst_d_quad, quadLen, quadDue] at hqodue
  have hqorel : (inst A).r (Sum.inr (i, Part.shortOut)) = binStart A i := rfl
  have hqolen : (inst A).p (Sum.inr (i, Part.shortOut)) = q := rfl
  have hdqnn := Aux.dq_nonneg A i
  by_cases hblk : ∃ y : (inst A).Job, y ≠ Sum.inr (i, Part.longIn) ∧
      y ≠ Sum.inr (i, Part.shortOut) ∧ u y < binStart A i + q ∧
      binStart A i < u y + (inst A).p y
  · obtain ⟨y, hy1, hy2, hy3, hy4⟩ := hblk
    obtain ⟨hyb, hylen⟩ := blocker_at_head A h i hpin hy1 hy3 hy4
    have hyin : binStart A i ≤ u y ∧ u y + (inst A).p y ≤ binStart A i + p + q := by
      rw [hyb, hylen]; omega
    rcases y with o | ⟨j, part⟩
    · exact absurd (le_trans (A.r_nonneg o) (h.1 (Sum.inl o)).1) (by rw [hyb]; omega)
    have hpart : part ≠ Part.sep := by
      rintro rfl
      exact sep_not_in_bin A h i j hyin.1 hyin.2
    have hji : (i : ℕ) ≤ (j : ℕ) :=
      parked_index_ge A h i j hpart hyin.1 (by simpa only [inst_p_quad] using hyin.2)
    have hshort : part = Part.shortIn ∨ part = Part.shortOut := by
      cases part <;> simp only [inst_p_quad, quadLen] at hylen <;> simp_all
    have hjk : (i : ℕ) < (j : ℕ) := by
      rcases Nat.eq_or_lt_of_le hji with heq | hlt
      · exfalso
        have hij : j = i := Fin.ext heq.symm
        subst hij
        rcases hshort with rfl | rfl
        · have hrel := (h.1 (Sum.inr (j, Part.shortIn))).1
          simp only [inst_r_quad, quadRel] at hrel
          omega
        · exact hy2 rfl
      · exact hlt
    have hydue : u (Sum.inr (i, Part.shortOut)) + (inst A).p (Sum.inr (j, part)) ≤
        (inst A).d (Sum.inr (j, part)) := by
      have hchain := Aux.dq_le_dq'_of_lt A ((j : ℕ) - (i : ℕ) - 1) i j (by omega)
      rw [hylen]
      rcases hshort with rfl | rfl
      · simp only [inst_d_quad, quadDue]
        omega
      · have := A.dq'_le_dq j
        simp only [inst_d_quad, quadDue]
        omega
    have hrely : (inst A).r (Sum.inr (j, part)) ≤ u (Sum.inr (i, Part.shortOut)) := by
      have := quadRel_nonpos A j part
      simp only [inst_r_quad]
      omega
    set u' : (inst A).Schedule := fun x =>
      if x = Sum.inr (i, Part.shortOut) then binStart A i
      else if x = Sum.inr (j, part) then u (Sum.inr (i, Part.shortOut)) else u x with hu'
    have hv1 : u' (Sum.inr (i, Part.shortOut)) = binStart A i := by
      simp only [hu']
      exact if_pos rfl
    have hv2 : u' (Sum.inr (j, part)) = u (Sum.inr (i, Part.shortOut)) := by
      simp only [hu']
      rw [if_neg hy2]
      exact if_pos rfl
    have hv3 : ∀ z : (inst A).Job, z ≠ Sum.inr (i, Part.shortOut) →
        z ≠ Sum.inr (j, part) → u' z = u z := by
      intro z hz1 hz2
      simp only [hu']
      rw [if_neg hz1, if_neg hz2]
    have hfeas : (inst A).Feasible u' := by
      refine Instance.feasible_of_move_two h hv3 ?_ ?_ ?_ ?_ ?_
      · refine ⟨by rw [hv1]; exact le_of_eq hqorel, ?_⟩
        simp only [Instance.completion, hv1, hqolen, inst_d_quad, quadDue]
        omega
      · refine ⟨by rw [hv2]; exact hrely, ?_⟩
        simp only [Instance.completion, hv2]
        exact hydue
      · left
        simp only [Instance.completion, hv1, hv2, hqolen]
        omega
      · intro z hz1 hz2
        simp only [Instance.completion, hv1, hqolen]
        by_contra hc
        push Not at hc
        obtain ⟨hc1, hc2⟩ := hc
        have hzpI : z ≠ Sum.inr (i, Part.longIn) := by
          rintro rfl
          omega
        obtain ⟨hzb, hzlen⟩ := blocker_at_head A h i hpin hzpI (by omega) (by omega)
        have hsep2 := h.2 z (Sum.inr (j, part)) hz2
        simp only [Instance.completion, hzb, hyb, hzlen, hylen] at hsep2
        omega
      · intro z hz1 hz2
        have hsep2 := h.2 z (Sum.inr (i, Part.shortOut)) hz1
        simp only [Instance.completion, hv2, hqolen, hylen] at hsep2 ⊢
        omega
    have hpres : ∀ (jj : Fin A.N), (jj : ℕ) < k → ProperAt A u' jj := by
      intro jj hjj
      refine properAt_congr A jj (fun prt => ?_) (hup jj hjj)
      refine hv3 _ ?_ ?_
      · intro hc
        have h0 : jj = i := congrArg Prod.fst (Sum.inr.inj hc)
        have := congrArg Fin.val h0
        omega
      · intro hc
        have h0 : jj = j := congrArg Prod.fst (Sum.inr.inj hc)
        have := congrArg Fin.val h0
        omega
    refine ⟨u', hfeas, ?_, hpres⟩
    refine properAt_of_shortOut_head A hfeas hpres i hik hv1 ?_
    rw [hv3 _ (quadJob_ne A (by decide)) (fun hc =>
      hy1 (by rw [← hc])), hpin]
  · push Not at hblk
    set u' : (inst A).Schedule := fun x =>
      if x = Sum.inr (i, Part.shortOut) then binStart A i else u x with hu'
    have hv1 : u' (Sum.inr (i, Part.shortOut)) = binStart A i := by
      simp only [hu']
      exact if_pos rfl
    have hv3 : ∀ z : (inst A).Job, z ≠ Sum.inr (i, Part.shortOut) → u' z = u z := by
      intro z hz
      simp only [hu']
      rw [if_neg hz]
    have hfeas : (inst A).Feasible u' := by
      refine Instance.feasible_of_move_one h _ hv3 ?_ ?_
      · refine ⟨by rw [hv1]; exact le_of_eq hqorel, ?_⟩
        simp only [Instance.completion, hv1, hqolen, inst_d_quad, quadDue]
        omega
      · intro z hz
        simp only [Instance.completion, hv1, hqolen]
        by_contra hc
        push Not at hc
        obtain ⟨hc1, hc2⟩ := hc
        have hzpI : z ≠ Sum.inr (i, Part.longIn) := by
          rintro rfl
          omega
        exact absurd (hblk z hzpI hz (by omega)) (by omega)
    have hpres : ∀ (jj : Fin A.N), (jj : ℕ) < k → ProperAt A u' jj := by
      intro jj hjj
      refine properAt_congr A jj (fun prt => ?_) (hup jj hjj)
      refine hv3 _ ?_
      intro hc
      have h0 : jj = i := congrArg Prod.fst (Sum.inr.inj hc)
      have := congrArg Fin.val h0
      omega
    refine ⟨u', hfeas, ?_, hpres⟩
    refine properAt_of_shortOut_head A hfeas hpres i hik hv1 ?_
    rw [hv3 _ (quadJob_ne A (by decide)), hpin]

/-- **Case 2 of the exchange step.** Both the outer long job and the inner short job of
pair `k` are parked in bin `k`. Then they are already in the canonical positions — the
inner one is pinned against the far end, and the outer one has nowhere to sit but the head
— so the bin already holds a proper pair and nothing needs to move. -/
lemma exchange_bothIn {u : (inst A).Schedule} (h : (inst A).Feasible u) {k : ℕ}
    (hup : NormalizedUpTo A u k) (i : Fin A.N) (hik : (i : ℕ) = k)
    (hpO : u (Sum.inr (i, Part.longOut)) < 0)
    (hqI : u (Sum.inr (i, Part.shortIn)) < 0) : ProperAt A u i := by
  have hq := A.q_pos
  have hqp := A.q_lt_p
  obtain ⟨m, hm1, hm2, hm3, hm4, hm5⟩ :=
    placement_of_invariant A h hup i (by decide) (le_of_eq hik.symm) hpO
  have hmk : m = (i : ℕ) := by omega
  subst hmk
  rw [← binStart_eq_binAt] at hm4 hm5
  obtain ⟨m', hm1', hm2', hm3', hm4', hm5'⟩ :=
    placement_of_invariant A h hup i (by decide) (le_of_eq hik.symm) hqI
  have hmk' : m' = (i : ℕ) := by omega
  subst hmk'
  rw [← binStart_eq_binAt] at hm4' hm5'
  -- the inner short job is pinned against the far end
  have hpinS : u (Sum.inr (i, Part.shortIn)) = binStart A i + p :=
    innerShort_forced A h i (by simpa only [quadLen] using hm5')
  -- and then the outer long job has nowhere to sit but the head
  have hsep := h.2 (Sum.inr (i, Part.longOut)) (Sum.inr (i, Part.shortIn))
    (quadJob_ne A (by decide))
  simp only [Instance.completion, inst_p_quad, quadLen, hpinS] at hsep
  simp only [quadLen] at hm4 hm5
  exact properAt_of_longOut_head A h hup i hik (by omega) hpinS

/-- **Case 3 of the exchange step.** The outer long job of pair `k` is parked in bin `k`
but the inner short job is not. The long job takes `p` of the bin, so at most one short job
sits beside it; move the long job to the head, bring the inner short job in behind it, and
send whatever was beside it into the slot the inner short job vacates. -/
lemma exchange_longOutIn {u : (inst A).Schedule} (h : (inst A).Feasible u) {k : ℕ}
    (hup : NormalizedUpTo A u k) (i : Fin A.N) (hik : (i : ℕ) = k)
    (hpO : u (Sum.inr (i, Part.longOut)) < 0)
    (hqI : 0 ≤ u (Sum.inr (i, Part.shortIn))) :
    ∃ u' : (inst A).Schedule, (inst A).Feasible u' ∧ ProperAt A u' i ∧
      (∀ j : Fin A.N, (j : ℕ) < k → ProperAt A u' j) := by
  classical
  have hq := A.q_pos
  have hqp := A.q_lt_p
  have hbneg : binStart A i + (p : ℤ) + q < 0 := by
    have := binStart_add_width_nonpos A i
    simp only [width] at this
    push_cast at this
    omega
  obtain ⟨m, hm1, hm2, hm3, hm4, hm5⟩ :=
    placement_of_invariant A h hup i (by decide) (le_of_eq hik.symm) hpO
  have hmk : m = (i : ℕ) := by omega
  subst hmk
  rw [← binStart_eq_binAt] at hm4 hm5
  simp only [quadLen] at hm5
  have hdp := Aux.dp_nonneg A i
  have hdq' := A.dq'_nonneg i
  have hqIdue := (h.1 (Sum.inr (i, Part.shortIn))).2
  simp only [Instance.completion, inst_p_quad, inst_d_quad, quadLen, quadDue] at hqIdue
  have hpOlen : (inst A).p (Sum.inr (i, Part.longOut)) = p := rfl
  have hqIlen : (inst A).p (Sum.inr (i, Part.shortIn)) = q := rfl
  have hqIne : (Sum.inr (i, Part.shortIn) : (inst A).Job) ≠ Sum.inr (i, Part.longOut) :=
    quadJob_ne A (by decide)
  by_cases hblk : ∃ y : (inst A).Job, y ≠ Sum.inr (i, Part.longOut) ∧
      u y < binStart A i + p + q ∧ binStart A i < u y + (inst A).p y
  · obtain ⟨y, hy1, hy2, hy3⟩ := hblk
    have hyin : y ∈ binOcc A u i := mem_binOcc_of_meets A h i y hy2 hy3
    simp only [binOcc, Finset.mem_filter, Finset.mem_univ, true_and] at hyin
    have hyqI : y ≠ Sum.inr (i, Part.shortIn) := by
      rintro rfl
      omega
    -- the long job takes `p` of the bin, so what is beside it is short
    have hylen : (inst A).p y = q := by
      have hsep := h.2 y (Sum.inr (i, Part.longOut)) hy1
      simp only [Instance.completion, hpOlen] at hsep
      have hlen := inst_lengthsIn A y
      omega
    -- and it belongs to a pair no earlier than `k`, so it survives the move
    have hydue : u (Sum.inr (i, Part.shortIn)) + (inst A).p y ≤ (inst A).d y := by
      rcases y with o | ⟨j, part⟩
      · exact absurd (le_trans (A.r_nonneg o) (h.1 (Sum.inl o)).1) (by omega)
      have hpart : part ≠ Part.sep := by
        rintro rfl
        exact sep_not_in_bin A h i j hyin.1 hyin.2
      have hji : (i : ℕ) ≤ (j : ℕ) :=
        parked_index_ge A h i j hpart hyin.1 (by simpa only [inst_p_quad] using hyin.2)
      have hshort : part = Part.shortIn ∨ part = Part.shortOut := by
        cases part <;> simp only [inst_p_quad, quadLen] at hylen <;> simp_all
      rw [hylen]
      rcases Nat.eq_or_lt_of_le hji with heq | hlt
      · have hij : j = i := Fin.ext heq.symm
        subst hij
        rcases hshort with rfl | rfl
        · exact absurd rfl hyqI
        · simp only [inst_d_quad, quadDue]
          have := A.dq'_le_dq j
          omega
      · have hchain := Aux.dq_le_dq'_of_lt A ((j : ℕ) - (i : ℕ) - 1) i j (by omega)
        have := A.dq'_le_dq i
        rcases hshort with rfl | rfl
        · simp only [inst_d_quad, quadDue]
          omega
        · have := A.dq'_le_dq j
          simp only [inst_d_quad, quadDue]
          omega
    have hyrel : (inst A).r y ≤ u (Sum.inr (i, Part.shortIn)) := by
      rcases y with o | ⟨j, part⟩
      · exact absurd (le_trans (A.r_nonneg o) (h.1 (Sum.inl o)).1) (by omega)
      · have := quadRel_nonpos A j part
        simp only [inst_r_quad]
        omega
    set u' : (inst A).Schedule := fun x =>
      if x = Sum.inr (i, Part.longOut) then binStart A i
      else if x = Sum.inr (i, Part.shortIn) then binStart A i + p
      else if x = y then u (Sum.inr (i, Part.shortIn)) else u x with hu'
    have hv1 : u' (Sum.inr (i, Part.longOut)) = binStart A i := by
      simp only [hu']
      split_ifs <;> first | rfl | exact absurd rfl ‹_›
    have hv2 : u' (Sum.inr (i, Part.shortIn)) = binStart A i + p := by
      simp only [hu']
      split_ifs <;> first | rfl | exact absurd rfl ‹_› | simp_all
    have hv3 : u' y = u (Sum.inr (i, Part.shortIn)) := by
      simp only [hu']
      split_ifs <;> first | rfl | exact absurd rfl ‹_› | simp_all
    have hv4 : ∀ z : (inst A).Job, z ≠ Sum.inr (i, Part.longOut) →
        z ≠ Sum.inr (i, Part.shortIn) → z ≠ y → u' z = u z := by
      intro z h1 h2 h3
      simp only [hu']
      rw [if_neg h1, if_neg h2, if_neg h3]
    have hfeas : (inst A).Feasible u' := by
      refine Instance.feasible_of_move' h
        (fun x => x = Sum.inr (i, Part.longOut) ∨ x = Sum.inr (i, Part.shortIn) ∨ x = y)
        ?_ ?_ ?_ ?_
      · rintro z hz
        exact hv4 z (fun hc => hz (Or.inl hc)) (fun hc => hz (Or.inr (Or.inl hc)))
          (fun hc => hz (Or.inr (Or.inr hc)))
      · rintro x (rfl | rfl | rfl)
        · refine ⟨by rw [hv1]; exact le_refl _, ?_⟩
          simp only [Instance.completion, hv1, hpOlen, inst_d_quad, quadDue]
          omega
        · refine ⟨by rw [hv2]; exact le_refl _, ?_⟩
          simp only [Instance.completion, hv2, hqIlen, inst_d_quad, quadDue]
          omega
        · refine ⟨by rw [hv3]; exact hyrel, ?_⟩
          simp only [Instance.completion, hv3]
          exact hydue
      · rintro x (rfl | rfl | rfl) z (rfl | rfl | rfl) hxz <;>
          first
            | exact absurd rfl hxz
            | (simp only [Instance.completion, hv1, hv2, hv3, hpOlen, hqIlen, hylen]
               omega)
      · rintro x (rfl | rfl | rfl) z hz
        · simp only [Instance.completion, hv1, hpOlen]
          by_contra hc
          push Not at hc
          exact hz (Or.inr (Or.inr (by
            by_contra hzy
            have hzin := mem_binOcc_of_meets A h i z (by omega) (by omega)
            simp only [binOcc, Finset.mem_filter, Finset.mem_univ, true_and] at hzin
            have hsum := three_in_bin_le A h (fun hc2 => hy1 hc2.symm)
              (fun hc2 => hz (Or.inl hc2.symm)) (Ne.symm hzy)
              ⟨hm4, by simp only [Instance.completion, hpOlen]; omega⟩ hyin hzin
            have hzpos := (inst A).p_pos z
            rw [hpOlen, hylen] at hsum
            omega)))
        · simp only [Instance.completion, hv2, hqIlen]
          by_contra hc
          push Not at hc
          exact hz (Or.inr (Or.inr (by
            by_contra hzy
            have hzin := mem_binOcc_of_meets A h i z (by omega) (by omega)
            simp only [binOcc, Finset.mem_filter, Finset.mem_univ, true_and] at hzin
            have hsum := three_in_bin_le A h (fun hc2 => hy1 hc2.symm)
              (fun hc2 => hz (Or.inl hc2.symm)) (Ne.symm hzy)
              ⟨hm4, by simp only [Instance.completion, hpOlen]; omega⟩ hyin hzin
            have hzpos := (inst A).p_pos z
            rw [hpOlen, hylen] at hsum
            omega)))
        · have hsep2 := h.2 z (Sum.inr (i, Part.shortIn))
            (fun hc => hz (Or.inr (Or.inl hc)))
          simp only [Instance.completion, hv3, hqIlen, hylen] at hsep2 ⊢
          omega
    have hpres : ∀ (jj : Fin A.N), (jj : ℕ) < k → ProperAt A u' jj := by
      intro jj hjj
      refine properAt_congr A jj (fun prt => ?_) (hup jj hjj)
      refine hv4 _ ?_ ?_ ?_
      · intro hc
        have h0 : jj = i := congrArg Prod.fst (Sum.inr.inj hc)
        have := congrArg Fin.val h0
        omega
      · intro hc
        have h0 : jj = i := congrArg Prod.fst (Sum.inr.inj hc)
        have := congrArg Fin.val h0
        omega
      · rintro rfl
        have hpartne : prt ≠ Part.sep := by
          rintro rfl
          exact sep_not_in_bin A h i jj hyin.1 hyin.2
        have := parked_index_ge A h i jj hpartne hyin.1
          (by simpa only [inst_p_quad] using hyin.2)
        omega
    exact ⟨u', hfeas, properAt_of_longOut_head A hfeas hpres i hik hv1 hv2, hpres⟩
  · push Not at hblk
    set u' : (inst A).Schedule := fun x =>
      if x = Sum.inr (i, Part.longOut) then binStart A i
      else if x = Sum.inr (i, Part.shortIn) then binStart A i + p else u x with hu'
    have hv1 : u' (Sum.inr (i, Part.longOut)) = binStart A i := by
      simp only [hu']
      split_ifs <;> first | rfl | exact absurd rfl ‹_›
    have hv2 : u' (Sum.inr (i, Part.shortIn)) = binStart A i + p := by
      simp only [hu']
      split_ifs <;> first | rfl | exact absurd rfl ‹_› | simp_all
    have hv4 : ∀ z : (inst A).Job, z ≠ Sum.inr (i, Part.longOut) →
        z ≠ Sum.inr (i, Part.shortIn) → u' z = u z := by
      intro z h1 h2
      simp only [hu']
      rw [if_neg h1, if_neg h2]
    have hfeas : (inst A).Feasible u' := by
      refine Instance.feasible_of_move' h
        (fun x => x = Sum.inr (i, Part.longOut) ∨ x = Sum.inr (i, Part.shortIn)) ?_ ?_ ?_ ?_
      · rintro z hz
        exact hv4 z (fun hc => hz (Or.inl hc)) (fun hc => hz (Or.inr hc))
      · rintro x (rfl | rfl)
        · refine ⟨by rw [hv1]; exact le_refl _, ?_⟩
          simp only [Instance.completion, hv1, hpOlen, inst_d_quad, quadDue]
          omega
        · refine ⟨by rw [hv2]; exact le_refl _, ?_⟩
          simp only [Instance.completion, hv2, hqIlen, inst_d_quad, quadDue]
          omega
      · rintro x (rfl | rfl) z (rfl | rfl) hxz <;>
          first
            | exact absurd rfl hxz
            | (simp only [Instance.completion, hv1, hv2, hpOlen, hqIlen]
               omega)
      · rintro x (rfl | rfl) z hz
        · simp only [Instance.completion, hv1, hpOlen]
          by_contra hc
          push Not at hc
          exact absurd (hblk z (fun hc2 => hz (Or.inl hc2)) (by omega)) (by omega)
        · simp only [Instance.completion, hv2, hqIlen]
          by_contra hc
          push Not at hc
          exact absurd (hblk z (fun hc2 => hz (Or.inl hc2)) (by omega)) (by omega)
    have hpres : ∀ (jj : Fin A.N), (jj : ℕ) < k → ProperAt A u' jj := by
      intro jj hjj
      refine properAt_congr A jj (fun prt => ?_) (hup jj hjj)
      refine hv4 _ ?_ ?_ <;>
        · intro hc
          have h0 : jj = i := congrArg Prod.fst (Sum.inr.inj hc)
          have := congrArg Fin.val h0
          omega
    exact ⟨u', hfeas, properAt_of_longOut_head A hfeas hpres i hik hv1 hv2, hpres⟩

/-- **Case 4 of the exchange step.** Neither long job of pair `k` is parked in bin `k`, but
some *other* long job is. That job belongs to a later pair, so it can be sent to the slot
pair `k`'s outer long job vacates, and pair `k`'s own jobs take the bin. -/
lemma exchange_foreignLong {u : (inst A).Schedule} (h : (inst A).Feasible u) {k : ℕ}
    (hup : NormalizedUpTo A u k) (i : Fin A.N) (hik : (i : ℕ) = k)
    (hpI : 0 ≤ u (Sum.inr (i, Part.longIn)))
    (hpO : 0 ≤ u (Sum.inr (i, Part.longOut)))
    (hqI : u (Sum.inr (i, Part.shortIn)) < 0)
    (L : (inst A).Job) (hL1 : L ≠ Sum.inr (i, Part.longOut))
    (hLlen : (inst A).p L = p)
    (hLin : binStart A i ≤ u L ∧ u L + (inst A).p L ≤ binStart A i + p + q) :
    ∃ u' : (inst A).Schedule, (inst A).Feasible u' ∧ ProperAt A u' i ∧
      (∀ j : Fin A.N, (j : ℕ) < k → ProperAt A u' j) := by
  classical
  have hq := A.q_pos
  have hqp := A.q_lt_p
  have hbneg : binStart A i + (p : ℤ) + q < 0 := by
    have := binStart_add_width_nonpos A i
    simp only [width] at this
    push_cast at this
    omega
  obtain ⟨m, hm1, hm2, hm3, hm4, hm5⟩ :=
    placement_of_invariant A h hup i (by decide) (le_of_eq hik.symm) hqI
  have hmk : m = (i : ℕ) := by omega
  subst hmk
  rw [← binStart_eq_binAt] at hm4 hm5
  simp only [quadLen] at hm5
  -- the inner short job is pinned against the far end, so the long job sits at the head
  have hpinS : u (Sum.inr (i, Part.shortIn)) = binStart A i + p :=
    innerShort_forced A h i (by simpa only [quadLen] using hm5)
  have hLne : L ≠ Sum.inr (i, Part.shortIn) := by
    rintro rfl
    have hc := hLin.2
    rw [hLlen, hpinS] at hc
    omega
  have hLhead : u L = binStart A i := by
    have hsep := h.2 L (Sum.inr (i, Part.shortIn)) hLne
    simp only [Instance.completion, inst_p_quad, quadLen, hpinS, hLlen] at hsep
    rw [hLlen] at hLin
    omega
  -- the foreign long job belongs to a later pair, so it survives the swap
  have hLdue : u (Sum.inr (i, Part.longOut)) + (inst A).p L ≤ (inst A).d L := by
    rcases L with o | ⟨j, part⟩
    · exact absurd (le_trans (A.r_nonneg o) (h.1 (Sum.inl o)).1) (by rw [hLhead]; omega)
    have hpart : part ≠ Part.sep := by
      rintro rfl
      exact sep_not_in_bin A h i j hLin.1 hLin.2
    have hji : (i : ℕ) ≤ (j : ℕ) :=
      parked_index_ge A h i j hpart hLin.1 (by simpa only [inst_p_quad] using hLin.2)
    have hlong : part = Part.longIn ∨ part = Part.longOut := by
      cases part <;> simp only [inst_p_quad, quadLen] at hLlen <;> simp_all
    have hpOdue := (h.1 (Sum.inr (i, Part.longOut))).2
    simp only [Instance.completion, inst_p_quad, inst_d_quad, quadLen, quadDue] at hpOdue
    rw [hLlen]
    rcases Nat.eq_or_lt_of_le hji with heq | hlt
    · exfalso
      have hij : j = i := Fin.ext heq.symm
      subst hij
      rcases hlong with rfl | rfl
      · exact absurd hLhead (by omega)
      · exact hL1 rfl
    · have hchain := Aux.dp_le_dp'_of_lt A ((j : ℕ) - (i : ℕ) - 1) i j (by omega)
      rcases hlong with rfl | rfl
      · simp only [inst_d_quad, quadDue]
        omega
      · have := A.dp'_le_dp j
        simp only [inst_d_quad, quadDue]
        omega
  have hLrel : (inst A).r L ≤ u (Sum.inr (i, Part.longOut)) := by
    rcases L with o | ⟨j, part⟩
    · exact absurd (le_trans (A.r_nonneg o) (h.1 (Sum.inl o)).1) (by rw [hLhead]; omega)
    · have := quadRel_nonpos A j part
      simp only [inst_r_quad]
      omega
  have hdp := Aux.dp_nonneg A i
  have hpOlen : (inst A).p (Sum.inr (i, Part.longOut)) = p := rfl
  -- swap pair `k`'s outer long job with the foreign one
  set u' : (inst A).Schedule := fun x =>
    if x = Sum.inr (i, Part.longOut) then binStart A i
    else if x = L then u (Sum.inr (i, Part.longOut)) else u x with hu'
  have hv1 : u' (Sum.inr (i, Part.longOut)) = binStart A i := by
    simp only [hu']
    split_ifs <;> first | rfl | exact absurd rfl ‹_›
  have hv2 : u' L = u (Sum.inr (i, Part.longOut)) := by
    simp only [hu']
    split_ifs <;> first | rfl | exact absurd rfl ‹_› | simp_all
  have hv3 : ∀ z : (inst A).Job, z ≠ Sum.inr (i, Part.longOut) → z ≠ L → u' z = u z := by
    intro z h1 h2
    simp only [hu']
    rw [if_neg h1, if_neg h2]
  have hfeas : (inst A).Feasible u' := by
    refine Instance.feasible_of_move_two h hv3 ?_ ?_ ?_ ?_ ?_
    · refine ⟨by rw [hv1]; exact le_refl _, ?_⟩
      simp only [Instance.completion, hv1, hpOlen, inst_d_quad, quadDue]
      omega
    · refine ⟨by rw [hv2]; exact hLrel, ?_⟩
      simp only [Instance.completion, hv2]
      exact hLdue
    · left
      simp only [Instance.completion, hv1, hv2, hpOlen]
      omega
    · intro z hz1 hz2
      simp only [Instance.completion, hv1, hpOlen]
      by_contra hc
      push Not at hc
      obtain ⟨hc1, hc2⟩ := hc
      have hzqI : z ≠ Sum.inr (i, Part.shortIn) := by
        rintro rfl
        omega
      have hzin := mem_binOcc_of_meets A h i z (by omega) (by omega)
      simp only [binOcc, Finset.mem_filter, Finset.mem_univ, true_and] at hzin
      refine no_room_of_cover A h i hLhead ?_ ?_ hz2 hzqI hzin.1 hzin.2
      · rw [hLlen]
        exact hpinS
      · rw [hLlen]
        simp only [inst_p_quad, quadLen]
    · intro z hz1 hz2
      have hsep := h.2 z (Sum.inr (i, Part.longOut)) hz1
      simp only [Instance.completion, hv2, hpOlen, hLlen] at hsep ⊢
      omega
  have hpres : ∀ (jj : Fin A.N), (jj : ℕ) < k → ProperAt A u' jj := by
    intro jj hjj
    refine properAt_congr A jj (fun prt => ?_) (hup jj hjj)
    refine hv3 _ ?_ ?_
    · intro hc
      have h0 : jj = i := congrArg Prod.fst (Sum.inr.inj hc)
      have := congrArg Fin.val h0
      omega
    · rintro rfl
      have hpartne : prt ≠ Part.sep := by
        rintro rfl
        exact sep_not_in_bin A h i jj hLin.1 hLin.2
      have := parked_index_ge A h i jj hpartne hLin.1
        (by simpa only [inst_p_quad] using hLin.2)
      omega
  refine ⟨u', hfeas, ?_, hpres⟩
  refine properAt_of_longOut_head A hfeas hpres i hik hv1 ?_
  rw [hv3 _ (quadJob_ne A (by decide)) hLne.symm]
  exact hpinS

/-- **Case 5 of the exchange step.** No long job is parked in bin `k`, but the inner short
job of pair `k` is. It is pinned against the far end, so everything else in the bin sits in
the first `p` units; those jobs move together into the slot pair `k`'s outer long job
vacates, which is exactly `p` long. How many of them there are depends on `⌊p/q⌋`, so they
are placed by `Packing.exists_packing` rather than named one by one. -/
lemma exchange_noLongInnerIn {u : (inst A).Schedule} (h : (inst A).Feasible u) {k : ℕ}
    (hup : NormalizedUpTo A u k) (i : Fin A.N) (hik : (i : ℕ) = k)
    (hpO : 0 ≤ u (Sum.inr (i, Part.longOut)))
    (hqI : u (Sum.inr (i, Part.shortIn)) < 0)
    (hnolong : ∀ z ∈ binOcc A u i, (inst A).p z = q) :
    ∃ u' : (inst A).Schedule, (inst A).Feasible u' ∧ ProperAt A u' i ∧
      (∀ j : Fin A.N, (j : ℕ) < k → ProperAt A u' j) := by
  classical
  have hq := A.q_pos
  have hqp := A.q_lt_p
  have hwidth : (width p q : ℤ) = (p : ℤ) + 2 * q := by
    simp only [width]
    push_cast
    ring
  have hbneg : binStart A i + (p : ℤ) + q < 0 := by
    have := binStart_add_width_nonpos A i
    simp only [width] at this
    push_cast at this
    omega
  obtain ⟨m, hm1, hm2, hm3, hm4, hm5⟩ :=
    placement_of_invariant A h hup i (by decide) (le_of_eq hik.symm) hqI
  have hmk : m = (i : ℕ) := by omega
  subst hmk
  rw [← binStart_eq_binAt] at hm4 hm5
  simp only [quadLen] at hm5
  have hpinS : u (Sum.inr (i, Part.shortIn)) = binStart A i + p :=
    innerShort_forced A h i (by simpa only [quadLen] using hm5)
  have hpOlen : (inst A).p (Sum.inr (i, Part.longOut)) = p := rfl
  have hdp := Aux.dp_nonneg A i
  have hpOdue := (h.1 (Sum.inr (i, Part.longOut))).2
  simp only [Instance.completion, inst_p_quad, inst_d_quad, quadLen, quadDue] at hpOdue
  set E : Finset ((inst A).Job) := (binOcc A u i).erase (Sum.inr (i, Part.shortIn)) with hE
  have hEbin : ∀ z ∈ E, z ∈ binOcc A u i := fun z hz => (Finset.mem_erase.mp hz).2
  have hElen : ∀ z ∈ E, (inst A).p z = q := fun z hz => hnolong z (hEbin z hz)
  have hEmem : ∀ z ∈ E, binStart A i ≤ u z ∧ u z + (inst A).p z ≤ binStart A i + p := by
    intro z hz
    have hzne := (Finset.mem_erase.mp hz).1
    have hzin := hEbin z hz
    simp only [binOcc, Finset.mem_filter, Finset.mem_univ, true_and] at hzin
    have hsep := h.2 z (Sum.inr (i, Part.shortIn)) hzne
    simp only [Instance.completion, inst_p_quad, quadLen, hpinS] at hsep
    have hzlen := hElen z hz
    exact ⟨hzin.1, by omega⟩
  have hEquad : ∀ z ∈ E, ∃ (j : Fin A.N) (prt : Part), z = Sum.inr (j, prt) ∧
      (prt = Part.shortIn ∨ prt = Part.shortOut) := by
    intro z hz
    have hzm := hEmem z hz
    have hzlen := hElen z hz
    rcases z with o | ⟨j, prt⟩
    · exact absurd (le_trans (A.r_nonneg o) (h.1 (Sum.inl o)).1) (by
        have := (inst A).p_pos (Sum.inl o)
        omega)
    · refine ⟨j, prt, rfl, ?_⟩
      have hnotsep : prt ≠ Part.sep := by
        rintro rfl
        exact sep_not_in_bin A h i j hzm.1 (by omega)
      cases prt <;> simp only [inst_p_quad, quadLen] at hzlen <;> simp_all
  have hEsum : ∑ z ∈ E, (inst A).p z ≤ p := by
    have hsum := Instance.sum_p_le h.2 E (a := binStart A i) (b := binStart A i + p)
      (fun z hz => hEmem z hz)
    have harith : ((binStart A i + (p : ℤ)) - binStart A i).toNat = p := by omega
    omega
  have hpOnotE : Sum.inr (i, Part.longOut) ∉ E := by
    intro hmem
    have hc := hEmem _ hmem
    have := (inst A).p_pos (Sum.inr (i, Part.longOut))
    omega
  obtain ⟨t, ht1, ht2⟩ :=
    Packing.exists_packing (inst A).p E (u (Sum.inr (i, Part.longOut)))
  set u' : (inst A).Schedule := fun x =>
    if x = Sum.inr (i, Part.longOut) then binStart A i
    else if x ∈ E then t x else u x with hu'
  have hv1 : u' (Sum.inr (i, Part.longOut)) = binStart A i := by
    simp only [hu']
    split_ifs <;> first | rfl | exact absurd rfl ‹_›
  have hv2 : ∀ z ∈ E, u' z = t z := by
    intro z hz
    simp only [hu']
    rw [if_neg (fun hc => hpOnotE (by rw [← hc]; exact hz)), if_pos hz]
  have hv3 : ∀ z : (inst A).Job, z ≠ Sum.inr (i, Part.longOut) → z ∉ E → u' z = u z := by
    intro z h1 h2
    simp only [hu']
    rw [if_neg h1, if_neg h2]
  have hfeas : (inst A).Feasible u' := by
    refine Instance.feasible_of_move' h
      (fun x => x = Sum.inr (i, Part.longOut) ∨ x ∈ E) ?_ ?_ ?_ ?_
    · rintro z hz
      exact hv3 z (fun hc => hz (Or.inl hc)) (fun hc => hz (Or.inr hc))
    · rintro x (rfl | hx)
      · refine ⟨by rw [hv1]; exact le_refl _, ?_⟩
        simp only [Instance.completion, hv1, hpOlen, inst_d_quad, quadDue]
        omega
      · obtain ⟨j, prt, rfl, hshort⟩ := hEquad x hx
        have hb := ht1 _ hx
        have hxlen := hElen _ hx
        have hxmem := hEmem _ hx
        have hdue := parked_short_deadline A h i j hshort hxmem.1 (by omega)
        refine ⟨?_, ?_⟩
        · rw [hv2 _ hx]
          have := quadRel_nonpos A j prt
          simp only [inst_r_quad]
          omega
        · simp only [Instance.completion, hv2 _ hx]
          omega
    · rintro x (rfl | hx) z (rfl | hz) hxz
      · exact absurd rfl hxz
      · left
        have := (ht1 _ hz).1
        simp only [Instance.completion, hv1, hpOlen, hv2 _ hz]
        omega
      · right
        have := (ht1 _ hx).1
        simp only [Instance.completion, hv1, hpOlen, hv2 _ hx]
        omega
      · simp only [Instance.completion, hv2 _ hx, hv2 _ hz]
        exact ht2 x hx z hz hxz
    · rintro x (rfl | hx) z hz
      · simp only [Instance.completion, hv1, hpOlen]
        by_contra hc
        push Not at hc
        obtain ⟨hc1, hc2⟩ := hc
        have hzqI : z ≠ Sum.inr (i, Part.shortIn) := by
          rintro rfl
          omega
        have hzin := mem_binOcc_of_meets A h i z (by omega) (by omega)
        exact hz (Or.inr (Finset.mem_erase.mpr ⟨hzqI, hzin⟩))
      · have hsep := h.2 z (Sum.inr (i, Part.longOut)) (fun hc => hz (Or.inl hc))
        have hb := ht1 _ hx
        have hxlen := hElen _ hx
        simp only [Instance.completion, hv2 _ hx, hpOlen] at hsep ⊢
        omega
  have hpres : ∀ (jj : Fin A.N), (jj : ℕ) < k → ProperAt A u' jj := by
    intro jj hjj
    refine properAt_congr A jj (fun prt => ?_) (hup jj hjj)
    refine hv3 _ ?_ ?_
    · intro hc
      have h0 : jj = i := congrArg Prod.fst (Sum.inr.inj hc)
      have := congrArg Fin.val h0
      omega
    · intro hc
      obtain ⟨j2, prt2, heq2, hshort2⟩ := hEquad _ hc
      have h0 : jj = j2 := congrArg Prod.fst (Sum.inr.inj heq2)
      have hxmem := hEmem _ hc
      have hprtne : prt ≠ Part.sep := by
        have : prt = prt2 := congrArg Prod.snd (Sum.inr.inj heq2)
        rcases hshort2 with rfl | rfl <;> rw [this] <;> simp
      have hbound : u (Sum.inr (jj, prt)) + (quadLen A p q (jj, prt) : ℤ) ≤
          binStart A i + p + q := by
        have h2 := hxmem.2
        simp only [inst_p_quad] at h2
        omega
      have := parked_index_ge A h i jj hprtne hxmem.1 hbound
      omega
  refine ⟨u', hfeas, ?_, hpres⟩
  refine properAt_of_longOut_head A hfeas hpres i hik hv1 ?_
  rw [hv3 _ (quadJob_ne A (by decide)) (fun hc => (Finset.mem_erase.mp hc).1 rfl)]
  exact hpinS

/-- **Case 6 of the exchange step**, the last one. No long job is parked in bin `k` and
neither is pair `k`'s inner short job, so the bin holds only short jobs of later pairs,
totalling at most `p + q`. Two gaps open up — the `p` left by pair `k`'s outer long job and
the `q` left by its inner short one — and `Packing.sum_erase_le` splits the load: one job
goes into the `q`-sized gap, and everything else then fits in the `p`-sized one. -/
lemma exchange_noLongInnerOut {u : (inst A).Schedule} (h : (inst A).Feasible u) {k : ℕ}
    (hup : NormalizedUpTo A u k) (i : Fin A.N) (hik : (i : ℕ) = k)
    (hpO : 0 ≤ u (Sum.inr (i, Part.longOut)))
    (hqI : 0 ≤ u (Sum.inr (i, Part.shortIn)))
    (hnolong : ∀ z ∈ binOcc A u i, (inst A).p z = q) :
    ∃ u' : (inst A).Schedule, (inst A).Feasible u' ∧ ProperAt A u' i ∧
      (∀ j : Fin A.N, (j : ℕ) < k → ProperAt A u' j) := by
  classical
  have hq := A.q_pos
  have hqp := A.q_lt_p
  have hwidth : (width p q : ℤ) = (p : ℤ) + 2 * q := by
    simp only [width]
    push_cast
    ring
  have hbneg : binStart A i + (p : ℤ) + q < 0 := by
    have := binStart_add_width_nonpos A i
    omega
  have hpOlen : (inst A).p (Sum.inr (i, Part.longOut)) = p := rfl
  have hqIlen : (inst A).p (Sum.inr (i, Part.shortIn)) = q := rfl
  have hdp := Aux.dp_nonneg A i
  have hdq' := A.dq'_nonneg i
  have hpOdue := (h.1 (Sum.inr (i, Part.longOut))).2
  simp only [Instance.completion, inst_p_quad, inst_d_quad, quadLen, quadDue] at hpOdue
  have hqIdue := (h.1 (Sum.inr (i, Part.shortIn))).2
  simp only [Instance.completion, inst_p_quad, inst_d_quad, quadLen, quadDue] at hqIdue
  set E : Finset ((inst A).Job) := binOcc A u i with hE
  have hEmem : ∀ z ∈ E, binStart A i ≤ u z ∧ u z + (inst A).p z ≤ binStart A i + p + q := by
    intro z hz
    have hzin : z ∈ binOcc A u i := hz
    simp only [binOcc, Finset.mem_filter, Finset.mem_univ, true_and] at hzin
    exact hzin
  have hElen : ∀ z ∈ E, (inst A).p z = q := fun z hz => hnolong z hz
  have hEquad : ∀ z ∈ E, ∃ (j : Fin A.N) (prt : Part), z = Sum.inr (j, prt) ∧
      (prt = Part.shortIn ∨ prt = Part.shortOut) := by
    intro z hz
    have hzm := hEmem z hz
    have hzlen := hElen z hz
    rcases z with o | ⟨j, prt⟩
    · exact absurd (le_trans (A.r_nonneg o) (h.1 (Sum.inl o)).1) (by
        have := (inst A).p_pos (Sum.inl o)
        omega)
    · refine ⟨j, prt, rfl, ?_⟩
      have hnotsep : prt ≠ Part.sep := by
        rintro rfl
        exact sep_not_in_bin A h i j hzm.1 hzm.2
      cases prt <;> simp only [inst_p_quad, quadLen] at hzlen <;> simp_all
  -- anything parked in the bin is at least as patient as pair `k`'s inner short job
  have hEdue : ∀ z ∈ E, A.dq' i ≤ (inst A).d z := by
    intro z hz
    obtain ⟨j, prt, rfl, hshort⟩ := hEquad z hz
    have hzm := hEmem _ hz
    have hprtne : prt ≠ Part.sep := by rcases hshort with rfl | rfl <;> simp
    have hji := parked_index_ge A h i j hprtne hzm.1 (by
      have h2 := hzm.2
      simp only [inst_p_quad] at h2
      omega)
    rcases Nat.eq_or_lt_of_le hji with heq | hlt
    · have hij : j = i := Fin.ext heq.symm
      subst hij
      rcases hshort with rfl | rfl
      · exact absurd hzm.2 (by
          have := hElen _ hz
          omega)
      · simp only [inst_d_quad, quadDue]
        exact A.dq'_le_dq j
    · have hchain := Aux.dq_le_dq'_of_lt A ((j : ℕ) - (i : ℕ) - 1) i j (by omega)
      have hd := A.dq'_le_dq i
      rcases hshort with rfl | rfl
      · simp only [inst_d_quad, quadDue]
        omega
      · have := A.dq'_le_dq j
        simp only [inst_d_quad, quadDue]
        omega
  have hEsum : ∑ z ∈ E, (inst A).p z ≤ p + q := by
    have hsum := Instance.sum_p_le h.2 E (a := binStart A i) (b := binStart A i + p + q)
      (fun z hz => hEmem z hz)
    have harith : ((binStart A i + (p : ℤ) + q) - binStart A i).toNat = p + q := by omega
    omega
  have hpOnotE : Sum.inr (i, Part.longOut) ∉ E := by
    intro hmem
    have hc := hEmem _ hmem
    have := (inst A).p_pos (Sum.inr (i, Part.longOut))
    omega
  have hqInotE : Sum.inr (i, Part.shortIn) ∉ E := by
    intro hmem
    have hc := hEmem _ hmem
    have := (inst A).p_pos (Sum.inr (i, Part.shortIn))
    omega
  have hqIne : (Sum.inr (i, Part.shortIn) : (inst A).Job) ≠ Sum.inr (i, Part.longOut) :=
    quadJob_ne A (by decide)
  rcases Finset.eq_empty_or_nonempty E with hEempty | ⟨x, hx⟩
  · -- the bin is empty: only pair `k`'s own jobs move
    set u' : (inst A).Schedule := fun z =>
      if z = Sum.inr (i, Part.longOut) then binStart A i
      else if z = Sum.inr (i, Part.shortIn) then binStart A i + p else u z with hu'
    have hv1 : u' (Sum.inr (i, Part.longOut)) = binStart A i := by
      simp only [hu']
      split_ifs <;> first | rfl | exact absurd rfl ‹_›
    have hv2 : u' (Sum.inr (i, Part.shortIn)) = binStart A i + p := by
      simp only [hu']
      split_ifs <;> first | rfl | exact absurd rfl ‹_› | simp_all
    have hv3 : ∀ z : (inst A).Job, z ≠ Sum.inr (i, Part.longOut) →
        z ≠ Sum.inr (i, Part.shortIn) → u' z = u z := by
      intro z h1 h2
      simp only [hu']
      rw [if_neg h1, if_neg h2]
    have hclear : ∀ z : (inst A).Job, z ≠ Sum.inr (i, Part.longOut) →
        z ≠ Sum.inr (i, Part.shortIn) →
        binStart A i + p + q ≤ u z ∨ u z + (inst A).p z ≤ binStart A i := by
      intro z h1 h2
      by_contra hc
      push Not at hc
      obtain ⟨hc1, hc2⟩ := hc
      have hzin : z ∈ E := mem_binOcc_of_meets A h i z (by omega) (by omega)
      rw [hEempty] at hzin
      exact absurd hzin (Finset.notMem_empty z)
    have hfeas : (inst A).Feasible u' := by
      refine Instance.feasible_of_move' h
        (fun z => z = Sum.inr (i, Part.longOut) ∨ z = Sum.inr (i, Part.shortIn)) ?_ ?_ ?_ ?_
      · rintro z hz
        exact hv3 z (fun hc => hz (Or.inl hc)) (fun hc => hz (Or.inr hc))
      · rintro y (rfl | rfl)
        · refine ⟨by rw [hv1]; exact le_refl _, ?_⟩
          simp only [Instance.completion, hv1, hpOlen, inst_d_quad, quadDue]
          omega
        · refine ⟨by rw [hv2]; exact le_refl _, ?_⟩
          simp only [Instance.completion, hv2, hqIlen, inst_d_quad, quadDue]
          omega
      · rintro y (rfl | rfl) z (rfl | rfl) hyz <;>
          first
            | exact absurd rfl hyz
            | (simp only [Instance.completion, hv1, hv2, hpOlen, hqIlen]
               omega)
      · rintro y (rfl | rfl) z hz <;>
          [(simp only [Instance.completion, hv1, hpOlen]);
           (simp only [Instance.completion, hv2, hqIlen])] <;>
          · have := hclear z (fun hc => hz (Or.inl hc)) (fun hc => hz (Or.inr hc))
            have := (inst A).p_pos z
            omega
    have hpres : ∀ (jj : Fin A.N), (jj : ℕ) < k → ProperAt A u' jj := by
      intro jj hjj
      refine properAt_congr A jj (fun prt => ?_) (hup jj hjj)
      refine hv3 _ ?_ ?_ <;>
        · intro hc
          have h0 : jj = i := congrArg Prod.fst (Sum.inr.inj hc)
          have := congrArg Fin.val h0
          omega
    exact ⟨u', hfeas, properAt_of_longOut_head A hfeas hpres i hik hv1 hv2, hpres⟩
  · -- one job goes into the `q`-sized gap, the rest into the `p`-sized one
    have hxlen := hElen x hx
    have hEsum' : ∑ z ∈ E.erase x, (inst A).p z ≤ p :=
      Packing.sum_erase_le (inst A).p E hx (by rw [hxlen]; exact hEsum)
    obtain ⟨t, ht1, ht2⟩ :=
      Packing.exists_packing (inst A).p (E.erase x) (u (Sum.inr (i, Part.longOut)))
    have hxnotE' : x ∉ E.erase x := by simp
    have hE'sub : ∀ z ∈ E.erase x, z ∈ E := fun z hz => (Finset.mem_erase.mp hz).2
    set u' : (inst A).Schedule := fun z =>
      if z = Sum.inr (i, Part.longOut) then binStart A i
      else if z = Sum.inr (i, Part.shortIn) then binStart A i + p
      else if z = x then u (Sum.inr (i, Part.shortIn))
      else if z ∈ E.erase x then t z else u z with hu'
    have hxpO : x ≠ Sum.inr (i, Part.longOut) := fun hc => hpOnotE (hc ▸ hx)
    have hxqI : x ≠ Sum.inr (i, Part.shortIn) := fun hc => hqInotE (hc ▸ hx)
    have hv1 : u' (Sum.inr (i, Part.longOut)) = binStart A i := by
      simp only [hu']
      split_ifs <;> first | rfl | exact absurd rfl ‹_›
    have hv2 : u' (Sum.inr (i, Part.shortIn)) = binStart A i + p := by
      simp only [hu']
      split_ifs <;> first | rfl | exact absurd rfl ‹_› | simp_all
    have hv3 : u' x = u (Sum.inr (i, Part.shortIn)) := by
      simp only [hu']
      rw [if_neg hxpO, if_neg hxqI]
      split_ifs <;> first | rfl
    have hv4 : ∀ z ∈ E.erase x, u' z = t z := by
      intro z hz
      have hzE := hE'sub z hz
      simp only [hu']
      rw [if_neg (fun hc => hpOnotE (by rw [← hc]; exact hzE)),
        if_neg (fun hc => hqInotE (by rw [← hc]; exact hzE)),
        if_neg (fun (hc : z = x) => hxnotE' (hc ▸ hz)), if_pos hz]
    have hv5 : ∀ z : (inst A).Job, z ≠ Sum.inr (i, Part.longOut) →
        z ≠ Sum.inr (i, Part.shortIn) → z ≠ x → z ∉ E.erase x → u' z = u z := by
      intro z h1 h2 h3 h4
      simp only [hu']
      rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
    have hfeas : (inst A).Feasible u' := by
      refine Instance.feasible_of_move' h
        (fun z => z = Sum.inr (i, Part.longOut) ∨ z = Sum.inr (i, Part.shortIn) ∨
          z = x ∨ z ∈ E.erase x) ?_ ?_ ?_ ?_
      · rintro z hz
        exact hv5 z (fun hc => hz (Or.inl hc)) (fun hc => hz (Or.inr (Or.inl hc)))
          (fun hc => hz (Or.inr (Or.inr (Or.inl hc))))
          (fun hc => hz (Or.inr (Or.inr (Or.inr hc))))
      · rintro y (rfl | rfl | rfl | hy)
        · refine ⟨by rw [hv1]; exact le_refl _, ?_⟩
          simp only [Instance.completion, hv1, hpOlen, inst_d_quad, quadDue]
          omega
        · refine ⟨by rw [hv2]; exact le_refl _, ?_⟩
          simp only [Instance.completion, hv2, hqIlen, inst_d_quad, quadDue]
          omega
        · obtain ⟨j, prt, hxeq, hshort⟩ := hEquad _ hx
          have hdue := hEdue _ hx
          refine ⟨?_, ?_⟩
          · rw [hv3, hxeq]
            have := quadRel_nonpos A j prt
            simp only [inst_r_quad]
            omega
          · simp only [Instance.completion, hv3, hxlen]
            omega
        · have hyE := hE'sub _ hy
          have hb := ht1 _ hy
          have hylen := hElen _ hyE
          have hymem := hEmem _ hyE
          obtain ⟨j, prt, hyeq, hshort⟩ := hEquad _ hyE
          subst hyeq
          have hdue := parked_short_deadline A h i j hshort hymem.1 (by
            have h2 := hymem.2
            simp only [inst_p_quad] at h2
            omega)
          refine ⟨?_, ?_⟩
          · rw [hv4 _ hy]
            have := quadRel_nonpos A j prt
            simp only [inst_r_quad]
            omega
          · simp only [Instance.completion, hv4 _ hy]
            omega
      · have hposx : (0 : ℤ) ≤ u' x := by rw [hv3]; exact hqI
        have hposE : ∀ w ∈ E.erase x, (0 : ℤ) ≤ u' w := by
          intro w hw
          rw [hv4 _ hw]
          have := (ht1 _ hw).1
          omega
        have hEt : ∀ w ∈ E.erase x, u' w + (inst A).p w ≤
            u (Sum.inr (i, Part.longOut)) + p := by
          intro w hw
          rw [hv4 _ hw]
          have := (ht1 _ hw).2
          omega
        have hsepQP := h.2 (Sum.inr (i, Part.shortIn)) (Sum.inr (i, Part.longOut)) hqIne
        simp only [Instance.completion, hpOlen, hqIlen] at hsepQP
        rintro y (rfl | rfl | rfl | hy) z (rfl | rfl | rfl | hz) hyz
        · exact absurd rfl hyz
        · left; simp only [Instance.completion, hv1, hv2, hpOlen]; omega
        · left; simp only [Instance.completion, hv1, hpOlen]; omega
        · left
          have := hposE _ hz
          simp only [Instance.completion, hv1, hpOlen]
          omega
        · right; simp only [Instance.completion, hv1, hv2, hpOlen]; omega
        · exact absurd rfl hyz
        · left; simp only [Instance.completion, hv2, hqIlen]; omega
        · left
          have := hposE _ hz
          simp only [Instance.completion, hv2, hqIlen]
          omega
        · right; simp only [Instance.completion, hv1, hpOlen]; omega
        · right; simp only [Instance.completion, hv2, hqIlen]; omega
        · exact absurd rfl hyz
        · have h1 := hposE _ hz
          have h2 := hEt _ hz
          have h3 := (ht1 _ hz).1
          simp only [Instance.completion, hv3, hxlen]
          rcases hsepQP with hc | hc
          · left; rw [hv4 _ hz] at *; omega
          · right
            have := hElen _ (hE'sub _ hz)
            rw [hv4 _ hz] at *
            omega
        · right
          have := hposE _ hy
          simp only [Instance.completion, hv1, hpOlen]
          omega
        · right
          have := hposE _ hy
          simp only [Instance.completion, hv2, hqIlen]
          omega
        · have h1 := hposE _ hy
          have h2 := hEt _ hy
          have h3 := (ht1 _ hy).1
          have h4 := hElen _ (hE'sub _ hy)
          simp only [Instance.completion, hv3, hxlen]
          rcases hsepQP with hc | hc
          · right; rw [hv4 _ hy] at *; omega
          · left; rw [hv4 _ hy] at *; omega
        · simp only [Instance.completion, hv4 _ hy, hv4 _ hz]
          exact ht2 y hy z hz hyz
      · rintro y (rfl | rfl | rfl | hy) z hz
        · simp only [Instance.completion, hv1, hpOlen]
          by_contra hc
          push Not at hc
          obtain ⟨hc1, hc2⟩ := hc
          have hzin := mem_binOcc_of_meets A h i z (by omega) (by omega)
          by_cases hzx : z = x
          · exact hz (Or.inr (Or.inr (Or.inl hzx)))
          · exact hz (Or.inr (Or.inr (Or.inr (Finset.mem_erase.mpr ⟨hzx, hzin⟩))))
        · simp only [Instance.completion, hv2, hqIlen]
          by_contra hc
          push Not at hc
          obtain ⟨hc1, hc2⟩ := hc
          have hzin := mem_binOcc_of_meets A h i z (by omega) (by omega)
          by_cases hzx : z = x
          · exact hz (Or.inr (Or.inr (Or.inl hzx)))
          · exact hz (Or.inr (Or.inr (Or.inr (Finset.mem_erase.mpr ⟨hzx, hzin⟩))))
        · have hsep := h.2 z (Sum.inr (i, Part.shortIn))
            (fun hc => hz (Or.inr (Or.inl hc)))
          simp only [Instance.completion, hv3, hqIlen, hxlen] at hsep ⊢
          omega
        · have hsep := h.2 z (Sum.inr (i, Part.longOut)) (fun hc => hz (Or.inl hc))
          have hb := ht1 _ hy
          have hylen := hElen _ (hE'sub _ hy)
          simp only [Instance.completion, hv4 _ hy, hpOlen] at hsep ⊢
          omega
    have hpres : ∀ (jj : Fin A.N), (jj : ℕ) < k → ProperAt A u' jj := by
      intro jj hjj
      refine properAt_congr A jj (fun prt => ?_) (hup jj hjj)
      have hnotbin : Sum.inr (jj, prt) ∉ E := by
        intro hc
        obtain ⟨j2, prt2, heq2, hshort2⟩ := hEquad _ hc
        have h0 : jj = j2 := congrArg Prod.fst (Sum.inr.inj heq2)
        have hzm := hEmem _ hc
        have hprtne : prt ≠ Part.sep := by
          have hpp : prt = prt2 := congrArg Prod.snd (Sum.inr.inj heq2)
          rcases hshort2 with rfl | rfl <;> rw [hpp] <;> simp
        have := parked_index_ge A h i jj hprtne hzm.1 (by
          have h2 := hzm.2
          simp only [inst_p_quad] at h2
          omega)
        omega
      refine hv5 _ ?_ ?_ ?_ ?_
      · intro hc
        have h0 : jj = i := congrArg Prod.fst (Sum.inr.inj hc)
        have := congrArg Fin.val h0
        omega
      · intro hc
        have h0 : jj = i := congrArg Prod.fst (Sum.inr.inj hc)
        have := congrArg Fin.val h0
        omega
      · rintro rfl
        exact hnotbin hx
      · intro hc
        exact hnotbin (hE'sub _ hc)
    exact ⟨u', hfeas, properAt_of_longOut_head A hfeas hpres i hik hv1 hv2, hpres⟩

/-- **Case 4b.** A foreign long job is parked in bin `k` and pair `k`'s inner short job is
*not*. Rather than rearrange the bin directly, swap the foreign long job with pair `k`'s
outer long one — they have the same length, so nothing else has to move — and the situation
becomes case 3. -/
lemma exchange_foreignLongOut {u : (inst A).Schedule} (h : (inst A).Feasible u) {k : ℕ}
    (hup : NormalizedUpTo A u k) (i : Fin A.N) (hik : (i : ℕ) = k)
    (hpI : 0 ≤ u (Sum.inr (i, Part.longIn)))
    (hpO : 0 ≤ u (Sum.inr (i, Part.longOut)))
    (hqI : 0 ≤ u (Sum.inr (i, Part.shortIn)))
    (L : (inst A).Job) (hL1 : L ≠ Sum.inr (i, Part.longOut))
    (hLlen : (inst A).p L = p)
    (hLin : binStart A i ≤ u L ∧ u L + (inst A).p L ≤ binStart A i + p + q) :
    ∃ u' : (inst A).Schedule, (inst A).Feasible u' ∧ ProperAt A u' i ∧
      (∀ j : Fin A.N, (j : ℕ) < k → ProperAt A u' j) := by
  classical
  have hq := A.q_pos
  have hqp := A.q_lt_p
  have hwidth : (width p q : ℤ) = (p : ℤ) + 2 * q := by
    simp only [width]
    push_cast
    ring
  have hbneg : binStart A i + (p : ℤ) + q < 0 := by
    have := binStart_add_width_nonpos A i
    omega
  have hpOlen : (inst A).p (Sum.inr (i, Part.longOut)) = p := rfl
  have hdp := Aux.dp_nonneg A i
  have hpOdue := (h.1 (Sum.inr (i, Part.longOut))).2
  simp only [Instance.completion, inst_p_quad, inst_d_quad, quadLen, quadDue] at hpOdue
  have hLneg : u L + (inst A).p L < 0 := by omega
  have hLplen : 0 < (inst A).p L := (inst A).p_pos L
  -- the foreign long job is a quad job of a strictly later pair
  obtain ⟨j, prt, rfl⟩ : ∃ (j : Fin A.N) (prt : Part), L = Sum.inr (j, prt) := by
    rcases L with o | ⟨j, prt⟩
    · exact absurd (le_trans (A.r_nonneg o) (h.1 (Sum.inl o)).1) (by omega)
    · exact ⟨j, prt, rfl⟩
  have hprt : prt ≠ Part.sep := by
    rintro rfl
    exact sep_not_in_bin A h i j hLin.1 hLin.2
  have hji : (i : ℕ) ≤ (j : ℕ) :=
    parked_index_ge A h i j hprt hLin.1 (by simpa only [inst_p_quad] using hLin.2)
  have hlong : prt = Part.longIn ∨ prt = Part.longOut := by
    cases prt <;> simp only [inst_p_quad, quadLen] at hLlen <;> simp_all
  have hjlt : (i : ℕ) < (j : ℕ) := by
    rcases Nat.eq_or_lt_of_le hji with heq | hlt
    · exfalso
      have hij : j = i := Fin.ext heq.symm
      subst hij
      rcases hlong with rfl | rfl
      · exact absurd hpI (by simp only [inst_p_quad, quadLen] at hLlen; omega)
      · exact hL1 rfl
    · exact hlt
  have hLqI : (Sum.inr (j, prt) : (inst A).Job) ≠ Sum.inr (i, Part.shortIn) := by
    intro hc
    have h0 : j = i := congrArg Prod.fst (Sum.inr.inj hc)
    have := congrArg Fin.val h0
    omega
  have hLdue : u (Sum.inr (i, Part.longOut)) + (inst A).p (Sum.inr (j, prt)) ≤
      (inst A).d (Sum.inr (j, prt)) := by
    rw [hLlen]
    have hchain := Aux.dp_le_dp'_of_lt A ((j : ℕ) - (i : ℕ) - 1) i j (by omega)
    rcases hlong with rfl | rfl
    · simp only [inst_d_quad, quadDue]
      omega
    · have := A.dp'_le_dp j
      simp only [inst_d_quad, quadDue]
      omega
  have hLrel : (inst A).r (Sum.inr (j, prt)) ≤ u (Sum.inr (i, Part.longOut)) := by
    have := quadRel_nonpos A j prt
    simp only [inst_r_quad]
    omega
  -- swap the two long jobs
  set u'' : (inst A).Schedule := fun z =>
    if z = Sum.inr (i, Part.longOut) then u (Sum.inr (j, prt))
    else if z = Sum.inr (j, prt) then u (Sum.inr (i, Part.longOut)) else u z with hu''
  have hw1 : u'' (Sum.inr (i, Part.longOut)) = u (Sum.inr (j, prt)) := by
    simp only [hu'']
    split_ifs <;> first | rfl | exact absurd rfl ‹_›
  have hw2 : u'' (Sum.inr (j, prt)) = u (Sum.inr (i, Part.longOut)) := by
    simp only [hu'']
    rw [if_neg hL1]
    split_ifs <;> first | rfl | exact absurd rfl ‹_›
  have hw3 : ∀ z : (inst A).Job, z ≠ Sum.inr (i, Part.longOut) → z ≠ Sum.inr (j, prt) → u'' z = u z := by
    intro z h1 h2
    simp only [hu'']
    rw [if_neg h1, if_neg h2]
  have hfeas : (inst A).Feasible u'' := by
    refine Instance.feasible_of_move_two h hw3 ?_ ?_ ?_ ?_ ?_
    · refine ⟨?_, ?_⟩
      · rw [hw1]
        simp only [inst_r_quad, quadRel]
        omega
      · simp only [Instance.completion, hw1, hpOlen, inst_d_quad, quadDue]
        rw [hLlen] at hLin
        omega
    · refine ⟨by rw [hw2]; exact hLrel, ?_⟩
      simp only [Instance.completion, hw2]
      exact hLdue
    · rcases h.2 (Sum.inr (j, prt)) (Sum.inr (i, Part.longOut)) hL1 with hc | hc <;>
        simp only [Instance.completion, hw1, hw2, hpOlen, hLlen] at * <;> omega
    · intro z hz1 hz2
      have hsep := h.2 z (Sum.inr (j, prt)) hz2
      simp only [Instance.completion, hw1, hpOlen, hLlen] at hsep ⊢
      omega
    · intro z hz1 hz2
      have hsep := h.2 z (Sum.inr (i, Part.longOut)) hz1
      simp only [Instance.completion, hw2, hpOlen, hLlen] at hsep ⊢
      omega
  have hup'' : NormalizedUpTo A u'' k := by
    intro jj hjj
    refine properAt_congr A jj (fun prt => ?_) (hup jj hjj)
    refine hw3 _ ?_ ?_
    · intro hc
      have h0 : jj = i := congrArg Prod.fst (Sum.inr.inj hc)
      have := congrArg Fin.val h0
      omega
    · intro hc
      have h0 : jj = j := congrArg Prod.fst (Sum.inr.inj hc)
      have := congrArg Fin.val h0
      omega
  -- now pair `k`'s outer long job is in the bin: that is case 3
  refine exchange_longOutIn A hfeas hup'' i hik ?_ ?_
  · rw [hw1]
    omega
  · rw [hw3 _ (quadJob_ne A (by decide)) hLqI.symm]
    exact hqI

/-- **One step of the exchange argument**: given that bins `0 … k-1` already hold proper
pairs, the schedule can be rewritten so that bin `k` does too.

Every case is bounded, but not by a fixed number of jobs: a bin can hold `⌊(p+q)/q⌋` short
jobs, so the displaced set has no fixed size and `Packing.exists_packing` re-places it
wholesale. Writing `b` for the start of bin `k`, and using that each of quad `k`'s jobs is
either running after `0` or parked in bin `k` (`placement_of_invariant`), the dispatch is:

1. `J^I_{p,k}` in bin `k`. It is pinned at `b + q` (`innerLong_forced`), so the only room
   left is `[b, b+q)`, which holds at most one short job. Target the pairing
   `(J^O_{q,k}, J^I_{p,k})`: move `J^O_{q,k}` to `b`, and whatever was there — necessarily
   a short job of a later pair — into the slot `J^O_{q,k}` vacates. Two jobs move.
2. `J^O_{p,k}` and `J^I_{q,k}` both in bin `k`: they are already in the canonical
   positions, and nothing moves.
3. `J^O_{p,k}` in bin `k`, `J^I_{q,k}` after `0`. The long job takes `p` of the bin, so at
   most one short sits beside it. Three jobs move.
4. `J^O_{p,k}` after `0`, some other long job in the bin, and `J^I_{q,k}` in the bin too.
   That long job goes into the slot `J^O_{p,k}` vacates, with at most one short beside it.
5. As case 4 but with `J^I_{q,k}` after `0`. The paper folds this into case 4, where the
   argument does not run: without `J^I_{q,k}` in the bin the foreign long job is no longer
   forced to the head. Swapping it with `J^O_{p,k}` — same length, so nothing else moves —
   reduces it to case 3.
6. `J^O_{p,k}` after `0`, no long job in the bin, `J^I_{q,k}` in the bin. The bin's short
   jobs then total at most `p`, and `Packing.exists_packing` re-places all of them in the
   single slot `J^O_{p,k}` vacates.
7. As case 6 but `J^I_{q,k}` after `0` as well. Two slots open, of sizes `p` and `q`, and
   the bin holds only short jobs of later pairs totalling at most `p + q`; by
   `Packing.sum_erase_le` one of them goes into the `q`-sized slot and the rest fit in the
   `p`-sized one.

In every case feasibility reduces to `Instance.feasible_of_move_one` or
`Instance.feasible_of_move_two`: the moved jobs land in
their own availability intervals (the deadline side is `parked_short_deadline` and the
chain conditions), they do not collide with each other by construction, and they do not
collide with anything untouched — inside the bin by `mem_binOcc_of_meets`, inside a vacated
slot because its previous occupant is itself moving. -/
theorem exchange_step {u : (inst A).Schedule} (h : (inst A).Feasible u) (k : ℕ)
    (hk : k < A.N) (hup : NormalizedUpTo A u k) :
    ∃ u' : (inst A).Schedule, (inst A).Feasible u' ∧ NormalizedUpTo A u' (k + 1) := by
  classical
  set i : Fin A.N := ⟨k, hk⟩ with hidef
  have hik : (i : ℕ) = k := rfl
  have hq := A.q_pos
  have hqp := A.q_lt_p
  have hwidth : (width p q : ℤ) = (p : ℤ) + 2 * q := by
    simp only [width]
    push_cast
    ring
  have hbneg : binStart A i + (p : ℤ) + q < 0 := by
    have := binStart_add_width_nonpos A i
    omega
  -- a job parked in bin `k` starts before `0`, so it is not one running after `0`
  have hbin_neg : ∀ z ∈ binOcc A u i, u z < 0 := by
    intro z hz
    have h2 := (Finset.mem_filter.mp hz).2.2
    have := (inst A).p_pos z
    omega
  -- settle bin `k`, keeping every earlier bin proper
  have key : ∃ u' : (inst A).Schedule, (inst A).Feasible u' ∧ ProperAt A u' i ∧
      (∀ j : Fin A.N, (j : ℕ) < k → ProperAt A u' j) := by
    by_cases hpI : u (Sum.inr (i, Part.longIn)) < 0
    · -- case 1
      exact exchange_innerLong A h hup i hik hpI
    push Not at hpI
    by_cases hpO : u (Sum.inr (i, Part.longOut)) < 0
    · by_cases hqI : u (Sum.inr (i, Part.shortIn)) < 0
      · -- case 2: already canonical
        exact ⟨u, h, exchange_bothIn A h hup i hik hpO hqI, hup⟩
      · -- case 3
        push Not at hqI
        exact exchange_longOutIn A h hup i hik hpO hqI
    push Not at hpO
    by_cases hL : ∃ z ∈ binOcc A u i, (inst A).p z = p
    · -- a foreign long job is parked in the bin: cases 4 and 4b
      obtain ⟨L, hLmem, hLlen⟩ := hL
      have hLin := (Finset.mem_filter.mp hLmem).2
      have hL1 : L ≠ Sum.inr (i, Part.longOut) := by
        rintro rfl
        exact absurd (hbin_neg _ hLmem) (by omega)
      by_cases hqI : u (Sum.inr (i, Part.shortIn)) < 0
      · exact exchange_foreignLong A h hup i hik hpI hpO hqI L hL1 hLlen hLin
      · push Not at hqI
        exact exchange_foreignLongOut A h hup i hik hpI hpO hqI L hL1 hLlen hLin
    · -- the bin holds only short jobs: cases 5 and 6
      push Not at hL
      have hnolong : ∀ z ∈ binOcc A u i, (inst A).p z = q := by
        intro z hz
        rcases inst_lengthsIn A z with h1 | h1
        · exact absurd h1 (hL z hz)
        · exact h1
      by_cases hqI : u (Sum.inr (i, Part.shortIn)) < 0
      · exact exchange_noLongInnerIn A h hup i hik hpO hqI hnolong
      · push Not at hqI
        exact exchange_noLongInnerOut A h hup i hik hpO hqI hnolong
  obtain ⟨u', hfeas, hprop, hrest⟩ := key
  refine ⟨u', hfeas, ?_⟩
  intro j hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
  · exact hrest j hlt
  · have hji : j = i := Fin.ext (by rw [heq, hik])
    exact hji ▸ hprop

/-- **The exchange argument.** Every feasible schedule can be rewritten into a normalized
one, one bin at a time. -/
theorem exists_normalized {u : (inst A).Schedule} (h : (inst A).Feasible u) :
    ∃ u' : (inst A).Schedule, (inst A).Feasible u' ∧ Normalized A u' := by
  have key : ∀ k, k ≤ A.N →
      ∃ u' : (inst A).Schedule, (inst A).Feasible u' ∧ NormalizedUpTo A u' k := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨u, h, fun i hi => absurd hi (by omega)⟩
    | succ k ih =>
      intro hk
      obtain ⟨u', h', hup'⟩ := ih (by omega)
      exact exchange_step A h' k (by omega) hup'
  obtain ⟨u', h', hup'⟩ := key A.N (le_refl _)
  exact ⟨u', h', fun i => hup' i i.isLt⟩

/-! ### Reading the solution off a normalized schedule

Once every bin holds a proper pair, the two jobs of each quad left over after time `0` *are*
the pending pair, and the reading-off is mechanical. Which of the two proper pairings a bin
holds is exactly the choice "`J_{p,i}` early or `J_{q,i}` early". -/

/-- Which job of the constructed instance stands in for a given job of `A`, once the
schedule is normalized. -/
noncomputable def source (u : (inst A).Schedule) : A.Job → A.Ord ⊕ Fin A.N × Part :=
  Sum.elim (fun o => Sum.inl o)
    (Sum.elim
      (fun i => Sum.inr (i, if u (Sum.inr (i, Part.longOut)) = binStart A i
        then Part.longIn else Part.longOut))
      (fun i => Sum.inr (i, if u (Sum.inr (i, Part.longOut)) = binStart A i
        then Part.shortOut else Part.shortIn)))

/-- The schedule for `A` read off a normalized schedule. -/
noncomputable def readOff (u : (inst A).Schedule) : A.toInstance.Schedule :=
  fun x => u (source A u x)

lemma source_injective (u : (inst A).Schedule) : Function.Injective (source A u) := by
  rintro (o | i | i) (o' | i' | i') hxy <;>
    simp only [source, Sum.elim_inl, Sum.elim_inr] at hxy
  · exact congrArg Sum.inl (Sum.inl.inj hxy)
  · exact absurd hxy (by simp)
  · exact absurd hxy (by simp)
  · exact absurd hxy (by simp)
  · have := Sum.inr.inj hxy
    exact congrArg (fun z => Sum.inr (Sum.inl z)) (congrArg Prod.fst this)
  · exfalso
    have := congrArg Prod.snd (Sum.inr.inj hxy)
    split_ifs at this
  · exact absurd hxy (by simp)
  · exfalso
    have := congrArg Prod.snd (Sum.inr.inj hxy)
    split_ifs at this
  · have := Sum.inr.inj hxy
    exact congrArg (fun z => Sum.inr (Sum.inr z)) (congrArg Prod.fst this)

lemma source_len (u : (inst A).Schedule) (x : A.Job) :
    (inst A).p (source A u x) = A.toInstance.p x := by
  rcases x with o | i | i
  · rfl
  · simp only [source, Sum.elim_inl, Sum.elim_inr, inst_p_quad, Aux.toInstance_p_long]
    split <;> rfl
  · simp only [source, Sum.elim_inr, inst_p_quad, Aux.toInstance_p_short]
    split <;> rfl

lemma binStart_neg (i : Fin A.N) : binStart A i < 0 := by
  have h1 := binStart_add_width_nonpos A i
  have h2 := A.q_pos
  simp only [width] at h1 ⊢
  push_cast at h1
  omega

/-- In a normalized schedule the two proper pairings are told apart by where the outer long
job sits. -/
lemma normalized_cases {u : (inst A).Schedule} (hn : Normalized A u) (i : Fin A.N) :
    (u (Sum.inr (i, Part.longOut)) = binStart A i ∧
        0 ≤ u (Sum.inr (i, Part.longIn)) ∧ 0 ≤ u (Sum.inr (i, Part.shortOut))) ∨
      (¬ u (Sum.inr (i, Part.longOut)) = binStart A i ∧
        0 ≤ u (Sum.inr (i, Part.longOut)) ∧ 0 ≤ u (Sum.inr (i, Part.shortIn))) := by
  have hneg := binStart_neg A i
  rcases hn i with ⟨h1, -, h3, h4⟩ | ⟨-, -, h3, h4⟩
  · exact Or.inl ⟨h1, h3, h4⟩
  · exact Or.inr ⟨by omega, h3, h4⟩

/-- **Lemma 1, converse direction, given a normalized schedule.** The two jobs of each quad
that the bin does not hold are the pending pair, and which pairing the bin holds is exactly
the choice "`J_{p,i}` early or `J_{q,i}` early". -/
theorem yes_of_normalized {u : (inst A).Schedule} (h : (inst A).Feasible u)
    (hn : Normalized A u) : A.Yes := by
  refine ⟨readOff A u, ⟨?_, ?_⟩, ?_⟩
  · intro x
    rcases x with o | i | i
    · refine ⟨(h.1 (Sum.inl o)).1, ?_⟩
      have hd := (h.1 (Sum.inl o)).2
      simp only [Instance.completion, inst_p_ord, inst_d_ord] at hd
      simpa only [Instance.completion, readOff, source, Aux.ordJob, Sum.elim_inl,
        Aux.toInstance_p_ord, Aux.toInstance_d_ord] using hd
    · rcases normalized_cases A hn i with ⟨htest, hp1, -⟩ | ⟨htest, hp1, -⟩
      · have hsrc : source A u (Aux.longJob i) = Sum.inr (i, Part.longIn) := by
          simp only [source, Aux.longJob, Sum.elim_inl, Sum.elim_inr]
          rw [if_pos htest]
        have hd := (h.1 (Sum.inr (i, Part.longIn))).2
        simp only [Instance.completion, inst_p_quad, inst_d_quad, quadDue, quadLen] at hd
        refine ⟨by simpa only [Aux.toInstance_r_long, readOff, hsrc] using hp1, ?_⟩
        simp only [Instance.completion, readOff, hsrc, Aux.toInstance_p_long,
          Aux.toInstance_d_long]
        exact le_trans hd (A.dp'_le_dp i)
      · have hsrc : source A u (Aux.longJob i) = Sum.inr (i, Part.longOut) := by
          simp only [source, Aux.longJob, Sum.elim_inl, Sum.elim_inr]
          rw [if_neg htest]
        have hd := (h.1 (Sum.inr (i, Part.longOut))).2
        simp only [Instance.completion, inst_p_quad, inst_d_quad, quadDue, quadLen] at hd
        refine ⟨by simpa only [Aux.toInstance_r_long, readOff, hsrc] using hp1, ?_⟩
        simp only [Instance.completion, readOff, hsrc, Aux.toInstance_p_long,
          Aux.toInstance_d_long]
        exact hd
    · rcases normalized_cases A hn i with ⟨htest, -, hp2⟩ | ⟨htest, -, hp2⟩
      · have hsrc : source A u (Aux.shortJob i) = Sum.inr (i, Part.shortOut) := by
          simp only [source, Aux.shortJob, Sum.elim_inr]
          rw [if_pos htest]
        have hd := (h.1 (Sum.inr (i, Part.shortOut))).2
        simp only [Instance.completion, inst_p_quad, inst_d_quad, quadDue, quadLen] at hd
        refine ⟨by simpa only [Aux.toInstance_r_short, readOff, hsrc] using hp2, ?_⟩
        simp only [Instance.completion, readOff, hsrc, Aux.toInstance_p_short,
          Aux.toInstance_d_short]
        exact hd
      · have hsrc : source A u (Aux.shortJob i) = Sum.inr (i, Part.shortIn) := by
          simp only [source, Aux.shortJob, Sum.elim_inr]
          rw [if_neg htest]
        have hd := (h.1 (Sum.inr (i, Part.shortIn))).2
        simp only [Instance.completion, inst_p_quad, inst_d_quad, quadDue, quadLen] at hd
        refine ⟨by simpa only [Aux.toInstance_r_short, readOff, hsrc] using hp2, ?_⟩
        simp only [Instance.completion, readOff, hsrc, Aux.toInstance_p_short,
          Aux.toInstance_d_short]
        exact le_trans hd (A.dq'_le_dq i)
  · intro x y hxy
    have hx := source_len A u x
    have hy := source_len A u y
    have hsep := h.2 (source A u x) (source A u y) (fun hc => hxy (source_injective A u hc))
    simp only [Instance.completion, hx, hy] at hsep
    simpa only [Instance.completion, readOff] using hsep
  · intro i
    rcases normalized_cases A hn i with ⟨htest, -, -⟩ | ⟨htest, -, -⟩
    · left
      have hsrc : source A u (Aux.longJob i) = Sum.inr (i, Part.longIn) := by
        simp only [source, Aux.longJob, Sum.elim_inl, Sum.elim_inr]
        rw [if_pos htest]
      have hd := (h.1 (Sum.inr (i, Part.longIn))).2
      simp only [Instance.completion, inst_p_quad, inst_d_quad, quadDue, quadLen] at hd
      simp only [Aux.LongEarly, Instance.completion, readOff, hsrc, Aux.toInstance_p_long]
      exact hd
    · right
      have hsrc : source A u (Aux.shortJob i) = Sum.inr (i, Part.shortIn) := by
        simp only [source, Aux.shortJob, Sum.elim_inr]
        rw [if_neg htest]
      have hd := (h.1 (Sum.inr (i, Part.shortIn))).2
      simp only [Instance.completion, inst_p_quad, inst_d_quad, quadDue, quadLen] at hd
      simp only [Aux.ShortEarly, Instance.completion, readOff, hsrc, Aux.toInstance_p_short]
      exact hd

/-- **Lemma 1, converse direction.** A feasible schedule for the constructed instance
yields a solution to `AUX(p, q)`: normalize it, then read the answer off. -/
theorem yes_of_isYes (h : (inst A).IsYes) : auxProblem p q A := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨u', hu', hn⟩ := exists_normalized A hu
  exact yes_of_normalized A hu' hn

/-- **Lemma 1.** An instance of `AUX(p, q)` has a solution exactly when the constructed
instance has a feasible schedule. -/
theorem correct : auxProblem p q A ↔ (inst A).IsYes :=
  ⟨isYes_of_yes A, yes_of_isYes A⟩

end Stacked

end RjLmax

end Lax391470Proofs
