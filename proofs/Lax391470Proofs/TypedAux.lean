import Mathlib.Data.Fintype.Sum
import Lax391470Proofs.TypedPacking

namespace Lax391470Proofs

/-!
# The Auxiliary Problem `AUX(p, q)`

Definition 2 of Elffers–de Weerdt. The paper's hardness proof does not go from SAT to
`1|rⱼ|Lmax` directly. It goes through an intermediate problem in which some jobs carry
*two* deadlines, an early one and a late one, and the jobs are linked in pairs of which at
least one must meet its early deadline. `RjLmax.FromSat` reduces SAT to `AUX(p, q)`
(Lemma 2), and `RjLmax.Stacked` reduces `AUX(p, q)` back to `1|rⱼ|Lmax` (Lemma 1).

The point of the detour is stated in the paper as: "The key property of this model is that
it is possible to specify dependencies between jobs with deadlines far away from each
other." A pair `(J_{p,i}, J_{q,i})` is a disjunction — *this* long job is early *or* *that*
short job is early — between two jobs that may sit anywhere on the time line, and a
disjunction is what a clause needs.

## The Shape of an Instance

Ordinary jobs `J` behave as in `1|rⱼ|Lmax`, with non-negative release times. On top of
them sit two sequences of `N` pending jobs, `J_p` (all of length `p`) and `J_q` (all of
length `q`), all released at time `0`, the `i`'th of each carrying an early deadline
`d'` and a late deadline `d`. The late deadline is a hard constraint like any other; the
early one is what the pairing is about.

The deadlines are constrained by Definition 2's display:

* `d'_{p,1} ≤ d_{p,1} ≤ d'_{p,2} ≤ … ≤ d'_{p,N} ≤ d_{p,N}` — the long jobs' two-deadline
  intervals are ordered and pairwise disjoint, so "the `i`'th most urgent long job" is
  unambiguous;
* the same for the short jobs;
* `d_{p,i} ≤ d'_{q,i}` — within a pair, the long job is the more urgent one. This is the
  nesting that `RjLmax.Stacked` turns into a stack of four jobs per pair.
-/

namespace RjLmax

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- **Definition 2: an instance of `AUX(p, q)`.** Ordinary jobs with non-negative release
times and lengths in `{p, q}`, together with `N` pairs of pending jobs — one long, one
short — released at `0` and carrying an early and a late deadline each. -/
structure Aux (p q : ℕ) where
  /-- The ordinary jobs. -/
  Ord : Type
  /-- The ordinary jobs are finite. -/
  ordFintype : Fintype Ord
  /-- The ordinary jobs have decidable equality. -/
  ordDecEq : DecidableEq Ord
  /-- Release time of an ordinary job. -/
  r : Ord → ℤ
  /-- Deadline of an ordinary job. -/
  d : Ord → ℤ
  /-- Length of an ordinary job. -/
  len : Ord → ℕ
  /-- Ordinary jobs are released at or after time `0`. -/
  r_nonneg : ∀ o, 0 ≤ r o
  /-- Ordinary jobs are long or short. -/
  len_eq : ∀ o, len o = p ∨ len o = q
  /-- The short job length is positive. -/
  q_pos : 0 < q
  /-- The long job length exceeds the short one. -/
  q_lt_p : q < p
  /-- The number of pending job pairs. -/
  N : ℕ
  /-- Early deadline of the `i`'th long pending job, `d'_{p,i}`. -/
  dp' : Fin N → ℤ
  /-- Late deadline of the `i`'th long pending job, `d_{p,i}`. -/
  dp : Fin N → ℤ
  /-- Early deadline of the `i`'th short pending job, `d'_{q,i}`. -/
  dq' : Fin N → ℤ
  /-- Late deadline of the `i`'th short pending job, `d_{q,i}`. -/
  dq : Fin N → ℤ
  /-- `d'_{p,i} ≤ d_{p,i}`. -/
  dp'_le_dp : ∀ i, dp' i ≤ dp i
  /-- `d_{p,i} ≤ d'_{p,i+1}`: the long jobs' deadline intervals do not intersect. -/
  dp_le_dp'_succ : ∀ i j : Fin N, (i : ℕ) + 1 = (j : ℕ) → dp i ≤ dp' j
  /-- `d'_{q,i} ≤ d_{q,i}`. -/
  dq'_le_dq : ∀ i, dq' i ≤ dq i
  /-- `d_{q,i} ≤ d'_{q,i+1}`: the short jobs' deadline intervals do not intersect. -/
  dq_le_dq'_succ : ∀ i j : Fin N, (i : ℕ) + 1 = (j : ℕ) → dq i ≤ dq' j
  /-- `d_{p,i} ≤ d'_{q,i}`: inside a pair, the long job is the more urgent. -/
  dp_le_dq' : ∀ i, dp i ≤ dq' i
  /-- Early deadlines are non-negative. A pending job is released at `0`, so a negative
  deadline would make it unschedulable outright; the paper's instances all have positive
  deadlines. Late deadlines inherit this through `dp'_le_dp` and `dq'_le_dq`. -/
  dp'_nonneg : ∀ i, 0 ≤ dp' i
  /-- Early deadlines are non-negative; see `dp'_nonneg`. -/
  dq'_nonneg : ∀ i, 0 ≤ dq' i

attribute [instance] Aux.ordFintype Aux.ordDecEq

namespace Aux

variable {p q : ℕ} (A : Aux p q)

/-! ## 1. The jobs of an `AUX` instance -/

/-- The jobs of `A`: the ordinary ones, the `N` long pending ones, the `N` short pending
ones. -/
abbrev Job : Type := A.Ord ⊕ Fin A.N ⊕ Fin A.N

variable {A}

/-- An ordinary job, as a job. -/
abbrev ordJob (o : A.Ord) : A.Job := Sum.inl o

/-- The `i`'th long pending job `J_{p,i}`. -/
abbrev longJob (i : Fin A.N) : A.Job := Sum.inr (Sum.inl i)

/-- The `i`'th short pending job `J_{q,i}`. -/
abbrev shortJob (i : Fin A.N) : A.Job := Sum.inr (Sum.inr i)

variable (A)

/-! ## 2. The underlying scheduling instance

Forgetting the early deadlines leaves an ordinary `1|rⱼ|Lmax` instance: pending jobs are
released at `0` and must meet their *late* deadline. -/

/-- The `1|rⱼ|Lmax` instance underlying `A`: the early deadlines are dropped, and the
pending jobs become ordinary jobs released at `0` with their late deadlines. -/
def toInstance : Instance where
  Job := A.Job
  jobFintype := inferInstance
  jobDecEq := inferInstance
  r := Sum.elim A.r (Sum.elim (fun _ => 0) (fun _ => 0))
  d := Sum.elim A.d (Sum.elim A.dp A.dq)
  p := Sum.elim A.len (Sum.elim (fun _ => p) (fun _ => q))
  p_pos := by
    rintro (o | i | i)
    · rcases A.len_eq o with h | h <;> simp only [Sum.elim_inl, h] <;>
        [exact lt_trans A.q_pos A.q_lt_p; exact A.q_pos]
    · exact lt_trans A.q_pos A.q_lt_p
    · exact A.q_pos

/-! ## 3. Early completion, and the question -/

variable {A}

/- These are proved by `simp` rather than `rfl`: a `rfl` lemma is used by `simp` without
appearing in the proof term, and the archive's usage check would report it as unused. -/
@[simp] lemma toInstance_r_ord (o : A.Ord) : A.toInstance.r (ordJob o) = A.r o := by
  simp [toInstance]
@[simp] lemma toInstance_r_long (i : Fin A.N) : A.toInstance.r (longJob i) = 0 := by
  simp [toInstance]
@[simp] lemma toInstance_r_short (i : Fin A.N) : A.toInstance.r (shortJob i) = 0 := by
  simp [toInstance]
@[simp] lemma toInstance_d_ord (o : A.Ord) : A.toInstance.d (ordJob o) = A.d o := by
  simp [toInstance]
@[simp] lemma toInstance_d_long (i : Fin A.N) : A.toInstance.d (longJob i) = A.dp i := by
  simp [toInstance]
@[simp] lemma toInstance_d_short (i : Fin A.N) : A.toInstance.d (shortJob i) = A.dq i := by
  simp [toInstance]
@[simp] lemma toInstance_p_ord (o : A.Ord) : A.toInstance.p (ordJob o) = A.len o := by
  simp [toInstance]
@[simp] lemma toInstance_p_long (i : Fin A.N) : A.toInstance.p (longJob i) = p := by
  simp [toInstance]

@[simp] lemma toInstance_p_short (i : Fin A.N) : A.toInstance.p (shortJob i) = q := by
  simp [toInstance]

/-- The `i`'th long pending job meets its **early** deadline. -/
def LongEarly (t : A.toInstance.Schedule) (i : Fin A.N) : Prop :=
  Instance.completion t (longJob i) ≤ A.dp' i

/-- The `i`'th short pending job meets its **early** deadline. -/
def ShortEarly (t : A.toInstance.Schedule) (i : Fin A.N) : Prop :=
  Instance.completion t (shortJob i) ≤ A.dq' i

instance (t : A.toInstance.Schedule) (i : Fin A.N) : Decidable (LongEarly t i) := by
  unfold LongEarly; infer_instance

instance (t : A.toInstance.Schedule) (i : Fin A.N) : Decidable (ShortEarly t i) := by
  unfold ShortEarly; infer_instance

/-- A schedule *solves* `A`: it is feasible, and in every connected pair at least one of
the two pending jobs meets its early deadline. -/
def Solves (t : A.toInstance.Schedule) : Prop :=
  A.toInstance.Feasible t ∧ ∀ i : Fin A.N, LongEarly t i ∨ ShortEarly t i

variable (A)

/-- **The question of Definition 2**: is there a feasible schedule in which, for every
`1 ≤ i ≤ N`, `J_{p,i}` or `J_{q,i}` completes by its early deadline? -/
def Yes : Prop := ∃ t : A.toInstance.Schedule, Solves t

variable {A}

lemma dp_nonneg (A : Aux p q) (i : Fin A.N) : 0 ≤ A.dp i :=
  le_trans (A.dp'_nonneg i) (A.dp'_le_dp i)

lemma dq_nonneg (A : Aux p q) (i : Fin A.N) : 0 ≤ A.dq i :=
  le_trans (A.dq'_nonneg i) (A.dq'_le_dq i)

/-- Every job of `A.toInstance` is released at or after time `0`. -/
lemma toInstance_r_nonneg (A : Aux p q) (x : A.Job) : 0 ≤ A.toInstance.r x := by
  rcases x with o | i | i
  · exact A.r_nonneg o
  · exact le_refl 0
  · exact le_refl 0

/-- Consequently every job of a feasible schedule of `A.toInstance` starts at or after
time `0` — the whole of an `AUX` instance lives in `[0, ∞)`. -/
lemma nonneg_of_feasible {A : Aux p q} {t : A.toInstance.Schedule}
    (h : A.toInstance.Feasible t) (x : A.Job) : 0 ≤ t x :=
  le_trans (toInstance_r_nonneg A x) (h.1 x).1

/-! ## 2b. The chain conditions, in transitive form

Definition 2 states its deadline conditions between *consecutive* pairs: `d_{p,i}` is at
most `d'_{p,i+1}`. What a construction wants to check, and what the proofs downstream
actually use, is the transitive consequence — an earlier pair's late deadline is at most
any later pair's early deadline. The two are equivalent, and this section proves the
direction that needs an argument, so a construction may verify whichever is convenient.

This is also what lets a reduction index its pending pairs by any finite linear order it
finds natural (sections, blocks, clauses) rather than by an explicit `Fin N` enumeration:
transport along the order isomorphism, and only the `i < j` form has to be checked. -/

/-- The long pending jobs' deadline intervals are ordered, not merely non-overlapping
between neighbours: pair `i`'s late deadline is at most pair `j`'s early deadline whenever
`i` comes before `j`. -/
lemma dp_le_dp'_of_lt (A : Aux p q) :
    ∀ (d : ℕ) (i j : Fin A.N), (j : ℕ) = (i : ℕ) + d + 1 → A.dp i ≤ A.dp' j := by
  intro d
  induction d with
  | zero =>
    intro i j hj
    exact A.dp_le_dp'_succ i j (by omega)
  | succ d ih =>
    intro i j hj
    have hlt : (i : ℕ) + d + 1 < A.N := by
      have := j.isLt
      omega
    refine le_trans (le_trans (ih i ⟨(i : ℕ) + d + 1, hlt⟩ rfl) (A.dp'_le_dp _)) ?_
    exact A.dp_le_dp'_succ _ j (by simp only []; omega)

/-- The same for the short pending jobs. -/
lemma dq_le_dq'_of_lt (A : Aux p q) :
    ∀ (d : ℕ) (i j : Fin A.N), (j : ℕ) = (i : ℕ) + d + 1 → A.dq i ≤ A.dq' j := by
  intro d
  induction d with
  | zero =>
    intro i j hj
    exact A.dq_le_dq'_succ i j (by omega)
  | succ d ih =>
    intro i j hj
    have hlt : (i : ℕ) + d + 1 < A.N := by
      have := j.isLt
      omega
    refine le_trans (le_trans (ih i ⟨(i : ℕ) + d + 1, hlt⟩ rfl) (A.dq'_le_dq _)) ?_
    exact A.dq_le_dq'_succ _ j (by simp only []; omega)

/-- Pair `i`'s long job is more urgent than pair `j`'s short job whenever `i ≤ j`: within a
pair by `dp_le_dq'`, across pairs by the chain. This is the nesting that
`TypedStacked.lean` turns into a stack of four jobs. -/
lemma dp_le_dq'_of_le (A : Aux p q) {i j : Fin A.N} (h : (i : ℕ) ≤ (j : ℕ)) :
    A.dp i ≤ A.dq' j := by
  rcases Nat.eq_or_lt_of_le h with heq | hlt
  · have : i = j := Fin.ext heq
    subst this
    exact A.dp_le_dq' i
  · refine le_trans (dp_le_dp'_of_lt A ((j : ℕ) - (i : ℕ) - 1) i j (by omega)) ?_
    exact le_trans (A.dp'_le_dp j) (A.dp_le_dq' j)

/-- An instance with no jobs at all is trivially solvable: the empty schedule solves it,
and there are no pairs to satisfy. -/
lemma yes_of_isEmpty (A : Aux p q) (h : IsEmpty A.Job) : A.Yes :=
  ⟨fun i => (h.false i).elim,
    ⟨fun i => (h.false i).elim, fun i _ _ => (h.false i).elim⟩,
    fun i => (h.false (longJob i)).elim⟩

lemma Solves.feasible {t : A.toInstance.Schedule} (h : Solves t) : A.toInstance.Feasible t :=
  h.1

lemma Solves.pair {t : A.toInstance.Schedule} (h : Solves t) (i : Fin A.N) :
    LongEarly t i ∨ ShortEarly t i := h.2 i

/-- In a solving schedule the two pending jobs of a pair are never *both* late — that is
the whole content of the pairing. -/
lemma Solves.not_both_late {t : A.toInstance.Schedule} (h : Solves t) (i : Fin A.N)
    (hlong : ¬ LongEarly t i) : ShortEarly t i :=
  (h.pair i).resolve_left hlong

end Aux

end RjLmax

end Lax391470Proofs
