import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.Sort
import Lax391470Proofs.TypedBlocks
import Lax391470Proofs.TypedProblems

namespace Lax391470Proofs

/-!
# Lemma 2: SAT reduces to `AUX(p, q)`

Definition 7 of Elffers–de Weerdt. Given a CNF formula with `n` variables and `m` clauses,
the instance of `AUX(p, q)` is `2n` **sections**, one per literal, laid out left to right
in the order `x₀, ¬x₀, x₁, ¬x₁, …`. Each section is

* a **literal block** `Lit[l]` at the start of the section — `V⁺` if `l` is positive,
  `V⁻` if negative (`TypedBlocks.lean`);
* one **clause block** `Cl[l, j]` per clause, laid end to end after it — `C_active` if
  `l` occurs in clause `j`, `C_inactive` otherwise;
* a **separator** job of length `q` occupying the last `q` units of the section, with an
  availability interval exactly its own length, so it is pinned.

Every section has the same length `S = p + 2q + m(p+q) + 1 + q`, and the total job length
inside one is `S - 1`: one unit of slack, and no more. A section can spend that unit at the
start, which lets its literal block's pending job finish early and displaces everything
after it by one; or it can pack tight, and the pending job is late. So the pending job of
`Lit[l]` is late exactly when `l` is true.

The file is organised as: the layout and its geometry (§1–§3), the pairing and Definition
2's four chain conditions (§4–§7), the instance itself (§8), Lemma 3 (§9–§10) and Lemma 4
with Propositions 2 and 3 beneath it (§11).

## A formula with no variables

Definition 7 tacitly assumes `n ≥ 1`. With `n = 0` there are no literals, hence no
sections and no jobs, so the constructed instance is trivially a yes-instance — while the
formula itself is satisfiable only if it also has no clauses, an empty clause being
unsatisfiable by definition. The assembled reduction therefore has to treat `n = 0`
separately, mapping such a formula to an explicitly infeasible instance when it has
clauses. Nothing else in the construction is affected.
-/

namespace RjLmax
namespace FromSat

open Sat

variable (p q : ℕ) (φ : Cnf)

/-! ## 1. Where everything sits

All offsets are absolute times. A section is `S` long; within it the literal block starts
at `0`, clause block `j` at `p + 2q + j(p+q)`, and the separator at `S - q`. -/

/-- `S`, the length of one section: the literal block, the `m` clause blocks, one unit of
slack, and the separator. -/
def secLen : ℕ := p + 2 * q + φ.m * (p + q) + 1 + q

/-- The position of a literal in the order `x₀, ¬x₀, x₁, ¬x₁, …`. -/
def secIndex {n : ℕ} (l : Literal n) : ℕ := 2 * (l.var : ℕ) + (if l.pos then 0 else 1)

/-- Where the section for `l` begins. -/
def secOffset (l : Literal φ.n) : ℤ := (secLen p q φ : ℤ) * secIndex l

/-- Where the literal block `Lit[l]` begins: at the start of its section. -/
def litOffset (l : Literal φ.n) : ℤ := secOffset p q φ l

/-- Where the clause block `Cl[l, j]` begins. -/
def clOffset (l : Literal φ.n) (j : Fin φ.m) : ℤ :=
  secOffset p q φ l + (p : ℤ) + 2 * q + (j : ℕ) * ((p : ℤ) + q)

/-- Where the separator of `l`'s section begins: the last `q` units of the section. -/
def sepOffset (l : Literal φ.n) : ℤ := secOffset p q φ l + (secLen p q φ : ℤ) - q

/-- `Cl[l, j]` is a `C_active` block exactly when `l` occurs in clause `j`. -/
def active (l : Literal φ.n) (j : Fin φ.m) : Bool := decide (l ∈ φ.clause j)

/-! ## 2. The jobs

Three families: the three jobs of each literal block, the two pending jobs of each clause
block, and one separator per section. -/

/-- The jobs of the constructed instance. -/
abbrev Job : Type :=
  (Literal φ.n × Blocks.LitJob) ⊕ (Literal φ.n × Fin φ.m × Blocks.ClJob) ⊕ Literal φ.n

/-- Release time of a job. The pending jobs — the `pend` job of a literal block and both
jobs of a clause block — are released at `0`, as Definition 2 requires; it is Proposition 2
that will confine them to their own blocks. -/
def rel : Job φ → ℤ
  | Sum.inl (_l, .pend) => 0
  | Sum.inl (l, c) => litOffset p q φ l + Blocks.LitJob.rel p q l.pos c
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr l) => sepOffset p q φ l

/-- Processing time of a job. -/
def len : Job φ → ℕ
  | Sum.inl (l, c) => Blocks.LitJob.len p q l.pos c
  | Sum.inr (Sum.inl (_, _, c)) => Blocks.clLen p q c
  | Sum.inr (Sum.inr _) => q

/-- The **late** deadline of a job — the one every schedule must meet. -/
def due : Job φ → ℤ
  | Sum.inl (l, c) => litOffset p q φ l + Blocks.LitJob.due p q l.pos c
  | Sum.inr (Sum.inl (l, j, _)) => clOffset p q φ l j + Blocks.clDue p q
  | Sum.inr (Sum.inr l) => sepOffset p q φ l + q

/-! ## 3. The geometry

The facts the rest of Lemma 2 needs: sections are disjoint and in order, the blocks inside
a section are laid end to end, the separator is pinned at the end, and the total job length
in a section is `S - 1` — one unit of slack. -/

variable {p q φ}

/-- The separator ends exactly at the end of its section. -/
lemma sepOffset_add (l : Literal φ.n) :
    sepOffset p q φ l + q = secOffset p q φ l + (secLen p q φ : ℤ) := by
  simp only [sepOffset]
  ring

/-- Sections are laid out in order of `secIndex`, each `S` long, so an earlier section ends
before a later one begins. -/
lemma secOffset_mono {l l' : Literal φ.n} (h : secIndex l < secIndex l') :
    secOffset p q φ l + (secLen p q φ : ℤ) ≤ secOffset p q φ l' := by
  simp only [secOffset]
  have h1 : (secIndex l : ℤ) + 1 ≤ (secIndex l' : ℤ) := by exact_mod_cast h
  have h2 : (0 : ℤ) ≤ (secLen p q φ : ℤ) := by positivity
  nlinarith

/-- Distinct literals occupy distinct sections. -/
lemma secIndex_injective {n : ℕ} {l l' : Literal n} (h : secIndex l = secIndex l') :
    l = l' := by
  obtain ⟨v, s⟩ := l
  obtain ⟨v', s'⟩ := l'
  simp only [secIndex] at h
  cases s <;> cases s' <;> simp_all <;> omega

/-- There are `2n` sections, and `secIndex` numbers them `0, …, 2n-1`. -/
lemma secIndex_lt {n : ℕ} (l : Literal n) : secIndex l < 2 * n := by
  have h := l.var.isLt
  have hb : (if l.pos then 0 else 1) ≤ 1 := by split <;> omega
  simp only [secIndex]
  omega

/-! ## 4. The connected pairs

Definition 7's pairing. For each variable `i` the long pending job of `Lit[xᵢ]` is paired
with the short one of `Lit[¬xᵢ]`; and for each clause `j` and each of the `2n-1` adjacent
section pairs `k`, the long pending job of `Cl[l(k), j]` is paired with the short one of
`Cl[l(k+1), j]`. That leaves the last `m` long and the first `m` short pending jobs
unpaired, which is why there are `n + (2n-1)m` pairs and not more.

Definition 2 wants these indexed by `Fin N` in deadline order. Rather than build that
enumeration by hand — which means dividing by the group size `1 + 2m` and reasoning about
`i·(1+2m)`, nonlinear and out of `omega`'s reach — the pairs are given their natural
structure, ordered by a sort key, and handed to `monoEquivOfFin`. The enumeration comes
back for free, and the chain conditions can then be checked structurally, one constructor
at a time. `Aux.dp_le_dp'_of_lt` is what makes that sound: the consecutive conditions of
Definition 2 and the transitive ones are equivalent. -/

variable (φ)

/-- A connected pair of pending jobs: a literal pair, or a clause pair between two
adjacent sections. -/
abbrev Pair : Type := Fin φ.n ⊕ Fin (2 * φ.n - 1) × Fin φ.m

/-- The number of connected pairs, `N = n + (2n-1)m`. -/
def numPairs : ℕ := φ.n + (2 * φ.n - 1) * φ.m

/-- The sort key of a pair: which variable's group it belongs to, and where it sits inside
that group. A group is the literal pair of `xᵢ` (position `0`), then the `m` clause pairs
running from `xᵢ` to `¬xᵢ` (positions `1 … m`), then the `m` running from `¬xᵢ` to
`xᵢ₊₁` (positions `m+1 … 2m`). Ordering by this key is ordering by deadline. -/
def key : Pair φ → ℕ × ℕ
  | Sum.inl i => ((i : ℕ), 0)
  | Sum.inr (k, j) =>
      ((k : ℕ) / 2, if (k : ℕ) % 2 = 0 then (j : ℕ) + 1 else φ.m + 1 + (j : ℕ))

lemma key_injective : Function.Injective (key φ) := by
  rintro (i | ⟨k, j⟩) (i' | ⟨k', j'⟩) h <;>
    simp only [key, Prod.mk.injEq] at h
  · exact congrArg Sum.inl (Fin.ext h.1)
  · have := j'.isLt
    split at h <;> omega
  · have := j.isLt
    split at h <;> omega
  · obtain ⟨h1, h2⟩ := h
    have hj := j.isLt
    have hj' := j'.isLt
    have hkk : (k : ℕ) = (k' : ℕ) := by
      split at h2 <;> split at h2 <;> omega
    have hjj : (j : ℕ) = (j' : ℕ) := by
      split at h2 <;> split at h2 <;> omega
    simp only [Sum.inr.injEq, Prod.mk.injEq]
    exact ⟨Fin.ext hkk, Fin.ext hjj⟩

/-- The pairs, linearly ordered by their deadlines. -/
instance : LinearOrder (Pair φ) :=
  LinearOrder.lift' (fun P => (toLex (key φ P) : ℕ ×ₗ ℕ))
    (fun P Q h => key_injective φ (by simpa using h))

lemma card_pair : Fintype.card (Pair φ) = numPairs φ := by
  simp [numPairs]

/-- The pairs of Definition 7, enumerated in deadline order — the `Fin N` indexing that
Definition 2 asks for. -/
noncomputable def pairEquiv : Fin (numPairs φ) ≃o Pair φ :=
  monoEquivOfFin (Pair φ) (card_pair φ)

/-! ## 5. The deadlines of a pair

Each pair carries four deadlines: the early and late one of its long pending job, and of
its short one. Where those jobs sit is Definition 7's pairing, and their deadlines are
read off the block they sit in — `TypedBlocks.lean` for the values, §1 above for the
offsets. -/

/-- The literal whose section has index `s` in the order `x₀, ¬x₀, x₁, ¬x₁, …`. -/
def litOfIndex {n : ℕ} (s : ℕ) (h : s < 2 * n) : Literal n :=
  ⟨⟨s / 2, by omega⟩, decide (s % 2 = 0)⟩

@[simp] lemma secIndex_litOfIndex {n : ℕ} (s : ℕ) (h : s < 2 * n) :
    secIndex (litOfIndex s h) = s := by
  by_cases hs : s % 2 = 0 <;>
    simp only [secIndex, litOfIndex, hs, decide_true, decide_false, if_true, if_false,
      Bool.false_eq_true] <;>
    omega

/-- The section index of the literal a clause pair's long job sits in. -/
lemma clause_lt {k : Fin (2 * φ.n - 1)} : (k : ℕ) < 2 * φ.n := by
  have := k.isLt
  omega

/-- The section index of the literal its short job sits in: the next one along. -/
lemma clause_succ_lt {k : Fin (2 * φ.n - 1)} : (k : ℕ) + 1 < 2 * φ.n := by
  have := k.isLt
  omega

variable (p q)

/-- The **late** deadline of a pair's long pending job. -/
def dpOf : Pair φ → ℤ
  | Sum.inl i => litOffset p q φ ⟨i, true⟩ + Blocks.LitJob.due p q true .pend
  | Sum.inr (k, j) => clOffset p q φ (litOfIndex (k : ℕ) (clause_lt φ)) j + Blocks.clDue p q

/-- The **early** deadline of a pair's long pending job. -/
def dpOf' : Pair φ → ℤ
  | Sum.inl i => litOffset p q φ ⟨i, true⟩ + Blocks.litEarly p q true
  | Sum.inr (k, j) =>
      let l := litOfIndex (k : ℕ) (clause_lt φ)
      clOffset p q φ l j + Blocks.clEarly p q (active φ l j)

/-- The **late** deadline of a pair's short pending job. -/
def dqOf : Pair φ → ℤ
  | Sum.inl i => litOffset p q φ ⟨i, false⟩ + Blocks.LitJob.due p q false .pend
  | Sum.inr (k, j) =>
      clOffset p q φ (litOfIndex ((k : ℕ) + 1) (clause_succ_lt φ)) j + Blocks.clDue p q

/-- The **early** deadline of a pair's short pending job. -/
def dqOf' : Pair φ → ℤ
  | Sum.inl i => litOffset p q φ ⟨i, false⟩ + Blocks.litEarly p q false
  | Sum.inr (k, j) =>
      let l := litOfIndex ((k : ℕ) + 1) (clause_succ_lt φ)
      clOffset p q φ l j + Blocks.clEarly p q (active φ l j)

/-! ## 6. Where a pair's jobs sit, as a function of its sort key

To order one pair's deadlines against another's, the block offsets have to be compared,
and for that it helps to have them as a single formula in the sort key rather than as a
case split over constructors. Within a variable's group the long job's block advances by
at least `p + q` at every step; between groups it advances by two whole sections. -/

/-- The offset, relative to the start of its variable's group, of the block holding a
pair's long pending job. Position `0` is the literal block of `xᵢ`; positions `1 … m` are
the clause blocks of `xᵢ`'s section; positions `m+1 … 2m` those of `¬xᵢ`'s, one section
further along. -/
def posOffset (pos : ℕ) : ℤ :=
  if pos = 0 then 0
  else if pos ≤ φ.m then (p : ℤ) + 2 * q + ((pos : ℤ) - 1) * ((p : ℤ) + q)
  else (secLen p q φ : ℤ) + (p : ℤ) + 2 * q + ((pos : ℤ) - φ.m - 1) * ((p : ℤ) + q)

/-- Where the block holding a pair's long pending job begins. -/
def longOffset (P : Pair φ) : ℤ :=
  2 * (secLen p q φ : ℤ) * (key φ P).1 + posOffset p q φ (key φ P).2

lemma longOffset_inl (i : Fin φ.n) :
    longOffset p q φ (Sum.inl i) = litOffset p q φ ⟨i, true⟩ := by
  simp only [longOffset, key, posOffset, litOffset, secOffset, secIndex, if_true]
  push_cast
  ring

lemma longOffset_inr (k : Fin (2 * φ.n - 1)) (j : Fin φ.m) :
    longOffset p q φ (Sum.inr (k, j)) =
      clOffset p q φ (litOfIndex (k : ℕ) (clause_lt φ)) j := by
  have hj := j.isLt
  have hk : ((k : ℕ) : ℤ) = 2 * (((k : ℕ) / 2 : ℕ) : ℤ) + (((k : ℕ) % 2 : ℕ) : ℤ) := by
    have : (k : ℕ) = 2 * ((k : ℕ) / 2) + (k : ℕ) % 2 := by omega
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) this
  simp only [longOffset, key, clOffset, secOffset, secIndex_litOfIndex]
  by_cases hpar : (k : ℕ) % 2 = 0
  · simp only [hpar, if_true, posOffset]
    rw [if_neg (by omega), if_pos (by omega)]
    rw [hk, hpar]
    push_cast
    ring
  · have hpar1 : (k : ℕ) % 2 = 1 := by omega
    simp only [hpar, if_false, posOffset]
    rw [if_neg (by omega), if_neg (by omega)]
    rw [hk, hpar1]
    push_cast
    ring

/-! ### The long job's block advances by at least `p + q` at every step -/

lemma posOffset_nonneg (pos : ℕ) : 0 ≤ posOffset p q φ pos := by
  by_cases h0 : pos = 0
  · simp [posOffset, h0]
  by_cases hm : pos ≤ φ.m
  · simp only [posOffset, if_neg h0, if_pos hm]
    have h1 : (0 : ℤ) ≤ ((pos : ℤ) - 1) * ((p : ℤ) + q) :=
      mul_nonneg (by omega) (by positivity)
    omega
  · simp only [posOffset, if_neg h0, if_neg hm]
    have h1 : (0 : ℤ) ≤ ((pos : ℤ) - φ.m - 1) * ((p : ℤ) + q) :=
      mul_nonneg (by omega) (by positivity)
    have h2 : (0 : ℤ) ≤ (secLen p q φ : ℤ) := by positivity
    omega

/-- A group spans less than two sections: everything in it, plus one more block, still
fits. -/
lemma posOffset_le (hq : 0 < q) {pos : ℕ} (h : pos ≤ 2 * φ.m) :
    posOffset p q φ pos + ((p : ℤ) + q) ≤ 2 * (secLen p q φ : ℤ) := by
  have hS : (secLen p q φ : ℤ) = (p : ℤ) + 2 * q + φ.m * ((p : ℤ) + q) + 1 + q := by
    simp only [secLen]
    push_cast
    ring
  have hM : (0 : ℤ) ≤ (φ.m : ℤ) * ((p : ℤ) + q) := by positivity
  by_cases h0 : pos = 0
  · simp only [posOffset, if_pos h0]
    omega
  by_cases hm : pos ≤ φ.m
  · simp only [posOffset, if_neg h0, if_pos hm]
    have hstep : ((pos : ℤ) - 1) * ((p : ℤ) + q) + ((p : ℤ) + q) =
        (pos : ℤ) * ((p : ℤ) + q) := by ring
    have h1 : (pos : ℤ) * ((p : ℤ) + q) ≤ (φ.m : ℤ) * ((p : ℤ) + q) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact_mod_cast hm
    omega
  · simp only [posOffset, if_neg h0, if_neg hm]
    have hstep : ((pos : ℤ) - φ.m - 1) * ((p : ℤ) + q) + ((p : ℤ) + q) =
        ((pos : ℤ) - φ.m) * ((p : ℤ) + q) := by ring
    have h1 : ((pos : ℤ) - φ.m) * ((p : ℤ) + q) ≤ (φ.m : ℤ) * ((p : ℤ) + q) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have : (pos : ℤ) ≤ 2 * (φ.m : ℤ) := by exact_mod_cast h
      omega
    omega

/-- Inside a group, the long job's block advances by at least `p + q` per step. -/
lemma posOffset_step (hq : 0 < q) {pos pos' : ℕ} (h : pos < pos') :
    posOffset p q φ pos + ((p : ℤ) + q) ≤ posOffset p q φ pos' := by
  have hS : (secLen p q φ : ℤ) = (p : ℤ) + 2 * q + φ.m * ((p : ℤ) + q) + 1 + q := by
    simp only [secLen]
    push_cast
    ring
  have hpq : (0 : ℤ) ≤ (p : ℤ) + q := by positivity
  by_cases h0 : pos = 0
  · -- from the literal block to anything else
    subst h0
    have hnn := posOffset_nonneg (p := p) (q := q) (φ := φ) pos'
    by_cases hm' : pos' ≤ φ.m
    · simp only [posOffset, if_neg (by omega : ¬ pos' = 0), if_pos hm']
      have : (0 : ℤ) ≤ ((pos' : ℤ) - 1) * ((p : ℤ) + q) :=
        mul_nonneg (by omega) hpq
      omega
    · simp only [posOffset, if_neg (by omega : ¬ pos' = 0), if_neg hm']
      have h1 : (0 : ℤ) ≤ ((pos' : ℤ) - φ.m - 1) * ((p : ℤ) + q) :=
        mul_nonneg (by omega) hpq
      have h2 : (0 : ℤ) ≤ (φ.m : ℤ) * ((p : ℤ) + q) := by positivity
      omega
  by_cases hm : pos ≤ φ.m
  · by_cases hm' : pos' ≤ φ.m
    · -- both clause blocks of the same section
      simp only [posOffset, if_neg h0, if_pos hm, if_neg (by omega : ¬ pos' = 0), if_pos hm']
      have : ((pos : ℤ) - 1 + 1) * ((p : ℤ) + q) ≤ ((pos' : ℤ) - 1) * ((p : ℤ) + q) := by
        refine mul_le_mul_of_nonneg_right ?_ hpq
        have : (pos : ℤ) < (pos' : ℤ) := by exact_mod_cast h
        omega
      nlinarith [this]
    · -- across the section boundary inside a group
      simp only [posOffset, if_neg h0, if_pos hm, if_neg (by omega : ¬ pos' = 0), if_neg hm']
      have h1 : ((pos : ℤ) - 1 + 1) * ((p : ℤ) + q) ≤ (φ.m : ℤ) * ((p : ℤ) + q) := by
        refine mul_le_mul_of_nonneg_right ?_ hpq
        have : (pos : ℤ) ≤ (φ.m : ℤ) := by exact_mod_cast hm
        omega
      have h2 : (0 : ℤ) ≤ ((pos' : ℤ) - φ.m - 1) * ((p : ℤ) + q) :=
        mul_nonneg (by omega) hpq
      nlinarith [h1, h2]
  · -- both in the second section of the group
    have hm' : ¬ pos' ≤ φ.m := by omega
    simp only [posOffset, if_neg h0, if_neg hm, if_neg (by omega : ¬ pos' = 0), if_neg hm']
    have : ((pos : ℤ) - φ.m - 1 + 1) * ((p : ℤ) + q) ≤ ((pos' : ℤ) - φ.m - 1) * ((p : ℤ) + q) := by
      refine mul_le_mul_of_nonneg_right ?_ hpq
      have : (pos : ℤ) < (pos' : ℤ) := by exact_mod_cast h
      omega
    nlinarith [this]

/-- The sort key's second component never leaves its group. -/
lemma key_snd_le (P : Pair φ) : (key φ P).2 ≤ 2 * φ.m := by
  cases P with
  | inl i => simp [key]
  | inr kj =>
    obtain ⟨k, j⟩ := kj
    have := j.isLt
    simp only [key]
    split <;> omega

/-- **The long jobs' blocks are ordered**, with a gap of at least `p + q` between any pair
and any later one. This is what makes Definition 2's chain conditions hold. -/
lemma longOffset_lt (hq : 0 < q) {P Q : Pair φ} (h : P < Q) :
    longOffset p q φ P + ((p : ℤ) + q) ≤ longOffset p q φ Q := by
  have hkey : toLex (key φ P) < toLex (key φ Q) := h
  rw [Prod.Lex.lt_iff] at hkey
  have hS : (0 : ℤ) ≤ (secLen p q φ : ℤ) := by positivity
  simp only [ofLex_toLex] at hkey
  rcases hkey with hlt | ⟨heq, hlt⟩
  · -- different variables: two whole sections apart
    have h1 := posOffset_le (p := p) (q := q) (φ := φ) hq (key_snd_le φ P)
    have h2 := posOffset_nonneg (p := p) (q := q) (φ := φ) (key φ Q).2
    have h3 : 2 * (secLen p q φ : ℤ) * ((key φ P).1 + 1) ≤
        2 * (secLen p q φ : ℤ) * (key φ Q).1 := by
      refine mul_le_mul_of_nonneg_left ?_ (by omega)
      have : ((key φ P).1 : ℤ) < ((key φ Q).1 : ℤ) := by exact_mod_cast hlt
      omega
    simp only [longOffset]
    nlinarith [h1, h2, h3]
  · -- same variable: one step within the group
    simp only [longOffset, heq]
    have := posOffset_step (p := p) (q := q) (φ := φ) hq hlt
    omega

/-! ### The short job sits exactly one section further along

In both kinds of pair — the literal pair `(Lit[xᵢ], Lit[¬xᵢ])` and the clause pair
`(Cl[l(k), j], Cl[l(k+1), j])` — the short pending job sits in the same block position of
the *next* section. That single fact is what makes the pair's two deadlines nest. -/

lemma shortOffset_inl (i : Fin φ.n) :
    litOffset p q φ ⟨i, false⟩ = longOffset p q φ (Sum.inl i) + (secLen p q φ : ℤ) := by
  simp only [longOffset_inl, litOffset, secOffset, secIndex]
  push_cast
  ring

lemma shortOffset_inr (k : Fin (2 * φ.n - 1)) (j : Fin φ.m) :
    clOffset p q φ (litOfIndex ((k : ℕ) + 1) (clause_succ_lt φ)) j =
      longOffset p q φ (Sum.inr (k, j)) + (secLen p q φ : ℤ) := by
  rw [longOffset_inr]
  simp only [clOffset, secOffset, secIndex_litOfIndex]
  push_cast
  ring

/-! ### The four deadlines, bracketed by the block offset -/

lemma dpOf_le (hq : 0 < q) (P : Pair φ) :
    dpOf p q φ P ≤ longOffset p q φ P + ((p : ℤ) + 2 * q) := by
  cases P with
  | inl i =>
    simp only [dpOf, longOffset_inl, Blocks.LitJob.due]
    omega
  | inr kj =>
    obtain ⟨k, j⟩ := kj
    simp only [dpOf, longOffset_inr, Blocks.clDue]
    omega

lemma dpOf'_ge (P : Pair φ) :
    longOffset p q φ P + ((p : ℤ) + q - 1) ≤ dpOf' p q φ P := by
  cases P with
  | inl i =>
    simp only [dpOf', longOffset_inl, Blocks.litEarly]
    omega
  | inr kj =>
    obtain ⟨k, j⟩ := kj
    simp only [dpOf', longOffset_inr]
    cases active φ (litOfIndex (k : ℕ) (clause_lt φ)) j <;>
      simp only [Blocks.clEarly] <;> omega

lemma dqOf_le (hq : 0 < q) (P : Pair φ) :
    dqOf p q φ P ≤ longOffset p q φ P + (secLen p q φ : ℤ) + ((p : ℤ) + 2 * q) := by
  cases P with
  | inl i =>
    simp only [dqOf, shortOffset_inl, Blocks.LitJob.due]
    omega
  | inr kj =>
    obtain ⟨k, j⟩ := kj
    simp only [dqOf, shortOffset_inr, Blocks.clDue]
    omega

lemma dqOf'_ge (hqp : q < p) (P : Pair φ) :
    longOffset p q φ P + (secLen p q φ : ℤ) + q ≤ dqOf' p q φ P := by
  cases P with
  | inl i =>
    simp only [dqOf', shortOffset_inl, Blocks.litEarly]
    omega
  | inr kj =>
    obtain ⟨k, j⟩ := kj
    simp only [dqOf', shortOffset_inr]
    cases active φ (litOfIndex ((k : ℕ) + 1) (clause_succ_lt φ)) j <;>
      simp only [Blocks.clEarly] <;> omega

/-! ## 7. The chain conditions

Definition 2 asks for four inequalities. Two are local to a single pair — the early deadline
of each pending job is at most its late one. The two that order one pair against the next
run on the geometry of §6. -/

variable {p q φ}

/-- Within a pair, the long pending job's early deadline is at most its late one. For a
literal pair this is `p + q + 1 ≤ p + 2q`, which needs `q > 1` — the corrected `V⁺`
deadline of `TypedBlocks.lean` sitting strictly below the late one. -/
lemma dpOf'_le_dpOf (hq : 1 < q) (P : Pair φ) : dpOf' p q φ P ≤ dpOf p q φ P := by
  cases P with
  | inl i =>
    simp only [dpOf', dpOf, Blocks.litEarly, Blocks.LitJob.due]
    omega
  | inr kj =>
    obtain ⟨k, j⟩ := kj
    simp only [dpOf', dpOf, Blocks.clDue]
    cases h : active φ (litOfIndex (k : ℕ) (clause_lt φ)) j <;>
      simp only [Blocks.clEarly] <;> omega

/-- Within a pair, the short pending job's early deadline is at most its late one. -/
lemma dqOf'_le_dqOf (hq : 1 < q) (P : Pair φ) : dqOf' p q φ P ≤ dqOf p q φ P := by
  cases P with
  | inl i =>
    simp only [dqOf', dqOf, Blocks.litEarly, Blocks.LitJob.due]
    omega
  | inr kj =>
    obtain ⟨k, j⟩ := kj
    simp only [dqOf', dqOf, Blocks.clDue]
    cases h : active φ (litOfIndex ((k : ℕ) + 1) (clause_succ_lt φ)) j <;>
      simp only [Blocks.clEarly] <;> omega

/-! ### The two conditions that order one pair against the next

With the block offsets bracketing all four deadlines and advancing by at least `p + q` per
step, Definition 2's remaining conditions fall out. Note where each hypothesis is spent:
the long jobs need `p > 1` to clear the gap, and the short jobs need exactly the gap
itself, with the `V⁻` block's early deadline of `q` leaving no room to spare. -/

/-- Long pending jobs: an earlier pair's late deadline is at most a later pair's early
one. -/
lemma dpOf_le_dpOf' (hq : 1 < q) (hqp : q < p) {P Q : Pair φ} (h : P < Q) :
    dpOf p q φ P ≤ dpOf' p q φ Q := by
  have h1 := dpOf_le (p := p) (q := q) (φ := φ) (by omega) P
  have h2 := dpOf'_ge (p := p) (q := q) (φ := φ) Q
  have h3 := longOffset_lt (p := p) (q := q) (φ := φ) (by omega) h
  omega

/-- Short pending jobs: the same, and here the margin is exactly zero. -/
lemma dqOf_le_dqOf' (hq : 1 < q) (hqp : q < p) {P Q : Pair φ} (h : P < Q) :
    dqOf p q φ P ≤ dqOf' p q φ Q := by
  have h1 := dqOf_le (p := p) (q := q) (φ := φ) (by omega) P
  have h2 := dqOf'_ge (p := p) (q := q) (φ := φ) hqp Q
  have h3 := longOffset_lt (p := p) (q := q) (φ := φ) (by omega) h
  omega

/-- Inside a pair, the long job is the more urgent: its late deadline is at most the short
job's early one. This is Definition 2's nesting condition, and it holds because the short
job sits a whole section later. -/
lemma dpOf_le_dqOf' (hq : 1 < q) (hqp : q < p) (P : Pair φ) :
    dpOf p q φ P ≤ dqOf' p q φ P := by
  have h1 := dpOf_le (p := p) (q := q) (φ := φ) (by omega) P
  have h2 := dqOf'_ge (p := p) (q := q) (φ := φ) hqp P
  have h3 : (p : ℤ) + q ≤ (secLen p q φ : ℤ) := by
    have : (0 : ℤ) ≤ (φ.m : ℤ) * ((p : ℤ) + q) := by positivity
    simp only [secLen]
    push_cast
    omega
  omega

/-! ### Deadlines are non-negative

`Aux` requires this of its early deadlines: a pending job is released at `0`, so a negative
deadline would make it unschedulable outright. Every block sits at a non-negative offset,
so it holds. -/

lemma longOffset_nonneg (P : Pair φ) : 0 ≤ longOffset p q φ P := by
  have h1 := posOffset_nonneg (p := p) (q := q) (φ := φ) (key φ P).2
  have h2 : (0 : ℤ) ≤ 2 * (secLen p q φ : ℤ) * ((key φ P).1 : ℕ) := by positivity
  simp only [longOffset]
  omega

lemma dpOf'_nonneg (hq : 1 < q) (P : Pair φ) : 0 ≤ dpOf' p q φ P := by
  have h1 := dpOf'_ge (p := p) (q := q) (φ := φ) P
  have h2 := longOffset_nonneg (p := p) (q := q) (φ := φ) P
  omega

lemma dqOf'_nonneg (hq : 1 < q) (hqp : q < p) (P : Pair φ) : 0 ≤ dqOf' p q φ P := by
  have h1 := dqOf'_ge (p := p) (q := q) (φ := φ) hqp P
  have h2 := longOffset_nonneg (p := p) (q := q) (φ := φ) P
  have h3 : (0 : ℤ) ≤ (secLen p q φ : ℤ) := by positivity
  omega

/-! ## 8. The `AUX(p, q)` instance

The ordinary jobs are the two ordinary jobs of each literal block, the separators, and the
`2m` pending jobs Definition 7 leaves unpaired — the long ones of the last section and the
short ones of the first, "required to complete by their early deadline, effectively being
ordinary jobs". Indexing those two families by a subtype of the literals rather than by
`Fin m` alone is deliberate: when there are no variables the subtypes are empty, and the
whole construction degenerates gracefully. -/

variable (p q φ)

/-- The literals whose section is the last one — where the unpaired long pending jobs
live. -/
abbrev LastSec : Type := {l : Literal φ.n // secIndex l = 2 * φ.n - 1}

/-- The literals whose section is the first one — where the unpaired short pending jobs
live. -/
abbrev FirstSec : Type := {l : Literal φ.n // secIndex l = 0}

/-- The ordinary jobs of the constructed `AUX(p, q)` instance. -/
abbrev Ord : Type :=
  (Literal φ.n × Bool) ⊕ Literal φ.n ⊕ (LastSec φ × Fin φ.m) ⊕ (FirstSec φ × Fin φ.m)

/-- Release time of an ordinary job. The unpaired pending jobs keep the release time `0`
they had as pending jobs. -/
def ordRel : Ord φ → ℤ
  | Sum.inl (l, b) =>
      litOffset p q φ l + Blocks.LitJob.rel p q l.pos (if b then .ord1 else .ord2)
  | Sum.inr (Sum.inl l) => sepOffset p q φ l
  | Sum.inr (Sum.inr (Sum.inl _)) => 0
  | Sum.inr (Sum.inr (Sum.inr _)) => 0

/-- Deadline of an ordinary job. For the unpaired pending jobs this is their *early*
deadline: that is what "required to complete by their early deadline" means. -/
def ordDue : Ord φ → ℤ
  | Sum.inl (l, b) =>
      litOffset p q φ l + Blocks.LitJob.due p q l.pos (if b then .ord1 else .ord2)
  | Sum.inr (Sum.inl l) => sepOffset p q φ l + q
  | Sum.inr (Sum.inr (Sum.inl (l, j))) =>
      clOffset p q φ l.1 j + Blocks.clEarly p q (active φ l.1 j)
  | Sum.inr (Sum.inr (Sum.inr (l, j))) =>
      clOffset p q φ l.1 j + Blocks.clEarly p q (active φ l.1 j)

/-- Processing time of an ordinary job. -/
def ordLen : Ord φ → ℕ
  | Sum.inl (l, b) => Blocks.LitJob.len p q l.pos (if b then .ord1 else .ord2)
  | Sum.inr (Sum.inl _) => q
  | Sum.inr (Sum.inr (Sum.inl _)) => p
  | Sum.inr (Sum.inr (Sum.inr _)) => q

variable {p q φ}

lemma secOffset_nonneg (l : Literal φ.n) : 0 ≤ secOffset p q φ l := by
  simp only [secOffset]
  positivity

lemma sepOffset_nonneg (l : Literal φ.n) : 0 ≤ sepOffset p q φ l := by
  have h1 := secOffset_nonneg (p := p) (q := q) (φ := φ) l
  have h2 : (q : ℤ) ≤ (secLen p q φ : ℤ) := by
    have : (0 : ℤ) ≤ (φ.m : ℤ) * ((p : ℤ) + q) := by positivity
    simp only [secLen]
    push_cast
    omega
  simp only [sepOffset]
  omega

lemma ordRel_nonneg (o : Ord φ) : 0 ≤ ordRel p q φ o := by
  rcases o with ⟨l, b⟩ | l | ⟨l, j⟩ | ⟨l, j⟩
  · obtain ⟨v, sgn⟩ := l
    have h1 := secOffset_nonneg (p := p) (q := q) (φ := φ) ⟨v, sgn⟩
    have h2 : (0 : ℤ) ≤ (q : ℤ) := by positivity
    cases b <;> cases sgn <;>
      simp only [ordRel, litOffset, Blocks.LitJob.rel, if_true, if_false,
        Bool.false_eq_true] <;> omega
  · exact sepOffset_nonneg l
  · exact le_refl 0
  · exact le_refl 0

lemma ordLen_eq (o : Ord φ) : ordLen p q φ o = p ∨ ordLen p q φ o = q := by
  rcases o with ⟨l, b⟩ | l | ⟨l, j⟩ | ⟨l, j⟩
  · obtain ⟨v, sgn⟩ := l
    cases b <;> cases sgn <;> simp [ordLen, Blocks.LitJob.len]
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

variable (p q φ)

/-- **Definition 7**: the `AUX(p, q)` instance built from a formula with at least one
variable. Its pending pairs are `RjLmax.FromSat.Pair`, enumerated in deadline order by
`pairEquiv`, and every one of Definition 2's chain conditions is discharged by §6–7. -/
noncomputable def toAux (hq : 1 < q) (hqp : q < p) : Aux p q where
  Ord := Ord φ
  ordFintype := inferInstance
  ordDecEq := inferInstance
  r := ordRel p q φ
  d := ordDue p q φ
  len := ordLen p q φ
  r_nonneg := ordRel_nonneg
  len_eq := ordLen_eq
  q_pos := by omega
  q_lt_p := hqp
  N := numPairs φ
  dp' i := dpOf' p q φ (pairEquiv φ i)
  dp i := dpOf p q φ (pairEquiv φ i)
  dq' i := dqOf' p q φ (pairEquiv φ i)
  dq i := dqOf p q φ (pairEquiv φ i)
  dp'_le_dp i := dpOf'_le_dpOf hq _
  dp_le_dp'_succ i j hij :=
    dpOf_le_dpOf' hq hqp ((pairEquiv φ).lt_iff_lt.mpr (Fin.lt_def.mpr (by omega)))
  dq'_le_dq i := dqOf'_le_dqOf hq _
  dq_le_dq'_succ i j hij :=
    dqOf_le_dqOf' hq hqp ((pairEquiv φ).lt_iff_lt.mpr (Fin.lt_def.mpr (by omega)))
  dp_le_dq' i := dpOf_le_dqOf' hq hqp _
  dp'_nonneg i := dpOf'_nonneg hq _
  dq'_nonneg i := dqOf'_nonneg hq hqp _

/-! ## 9. The schedule a model induces

Given a satisfying assignment, every section is scheduled according to the truth value of
its literal: a **true** literal packs its section tight, spending no idle time, and its
literal block's pending job is late; a **false** literal spends the section's one unit of
slack at the start, its pending job finishes early, and everything after it in the section
is displaced by one.

The pending job of `Lit[l]` is late exactly when `l` is true; Lemma 4 reads the assignment
back off a schedule by that same rule. -/

/-- How far a section is displaced: nothing if its literal is true, one unit if false. -/
def delay (v : φ.Assignment) (l : Literal φ.n) : ℤ :=
  if Literal.Holds v l then 0 else 1

lemma delay_nonneg (v : φ.Assignment) (l : Literal φ.n) : 0 ≤ delay φ v l := by
  unfold delay
  split <;> omega

lemma delay_le_one (v : φ.Assignment) (l : Literal φ.n) : delay φ v l ≤ 1 := by
  unfold delay
  split <;> omega

/-- The start times of the three jobs of `Lit[l]`: the tight layout when `l` is true, the
delayed one when it is false. -/
def litSched (v : φ.Assignment) (l : Literal φ.n) : Blocks.LitJob → ℤ :=
  if Literal.Holds v l then Blocks.litLate p q (litOffset p q φ l) l.pos
  else Blocks.litEarlySched p q (litOffset p q φ l) l.pos

/-- Whichever layout a literal block gets, its jobs run inside their availability
intervals and do not overlap. -/
lemma litSched_fits (hq : 1 < q) (hqp : q < p) (v : φ.Assignment) (l : Literal φ.n) :
    Blocks.LitFits p q l.pos (litOffset p q φ l) (litSched p q φ v l) := by
  unfold litSched
  split
  · exact Blocks.litLate_fits _ _ hq hqp
  · exact Blocks.litEarly_fits _ _ hq hqp

/-- A literal block finishes by the end of its own span, `p + 2q` plus its delay. This is
what confines the section's later blocks. -/
lemma litSched_le (hqp : q < p) (v : φ.Assignment) (l : Literal φ.n) (c : Blocks.LitJob) :
    litSched p q φ v l c + Blocks.LitJob.len p q l.pos c ≤
      litOffset p q φ l + (p : ℤ) + 2 * q + delay φ v l := by
  unfold litSched delay
  split
  · have := Blocks.litLate_le (p := p) (q := q) l.pos (litOffset p q φ l) c
    omega
  · have := Blocks.litEarly_le (p := p) (q := q) l.pos (litOffset p q φ l) hqp c
    omega

/-- **The pending job of a literal block is early exactly when its literal is false.** -/
lemma litSched_pend_early_iff (hq : 1 < q) (hqp : q < p) (v : φ.Assignment)
    (l : Literal φ.n) :
    Blocks.LitPendEarly p q l.pos (litOffset p q φ l) (litSched p q φ v l) ↔
      ¬ Literal.Holds v l := by
  unfold litSched
  split
  · rename_i h
    simp only [h, not_true, iff_false]
    exact Blocks.litLate_pend_late _ _ hq hqp
  · rename_i h
    simp only [h, not_false_iff, iff_true]
    exact Blocks.litEarly_pend_early _ _

/-! ### The clause blocks

Within a section, each clause block is scheduled long-first or short-first, and which one
depends on the clause rather than on the section: for clause `j` fix a literal of it that
the assignment makes true, and order every section's `j`-th block by whether it comes
before or after that literal's section. Sections after it run long-first, sections before
it short-first, and the chosen section itself — which has no idle time and an active block
— gets *both* its pending jobs in early.

That is what discharges the two families Definition 7 leaves unpaired. The unpaired long
jobs sit in the last section, which is never before the chosen one, so they run long-first
or come from the chosen section itself; either way they are early. The unpaired short jobs
sit in the first section, and symmetrically. -/

/-- A literal of clause `j` that the assignment makes true. -/
noncomputable def witness (v : φ.Assignment) (hv : Cnf.Satisfies v) (j : Fin φ.m) :
    Literal φ.n := (hv j).choose

lemma witness_mem (v : φ.Assignment) (hv : Cnf.Satisfies v) (j : Fin φ.m) :
    witness φ v hv j ∈ φ.clause j := (hv j).choose_spec.1

lemma witness_holds (v : φ.Assignment) (hv : Cnf.Satisfies v) (j : Fin φ.m) :
    Literal.Holds v (witness φ v hv j) := (hv j).choose_spec.2

/-- Which way round to schedule `Cl[l, j]`: the long job first exactly when `l`'s section
comes after the section of the literal chosen for `j`. -/
noncomputable def clOrder (v : φ.Assignment) (hv : Cnf.Satisfies v) (l : Literal φ.n)
    (j : Fin φ.m) : Bool :=
  decide (secIndex (witness φ v hv j) < secIndex l)

/-- The start times of the two pending jobs of `Cl[l, j]`. -/
noncomputable def clSchedAt (v : φ.Assignment) (hv : Cnf.Satisfies v) (l : Literal φ.n)
    (j : Fin φ.m) : Blocks.ClJob → ℤ :=
  Blocks.clSched p q (clOffset p q φ l j) (delay φ v l) (clOrder φ v hv l j)

lemma clSchedAt_fits (v : φ.Assignment) (hv : Cnf.Satisfies v) (l : Literal φ.n)
    (j : Fin φ.m) :
    Blocks.ClFits p q (clOffset p q φ l j) (delay φ v l) (clSchedAt p q φ v hv l j) :=
  Blocks.clSched_fits _ _ _ (delay_le_one φ v l)

/-- In the chosen literal's own section the block is active and runs without delay, so
*both* its pending jobs are early. -/
lemma clSchedAt_both_early (_hq : 1 < q) (_hqp : q < p) (v : φ.Assignment)
    (hv : Cnf.Satisfies v) (l : Literal φ.n) (j : Fin φ.m)
    (h : secIndex l = secIndex (witness φ v hv j)) (c : Blocks.ClJob) :
    Blocks.ClEarlyAt p q (active φ l j) (clOffset p q φ l j)
      (clSchedAt p q φ v hv l j) c := by
  have hlw : l = witness φ v hv j := secIndex_injective h
  have hact : active φ l j = true := by
    simp only [active, decide_eq_true_eq, hlw]
    exact witness_mem φ v hv j
  have hd : delay φ v l = 0 := by
    simp only [delay, hlw, if_pos (witness_holds φ v hv j)]
  rw [hact]
  simp only [clSchedAt, hd]
  exact Blocks.clSched_both_early _ _ c

/-- A section at or after the chosen one gets its **long** pending job in early. -/
lemma clSchedAt_long_early (hq : 1 < q) (hqp : q < p) (v : φ.Assignment)
    (hv : Cnf.Satisfies v) (l : Literal φ.n) (j : Fin φ.m)
    (h : secIndex (witness φ v hv j) ≤ secIndex l) :
    Blocks.ClEarlyAt p q (active φ l j) (clOffset p q φ l j)
      (clSchedAt p q φ v hv l j) .long := by
  rcases Nat.eq_or_lt_of_le h with heq | hlt
  · exact clSchedAt_both_early p q φ hq hqp v hv l j heq.symm _
  · have hord : clOrder φ v hv l j = true := by
      simp only [clOrder, decide_eq_true_eq]
      exact hlt
    simp only [clSchedAt, hord]
    exact Blocks.clSched_long_early _ _ _ hq hqp (delay_nonneg φ v l) (delay_le_one φ v l)

/-- A section at or before the chosen one gets its **short** pending job in early. -/
lemma clSchedAt_short_early (hq : 1 < q) (hqp : q < p) (v : φ.Assignment)
    (hv : Cnf.Satisfies v) (l : Literal φ.n) (j : Fin φ.m)
    (h : secIndex l ≤ secIndex (witness φ v hv j)) :
    Blocks.ClEarlyAt p q (active φ l j) (clOffset p q φ l j)
      (clSchedAt p q φ v hv l j) .short := by
  rcases Nat.eq_or_lt_of_le h with heq | hlt
  · exact clSchedAt_both_early p q φ hq hqp v hv l j heq _
  · have hord : clOrder φ v hv l j = false := by
      simp only [clOrder, decide_eq_false_iff_not, not_lt]
      exact le_of_lt hlt
    simp only [clSchedAt, hord]
    exact Blocks.clSched_short_early _ _ _ hq hqp (delay_nonneg φ v l) (delay_le_one φ v l)

/-- The unpaired **long** pending jobs sit in the last section, which is never before the
chosen one, so they are early — which is what Definition 7 demands of them. -/
lemma clSchedAt_last_early (hq : 1 < q) (hqp : q < p) (v : φ.Assignment)
    (hv : Cnf.Satisfies v) (l : LastSec φ) (j : Fin φ.m) :
    Blocks.ClEarlyAt p q (active φ l.1 j) (clOffset p q φ l.1 j)
      (clSchedAt p q φ v hv l.1 j) .long := by
  refine clSchedAt_long_early p q φ hq hqp v hv l.1 j ?_
  have h1 := secIndex_lt (witness φ v hv j)
  have h2 := l.2
  omega

/-- The unpaired **short** pending jobs sit in the first section, which is never after the
chosen one, so they too are early. -/
lemma clSchedAt_first_early (hq : 1 < q) (hqp : q < p) (v : φ.Assignment)
    (hv : Cnf.Satisfies v) (l : FirstSec φ) (j : Fin φ.m) :
    Blocks.ClEarlyAt p q (active φ l.1 j) (clOffset p q φ l.1 j)
      (clSchedAt p q φ v hv l.1 j) .short := by
  refine clSchedAt_short_early p q φ hq hqp v hv l.1 j ?_
  have h2 := l.2
  omega

/-! ### The pairing condition

Definition 2 asks that in every connected pair at least one of the two pending jobs be
early. For a literal pair that is immediate: exactly one of `xᵢ`, `¬xᵢ` is true, and a
literal block's pending job is early exactly when its literal is false. For a clause pair
it is the ordering argument — the pair straddles two adjacent sections, and the chosen
literal's section cannot be strictly between them. -/

/-- A literal pair: exactly one of its two pending jobs is early, because exactly one of
`xᵢ` and `¬xᵢ` is false. -/
lemma litPair_one_early (hq : 1 < q) (hqp : q < p) (v : φ.Assignment) (i : Fin φ.n) :
    Blocks.LitPendEarly p q true (litOffset p q φ ⟨i, true⟩)
        (litSched p q φ v ⟨i, true⟩) ∨
      Blocks.LitPendEarly p q false (litOffset p q φ ⟨i, false⟩)
        (litSched p q φ v ⟨i, false⟩) := by
  have hneg : (⟨i, false⟩ : Literal φ.n) = (⟨i, true⟩ : Literal φ.n).neg := rfl
  by_cases h : Literal.Holds v (⟨i, true⟩ : Literal φ.n)
  · right
    have := litSched_pend_early_iff p q φ hq hqp v (⟨i, false⟩ : Literal φ.n)
    exact this.mpr (by rw [hneg, Literal.holds_neg_iff]; exact not_not_intro h)
  · left
    have := litSched_pend_early_iff p q φ hq hqp v (⟨i, true⟩ : Literal φ.n)
    exact this.mpr h

/-- A clause pair: its long job sits in section `k` and its short job in section `k+1`, and
the chosen literal's section is either at most `k` — making the long job early — or at
least `k+1` — making the short one early. -/
lemma clPair_one_early (hq : 1 < q) (hqp : q < p) (v : φ.Assignment)
    (hv : Cnf.Satisfies v) (k : Fin (2 * φ.n - 1)) (j : Fin φ.m) :
    Blocks.ClEarlyAt p q (active φ (litOfIndex (k : ℕ) (clause_lt φ)) j)
        (clOffset p q φ (litOfIndex (k : ℕ) (clause_lt φ)) j)
        (clSchedAt p q φ v hv (litOfIndex (k : ℕ) (clause_lt φ)) j) .long ∨
      Blocks.ClEarlyAt p q (active φ (litOfIndex ((k : ℕ) + 1) (clause_succ_lt φ)) j)
        (clOffset p q φ (litOfIndex ((k : ℕ) + 1) (clause_succ_lt φ)) j)
        (clSchedAt p q φ v hv (litOfIndex ((k : ℕ) + 1) (clause_succ_lt φ)) j) .short := by
  by_cases h : secIndex (witness φ v hv j) ≤ (k : ℕ)
  · left
    refine clSchedAt_long_early p q φ hq hqp v hv _ j ?_
    rw [secIndex_litOfIndex]
    exact h
  · right
    refine clSchedAt_short_early p q φ hq hqp v hv _ j ?_
    rw [secIndex_litOfIndex]
    omega

/-! ### The schedule, assembled

Every job of the instance now has a start time: the ordinary jobs of a literal block from
`litSched`, the separators at their pinned position, the pending jobs of a clause block
from `clSchedAt`, and the two jobs of a connected pair from whichever block they sit in. -/

/-- The start time of a pair's long pending job. -/
noncomputable def longPos (v : φ.Assignment) (hv : Cnf.Satisfies v) : Pair φ → ℤ
  | Sum.inl i => litSched p q φ v ⟨i, true⟩ .pend
  | Sum.inr (k, j) => clSchedAt p q φ v hv (litOfIndex (k : ℕ) (clause_lt φ)) j .long

/-- The start time of a pair's short pending job. -/
noncomputable def shortPos (v : φ.Assignment) (hv : Cnf.Satisfies v) : Pair φ → ℤ
  | Sum.inl i => litSched p q φ v ⟨i, false⟩ .pend
  | Sum.inr (k, j) =>
      clSchedAt p q φ v hv (litOfIndex ((k : ℕ) + 1) (clause_succ_lt φ)) j .short

/-- **The schedule a satisfying assignment induces.** -/
noncomputable def sched (v : φ.Assignment) (hv : Cnf.Satisfies v) :
    Ord φ ⊕ Fin (numPairs φ) ⊕ Fin (numPairs φ) → ℤ
  | Sum.inl (Sum.inl (l, b)) => litSched p q φ v l (if b then .ord1 else .ord2)
  | Sum.inl (Sum.inr (Sum.inl l)) => sepOffset p q φ l
  | Sum.inl (Sum.inr (Sum.inr (Sum.inl (l, j)))) => clSchedAt p q φ v hv l.1 j .long
  | Sum.inl (Sum.inr (Sum.inr (Sum.inr (l, j)))) => clSchedAt p q φ v hv l.1 j .short
  | Sum.inr (Sum.inl i) => longPos p q φ v hv (pairEquiv φ i)
  | Sum.inr (Sum.inr i) => shortPos p q φ v hv (pairEquiv φ i)

/-! ### Every job runs inside its own section

The first half of feasibility: each job starts at or after the beginning of its section and
finishes by the end of it. Combined with the fact that sections are laid end to end
(`secOffset_mono`), this is what keeps jobs of different sections apart. -/

/-- A literal block's jobs run inside the first `p + 2q + 1` units of their section. -/
lemma litSched_within (hq : 1 < q) (hqp : q < p) (v : φ.Assignment) (l : Literal φ.n)
    (c : Blocks.LitJob) :
    secOffset p q φ l ≤ litSched p q φ v l c ∧
      litSched p q φ v l c + Blocks.LitJob.len p q l.pos c ≤
        secOffset p q φ l + (p : ℤ) + 2 * q + 1 := by
  have h1 := (litSched_fits p q φ hq hqp v l).lower c
  have h2 := litSched_le p q φ hqp v l c
  have h3 := delay_nonneg φ v l
  have h4 := delay_le_one φ v l
  have h5 : 0 ≤ Blocks.LitJob.rel p q l.pos c := by
    cases l.pos <;> cases c <;> simp only [Blocks.LitJob.rel] <;> omega
  simp only [litOffset] at h1 h2
  omega

/-- A clause block's jobs run inside their own `p + q` slot, displaced by the delay. -/
lemma clSchedAt_within (v : φ.Assignment) (hv : Cnf.Satisfies v) (l : Literal φ.n)
    (j : Fin φ.m) (c : Blocks.ClJob) :
    clOffset p q φ l j + delay φ v l ≤ clSchedAt p q φ v hv l j c ∧
      clSchedAt p q φ v hv l j c + Blocks.clLen p q c ≤
        clOffset p q φ l j + delay φ v l + (p : ℤ) + q := by
  constructor
  · exact Blocks.clSched_ge _ _ _ c
  · exact Blocks.clSched_le _ _ _ c

/-! ### The blocks of a section are laid end to end

Three inequalities put the blocks of one section in order, whatever delay it runs at: the
literal block ends where the first clause block begins, clause blocks advance by `p + q`,
and the last of them ends a unit before the separator — the unit of slack the delay is
allowed to consume. -/

lemma litOffset_le_clOffset (l : Literal φ.n) (j : Fin φ.m) :
    litOffset p q φ l + ((p : ℤ) + 2 * q) ≤ clOffset p q φ l j := by
  have h : (0 : ℤ) ≤ ((j : ℕ) : ℤ) * ((p : ℤ) + q) := by positivity
  simp only [litOffset, clOffset]
  omega

lemma clOffset_mono {l : Literal φ.n} {j j' : Fin φ.m} (h : (j : ℕ) < (j' : ℕ)) :
    clOffset p q φ l j + ((p : ℤ) + q) ≤ clOffset p q φ l j' := by
  have hstep : (((j : ℕ) : ℤ) + 1) * ((p : ℤ) + q) ≤ ((j' : ℕ) : ℤ) * ((p : ℤ) + q) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have : ((j : ℕ) : ℤ) < ((j' : ℕ) : ℤ) := by exact_mod_cast h
    omega
  simp only [clOffset]
  nlinarith [hstep]

lemma clOffset_lt_sep (l : Literal φ.n) (j : Fin φ.m) :
    clOffset p q φ l j + ((p : ℤ) + q) + 1 ≤ sepOffset p q φ l := by
  have hj := j.isLt
  have hstep : (((j : ℕ) : ℤ) + 1) * ((p : ℤ) + q) ≤ ((φ.m : ℕ) : ℤ) * ((p : ℤ) + q) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have : ((j : ℕ) : ℤ) + 1 ≤ ((φ.m : ℕ) : ℤ) := by exact_mod_cast hj
    omega
  simp only [clOffset, sepOffset, secLen]
  push_cast
  nlinarith [hstep]

lemma sepOffset_add_le (l : Literal φ.n) :
    sepOffset p q φ l + q ≤ secOffset p q φ l + (secLen p q φ : ℤ) :=
  le_of_eq (sepOffset_add l)

/-! ## 10. Lemma 3: the induced schedule solves the instance

The schedule of §9 is feasible. Proving it directly over `Aux.Job` means reasoning about
`pairEquiv`, which is opaque; so the work is done first over the *physical* jobs of
Definition 7 — three families, laid out by section and block — and then transported along
the map that sends each job of the `AUX` instance to the physical job it is.

Feasibility splits by geometry. Every job runs inside the span of its own block; the blocks
of a section are laid end to end (§3); and the sections themselves are disjoint and in
order (`secOffset_mono`). So two jobs can only overlap if they share a block, and inside a
block `Blocks.LitFits` and `Blocks.ClFits` say they do not. -/

section Lemma3

/-- The section a physical job belongs to. -/
def sec : Job φ → Literal φ.n
  | Sum.inl (l, _) => l
  | Sum.inr (Sum.inl (l, _, _)) => l
  | Sum.inr (Sum.inr l) => l

/-- Which block of its section a physical job belongs to: `0` is the literal block,
`j+1` the `j`-th clause block, and `m+1` the separator. -/
def blk : Job φ → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl (_, j, _)) => (j : ℕ) + 1
  | Sum.inr (Sum.inr _) => φ.m + 1

/-- The start time of each physical job under the schedule a model induces. -/
noncomputable def physSched (v : φ.Assignment) (hv : Cnf.Satisfies v) : Job φ → ℤ
  | Sum.inl (l, c) => litSched p q φ v l c
  | Sum.inr (Sum.inl (l, j, c)) => clSchedAt p q φ v hv l j c
  | Sum.inr (Sum.inr l) => sepOffset p q φ l

/-- Where a job's block begins, delay included. -/
noncomputable def spanLo (v : φ.Assignment) : Job φ → ℤ
  | Sum.inl (l, _) => secOffset p q φ l
  | Sum.inr (Sum.inl (l, j, _)) => clOffset p q φ l j + delay φ v l
  | Sum.inr (Sum.inr l) => sepOffset p q φ l

/-- Where a job's block ends, delay included. -/
noncomputable def spanHi (v : φ.Assignment) : Job φ → ℤ
  | Sum.inl (l, _) => secOffset p q φ l + (p : ℤ) + 2 * q + delay φ v l
  | Sum.inr (Sum.inl (l, j, _)) => clOffset p q φ l j + delay φ v l + (p : ℤ) + q
  | Sum.inr (Sum.inr l) => sepOffset p q φ l + q

/-- Every job runs inside the span of its own block. -/
lemma phys_in_span (hq : 1 < q) (hqp : q < p) (v : φ.Assignment) (hv : Cnf.Satisfies v)
    (x : Job φ) :
    spanLo p q φ v x ≤ physSched p q φ v hv x ∧
      physSched p q φ v hv x + len p q φ x ≤ spanHi p q φ v x := by
  rcases x with ⟨l, c⟩ | ⟨l, j, c⟩ | l
  · refine ⟨?_, ?_⟩
    · have := (litSched_within p q φ hq hqp v l c).1
      simpa only [spanLo, physSched] using this
    · have := litSched_le p q φ hqp v l c
      simp only [spanHi, physSched, len, litOffset] at *
      omega
  · exact ⟨(clSchedAt_within p q φ v hv l j c).1, (clSchedAt_within p q φ v hv l j c).2⟩
  · exact ⟨le_refl _, by simp only [spanHi, physSched, len]; omega⟩

/-- The separator never precedes the start of its own section. -/
lemma secOffset_le_sepOffset (l : Literal φ.n) :
    secOffset p q φ l ≤ sepOffset p q φ l := by
  have h : (q : ℤ) ≤ (secLen p q φ : ℤ) := by
    have : (0 : ℤ) ≤ (φ.m : ℤ) * ((p : ℤ) + q) := by positivity
    simp only [secLen]
    push_cast
    omega
  simp only [sepOffset]
  omega

/-- A block's span sits inside its own section. -/
lemma span_in_section (v : φ.Assignment) (x : Job φ) :
    secOffset p q φ (sec φ x) ≤ spanLo p q φ v x ∧
      spanHi p q φ v x ≤ secOffset p q φ (sec φ x) + (secLen p q φ : ℤ) := by
  have hd0 : ∀ l, (0 : ℤ) ≤ delay φ v l := delay_nonneg φ v
  have hd1 : ∀ l, delay φ v l ≤ 1 := delay_le_one φ v
  have hmq : (0 : ℤ) ≤ (φ.m : ℤ) * ((p : ℤ) + q) := by positivity
  rcases x with ⟨l, c⟩ | ⟨l, j, c⟩ | l
  · refine ⟨le_refl _, ?_⟩
    have h1 := hd1 l
    have h2 := hd0 l
    simp only [spanHi, sec, secLen]
    push_cast
    omega
  · have h1 := hd0 l
    have h2 := hd1 l
    have h3 := litOffset_le_clOffset p q φ l j
    have h4 := clOffset_lt_sep p q φ l j
    have h5 := sepOffset_add_le p q φ l
    have h6 : (0 : ℤ) ≤ (q : ℤ) := by positivity
    simp only [spanLo, spanHi, sec, litOffset] at *
    omega
  · have h5 := sepOffset_add_le p q φ l
    have h7 := secOffset_le_sepOffset p q φ l
    exact ⟨h7, by simp only [spanHi, sec]; omega⟩

/-- The blocks of a section are laid end to end, so an earlier block's span ends where a
later one's begins — whatever delay the section runs at. -/
lemma span_ordered (v : φ.Assignment) {x y : Job φ} (hs : sec φ x = sec φ y)
    (hb : blk φ x < blk φ y) : spanHi p q φ v x ≤ spanLo p q φ v y := by
  have hd0 : ∀ l, (0 : ℤ) ≤ delay φ v l := delay_nonneg φ v
  have hd1 : ∀ l, delay φ v l ≤ 1 := delay_le_one φ v
  have hmq : (0 : ℤ) ≤ (φ.m : ℤ) * ((p : ℤ) + q) := by positivity
  rcases x with ⟨l, c⟩ | ⟨l, j, c⟩ | l <;> rcases y with ⟨l', c'⟩ | ⟨l', j', c'⟩ | l' <;>
    simp only [sec] at hs <;> subst hs <;>
    simp only [blk] at hb
  · omega
  · have h3 := litOffset_le_clOffset p q φ l j'
    have h1 := hd0 l
    simp only [spanHi, spanLo, litOffset] at *
    omega
  · have h7 := secOffset_le_sepOffset p q φ l
    have h1 := hd1 l
    have h2 := hd0 l
    have hsl : secOffset p q φ l + ((p : ℤ) + 2 * q + 1) ≤ sepOffset p q φ l := by
      simp only [sepOffset, secLen]
      push_cast
      omega
    simp only [spanHi, spanLo]
    omega
  · omega
  · have h3 := clOffset_mono p q φ (l := l) (j := j) (j' := j') (by omega)
    simp only [spanHi, spanLo]
    omega
  · have h4 := clOffset_lt_sep p q φ l j
    have h1 := hd1 l
    have h2 := hd0 l
    simp only [spanHi, spanLo]
    omega
  · omega
  · have hj := j'.isLt
    omega
  · omega

/-- Two jobs of different blocks never overlap: their spans are disjoint, whether the
blocks are in the same section or in different ones. -/
lemma phys_disjoint_spans (hq : 1 < q) (hqp : q < p) (v : φ.Assignment)
    (hv : Cnf.Satisfies v) {x y : Job φ}
    (hne : sec φ x ≠ sec φ y ∨ blk φ x ≠ blk φ y) :
    physSched p q φ v hv x + len p q φ x ≤ physSched p q φ v hv y ∨
      physSched p q φ v hv y + len p q φ y ≤ physSched p q φ v hv x := by
  have hx := phys_in_span p q φ hq hqp v hv x
  have hy := phys_in_span p q φ hq hqp v hv y
  rcases hne with hne | hne
  · -- different sections: the sections themselves are disjoint
    have hxs := span_in_section p q φ v x
    have hys := span_in_section p q φ v y
    have hidx : secIndex (sec φ x) ≠ secIndex (sec φ y) := fun hc => hne (secIndex_injective hc)
    rcases Nat.lt_or_ge (secIndex (sec φ x)) (secIndex (sec φ y)) with hlt | hge
    · left
      have hmono : secOffset p q φ (sec φ x) + (secLen p q φ : ℤ) ≤ secOffset p q φ (sec φ y) :=
        secOffset_mono hlt
      omega
    · right
      have hmono : secOffset p q φ (sec φ y) + (secLen p q φ : ℤ) ≤ secOffset p q φ (sec φ x) :=
        secOffset_mono (Nat.lt_of_le_of_ne hge (Ne.symm hidx))
      omega
  · -- same section, different blocks
    by_cases hsec : sec φ x = sec φ y
    · rcases Nat.lt_or_ge (blk φ x) (blk φ y) with hlt | hge
      · left
        have := span_ordered p q φ v hsec hlt
        omega
      · right
        have := span_ordered p q φ v hsec.symm (Nat.lt_of_le_of_ne hge (Ne.symm hne))
        omega
    · have hxs := span_in_section p q φ v x
      have hys := span_in_section p q φ v y
      have hidx : secIndex (sec φ x) ≠ secIndex (sec φ y) :=
        fun hc => hsec (secIndex_injective hc)
      rcases Nat.lt_or_ge (secIndex (sec φ x)) (secIndex (sec φ y)) with hlt | hge
      · left
        have hmono : secOffset p q φ (sec φ x) + (secLen p q φ : ℤ) ≤
            secOffset p q φ (sec φ y) := secOffset_mono hlt
        omega
      · right
        have hmono : secOffset p q φ (sec φ y) + (secLen p q φ : ℤ) ≤
            secOffset p q φ (sec φ x) :=
          secOffset_mono (Nat.lt_of_le_of_ne hge (Ne.symm hidx))
        omega

/-- **No two physical jobs overlap.** Jobs of different blocks are kept apart by the
geometry; jobs of the same block by `Blocks.LitFits` and `Blocks.ClFits`. -/
lemma phys_no_overlap (hq : 1 < q) (hqp : q < p) (v : φ.Assignment)
    (hv : Cnf.Satisfies v) {x y : Job φ} (hxy : x ≠ y) :
    physSched p q φ v hv x + len p q φ x ≤ physSched p q φ v hv y ∨
      physSched p q φ v hv y + len p q φ y ≤ physSched p q φ v hv x := by
  by_cases hsec : sec φ x = sec φ y
  · by_cases hblk : blk φ x = blk φ y
    · -- the same block: the block's own separation
      rcases x with ⟨l, c⟩ | ⟨l, j, c⟩ | l <;> rcases y with ⟨l', c'⟩ | ⟨l', j', c'⟩ | l' <;>
        simp only [sec] at hsec <;> subst hsec <;>
        simp only [blk] at hblk
      · have hcc : c ≠ c' := fun hc => hxy (by rw [hc])
        have := (litSched_fits p q φ hq hqp v l).sep c c' hcc
        simpa only [physSched, len] using this
      · exact absurd hblk (by omega)
      · exact absurd hblk (by omega)
      · exact absurd hblk (by omega)
      · have hjj : j = j' := Fin.ext (by omega)
        subst hjj
        have hcc : c ≠ c' := fun hc => hxy (by rw [hc])
        have hsep := (clSchedAt_fits p q φ v hv l j).sep
        cases c <;> cases c' <;>
          first
            | exact absurd rfl hcc
            | (simp only [physSched, len]; tauto)
      · have hj := j.isLt
        exact absurd hblk (by omega)
      · exact absurd hblk (by omega)
      · have hj := j'.isLt
        exact absurd hblk (by omega)
      · exact absurd rfl hxy
    · exact phys_disjoint_spans p q φ hq hqp v hv (Or.inr hblk)
  · exact phys_disjoint_spans p q φ hq hqp v hv (Or.inl hsec)

/-! ### Availability

Each job runs inside its own availability interval. For the ordinary jobs of a literal
block this is `Blocks.LitFits` directly; for a clause block's jobs, `Blocks.ClFits`; for
the two unpaired families it is the *early* deadline, which is what Definition 7 requires
of them and what `clSchedAt_last_early` and `clSchedAt_first_early` supply. -/

lemma clOffset_nonneg (l : Literal φ.n) (j : Fin φ.m) : 0 ≤ clOffset p q φ l j := by
  have h1 := secOffset_nonneg (p := p) (q := q) (φ := φ) l
  have h2 : (0 : ℤ) ≤ ((j : ℕ) : ℤ) * ((p : ℤ) + q) := by positivity
  simp only [clOffset]
  omega

lemma litSched_nonneg (hq : 1 < q) (hqp : q < p) (v : φ.Assignment) (l : Literal φ.n)
    (c : Blocks.LitJob) : 0 ≤ litSched p q φ v l c := by
  have h1 := (litSched_within p q φ hq hqp v l c).1
  have h2 := secOffset_nonneg (p := p) (q := q) (φ := φ) l
  omega

lemma clSchedAt_nonneg (v : φ.Assignment) (hv : Cnf.Satisfies v) (l : Literal φ.n)
    (j : Fin φ.m) (c : Blocks.ClJob) : 0 ≤ clSchedAt p q φ v hv l j c := by
  have h1 := (clSchedAt_within p q φ v hv l j c).1
  have h2 := clOffset_nonneg p q φ l j
  have h3 := delay_nonneg φ v l
  omega

/-- A pair's long pending job meets its late deadline, wherever it sits. -/
lemma longPos_due (hq : 1 < q) (hqp : q < p) (v : φ.Assignment) (hv : Cnf.Satisfies v)
    (P : Pair φ) : longPos p q φ v hv P + (p : ℤ) ≤ dpOf p q φ P := by
  rcases P with i | ⟨k, j⟩
  · have := (litSched_fits p q φ hq hqp v ⟨i, true⟩).upper .pend
    simpa only [longPos, dpOf, Blocks.LitJob.len] using this
  · have := (clSchedAt_fits p q φ v hv (litOfIndex (k : ℕ) (clause_lt φ)) j).upper .long
    simpa only [longPos, dpOf, Blocks.clLen] using this

/-- A pair's short pending job meets its late deadline. -/
lemma shortPos_due (hq : 1 < q) (hqp : q < p) (v : φ.Assignment) (hv : Cnf.Satisfies v)
    (P : Pair φ) : shortPos p q φ v hv P + (q : ℤ) ≤ dqOf p q φ P := by
  rcases P with i | ⟨k, j⟩
  · have := (litSched_fits p q φ hq hqp v ⟨i, false⟩).upper .pend
    simpa only [shortPos, dqOf, Blocks.LitJob.len] using this
  · have := (clSchedAt_fits p q φ v hv (litOfIndex ((k : ℕ) + 1) (clause_succ_lt φ)) j).upper
      .short
    simpa only [shortPos, dqOf, Blocks.clLen] using this

lemma longPos_nonneg (hq : 1 < q) (hqp : q < p) (v : φ.Assignment) (hv : Cnf.Satisfies v)
    (P : Pair φ) : 0 ≤ longPos p q φ v hv P := by
  rcases P with i | ⟨k, j⟩
  · exact litSched_nonneg p q φ hq hqp v _ _
  · exact clSchedAt_nonneg p q φ v hv _ _ _

lemma shortPos_nonneg (hq : 1 < q) (hqp : q < p) (v : φ.Assignment) (hv : Cnf.Satisfies v)
    (P : Pair φ) : 0 ≤ shortPos p q φ v hv P := by
  rcases P with i | ⟨k, j⟩
  · exact litSched_nonneg p q φ hq hqp v _ _
  · exact clSchedAt_nonneg p q φ v hv _ _ _

/-! ### From the `AUX` instance's jobs to the physical ones

Each job of the constructed instance *is* one of the physical jobs of Definition 7; the map
saying which is injective, so the fact that no two physical jobs overlap transports. -/

/-- The physical job a pair's long pending job is. -/
def longPhys : Pair φ → Job φ
  | Sum.inl i => Sum.inl (⟨i, true⟩, .pend)
  | Sum.inr (k, j) => Sum.inr (Sum.inl (litOfIndex (k : ℕ) (clause_lt φ), j, .long))

/-- The physical job a pair's short pending job is. -/
def shortPhys : Pair φ → Job φ
  | Sum.inl i => Sum.inl (⟨i, false⟩, .pend)
  | Sum.inr (k, j) =>
      Sum.inr (Sum.inl (litOfIndex ((k : ℕ) + 1) (clause_succ_lt φ), j, .short))

lemma len_longPhys (P : Pair φ) : len p q φ (longPhys φ P) = p := by
  rcases P with i | ⟨k, j⟩ <;> rfl

lemma len_shortPhys (P : Pair φ) : len p q φ (shortPhys φ P) = q := by
  rcases P with i | ⟨k, j⟩ <;> rfl

lemma physSched_longPhys (v : φ.Assignment) (hv : Cnf.Satisfies v) (P : Pair φ) :
    physSched p q φ v hv (longPhys φ P) = longPos p q φ v hv P := by
  rcases P with i | ⟨k, j⟩ <;> rfl

lemma physSched_shortPhys (v : φ.Assignment) (hv : Cnf.Satisfies v) (P : Pair φ) :
    physSched p q φ v hv (shortPhys φ P) = shortPos p q φ v hv P := by
  rcases P with i | ⟨k, j⟩ <;> rfl

lemma longPhys_injective : Function.Injective (longPhys φ) := by
  rintro (i | ⟨k, j⟩) (i' | ⟨k', j'⟩) h
  · simp only [longPhys] at h
    injection h with h1
    injection h1 with hA hB
    injection hA with hv hp
    exact congrArg Sum.inl hv
  · simp only [longPhys] at h
    simp at h
  · simp only [longPhys] at h
    simp at h
  · simp only [longPhys] at h
    injection h with h1
    injection h1 with h2
    injection h2 with hl h3
    injection h3 with hj hc
    have hk : (k : ℕ) = (k' : ℕ) := by
      have hs := congrArg secIndex hl
      rwa [secIndex_litOfIndex, secIndex_litOfIndex] at hs
    subst hj
    have hkk : k = k' := Fin.ext hk
    subst hkk
    rfl

lemma shortPhys_injective : Function.Injective (shortPhys φ) := by
  rintro (i | ⟨k, j⟩) (i' | ⟨k', j'⟩) h
  · simp only [shortPhys] at h
    injection h with h1
    injection h1 with hA hB
    injection hA with hv hp
    exact congrArg Sum.inl hv
  · simp only [shortPhys] at h
    simp at h
  · simp only [shortPhys] at h
    simp at h
  · simp only [shortPhys] at h
    injection h with h1
    injection h1 with h2
    injection h2 with hl h3
    injection h3 with hj hc
    have hk : (k : ℕ) + 1 = (k' : ℕ) + 1 := by
      have hs := congrArg secIndex hl
      rwa [secIndex_litOfIndex, secIndex_litOfIndex] at hs
    subst hj
    have hkk : k = k' := Fin.ext (by omega)
    subst hkk
    rfl

lemma longPhys_ne_ord (P : Pair φ) (l : Literal φ.n) (b : Bool) :
    longPhys φ P ≠ Sum.inl (l, if b then Blocks.LitJob.ord1 else Blocks.LitJob.ord2) := by
  rcases P with i | ⟨k, j⟩ <;> cases b <;> simp [longPhys]

lemma shortPhys_ne_ord (P : Pair φ) (l : Literal φ.n) (b : Bool) :
    shortPhys φ P ≠ Sum.inl (l, if b then Blocks.LitJob.ord1 else Blocks.LitJob.ord2) := by
  rcases P with i | ⟨k, j⟩ <;> cases b <;> simp [shortPhys]

lemma longPhys_ne_shortPhys (P Q : Pair φ) : longPhys φ P ≠ shortPhys φ Q := by
  rcases P with i | ⟨k, j⟩ <;> rcases Q with i' | ⟨k', j'⟩ <;> simp [longPhys, shortPhys]

lemma longPhys_ne_sep (P : Pair φ) (l : Literal φ.n) :
    longPhys φ P ≠ Sum.inr (Sum.inr l) := by
  rcases P with i | ⟨k, j⟩ <;> simp [longPhys]

lemma shortPhys_ne_sep (P : Pair φ) (l : Literal φ.n) :
    shortPhys φ P ≠ Sum.inr (Sum.inr l) := by
  rcases P with i | ⟨k, j⟩ <;> simp [shortPhys]

/-- The unpaired long pending jobs of the last section are not the long job of any pair:
a pair's long job sits in a section strictly before the last one. -/
lemma longPhys_ne_last (P : Pair φ) (l : LastSec φ) (j : Fin φ.m) :
    longPhys φ P ≠ Sum.inr (Sum.inl (l.1, j, Blocks.ClJob.long)) := by
  rcases P with i | ⟨k, j'⟩
  · simp [longPhys]
  · intro h
    simp only [longPhys] at h
    injection h with h1
    injection h1 with h2
    injection h2 with hl h3
    have hk : (k : ℕ) = secIndex l.1 := by
      have hs := congrArg secIndex hl
      rwa [secIndex_litOfIndex] at hs
    have hlt := k.isLt
    have := l.2
    omega

/-- Symmetrically, the unpaired short pending jobs of the first section are not the short
job of any pair. -/
lemma shortPhys_ne_first (P : Pair φ) (l : FirstSec φ) (j : Fin φ.m) :
    shortPhys φ P ≠ Sum.inr (Sum.inl (l.1, j, Blocks.ClJob.short)) := by
  rcases P with i | ⟨k, j'⟩
  · simp [shortPhys]
  · intro h
    simp only [shortPhys] at h
    injection h with h1
    injection h1 with h2
    injection h2 with hl h3
    have hk : (k : ℕ) + 1 = secIndex l.1 := by
      have hs := congrArg secIndex hl
      rwa [secIndex_litOfIndex] at hs
    have := l.2
    omega

lemma longPhys_ne_clShort (P : Pair φ) (l : Literal φ.n) (j : Fin φ.m) :
    longPhys φ P ≠ Sum.inr (Sum.inl (l, j, Blocks.ClJob.short)) := by
  rcases P with i | ⟨k, jj⟩ <;> simp [longPhys]

lemma shortPhys_ne_clLong (P : Pair φ) (l : Literal φ.n) (j : Fin φ.m) :
    shortPhys φ P ≠ Sum.inr (Sum.inl (l, j, Blocks.ClJob.long)) := by
  rcases P with i | ⟨k, jj⟩ <;> simp [shortPhys]

/-- Each job of the constructed `AUX` instance, as a physical job of Definition 7. -/
noncomputable def toPhys : Ord φ ⊕ Fin (numPairs φ) ⊕ Fin (numPairs φ) → Job φ
  | Sum.inl (Sum.inl (l, b)) => Sum.inl (l, if b then .ord1 else .ord2)
  | Sum.inl (Sum.inr (Sum.inl l)) => Sum.inr (Sum.inr l)
  | Sum.inl (Sum.inr (Sum.inr (Sum.inl (l, j)))) => Sum.inr (Sum.inl (l.1, j, .long))
  | Sum.inl (Sum.inr (Sum.inr (Sum.inr (l, j)))) => Sum.inr (Sum.inl (l.1, j, .short))
  | Sum.inr (Sum.inl i) => longPhys φ (pairEquiv φ i)
  | Sum.inr (Sum.inr i) => shortPhys φ (pairEquiv φ i)

lemma physSched_toPhys (v : φ.Assignment) (hv : Cnf.Satisfies v)
    (x : Ord φ ⊕ Fin (numPairs φ) ⊕ Fin (numPairs φ)) :
    physSched p q φ v hv (toPhys φ x) = sched p q φ v hv x := by
  rcases x with (⟨l, b⟩ | l | ⟨l, j⟩ | ⟨l, j⟩) | i | i
  · cases b <;> rfl
  · rfl
  · rfl
  · rfl
  · exact physSched_longPhys p q φ v hv _
  · exact physSched_shortPhys p q φ v hv _

lemma len_toPhys (x : Ord φ ⊕ Fin (numPairs φ) ⊕ Fin (numPairs φ)) :
    len p q φ (toPhys φ x) =
      Sum.elim (ordLen p q φ) (Sum.elim (fun _ => p) (fun _ => q)) x := by
  rcases x with (⟨l, b⟩ | l | ⟨l, j⟩ | ⟨l, j⟩) | i | i
  · cases b <;> rfl
  · rfl
  · rfl
  · rfl
  · exact len_longPhys p q φ _
  · exact len_shortPhys p q φ _

/-- **The map is injective**: no two jobs of the `AUX` instance are the same physical
job. -/
lemma toPhys_injective : Function.Injective (toPhys φ) := by
  have hpe : Function.Injective (pairEquiv φ) := (pairEquiv φ).injective
  rintro ((⟨l, b⟩ | l | ⟨l, j⟩ | ⟨l, j⟩) | i | i)
    ((⟨l', b'⟩ | l' | ⟨l', j'⟩ | ⟨l', j'⟩) | i' | i') h <;>
    simp only [toPhys] at h
  -- literal-block ordinary jobs
  · cases b <;> cases b' <;> simp_all
  · simp at h
  · simp at h
  · simp at h
  · exact absurd h.symm (longPhys_ne_ord φ _ l b)
  · exact absurd h.symm (shortPhys_ne_ord φ _ l b)
  -- separators
  · simp at h
  · injection h with h1; injection h1 with h2; rw [h2]
  · simp at h
  · simp at h
  · exact absurd h.symm (longPhys_ne_sep φ _ l)
  · exact absurd h.symm (shortPhys_ne_sep φ _ l)
  -- unpaired long pending jobs
  · simp at h
  · simp at h
  · injection h with h1
    injection h1 with h2
    injection h2 with hl h3
    injection h3 with hj hc
    subst hj
    rw [Subtype.ext hl]
  · simp at h
  · exact absurd h.symm (longPhys_ne_last φ _ l j)
  · exact absurd h.symm (shortPhys_ne_clLong φ _ l.1 j)
  -- unpaired short pending jobs
  · simp at h
  · simp at h
  · simp at h
  · injection h with h1
    injection h1 with h2
    injection h2 with hl h3
    injection h3 with hj hc
    subst hj
    rw [Subtype.ext hl]
  · exact absurd h.symm (longPhys_ne_clShort φ _ l.1 j)
  · exact absurd h.symm (shortPhys_ne_first φ _ l j)
  -- long pending jobs
  · exact absurd h (longPhys_ne_ord φ _ l' b')
  · exact absurd h (longPhys_ne_sep φ _ l')
  · exact absurd h (longPhys_ne_last φ _ l' j')
  · exact absurd h (longPhys_ne_clShort φ _ l'.1 j')
  · rw [hpe (longPhys_injective φ h)]
  · exact absurd h (longPhys_ne_shortPhys φ _ _)
  -- short pending jobs
  · exact absurd h (shortPhys_ne_ord φ _ l' b')
  · exact absurd h (shortPhys_ne_sep φ _ l')
  · exact absurd h (shortPhys_ne_clLong φ _ l'.1 j')
  · exact absurd h (shortPhys_ne_first φ _ l' j')
  · exact absurd h.symm (longPhys_ne_shortPhys φ _ _)
  · rw [hpe (shortPhys_injective φ h)]

/-! ### Lemma 3

Everything the definition of `Aux.Solves` asks for: the schedule is feasible — availability
job by job, and no overlap by way of the physical layout — and every connected pair has an
early job. -/

/-- In every connected pair, one of the two pending jobs meets its early deadline. -/
lemma pair_one_early (hq : 1 < q) (hqp : q < p) (v : φ.Assignment) (hv : Cnf.Satisfies v)
    (P : Pair φ) :
    longPos p q φ v hv P + (p : ℤ) ≤ dpOf' p q φ P ∨
      shortPos p q φ v hv P + (q : ℤ) ≤ dqOf' p q φ P := by
  rcases P with i | ⟨k, j⟩
  · rcases litPair_one_early p q φ hq hqp v i with h | h
    · exact Or.inl (by simpa only [longPos, dpOf', Blocks.LitPendEarly,
        Blocks.LitJob.len] using h)
    · exact Or.inr (by simpa only [shortPos, dqOf', Blocks.LitPendEarly,
        Blocks.LitJob.len] using h)
  · rcases clPair_one_early p q φ hq hqp v hv k j with h | h
    · exact Or.inl (by simpa only [longPos, dpOf', Blocks.ClEarlyAt, Blocks.clLen] using h)
    · exact Or.inr (by simpa only [shortPos, dqOf', Blocks.ClEarlyAt, Blocks.clLen] using h)

/-- **No two jobs of the constructed instance overlap.** Stated over the raw job type, so
that it can be applied to the instance's own `Job` by unification: rewriting under that
projection does not work, exactly as in `RjLmax.Stacked`. -/
lemma sched_no_overlap (hq : 1 < q) (hqp : q < p) (v : φ.Assignment) (hv : Cnf.Satisfies v)
    {x y : Ord φ ⊕ Fin (numPairs φ) ⊕ Fin (numPairs φ)} (hxy : x ≠ y) :
    sched p q φ v hv x +
        ((Sum.elim (ordLen p q φ) (Sum.elim (fun _ => p) (fun _ => q)) x : ℕ) : ℤ) ≤
        sched p q φ v hv y ∨
      sched p q φ v hv y +
        ((Sum.elim (ordLen p q φ) (Sum.elim (fun _ => p) (fun _ => q)) y : ℕ) : ℤ) ≤
        sched p q φ v hv x := by
  have h := phys_no_overlap p q φ hq hqp v hv ((toPhys_injective φ).ne hxy)
  rw [physSched_toPhys, physSched_toPhys, len_toPhys, len_toPhys] at h
  exact h

/-- **Lemma 3.** The schedule a satisfying assignment induces solves the instance. -/
theorem sched_solves (hq : 1 < q) (hqp : q < p) (v : φ.Assignment) (hv : Cnf.Satisfies v) :
    (toAux p q φ hq hqp).Solves (sched p q φ v hv) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- availability
    rintro ((⟨l, b⟩ | l | ⟨l, j⟩ | ⟨l, j⟩) | i | i)
    · exact ⟨(litSched_fits p q φ hq hqp v l).lower _,
        (litSched_fits p q φ hq hqp v l).upper _⟩
    · exact ⟨le_refl _, le_refl _⟩
    · exact ⟨clSchedAt_nonneg p q φ v hv l.1 j .long,
        clSchedAt_last_early p q φ hq hqp v hv l j⟩
    · exact ⟨clSchedAt_nonneg p q φ v hv l.1 j .short,
        clSchedAt_first_early p q φ hq hqp v hv l j⟩
    · exact ⟨longPos_nonneg p q φ hq hqp v hv _, longPos_due p q φ hq hqp v hv _⟩
    · exact ⟨shortPos_nonneg p q φ hq hqp v hv _, shortPos_due p q φ hq hqp v hv _⟩
  · -- no two jobs overlap
    intro x y hxy
    exact sched_no_overlap p q φ hq hqp v hv hxy
  · -- the pairing condition
    intro i
    exact pair_one_early p q φ hq hqp v hv (pairEquiv φ i)

/-- A satisfiable formula gives a solvable instance. -/
theorem yes_of_satisfiable (hq : 1 < q) (hqp : q < p) (h : φ.Satisfiable) :
    (toAux p q φ hq hqp).Yes := by
  obtain ⟨v, hv⟩ := h
  exact ⟨sched p q φ v hv, sched_solves p q φ hq hqp v hv⟩

/-- `litOfIndex` does not depend on the proof it is handed. -/
lemma litOfIndex_congr {n s s' : ℕ} (h : s < 2 * n) (h' : s' < 2 * n) (he : s = s') :
    litOfIndex s h = litOfIndex (n := n) s' h' := by
  subst he
  rfl

/-- `litOfIndex` and `secIndex` are inverse to each other. -/
lemma litOfIndex_secIndex {n : ℕ} (l : Literal n) (h : secIndex l < 2 * n) :
    litOfIndex (secIndex l) h = l := by
  obtain ⟨w, sgn⟩ := l
  cases sgn
  · have hs : secIndex (⟨w, false⟩ : Literal n) = 2 * (w : ℕ) + 1 := by
      simp only [secIndex, if_false, Bool.false_eq_true]
    simp only [litOfIndex, hs, Literal.mk.injEq]
    refine ⟨Fin.ext ?_, ?_⟩
    · simp only []
      omega
    · simp only [decide_eq_false_iff_not]
      omega
  · have hs : secIndex (⟨w, true⟩ : Literal n) = 2 * (w : ℕ) := by
      simp only [secIndex, if_true]
      omega
    simp only [litOfIndex, hs, Literal.mk.injEq]
    refine ⟨Fin.ext ?_, ?_⟩
    · simp only []
      omega
    · simp only [decide_eq_true_eq]
      omega

/-- **The map onto the physical jobs is onto.** Every job of Definition 7 is a job of the
constructed instance: the three of each literal block and the separators are ordinary, and
each pending job is either one of a connected pair or one of the two unpaired families. -/
lemma toPhys_surjective : Function.Surjective (toPhys φ) := by
  classical
  rintro (⟨l, c⟩ | ⟨l, j, c⟩ | l)
  · cases c
    · exact ⟨Sum.inl (Sum.inl (l, true)), rfl⟩
    · exact ⟨Sum.inl (Sum.inl (l, false)), rfl⟩
    · -- the pending job of a literal block is the paired job of its variable
      obtain ⟨w, sgn⟩ := l
      cases sgn
      · refine ⟨Sum.inr (Sum.inr ((pairEquiv φ).symm (Sum.inl w))), ?_⟩
        simp only [toPhys, OrderIso.apply_symm_apply, shortPhys]
      · refine ⟨Sum.inr (Sum.inl ((pairEquiv φ).symm (Sum.inl w))), ?_⟩
        simp only [toPhys, OrderIso.apply_symm_apply, longPhys]
  · have hlt := secIndex_lt l
    cases c
    · -- a long pending job: paired unless its section is the last one
      by_cases hlast : secIndex l = 2 * φ.n - 1
      · exact ⟨Sum.inl (Sum.inr (Sum.inr (Sum.inl (⟨l, hlast⟩, j)))), rfl⟩
      · refine ⟨Sum.inr (Sum.inl ((pairEquiv φ).symm (Sum.inr (⟨secIndex l, by omega⟩, j)))), ?_⟩
        simp only [toPhys, OrderIso.apply_symm_apply, longPhys]
        rw [litOfIndex_secIndex l hlt]
    · -- a short pending job: paired unless its section is the first one
      by_cases hfirst : secIndex l = 0
      · exact ⟨Sum.inl (Sum.inr (Sum.inr (Sum.inr (⟨l, hfirst⟩, j)))), rfl⟩
      · refine ⟨Sum.inr (Sum.inr
          ((pairEquiv φ).symm (Sum.inr (⟨secIndex l - 1, by omega⟩, j)))), ?_⟩
        simp only [toPhys, OrderIso.apply_symm_apply, shortPhys]
        have hgoal : litOfIndex (((⟨secIndex l - 1, by omega⟩ : Fin (2 * φ.n - 1)) : ℕ) + 1)
            (clause_succ_lt φ) = l :=
          (litOfIndex_congr _ hlt (by simp only []; omega)).trans (litOfIndex_secIndex l hlt)
        rw [hgoal]
  · exact ⟨Sum.inl (Sum.inr (Sum.inl l)), rfl⟩

/-- The jobs of the constructed instance *are* the physical jobs of Definition 7. -/
noncomputable def physEquiv :
    (Ord φ ⊕ Fin (numPairs φ) ⊕ Fin (numPairs φ)) ≃ Job φ :=
  Equiv.ofBijective (toPhys φ) ⟨toPhys_injective φ, toPhys_surjective φ⟩

end Lemma3

/-! ## 11. Lemma 4: reading an assignment off a solution

A solution to the constructed instance is read back as a physical schedule of Definition
7's jobs, through the bijection above. Everything the converse needs is then stated over
the three structural families rather than over `Fin N`. -/

section Lemma4

/-- A schedule of the constructed instance, read as a schedule of the physical jobs. -/
noncomputable def readSched (t : Ord φ ⊕ Fin (numPairs φ) ⊕ Fin (numPairs φ) → ℤ) :
    Job φ → ℤ := fun y => t ((physEquiv φ).symm y)

@[simp] lemma readSched_toPhys (t : Ord φ ⊕ Fin (numPairs φ) ⊕ Fin (numPairs φ) → ℤ)
    (x : Ord φ ⊕ Fin (numPairs φ) ⊕ Fin (numPairs φ)) :
    readSched φ t (toPhys φ x) = t x := by
  simp only [readSched]
  rw [show ((physEquiv φ).symm (toPhys φ x)) = x from (physEquiv φ).symm_apply_apply x]

lemma rel_longPhys (P : Pair φ) : rel p q φ (longPhys φ P) = 0 := by
  rcases P with i | ⟨k, j⟩ <;> rfl

lemma rel_shortPhys (P : Pair φ) : rel p q φ (shortPhys φ P) = 0 := by
  rcases P with i | ⟨k, j⟩ <;> rfl

lemma due_longPhys (P : Pair φ) : due p q φ (longPhys φ P) = dpOf p q φ P := by
  rcases P with i | ⟨k, j⟩ <;> rfl

lemma due_shortPhys (P : Pair φ) : due p q φ (shortPhys φ P) = dqOf p q φ P := by
  rcases P with i | ⟨k, j⟩ <;> rfl

variable {p q φ}

/-- Every physical job starts at or after its own release time. -/
lemma read_rel (hq : 1 < q) (hqp : q < p)
    {t : Ord φ ⊕ Fin (numPairs φ) ⊕ Fin (numPairs φ) → ℤ}
    (h : (toAux p q φ hq hqp).Solves t) (y : Job φ) :
    rel p q φ y ≤ readSched φ t y := by
  obtain ⟨x, rfl⟩ := toPhys_surjective φ y
  rw [readSched_toPhys]
  rcases x with (⟨l, b⟩ | l | ⟨l, j⟩ | ⟨l, j⟩) | i | i
  · cases b <;> exact (h.1.1 _).1
  · exact (h.1.1 _).1
  · exact (h.1.1 (Sum.inl (Sum.inr (Sum.inr (Sum.inl (l, j)))))).1
  · exact (h.1.1 (Sum.inl (Sum.inr (Sum.inr (Sum.inr (l, j)))))).1
  · show rel p q φ (longPhys φ (pairEquiv φ i)) ≤ _
    rw [rel_longPhys]
    exact (h.1.1 (Sum.inr (Sum.inl i))).1
  · show rel p q φ (shortPhys φ (pairEquiv φ i)) ≤ _
    rw [rel_shortPhys]
    exact (h.1.1 (Sum.inr (Sum.inr i))).1

/-- Every physical job finishes by its own late deadline. -/
lemma read_due (hq : 1 < q) (hqp : q < p)
    {t : Ord φ ⊕ Fin (numPairs φ) ⊕ Fin (numPairs φ) → ℤ}
    (h : (toAux p q φ hq hqp).Solves t) (y : Job φ) :
    readSched φ t y + len p q φ y ≤ due p q φ y := by
  obtain ⟨x, rfl⟩ := toPhys_surjective φ y
  rw [readSched_toPhys]
  rcases x with (⟨l, b⟩ | l | ⟨l, j⟩ | ⟨l, j⟩) | i | i
  · cases b <;> exact (h.1.1 _).2
  · exact (h.1.1 _).2
  · have hx : t (Sum.inl (Sum.inr (Sum.inr (Sum.inl (l, j))))) + (p : ℤ) ≤
        clOffset p q φ l.1 j + Blocks.clEarly p q (active φ l.1 j) :=
      (h.1.1 (Sum.inl (Sum.inr (Sum.inr (Sum.inl (l, j)))))).2
    show t (Sum.inl (Sum.inr (Sum.inr (Sum.inl (l, j))))) + ((p : ℕ) : ℤ) ≤
      clOffset p q φ l.1 j + Blocks.clDue p q
    cases hact : active φ l.1 j <;>
      rw [hact] at hx <;>
      simp only [Blocks.clEarly] at hx <;>
      simp only [Blocks.clDue] <;>
      omega
  · have hx : t (Sum.inl (Sum.inr (Sum.inr (Sum.inr (l, j))))) + (q : ℤ) ≤
        clOffset p q φ l.1 j + Blocks.clEarly p q (active φ l.1 j) :=
      (h.1.1 (Sum.inl (Sum.inr (Sum.inr (Sum.inr (l, j)))))).2
    show t (Sum.inl (Sum.inr (Sum.inr (Sum.inr (l, j))))) + ((q : ℕ) : ℤ) ≤
      clOffset p q φ l.1 j + Blocks.clDue p q
    cases hact : active φ l.1 j <;>
      rw [hact] at hx <;>
      simp only [Blocks.clEarly] at hx <;>
      simp only [Blocks.clDue] <;>
      omega
  · show _ + ((len p q φ (longPhys φ (pairEquiv φ i)) : ℕ) : ℤ) ≤
      due p q φ (longPhys φ (pairEquiv φ i))
    rw [due_longPhys, len_longPhys]
    exact (h.1.1 (Sum.inr (Sum.inl i))).2
  · show _ + ((len p q φ (shortPhys φ (pairEquiv φ i)) : ℕ) : ℤ) ≤
      due p q φ (shortPhys φ (pairEquiv φ i))
    rw [due_shortPhys, len_shortPhys]
    exact (h.1.1 (Sum.inr (Sum.inr i))).2

/-- No two physical jobs overlap. -/
lemma read_sep (hq : 1 < q) (hqp : q < p)
    {t : Ord φ ⊕ Fin (numPairs φ) ⊕ Fin (numPairs φ) → ℤ}
    (h : (toAux p q φ hq hqp).Solves t) {y z : Job φ} (hyz : y ≠ z) :
    readSched φ t y + len p q φ y ≤ readSched φ t z ∨
      readSched φ t z + len p q φ z ≤ readSched φ t y := by
  obtain ⟨x, rfl⟩ := toPhys_surjective φ y
  obtain ⟨x', rfl⟩ := toPhys_surjective φ z
  rw [readSched_toPhys, readSched_toPhys, len_toPhys, len_toPhys]
  exact h.1.2 x x' (fun hc => hyz (congrArg (toPhys φ) hc))

/-- The unpaired long pending jobs of the last section meet their early deadline. -/
lemma read_last_early (hq : 1 < q) (hqp : q < p)
    {t : Ord φ ⊕ Fin (numPairs φ) ⊕ Fin (numPairs φ) → ℤ}
    (h : (toAux p q φ hq hqp).Solves t) (l : LastSec φ) (j : Fin φ.m) :
    Blocks.ClEarlyAt p q (active φ l.1 j) (clOffset p q φ l.1 j)
      (fun c => readSched φ t (Sum.inr (Sum.inl (l.1, j, c)))) .long := by
  have hx : t (Sum.inl (Sum.inr (Sum.inr (Sum.inl (l, j))))) + (p : ℤ) ≤
      clOffset p q φ l.1 j + Blocks.clEarly p q (active φ l.1 j) :=
    (h.1.1 (Sum.inl (Sum.inr (Sum.inr (Sum.inl (l, j)))))).2
  have he : readSched φ t (Sum.inr (Sum.inl (l.1, j, Blocks.ClJob.long))) =
      t (Sum.inl (Sum.inr (Sum.inr (Sum.inl (l, j))))) :=
    readSched_toPhys φ t (Sum.inl (Sum.inr (Sum.inr (Sum.inl (l, j)))))
  show readSched φ t (Sum.inr (Sum.inl (l.1, j, Blocks.ClJob.long))) + ((p : ℕ) : ℤ) ≤
    clOffset p q φ l.1 j + Blocks.clEarly p q (active φ l.1 j)
  rw [he]
  exact hx

/-- The unpaired short pending jobs of the first section meet their early deadline. -/
lemma read_first_early (hq : 1 < q) (hqp : q < p)
    {t : Ord φ ⊕ Fin (numPairs φ) ⊕ Fin (numPairs φ) → ℤ}
    (h : (toAux p q φ hq hqp).Solves t) (l : FirstSec φ) (j : Fin φ.m) :
    Blocks.ClEarlyAt p q (active φ l.1 j) (clOffset p q φ l.1 j)
      (fun c => readSched φ t (Sum.inr (Sum.inl (l.1, j, c)))) .short := by
  have hx : t (Sum.inl (Sum.inr (Sum.inr (Sum.inr (l, j))))) + (q : ℤ) ≤
      clOffset p q φ l.1 j + Blocks.clEarly p q (active φ l.1 j) :=
    (h.1.1 (Sum.inl (Sum.inr (Sum.inr (Sum.inr (l, j)))))).2
  have he : readSched φ t (Sum.inr (Sum.inl (l.1, j, Blocks.ClJob.short))) =
      t (Sum.inl (Sum.inr (Sum.inr (Sum.inr (l, j))))) :=
    readSched_toPhys φ t (Sum.inl (Sum.inr (Sum.inr (Sum.inr (l, j)))))
  show readSched φ t (Sum.inr (Sum.inl (l.1, j, Blocks.ClJob.short))) + ((q : ℕ) : ℤ) ≤
    clOffset p q φ l.1 j + Blocks.clEarly p q (active φ l.1 j)
  rw [he]
  exact hx

/-- In every connected pair, one of the two pending jobs is early. -/
lemma read_pair_early (hq : 1 < q) (hqp : q < p)
    {t : Ord φ ⊕ Fin (numPairs φ) ⊕ Fin (numPairs φ) → ℤ}
    (h : (toAux p q φ hq hqp).Solves t) (P : Pair φ) :
    readSched φ t (longPhys φ P) + (p : ℤ) ≤ dpOf' p q φ P ∨
      readSched φ t (shortPhys φ P) + (q : ℤ) ≤ dqOf' p q φ P := by
  have hi := h.2 ((pairEquiv φ).symm P)
  have hL : readSched φ t (longPhys φ P) = t (Sum.inr (Sum.inl ((pairEquiv φ).symm P))) := by
    have := readSched_toPhys φ t (Sum.inr (Sum.inl ((pairEquiv φ).symm P)))
    simpa only [toPhys, OrderIso.apply_symm_apply] using this
  have hS : readSched φ t (shortPhys φ P) = t (Sum.inr (Sum.inr ((pairEquiv φ).symm P))) := by
    have := readSched_toPhys φ t (Sum.inr (Sum.inr ((pairEquiv φ).symm P)))
    simpa only [toPhys, OrderIso.apply_symm_apply] using this
  rcases hi with hi | hi
  · left
    simp only [Aux.LongEarly, Instance.completion, Aux.toInstance_p_long, toAux,
      OrderIso.apply_symm_apply] at hi
    rw [hL]
    exact hi
  · right
    simp only [Aux.ShortEarly, Instance.completion, Aux.toInstance_p_short, toAux,
      OrderIso.apply_symm_apply] at hi
    rw [hS]
    exact hi

/-! ### Proposition 2, stage 1: every job runs inside its own section

The paper's Proposition 2 is stated for the whole layout at once; the counting behind it
only works locally, so it is proved here in two stages. The first confines each job to its
own section, by strong induction on the section index: the separators are pinned, so no job
straddles one, and an earlier section is already filled to within one unit — while every
job is at least `q > 1` long. This is the one place the hypothesis `q > 1` is used. -/

variable (p q φ)

/-- What a solution gives, read physically: release times, deadlines, and no overlap. -/
structure PhysFeasible (T : Job φ → ℤ) : Prop where
  /-- Each job starts at or after its release time. -/
  rel : ∀ y, rel p q φ y ≤ T y
  /-- Each job finishes by its late deadline. -/
  due : ∀ y, T y + len p q φ y ≤ due p q φ y
  /-- No two jobs overlap. -/
  sep : ∀ y z, y ≠ z → T y + len p q φ y ≤ T z ∨ T z + len p q φ z ≤ T y

/-- The non-separator jobs of one section: a literal block and `m` clause blocks. -/
def secJobs (l : Literal φ.n) : Finset (Job φ) :=
  (Finset.univ.image (fun c : Blocks.LitJob => (Sum.inl (l, c) : Job φ))) ∪
    (Finset.univ.image
      (fun jc : Fin φ.m × Blocks.ClJob => (Sum.inr (Sum.inl (l, jc.1, jc.2)) : Job φ)))

variable {p q φ}

/-- Anything in `secJobs l` belongs to section `l` and is not the separator. -/
lemma secJobs_spec {l : Literal φ.n} {y : Job φ} (hy : y ∈ secJobs φ l) :
    sec φ y = l ∧ blk φ y ≤ φ.m := by
  rcases Finset.mem_union.mp hy with h | h
  · obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp h
    exact ⟨rfl, by simp only [blk]; omega⟩
  · obtain ⟨⟨j, c⟩, -, rfl⟩ := Finset.mem_image.mp h
    exact ⟨rfl, by simp only [blk]; exact j.isLt⟩

lemma sum_clause_jobs : ∑ jc : Fin φ.m × Blocks.ClJob, Blocks.clLen p q jc.2 =
    φ.m * (p + q) := by
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [Blocks.sum_clLen]

/-- **A section's non-separator jobs total `S - 1 - q`** — the whole section length bar the
separator and the single unit of slack. -/
lemma sum_secJobs (l : Literal φ.n) :
    ∑ y ∈ secJobs φ l, len p q φ y = (p + 2 * q) + φ.m * (p + q) := by
  classical
  have hdisj : Disjoint
      (Finset.univ.image (fun c : Blocks.LitJob => (Sum.inl (l, c) : Job φ)))
      (Finset.univ.image
        (fun jc : Fin φ.m × Blocks.ClJob => (Sum.inr (Sum.inl (l, jc.1, jc.2)) : Job φ))) := by
    rw [Finset.disjoint_left]
    rintro y hy hy'
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨⟨j, c'⟩, -, hc⟩ := Finset.mem_image.mp hy'
    exact absurd hc (by simp)
  have h1 : ∑ y ∈ Finset.univ.image (fun c : Blocks.LitJob => (Sum.inl (l, c) : Job φ)),
      len p q φ y = p + 2 * q := by
    rw [Finset.sum_image (by rintro a - b - hab; simpa using hab)]
    exact Blocks.sum_litLen p q l.pos
  have h2 : ∑ y ∈ Finset.univ.image
      (fun jc : Fin φ.m × Blocks.ClJob => (Sum.inr (Sum.inl (l, jc.1, jc.2)) : Job φ)),
      len p q φ y = φ.m * (p + q) := by
    rw [Finset.sum_image (by
      rintro ⟨a1, a2⟩ - ⟨b1, b2⟩ - hab
      simpa [Prod.ext_iff] using hab)]
    exact sum_clause_jobs
  rw [secJobs, Finset.sum_union hdisj, h1, h2]

/-! The two geometric bounds the induction runs on. -/

lemma secLen_pos (hq : 1 < q) (hqp : q < p) : 0 < secLen p q φ := by
  simp only [secLen]
  omega

lemma len_ge_two (hq : 1 < q) (hqp : q < p) (y : Job φ) : 2 ≤ len p q φ y := by
  rcases y with ⟨l, c⟩ | ⟨l, j, c⟩ | l
  · obtain ⟨w, sgn⟩ := l
    cases sgn <;> cases c <;> simp only [len, Blocks.LitJob.len] <;> omega
  · cases c <;> simp only [len, Blocks.clLen] <;> omega
  · simp only [len]
    omega

/-- A non-separator job's deadline falls before its section's separator. -/
lemma due_le_sepOffset (hq : 1 < q) (_hqp : q < p) (y : Job φ) (hy : blk φ y ≤ φ.m) :
    due p q φ y ≤ sepOffset p q φ (sec φ y) := by
  rcases y with ⟨l, c⟩ | ⟨l, j, c⟩ | l
  · have hmq : (0 : ℤ) ≤ (φ.m : ℤ) * ((p : ℤ) + q) := by positivity
    have hd : Blocks.LitJob.due p q l.pos c ≤ (p : ℤ) + 2 * q + 1 := by
      obtain ⟨w, sgn⟩ := l
      cases sgn <;> cases c <;> simp only [Blocks.LitJob.due] <;> omega
    simp only [due, sec, litOffset, sepOffset, secLen]
    push_cast
    omega
  · have h := clOffset_lt_sep p q φ l j
    simp only [due, sec, Blocks.clDue]
    omega
  · exact absurd hy (by simp only [blk]; omega)

/-- Every job's deadline falls inside its own section. -/
lemma due_le_section (hq : 1 < q) (hqp : q < p) (y : Job φ) :
    due p q φ y ≤ secOffset p q φ (sec φ y) + (secLen p q φ : ℤ) := by
  by_cases hy : blk φ y ≤ φ.m
  · have h := due_le_sepOffset hq hqp y hy
    have h2 := sepOffset_add_le p q φ (sec φ y)
    have h3 : (0 : ℤ) ≤ (q : ℤ) := by positivity
    omega
  · rcases y with ⟨l, c⟩ | ⟨l, j, c⟩ | l
    · exact absurd (by simp only [blk]; omega) hy
    · exact absurd (by simp only [blk]; exact j.isLt) hy
    · have h2 := sepOffset_add_le p q φ l
      simp only [due, sec]
      omega

lemma rel_nonneg (y : Job φ) : 0 ≤ rel p q φ y := by
  rcases y with ⟨l, c⟩ | ⟨l, j, c⟩ | l
  · obtain ⟨w, sgn⟩ := l
    have h := secOffset_nonneg (p := p) (q := q) (φ := φ) ⟨w, sgn⟩
    cases sgn <;> cases c <;>
      simp only [rel, litOffset, Blocks.LitJob.rel] <;> positivity
  · exact le_refl 0
  · exact sepOffset_nonneg l

lemma sepOffset_litOfIndex (i : ℕ) (h : i < 2 * φ.n) :
    sepOffset p q φ (litOfIndex i h) = (secLen p q φ : ℤ) * i + (secLen p q φ : ℤ) - q := by
  simp only [sepOffset, secOffset, secIndex_litOfIndex]

/-- **The separators are pinned**: each has an availability interval exactly its own
length. -/
lemma sep_at (_hq : 1 < q) (_hqp : q < p) {T : Job φ → ℤ} (hf : PhysFeasible p q φ T)
    (l : Literal φ.n) : T (Sum.inr (Sum.inr l)) = sepOffset p q φ l := by
  have h1 := hf.rel (Sum.inr (Sum.inr l))
  have h2 := hf.due (Sum.inr (Sum.inr l))
  simp only [rel, due, len] at h1 h2
  omega

/-- **No job straddles a separator**: every non-separator job lies inside the window of a
single section, `[iS, (i+1)S - q)`. -/
lemma exists_window (hq : 1 < q) (hqp : q < p) {T : Job φ → ℤ} (hf : PhysFeasible p q φ T)
    (y : Job φ) (hy : blk φ y ≤ φ.m) :
    ∃ i : ℕ, i < 2 * φ.n ∧ (secLen p q φ : ℤ) * i ≤ T y ∧
      T y + len p q φ y ≤ (secLen p q φ : ℤ) * i + (secLen p q φ : ℤ) - q := by
  have hS : 0 < secLen p q φ := secLen_pos (φ := φ) hq hqp
  have hsecpos : (0 : ℤ) < (secLen p q φ : ℤ) := by exact_mod_cast hS
  have hTy : 0 ≤ T y := le_trans (rel_nonneg y) (hf.rel y)
  have hlen := len_ge_two hq hqp y
  have hdue := hf.due y
  have hsec := due_le_section hq hqp y
  -- locate `y` by dividing its start time by the section length
  set d : ℤ := T y / (secLen p q φ : ℤ) with hd
  have hd1 : (secLen p q φ : ℤ) * d + T y % (secLen p q φ : ℤ) = T y := Int.mul_ediv_add_emod _ _
  have hd2 : 0 ≤ T y % (secLen p q φ : ℤ) := Int.emod_nonneg _ (by omega)
  have hd3 : T y % (secLen p q φ : ℤ) < (secLen p q φ : ℤ) := Int.emod_lt_of_pos _ hsecpos
  have hd0 : 0 ≤ d := Int.ediv_nonneg hTy (le_of_lt hsecpos)
  have hlo : (secLen p q φ : ℤ) * d ≤ T y := by omega
  have hhi : T y < (secLen p q φ : ℤ) * d + (secLen p q φ : ℤ) := by omega
  have hidx : (secIndex (sec φ y) : ℤ) + 1 ≤ (2 * φ.n : ℤ) := by
    have := secIndex_lt (sec φ y)
    exact_mod_cast this
  have hd2n : d < 2 * φ.n := by
    by_contra hc
    push Not at hc
    have h2 : (secLen p q φ : ℤ) * (2 * φ.n) ≤ (secLen p q φ : ℤ) * d :=
      mul_le_mul_of_nonneg_left hc (le_of_lt hsecpos)
    have hmul : (secLen p q φ : ℤ) * ((secIndex (sec φ y) : ℤ) + 1) ≤
        (secLen p q φ : ℤ) * (2 * φ.n) :=
      mul_le_mul_of_nonneg_left hidx (le_of_lt hsecpos)
    have hexp : (secLen p q φ : ℤ) * ((secIndex (sec φ y) : ℤ) + 1) =
        (secLen p q φ : ℤ) * (secIndex (sec φ y)) + (secLen p q φ : ℤ) := by ring
    simp only [secOffset] at hsec
    linarith [hlo, hhi, hdue, hsec, h2, hmul, hexp.symm.le, hexp.le]
  have hi2n : d.toNat < 2 * φ.n := by omega
  have hcast : ((d.toNat : ℕ) : ℤ) = d := Int.toNat_of_nonneg hd0
  refine ⟨d.toNat, hi2n, by rw [hcast]; exact hlo, ?_⟩
  rw [hcast]
  -- the separator of that section is pinned just past the window
  have hsp := sep_at hq hqp hf (litOfIndex d.toNat hi2n)
  rw [sepOffset_litOfIndex, hcast] at hsp
  have hne : y ≠ Sum.inr (Sum.inr (litOfIndex d.toNat hi2n)) := by
    intro hc
    rw [hc] at hy
    simp only [blk] at hy
    omega
  rcases hf.sep _ _ hne with hc | hc
  · rw [hsp] at hc
    exact hc
  · exfalso
    rw [hsp] at hc
    simp only [len] at hc
    omega

/-- One step of Proposition 2's first stage: if every earlier section already holds its own
jobs, then so does section `k`. -/
lemma section_lower_step (hq : 1 < q) (hqp : q < p) {T : Job φ → ℤ}
    (hf : PhysFeasible p q φ T) (k : ℕ)
    (IH : ∀ i < k, ∀ z : Job φ, blk φ z ≤ φ.m → secIndex (sec φ z) = i →
      secOffset p q φ (sec φ z) ≤ T z)
    (y : Job φ) (hy : blk φ y ≤ φ.m) (hk : secIndex (sec φ y) = k) :
    secOffset p q φ (sec φ y) ≤ T y := by
  classical
  obtain ⟨i, hi2n, hlo, hhi⟩ := exists_window hq hqp hf y hy
  have hS : 0 < secLen p q φ := secLen_pos (φ := φ) hq hqp
  have hsecpos : (0 : ℤ) < (secLen p q φ : ℤ) := by exact_mod_cast hS
  have hik : i = k := by
    by_contra hne
    rcases Nat.lt_or_ge i k with hlt | hge
    · -- an earlier section is already full, and every job is longer than its slack
      exfalso
      obtain ⟨l, hlsec⟩ : ∃ l : Literal φ.n, secIndex l = i :=
        ⟨litOfIndex i hi2n, secIndex_litOfIndex i hi2n⟩
      have hlo' : secOffset p q φ l = (secLen p q φ : ℤ) * i := by
        simp only [secOffset, hlsec]
      have hsp' : sepOffset p q φ l =
          (secLen p q φ : ℤ) * i + (secLen p q φ : ℤ) - q := by
        simp only [sepOffset, secOffset, hlsec]
      have hynot : y ∉ secJobs φ l := by
        intro hc
        have hs := (secJobs_spec hc).1
        rw [hs, hlsec] at hk
        omega
      have hin : ∀ z ∈ insert y (secJobs φ l),
          (secLen p q φ : ℤ) * i ≤ T z ∧
            T z + len p q φ z ≤ (secLen p q φ : ℤ) * i + (secLen p q φ : ℤ) - q := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact ⟨hlo, hhi⟩
        · obtain ⟨hzsec, hzblk⟩ := secJobs_spec hz
          have h1 : secOffset p q φ (sec φ z) ≤ T z := by
            refine IH i hlt z hzblk ?_
            rw [hzsec, hlsec]
          have h2 := hf.due z
          have h3 := due_le_sepOffset hq hqp z hzblk
          rw [hzsec] at h1 h3
          rw [hlo'] at h1
          rw [hsp'] at h3
          exact ⟨h1, by omega⟩
      have hpack := Packing.sum_len_le (insert y (secJobs φ l)) T (len p q φ)
        ((secLen p q φ : ℤ) * i) ((secLen p q φ : ℤ) * i + (secLen p q φ : ℤ) - q)
        (fun a _ b _ hab => hf.sep a b hab) hin
      rw [Finset.sum_insert hynot, sum_secJobs] at hpack
      have hlen := len_ge_two hq hqp y
      have hq0 : q ≤ secLen p q φ := by simp only [secLen]; omega
      have htoNat : ((secLen p q φ : ℤ) * i + (secLen p q φ : ℤ) - q -
          (secLen p q φ : ℤ) * i).toNat = secLen p q φ - q := by
        have he : (secLen p q φ : ℤ) * i + (secLen p q φ : ℤ) - q - (secLen p q φ : ℤ) * i =
            ((secLen p q φ - q : ℕ) : ℤ) := by
          rw [Nat.cast_sub hq0]
          ring
        rw [he, Int.toNat_natCast]
      rw [htoNat] at hpack
      simp only [secLen] at hpack hq0 ⊢
      omega
    · -- a later section is out of reach: the deadline lies in section `k`
      exfalso
      have hgt : k < i := by omega
      have h2 := hf.due y
      have h3 := due_le_sepOffset hq hqp y hy
      have hsp : sepOffset p q φ (sec φ y) =
          (secLen p q φ : ℤ) * k + (secLen p q φ : ℤ) - q := by
        simp only [sepOffset, secOffset, hk]
      rw [hsp] at h3
      have hki : (secLen p q φ : ℤ) * ((k : ℤ) + 1) ≤ (secLen p q φ : ℤ) * i := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hsecpos)
        have : (k : ℤ) + 1 ≤ (i : ℤ) := by exact_mod_cast hgt
        exact this
      have hlen := len_ge_two hq hqp y
      nlinarith [hlo, hki, h2, h3, hlen]
  subst hik
  have hfin : secOffset p q φ (sec φ y) = (secLen p q φ : ℤ) * i := by
    simp only [secOffset, hk]
  rw [hfin]
  exact hlo

/-- **Proposition 2, stage 1.** Every non-separator job runs inside its own section. -/
lemma section_lower (hq : 1 < q) (hqp : q < p) {T : Job φ → ℤ} (hf : PhysFeasible p q φ T)
    (y : Job φ) (hy : blk φ y ≤ φ.m) : secOffset p q φ (sec φ y) ≤ T y := by
  have key : ∀ k : ℕ, ∀ i < k, ∀ z : Job φ, blk φ z ≤ φ.m → secIndex (sec φ z) = i →
      secOffset p q φ (sec φ z) ≤ T z := by
    intro k
    induction k with
    | zero => exact fun i hi => absurd hi (Nat.not_lt_zero i)
    | succ k IH =>
      intro i hi z hz hzk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · exact IH i h z hz hzk
      · exact section_lower_step hq hqp hf i IH z hz hzk
  exact section_lower_step hq hqp hf (secIndex (sec φ y)) (key (secIndex (sec φ y))) y hy rfl

/-! ### Proposition 2, stage 2: the blocks of a section are in order

With each job confined to its own section the local slack is one unit, and
`Packing.start_ge_of_slack` orders the blocks: nothing of block `j` starts before block
`j`'s own offset. If the literal block's pending job is early the block leaves its first
unit idle, the slack is spent, and everything after starts one unit later still. -/

variable (p q φ)

/-- The jobs of the blocks of section `l` strictly before clause block `j`, together with a
chosen subset of the literal block's own jobs. The subset varies: for `V⁺` the whole block
is pushed past the idle unit, while `V⁻` leaves its idle unit in the *middle* — its pending
job starts at the section boundary — so only its two ordinary jobs are counted. -/
def prefixJobs (l : Literal φ.n) (S₀ : Finset Blocks.LitJob) (j : ℕ) : Finset (Job φ) :=
  (S₀.image (fun c : Blocks.LitJob => (Sum.inl (l, c) : Job φ))) ∪
    (((Finset.univ.filter (fun j' : Fin φ.m => (j' : ℕ) < j)) ×ˢ
        (Finset.univ : Finset Blocks.ClJob)).image
      (fun jc => (Sum.inr (Sum.inl (l, jc.1, jc.2)) : Job φ)))

variable {p q φ}

lemma card_clause_prefix (j : ℕ) (hj : j ≤ φ.m) :
    (Finset.univ.filter (fun j' : Fin φ.m => (j' : ℕ) < j)).card = j := by
  classical
  have himg : (Finset.univ.filter (fun j' : Fin φ.m => (j' : ℕ) < j)).image Fin.val =
      Finset.range j := by
    ext a
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_range]
    constructor
    · rintro ⟨j', hj', rfl⟩
      exact hj'
    · intro ha
      exact ⟨⟨a, by omega⟩, ha, rfl⟩
  calc (Finset.univ.filter (fun j' : Fin φ.m => (j' : ℕ) < j)).card
      = ((Finset.univ.filter (fun j' : Fin φ.m => (j' : ℕ) < j)).image Fin.val).card :=
        (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ = (Finset.range j).card := by rw [himg]
    _ = j := Finset.card_range j

/-- **The prefix of a section totals exactly what its span accounts for.** -/
lemma sum_prefixJobs (l : Literal φ.n) (S₀ : Finset Blocks.LitJob) (j : ℕ) (hj : j ≤ φ.m) :
    ∑ y ∈ prefixJobs φ l S₀ j, len p q φ y =
      (∑ c ∈ S₀, Blocks.LitJob.len p q l.pos c) + j * (p + q) := by
  classical
  have hdisj : Disjoint
      (S₀.image (fun c : Blocks.LitJob => (Sum.inl (l, c) : Job φ)))
      (((Finset.univ.filter (fun j' : Fin φ.m => (j' : ℕ) < j)) ×ˢ
          (Finset.univ : Finset Blocks.ClJob)).image
        (fun jc => (Sum.inr (Sum.inl (l, jc.1, jc.2)) : Job φ))) := by
    rw [Finset.disjoint_left]
    rintro y hy hy'
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨⟨j', c'⟩, -, hc⟩ := Finset.mem_image.mp hy'
    exact absurd hc (by simp)
  have h1 : ∑ y ∈ S₀.image (fun c : Blocks.LitJob => (Sum.inl (l, c) : Job φ)),
      len p q φ y = ∑ c ∈ S₀, Blocks.LitJob.len p q l.pos c := by
    rw [Finset.sum_image (by rintro a - b - hab; simpa using hab)]
    rfl
  have h2 : ∑ y ∈ (((Finset.univ.filter (fun j' : Fin φ.m => (j' : ℕ) < j)) ×ˢ
      (Finset.univ : Finset Blocks.ClJob)).image
        (fun jc => (Sum.inr (Sum.inl (l, jc.1, jc.2)) : Job φ))),
      len p q φ y = j * (p + q) := by
    rw [Finset.sum_image (by
      rintro ⟨a1, a2⟩ - ⟨b1, b2⟩ - hab
      simpa [Prod.ext_iff] using hab)]
    rw [Finset.sum_product]
    simp only [len, Blocks.sum_clLen, Finset.sum_const, smul_eq_mul]
    rw [card_clause_prefix j hj]
  rw [prefixJobs, Finset.sum_union hdisj, h1, h2]

/-- Membership in `prefixJobs` is exactly what it looks like. -/
lemma prefixJobs_spec {l : Literal φ.n} {S₀ : Finset Blocks.LitJob} {j : ℕ} {y : Job φ}
    (hy : y ∈ prefixJobs φ l S₀ j) :
    (∃ c ∈ S₀, y = Sum.inl (l, c)) ∨ ∃ (j' : Fin φ.m) (c : Blocks.ClJob),
      (j' : ℕ) < j ∧ y = Sum.inr (Sum.inl (l, j', c)) := by
  classical
  rcases Finset.mem_union.mp hy with h | h
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp h
    exact Or.inl ⟨c, hc, rfl⟩
  · obtain ⟨⟨j', c⟩, hmem, rfl⟩ := Finset.mem_image.mp h
    exact Or.inr ⟨j', c, (Finset.mem_filter.mp (Finset.mem_product.mp hmem).1).2, rfl⟩

/-- The target job of a clause block is not in that block's own prefix. -/
lemma clause_notMem_prefix (l : Literal φ.n) (S₀ : Finset Blocks.LitJob) (j : Fin φ.m)
    (c : Blocks.ClJob) :
    (Sum.inr (Sum.inl (l, j, c)) : Job φ) ∉ prefixJobs φ l S₀ (j : ℕ) := by
  intro hc
  rcases prefixJobs_spec hc with ⟨c', -, hc'⟩ | ⟨j', c', hj', hc'⟩
  · exact absurd hc' (by simp)
  · injection hc' with h1
    injection h1 with h2
    injection h2 with h3 h4
    injection h4 with h5 h6
    rw [← h5] at hj'
    omega

/-- Every job of a section's prefix finishes by the start of clause block `j`, plus the
single unit of slack. -/
lemma prefix_upper (hq : 1 < q) (_hqp : q < p) {T : Job φ → ℤ} (hf : PhysFeasible p q φ T)
    (l : Literal φ.n) (S₀ : Finset Blocks.LitJob) (j : Fin φ.m) {z : Job φ}
    (hz : z ∈ prefixJobs φ l S₀ (j : ℕ)) :
    T z + len p q φ z ≤ clOffset p q φ l j + 1 := by
  have hdue := hf.due z
  rcases prefixJobs_spec hz with ⟨c', -, rfl⟩ | ⟨j', c', hj', rfl⟩
  · have hd : Blocks.LitJob.due p q l.pos c' ≤ (p : ℤ) + 2 * q + 1 := by
      obtain ⟨w, sgn⟩ := l
      cases sgn <;> cases c' <;> simp only [Blocks.LitJob.due] <;> omega
    have h0 : litOffset p q φ l + ((p : ℤ) + 2 * q) ≤ clOffset p q φ l j :=
      litOffset_le_clOffset p q φ l j
    simp only [due, litOffset] at hdue
    simp only [litOffset] at h0
    omega
  · have hmono : clOffset p q φ l j' + ((p : ℤ) + q) ≤ clOffset p q φ l j :=
      clOffset_mono p q φ hj'
    simp only [due, Blocks.clDue] at hdue
    omega

/-- **Proposition 2, stage 2.** No clause-block job starts before its own block. -/
lemma block_lower (hq : 1 < q) (hqp : q < p) {T : Job φ → ℤ} (hf : PhysFeasible p q φ T)
    (l : Literal φ.n) (j : Fin φ.m) (c : Blocks.ClJob) :
    clOffset p q φ l j ≤ T (Sum.inr (Sum.inl (l, j, c))) := by
  classical
  have hjm : (j : ℕ) ≤ φ.m := le_of_lt j.isLt
  set a : ℤ := secOffset p q φ l with ha
  set b : ℤ := clOffset p q φ l j + 1 with hb
  have hnotmem := clause_notMem_prefix l Finset.univ j c
  have hin : ∀ z ∈ prefixJobs φ l Finset.univ (j : ℕ),
      a ≤ T z ∧ T z + len p q φ z ≤ b := by
    intro z hz
    have hzsec : sec φ z = l ∧ blk φ z ≤ φ.m := by
      rcases prefixJobs_spec hz with ⟨c', -, rfl⟩ | ⟨j', c', hj', rfl⟩
      · exact ⟨rfl, by simp only [blk]; omega⟩
      · exact ⟨rfl, by simp only [blk]; exact j'.isLt⟩
    have hlow := section_lower hq hqp hf z hzsec.2
    rw [hzsec.1] at hlow
    exact ⟨hlow, prefix_upper hq hqp hf l Finset.univ j hz⟩
  have hfill : (b - a).toNat ≤
      (∑ i ∈ prefixJobs φ l Finset.univ (j : ℕ), len p q φ i) + 1 := by
    rw [sum_prefixJobs l Finset.univ (j : ℕ) hjm, Blocks.sum_litLen]
    have hba : b - a = (((p + 2 * q) + (j : ℕ) * (p + q) + 1 : ℕ) : ℤ) := by
      simp only [hb, ha, clOffset, secOffset]
      push_cast
      ring
    rw [hba, Int.toNat_natCast]
  have hlow := section_lower hq hqp hf (Sum.inr (Sum.inl (l, j, c))) (by
    simp only [blk]; exact j.isLt)
  simp only [sec] at hlow
  have hlen : 1 < len p q φ (Sum.inr (Sum.inl (l, j, c))) := by
    have := len_ge_two hq hqp (Sum.inr (Sum.inl (l, j, c)))
    omega
  have := Packing.start_ge_of_slack (prefixJobs φ l Finset.univ (j : ℕ)) T (len p q φ) a b 1
    (fun x _ y _ hxy => hf.sep x y hxy) hin hfill hnotmem hlow hlen
    (fun z hz => hf.sep _ z (fun hc => hnotmem (hc ▸ hz)))
  simp only [hb] at this
  omega

/-- The literal block of a section fits, in the sense `TypedBlocks.lean` asks for: this is
where stage 1 is spent, since the pending job's release time is `0` globally. -/
lemma litFits_of (hq : 1 < q) (hqp : q < p) {T : Job φ → ℤ} (hf : PhysFeasible p q φ T)
    (l : Literal φ.n) :
    Blocks.LitFits p q l.pos (litOffset p q φ l) (fun c => T (Sum.inl (l, c))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c
    cases c
    · exact hf.rel (Sum.inl (l, Blocks.LitJob.ord1))
    · exact hf.rel (Sum.inl (l, Blocks.LitJob.ord2))
    · have hlow := section_lower hq hqp hf (Sum.inl (l, Blocks.LitJob.pend))
        (by simp only [blk]; omega)
      simp only [sec] at hlow
      have hr : Blocks.LitJob.rel p q l.pos Blocks.LitJob.pend = 0 := by
        obtain ⟨w, sgn⟩ := l
        cases sgn <;> rfl
      simp only [litOffset, hr, add_zero]
      exact hlow
  · exact fun c => hf.due (Sum.inl (l, c))
  · intro c c' hcc
    have hne : (Sum.inl (l, c) : Job φ) ≠ Sum.inl (l, c') := by
      intro hc
      injection hc with h1
      injection h1 with h2 h3
      exact hcc h3
    exact hf.sep _ _ hne

/-- **Proposition 1, in the form stage 2 needs it.** If a literal block's pending job is
early the block leaves one unit of the section idle; which jobs of the block sit past that
unit, and where it is, depends on the block's type. -/
lemma lit_early_prefix (hq : 1 < q) (hqp : q < p) {T : Job φ → ℤ}
    (hf : PhysFeasible p q φ T) (l : Literal φ.n)
    (hearly : Blocks.LitPendEarly p q l.pos (litOffset p q φ l)
      (fun c => T (Sum.inl (l, c)))) :
    ∃ (S₀ : Finset Blocks.LitJob) (a : ℤ),
      (∀ c ∈ S₀, a ≤ T (Sum.inl (l, c))) ∧
      secOffset p q φ l + (p : ℤ) + 2 * q + 1 - a ≤
        ((∑ c ∈ S₀, Blocks.LitJob.len p q l.pos c : ℕ) : ℤ) ∧
      secOffset p q φ l + 1 ≤ a ∧ a ≤ secOffset p q φ l + (p : ℤ) + 2 * q := by
  have hfits := litFits_of hq hqp hf l
  have hlo : litOffset p q φ l = secOffset p q φ l := rfl
  obtain ⟨w, sgn⟩ := l
  cases sgn
  · -- `V⁻`: the pending job starts at the section boundary; the idle unit is behind it
    refine ⟨{Blocks.LitJob.ord1, Blocks.LitJob.ord2}, secOffset p q φ ⟨w, false⟩ + q + 1,
      ?_, ?_, by omega, by omega⟩
    · obtain ⟨-, h1, h2⟩ := Blocks.vminus_early_forces hq hqp hfits hearly
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · simpa only [hlo] using h1
      · rw [Finset.mem_singleton] at hc
        subst hc
        have : secOffset p q φ (⟨w, false⟩ : Literal φ.n) + 2 * (q : ℤ) + 1 ≤
            T (Sum.inl (⟨w, false⟩, Blocks.LitJob.ord2)) := by simpa only [hlo] using h2
        omega
    · rw [Finset.sum_insert (by decide), Finset.sum_singleton]
      simp only [Blocks.LitJob.len]
      push_cast
      omega
  · -- `V⁺`: the whole block is pushed past the idle unit at the section boundary
    refine ⟨Finset.univ, secOffset p q φ ⟨w, true⟩ + 1, ?_, ?_, by omega, by omega⟩
    · obtain ⟨h1, h2, h3⟩ := Blocks.vplus_early_forces hq hqp hfits hearly
      intro c _
      cases c
      · have : T (Sum.inl ((⟨w, true⟩ : Literal φ.n), Blocks.LitJob.ord1)) =
            secOffset p q φ ⟨w, true⟩ + 1 := by simpa only [hlo] using h1
        omega
      · have : secOffset p q φ (⟨w, true⟩ : Literal φ.n) + (p : ℤ) + q + 1 ≤
            T (Sum.inl (⟨w, true⟩, Blocks.LitJob.ord2)) := by simpa only [hlo] using h3
        omega
      · have : T (Sum.inl ((⟨w, true⟩ : Literal φ.n), Blocks.LitJob.pend)) =
            secOffset p q φ ⟨w, true⟩ + q + 1 := by simpa only [hlo] using h2
        omega
    · rw [Blocks.sum_litLen]
      push_cast
      omega

/-- One step of the delayed bound: if every earlier clause block of the section already
starts a unit late, so does this one. -/
lemma block_lower_early_step (hq : 1 < q) (hqp : q < p) {T : Job φ → ℤ}
    (hf : PhysFeasible p q φ T) (l : Literal φ.n)
    (hearly : Blocks.LitPendEarly p q l.pos (litOffset p q φ l)
      (fun c => T (Sum.inl (l, c))))
    (j : Fin φ.m)
    (IH : ∀ j' : Fin φ.m, (j' : ℕ) < (j : ℕ) → ∀ c : Blocks.ClJob,
      clOffset p q φ l j' + 1 ≤ T (Sum.inr (Sum.inl (l, j', c))))
    (c : Blocks.ClJob) :
    clOffset p q φ l j + 1 ≤ T (Sum.inr (Sum.inl (l, j, c))) := by
  classical
  obtain ⟨S₀, a, hS0, hsum, ha1, ha2⟩ := lit_early_prefix hq hqp hf l hearly
  have hjm : (j : ℕ) ≤ φ.m := le_of_lt j.isLt
  have hoff : clOffset p q φ l j =
      secOffset p q φ l + (p : ℤ) + 2 * q + ((j : ℕ) : ℤ) * ((p : ℤ) + q) := by
    simp only [clOffset]
  have hcl0 : secOffset p q φ l + (p : ℤ) + 2 * q ≤ clOffset p q φ l j := by
    have := litOffset_le_clOffset p q φ l j
    simp only [litOffset] at this
    omega
  set b : ℤ := clOffset p q φ l j + 1 with hb
  have hnotmem := clause_notMem_prefix l S₀ j c
  have hin : ∀ z ∈ prefixJobs φ l S₀ (j : ℕ), a ≤ T z ∧ T z + len p q φ z ≤ b := by
    intro z hz
    refine ⟨?_, prefix_upper hq hqp hf l S₀ j hz⟩
    rcases prefixJobs_spec hz with ⟨c', hc', rfl⟩ | ⟨j', c', hj', rfl⟩
    · exact hS0 c' hc'
    · have h1 := IH j' hj' c'
      have h2 : secOffset p q φ l + (p : ℤ) + 2 * q ≤ clOffset p q φ l j' := by
        have := litOffset_le_clOffset p q φ l j'
        simp only [litOffset] at this
        omega
      omega
  have hfill : (b - a).toNat ≤ (∑ i ∈ prefixJobs φ l S₀ (j : ℕ), len p q φ i) + 0 := by
    rw [Nat.add_zero, sum_prefixJobs l S₀ (j : ℕ) hjm]
    refine Int.toNat_le.mpr ?_
    push_cast
    rw [hb, hoff]
    push_cast at hsum
    omega
  have hxa : a ≤ T (Sum.inr (Sum.inl (l, j, c))) := by
    have := block_lower hq hqp hf l j c
    omega
  have hxlen : 0 < len p q φ (Sum.inr (Sum.inl (l, j, c))) := by
    have := len_ge_two hq hqp (Sum.inr (Sum.inl (l, j, c)))
    omega
  have := Packing.start_ge_of_slack (prefixJobs φ l S₀ (j : ℕ)) T (len p q φ) a b 0
    (fun x _ y _ hxy => hf.sep x y hxy) hin hfill hnotmem hxa hxlen
    (fun z hz => hf.sep _ z (fun hc => hnotmem (hc ▸ hz)))
  simp only [hb] at this
  omega

/-- **Proposition 2, the delayed bound.** A section whose literal block finishes its
pending job early has spent its unit of slack: every clause block of that section starts a
unit after its own offset. -/
lemma block_lower_early (hq : 1 < q) (hqp : q < p) {T : Job φ → ℤ}
    (hf : PhysFeasible p q φ T) (l : Literal φ.n)
    (hearly : Blocks.LitPendEarly p q l.pos (litOffset p q φ l)
      (fun c => T (Sum.inl (l, c))))
    (j : Fin φ.m) (c : Blocks.ClJob) :
    clOffset p q φ l j + 1 ≤ T (Sum.inr (Sum.inl (l, j, c))) := by
  have key : ∀ k : ℕ, ∀ j' : Fin φ.m, (j' : ℕ) < k → ∀ c' : Blocks.ClJob,
      clOffset p q φ l j' + 1 ≤ T (Sum.inr (Sum.inl (l, j', c'))) := by
    intro k
    induction k with
    | zero => exact fun j' hj' => absurd hj' (Nat.not_lt_zero _)
    | succ k IH =>
      intro j' hj' c'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h | h
      · exact IH j' h c'
      · exact block_lower_early_step hq hqp hf l hearly j' (fun j'' hj'' => IH j'' (by omega)) c'
  exact key ((j : ℕ) + 1) j (by omega) c

/-! ### The chain argument

With Proposition 2 in hand each section has a well-defined delay, `1` exactly when its
literal block's pending job is early, and each clause block satisfies `Blocks.ClFits` at
that delay. Proposition 1 then says a block with *both* pending jobs early must be active
and run at delay `0`.

For a clause `j`, walk the sections from the last one down. The long pending job of the
last section's block is early — it is unpaired, and required to be. Take the first section
whose long job is early: its short job is early too, either because the section is the
first one (where short jobs are unpaired and required to be early) or because the pair
straddling into it must have an early member and its long partner is not one. So that
block has both jobs early: it is active, and its section runs at delay `0` — which is to
say the literal of that section is true and occurs in the clause. -/

variable (p q φ)

open scoped Classical in
/-- How far a section runs late: one unit exactly when its literal block finishes its
pending job early. -/
noncomputable def delayOf (T : Job φ → ℤ) (l : Literal φ.n) : ℤ :=
  if Blocks.LitPendEarly p q l.pos (litOffset p q φ l) (fun c => T (Sum.inl (l, c)))
  then 1 else 0

variable {p q φ}

lemma delayOf_nonneg (T : Job φ → ℤ) (l : Literal φ.n) : 0 ≤ delayOf p q φ T l := by
  unfold delayOf
  split <;> omega

lemma delayOf_eq_zero (T : Job φ → ℤ) (l : Literal φ.n) (h : delayOf p q φ T l = 0) :
    ¬ Blocks.LitPendEarly p q l.pos (litOffset p q φ l) (fun c => T (Sum.inl (l, c))) := by
  unfold delayOf at h
  split at h
  · omega
  · assumption

/-- **Proposition 2, assembled.** Each clause block fits at its section's delay. -/
lemma clFits_of (hq : 1 < q) (hqp : q < p) {T : Job φ → ℤ} (hf : PhysFeasible p q φ T)
    (l : Literal φ.n) (j : Fin φ.m) :
    Blocks.ClFits p q (clOffset p q φ l j) (delayOf p q φ T l)
      (fun c => T (Sum.inr (Sum.inl (l, j, c)))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c
    unfold delayOf
    split
    · rename_i hearly
      have := block_lower_early hq hqp hf l hearly j c
      omega
    · have := block_lower hq hqp hf l j c
      omega
  · intro c
    have hd := hf.due (Sum.inr (Sum.inl (l, j, c)))
    simpa only [due, len] using hd
  · have hne : (Sum.inr (Sum.inl (l, j, Blocks.ClJob.long)) : Job φ) ≠
        Sum.inr (Sum.inl (l, j, Blocks.ClJob.short)) := by simp
    have := hf.sep _ _ hne
    simpa only [len] using this

/-- **Lemma 4.** A solution to the constructed instance is a satisfying assignment. -/
theorem satisfiable_of_yes (hq : 1 < q) (hqp : q < p) (hn : φ.n ≠ 0)
    (h : (toAux p q φ hq hqp).Yes) : φ.Satisfiable := by
  classical
  obtain ⟨t, hsolve⟩ := h
  set T : Job φ → ℤ := readSched φ t with hT
  have hf : PhysFeasible p q φ T :=
    ⟨read_rel hq hqp hsolve, read_due hq hqp hsolve, fun y z hyz => read_sep hq hqp hsolve hyz⟩
  -- a literal is true exactly when its own block's pending job is late
  set early : Literal φ.n → Prop := fun l =>
    Blocks.LitPendEarly p q l.pos (litOffset p q φ l) (fun c => T (Sum.inl (l, c)))
    with hearly
  refine ⟨fun i => !decide (early ⟨i, true⟩), fun j => ?_⟩
  set v : φ.Assignment := fun i => !decide (early ⟨i, true⟩) with hv
  -- a section running at delay `0` has a true literal
  have holds_of_late : ∀ l : Literal φ.n, ¬ early l → Literal.Holds v l := by
    intro l hl
    obtain ⟨w, sgn⟩ := l
    cases sgn
    · -- `¬xᵢ` is true when its block is late, because then `xᵢ`'s block must be early
      have hpair := read_pair_early hq hqp hsolve (Sum.inl w)
      have hshort : ¬ (T (shortPhys φ (Sum.inl w)) + (q : ℤ) ≤ dqOf' p q φ (Sum.inl w)) := hl
      have hlong : T (longPhys φ (Sum.inl w)) + (p : ℤ) ≤ dpOf' p q φ (Sum.inl w) := by
        rcases hpair with hc | hc
        · exact hc
        · exact absurd hc hshort
      have hE : early (⟨w, true⟩ : Literal φ.n) := hlong
      show v w = false
      simp only [hv]
      rw [decide_eq_true hE]
      rfl
    · have hE : ¬ early (⟨w, true⟩ : Literal φ.n) := hl
      show v w = true
      simp only [hv]
      rw [decide_eq_false hE]
      rfl
  -- walk the sections: some block of clause `j` has both its pending jobs early
  have hlast : (2 * φ.n - 1) < 2 * φ.n := by omega
  have hex : ∃ k : ℕ, ∃ l : Literal φ.n, secIndex l = k ∧
      Blocks.ClEarlyAt p q (active φ l j) (clOffset p q φ l j)
        (fun c => T (Sum.inr (Sum.inl (l, j, c)))) .long := by
    refine ⟨2 * φ.n - 1, litOfIndex (2 * φ.n - 1) hlast, secIndex_litOfIndex _ _, ?_⟩
    exact read_last_early hq hqp hsolve ⟨litOfIndex (2 * φ.n - 1) hlast,
      secIndex_litOfIndex _ _⟩ j
  obtain ⟨k₀, l₀, hl₀sec, hl₀long, hmin⟩ :
      ∃ (k₀ : ℕ) (l₀ : Literal φ.n), secIndex l₀ = k₀ ∧
        Blocks.ClEarlyAt p q (active φ l₀ j) (clOffset p q φ l₀ j)
          (fun c => T (Sum.inr (Sum.inl (l₀, j, c)))) .long ∧
        ∀ k < k₀, ¬ ∃ l : Literal φ.n, secIndex l = k ∧
          Blocks.ClEarlyAt p q (active φ l j) (clOffset p q φ l j)
            (fun c => T (Sum.inr (Sum.inl (l, j, c)))) .long := by
    obtain ⟨l, h1, h2⟩ := Nat.find_spec hex
    exact ⟨Nat.find hex, l, h1, h2, fun k hk => Nat.find_min hex hk⟩
  have hl₀lt : secIndex l₀ < 2 * φ.n := secIndex_lt l₀
  -- its short job is early too
  have hl₀short : Blocks.ClEarlyAt p q (active φ l₀ j) (clOffset p q φ l₀ j)
      (fun c => T (Sum.inr (Sum.inl (l₀, j, c)))) .short := by
    rcases Nat.eq_zero_or_pos k₀ with hz | hpos
    · exact read_first_early hq hqp hsolve ⟨l₀, by rw [hl₀sec, hz]⟩ j
    · have hk1 : k₀ - 1 < 2 * φ.n - 1 := by omega
      have hpair := read_pair_early hq hqp hsolve (Sum.inr (⟨k₀ - 1, hk1⟩, j))
      have hlit2 : litOfIndex (k₀ - 1 + 1) (show k₀ - 1 + 1 < 2 * φ.n by omega) = l₀ :=
        (litOfIndex_congr _ hl₀lt (by omega)).trans (litOfIndex_secIndex l₀ hl₀lt)
      rcases hpair with hc | hc
      · exfalso
        refine hmin (k₀ - 1) (by omega)
          ⟨litOfIndex (k₀ - 1) (show k₀ - 1 < 2 * φ.n by omega), secIndex_litOfIndex _ _, ?_⟩
        simp only [longPhys, dpOf'] at hc
        exact hc
      · simp only [shortPhys, dqOf'] at hc
        rw [hlit2] at hc
        exact hc
  -- Proposition 1: both early forces an active block at delay zero
  have hbound := Blocks.cl_both_early_bound (clFits_of hq hqp hf l₀ j) hl₀long hl₀short
  have hd0 := delayOf_nonneg (p := p) (q := q) T l₀
  have hact : active φ l₀ j = true := by
    by_contra hc
    simp only [Bool.not_eq_true] at hc
    rw [hc] at hbound
    simp only [Blocks.clEarly] at hbound
    omega
  rw [hact] at hbound
  simp only [Blocks.clEarly] at hbound
  have hdz : delayOf p q φ T l₀ = 0 := by omega
  refine ⟨l₀, ?_, holds_of_late l₀ ?_⟩
  · exact of_decide_eq_true hact
  · exact delayOf_eq_zero (p := p) (q := q) T l₀ hdz

end Lemma4

/-! ## 12. The reduction

Definition 7 assumes at least one variable, and with good reason: with none there are no
jobs at all, so the instance is trivially feasible, while the formula is satisfiable only
if it also has no clauses. The map therefore sends a variable-free formula with clauses to
an instance that is explicitly infeasible, and every other formula to `toAux`. -/

/-- An `AUX(p, q)` instance with no solution: one ordinary job whose deadline falls before
it could possibly finish. -/
def blocked (hqp : q < p) (hq : 1 < q) : Aux p q where
  Ord := Unit
  ordFintype := inferInstance
  ordDecEq := inferInstance
  r _ := 0
  d _ := 0
  len _ := q
  r_nonneg _ := le_refl 0
  len_eq _ := Or.inr rfl
  q_pos := by omega
  q_lt_p := hqp
  N := 0
  dp' := Fin.elim0
  dp := Fin.elim0
  dq' := Fin.elim0
  dq := Fin.elim0
  dp'_le_dp i := i.elim0
  dp_le_dp'_succ i := i.elim0
  dq'_le_dq i := i.elim0
  dq_le_dq'_succ i := i.elim0
  dp_le_dq' i := i.elim0
  dp'_nonneg i := i.elim0
  dq'_nonneg i := i.elim0

lemma blocked_not_yes (hqp : q < p) (hq : 1 < q) : ¬ (blocked p q hqp hq).Yes := by
  rintro ⟨t, ⟨hav, -⟩, -⟩
  have h := hav (Aux.ordJob ())
  simp only [Aux.toInstance_r_ord, Aux.toInstance_d_ord, Instance.completion,
    Aux.toInstance_p_ord, blocked] at h
  omega

/-- **The reduction of Definition 7**, as a map from formulas to `AUX(p, q)` instances. -/
noncomputable def map (hqp : q < p) (hq : 1 < q) (φ : Cnf) : Aux p q :=
  if φ.n = 0 ∧ 0 < φ.m then blocked p q hqp hq else toAux p q φ hq hqp

/-- **Lemma 2's correctness**: the formula is satisfiable exactly when the constructed
`AUX(p, q)` instance has a solution. Lemmas 3 and 4 of the paper, with Propositions 2 and 3
beneath them. -/
theorem map_correct (hqp : q < p) (hq : 1 < q) (φ : Cnf) :
    satProblem φ ↔ auxProblem p q (map p q hqp hq φ) := by
  by_cases hn : φ.n = 0
  · -- No variables: there is nothing to satisfy and nothing to schedule.
    have hlit : IsEmpty (Literal φ.n) := ⟨fun l => absurd l.var.isLt (by omega)⟩
    by_cases hm : 0 < φ.m
    · -- ... but there is a clause, which is then empty, hence unsatisfiable.
      rw [map, if_pos ⟨hn, hm⟩]
      constructor
      · rintro ⟨v, hv⟩
        obtain ⟨l, -, -⟩ := hv ⟨0, hm⟩
        exact (hlit.false l).elim
      · intro h
        exact absurd h (blocked_not_yes p q hqp hq)
    · -- No clauses either: both sides hold vacuously.
      rw [map, if_neg (by tauto)]
      have hN : numPairs φ = 0 := by simp [numPairs, hn]
      have hempty : IsEmpty ((toAux p q φ hq hqp).Job) := by
        constructor
        rintro (o | i | i)
        · rcases o with ⟨l, -⟩ | l | ⟨⟨l, -⟩, -⟩ | ⟨⟨l, -⟩, -⟩ <;> exact hlit.false l
        · have h : (i : ℕ) < numPairs φ := i.isLt
          omega
        · have h : (i : ℕ) < numPairs φ := i.isLt
          omega
      constructor
      · intro _
        exact Aux.yes_of_isEmpty _ hempty
      · intro _
        exact ⟨fun _ => false, fun j => absurd j.isLt (by omega)⟩
  · -- The case Definition 7 is written for: Lemmas 3 and 4.
    rw [map, if_neg (by tauto)]
    exact ⟨fun h => yes_of_satisfiable p q φ hq hqp h,
      fun h => satisfiable_of_yes hq hqp hn h⟩

end FromSat
end RjLmax

end Lax391470Proofs
