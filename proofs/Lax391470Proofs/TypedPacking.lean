import Mathlib.Algebra.BigOperators.Ring.Finset
import Lax391470Proofs.TypedDefs

namespace Lax391470Proofs

/-!
# Packing: How Much Fits in a Window

Almost every step of the paper's proof is one counting argument. "The jobs in each
section have length `S − 1`, each section ends with a separator job, and all job lengths
are greater than one, so all jobs are scheduled within their own section" (Proposition 2)
is the argument; "the four jobs representing the `i`'th quad have release times aligned
with the `i`'th bin, and a bin holds `p + q`" (Lemma 1) is the argument again. Both are
instances of:

> non-overlapping jobs that all run inside `[a, b)` have total length at most `b − a`,

together with its sharpening

> and if they leave only `s` units of slack, then a job of length `> s` that starts no
> earlier than `a` must start at `b − s` or later — it cannot squeeze in, and it cannot
> even *straddle* the right end by more than `s`.

The straddle clause is what makes the second one usable: an intruding job is not blocked
from starting inside a full window by a cardinality argument alone, since it could poke
out of the far end. It is blocked from starting *early* inside one, which is what the
paper's "they can start at time equal to their offset or later" asserts.

Over `ℤ` both are cardinality statements about `Finset.Ico`, which is why the
development works over `ℤ`.
-/

namespace RjLmax
namespace Packing

variable {J : Type*} {t : J → ℤ} {len : J → ℕ}

/-- The integer time points at which job `i` holds the machine. -/
def slot (t : J → ℤ) (len : J → ℕ) (i : J) : Finset ℤ := Finset.Ico (t i) (t i + len i)

@[simp] lemma card_slot (t : J → ℤ) (len : J → ℕ) (i : J) :
    (slot t len i).card = len i := by
  rw [slot, Int.card_Ico]
  omega

@[simp] lemma mem_slot {i : J} {x : ℤ} :
    x ∈ slot t len i ↔ t i ≤ x ∧ x < t i + len i := by
  simp [slot]

/-- Jobs that do not overlap hold disjoint sets of time points. -/
lemma disjoint_slot {i j : J} (h : t i + len i ≤ t j ∨ t j + len j ≤ t i) :
    Disjoint (slot t len i) (slot t len j) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [mem_slot] at hx hx'
  omega

/-- **The packing bound.** Non-overlapping jobs that all run inside `[a, b)` have total
length at most `b − a`. -/
theorem sum_len_le (S : Finset J) (t : J → ℤ) (len : J → ℕ) (a b : ℤ)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → t i + len i ≤ t j ∨ t j + len j ≤ t i)
    (hin : ∀ i ∈ S, a ≤ t i ∧ t i + len i ≤ b) :
    ∑ i ∈ S, len i ≤ (b - a).toNat := by
  have hsub : S.biUnion (slot t len) ⊆ Finset.Ico a b := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨i, hi, hx⟩ := hx
    rw [mem_slot] at hx
    have := hin i hi
    simp only [Finset.mem_Ico]
    omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_biUnion fun i hi j hj hij => disjoint_slot (hsep i hi j hj hij)] at hcard
  simpa [Int.card_Ico] using hcard

/-- **The straddle bound.** If the jobs of `S` run inside `[a, b)` and a further job `x`
starts no earlier than `a` and overlaps none of them, then the part of `x` that falls
inside the window fits in the slack the jobs of `S` leave. The job may poke out of the
far end of the window; only what is inside it is counted. -/
theorem overlap_le_slack (S : Finset J) (t : J → ℤ) (len : J → ℕ) (a b : ℤ)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → t i + len i ≤ t j ∨ t j + len j ≤ t i)
    (hin : ∀ i ∈ S, a ≤ t i ∧ t i + len i ≤ b)
    {x : J} (hx : x ∉ S) (hxa : a ≤ t x)
    (hxsep : ∀ i ∈ S, t x + len x ≤ t i ∨ t i + len i ≤ t x) :
    (∑ i ∈ S, len i) + (min (b - t x) (len x)).toNat ≤ (b - a).toNat := by
  classical
  rcases le_or_gt b (t x) with hbx | hbx
  · -- `x` starts after the window: nothing of it is inside.
    have h := sum_len_le S t len a b hsep hin
    omega
  -- Shorten `x` to the part inside the window and pack it with the rest.
  have key := sum_len_le (insert x S) t (Function.update len x (min (b - t x) (len x)).toNat)
      a b ?sep ?inn
  · have hsum : ∑ i ∈ S, Function.update len x (min (b - t x) (len x)).toNat i
        = ∑ i ∈ S, len i :=
      Finset.sum_congr rfl fun i hi =>
        Function.update_of_ne (by rintro rfl; exact hx hi) _ _
    rw [Finset.sum_insert hx, Function.update_self, hsum] at key
    omega
  case sep =>
    have hle : ∀ i, (Function.update len x (min (b - t x) (len x)).toNat i : ℤ) ≤ len i := by
      intro i
      by_cases h : i = x
      · subst h; rw [Function.update_self]; omega
      · rw [Function.update_of_ne h]
    intro i hi j hj hij
    have base : t i + (len i : ℤ) ≤ t j ∨ t j + (len j : ℤ) ≤ t i := by
      rcases Finset.mem_insert.mp hi with hi' | hi'
      · rcases Finset.mem_insert.mp hj with hj' | hj'
        · exact absurd (hi'.trans hj'.symm) hij
        · rw [hi']; exact hxsep j hj'
      · rcases Finset.mem_insert.mp hj with hj' | hj'
        · rw [hj']; exact (hxsep i hi').symm
        · exact hsep i hi' j hj' hij
    have h1 := hle i
    have h2 := hle j
    omega
  case inn =>
    intro i hi
    rcases Finset.mem_insert.mp hi with hi' | hi'
    · subst hi'
      rw [Function.update_self]
      omega
    · rw [Function.update_of_ne (by rintro rfl; exact hx hi') _ _]
      exact hin i hi'

/-- **No early intruder.** If the jobs of `S` fill `[a, b)` to within `s` units of slack,
then a job longer than `s` that starts no earlier than `a` and overlaps none of them
starts at `b − s` or later. This is the shape Proposition 2 uses: a job of a later block
cannot start before its own offset, because everything before it is already full. -/
theorem start_ge_of_slack (S : Finset J) (t : J → ℤ) (len : J → ℕ) (a b : ℤ) (s : ℕ)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → t i + len i ≤ t j ∨ t j + len j ≤ t i)
    (hin : ∀ i ∈ S, a ≤ t i ∧ t i + len i ≤ b)
    (hfill : (b - a).toNat ≤ (∑ i ∈ S, len i) + s)
    {x : J} (hx : x ∉ S) (hxa : a ≤ t x) (hxlen : s < len x)
    (hxsep : ∀ i ∈ S, t x + len x ≤ t i ∨ t i + len i ≤ t x) :
    b - s ≤ t x := by
  classical
  have h := overlap_le_slack S t len a b hsep hin hx hxa hxsep
  omega

/-- **Packing.** Jobs whose lengths sum to `L` can always be laid end to end starting at
`a`, occupying `[a, a + L)` and overlapping nowhere. The converse of `sum_len_le`, and what
the exchange argument of `TypedStacked.lean` needs in order to re-place the jobs it
displaces out of a bin: their total length is bounded, so a gap of that size takes them,
whatever their number. -/
theorem exists_packing {J : Type*} [DecidableEq J] (len : J → ℕ) (S : Finset J) :
    ∀ a : ℤ, ∃ t : J → ℤ,
      (∀ x ∈ S, a ≤ t x ∧ t x + len x ≤ a + (∑ y ∈ S, len y : ℕ)) ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → t x + len x ≤ t y ∨ t y + len y ≤ t x) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact fun a => ⟨fun _ => a, by simp, by simp⟩
  | insert x S hx ih =>
    intro a
    obtain ⟨t, h1, h2⟩ := ih (a + len x)
    refine ⟨Function.update t x a, ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with heq | hyS
      · subst heq
        rw [Function.update_self, Finset.sum_insert hx]
        omega
      · have hyx : y ≠ x := by rintro rfl; exact hx hyS
        rw [Function.update_of_ne hyx, Finset.sum_insert hx]
        have := h1 y hyS
        omega
    · intro y hy z hz hyz
      rcases Finset.mem_insert.mp hy with heqy | hyS <;>
        rcases Finset.mem_insert.mp hz with heqz | hzS
      · exact absurd (heqy.trans heqz.symm) hyz
      · subst heqy
        have hzx : z ≠ y := by rintro rfl; exact hx hzS
        rw [Function.update_self, Function.update_of_ne hzx]
        have := (h1 z hzS).1
        exact Or.inl (by omega)
      · subst heqz
        have hyx : y ≠ z := by rintro rfl; exact hx hyS
        rw [Function.update_self, Function.update_of_ne hyx]
        have := (h1 y hyS).1
        exact Or.inr (by omega)
      · have hyx : y ≠ x := by rintro rfl; exact hx hyS
        have hzx : z ≠ x := by rintro rfl; exact hx hzS
        rw [Function.update_of_ne hyx, Function.update_of_ne hzx]
        exact h2 y hyS z hzS hyz

/-- **Splitting off one job.** If a set of jobs fits in `m + ℓ` and one of them has length
`ℓ`, the rest fit in `m`. Trivial, but it is what makes the exchange argument's worst case
manageable: when a bin's contents have to be re-placed into two separate gaps, of sizes `p`
and `q`, one job goes into the `q` gap and everything else fits in the `p` gap — no
splitting by cardinality, no arithmetic on `⌊p/q⌋`. -/
theorem sum_erase_le {J : Type*} [DecidableEq J] (len : J → ℕ) (S : Finset J) {x : J}
    (hx : x ∈ S) {m : ℕ} (htot : ∑ y ∈ S, len y ≤ m + len x) :
    ∑ y ∈ S.erase x, len y ≤ m := by
  have := Finset.sum_erase_add S len hx
  omega

end Packing

/-! ## The same two bounds, for a schedule of an instance -/

namespace Instance

variable {I : Instance}

/-- **The packing bound** for a feasible schedule: jobs running inside `[a, b)` have
total processing time at most `b − a`. -/
theorem sum_p_le {t : I.Schedule} (h : NoOverlap t) (S : Finset I.Job) {a b : ℤ}
    (hin : ∀ i ∈ S, RunsIn t i a b) : ∑ i ∈ S, I.p i ≤ (b - a).toNat :=
  Packing.sum_len_le S t I.p a b (fun i _ j _ hij => h i j hij) fun i hi => hin i hi

end Instance

end RjLmax

end Lax391470Proofs
