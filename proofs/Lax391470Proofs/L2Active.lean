import Lax391470.SatConstruction
import Lax391470Proofs.L2ScanModel

/-!
Which clause blocks are active, as a table indexed by section and clause, and how the flat
form of a formula fills it.
-/

namespace Lax391470Proofs.L2Active

open Lax429075.CNF Lax391470.SatConstruction Lax391470Proofs.L2ScanModel

/-- The section of a literal. -/
def secOf (l : Literal) : ℕ := 2 * l.index + if l.positive then 0 else 1

lemma literalOf_secOf (l : Literal) : literalOf (secOf l) = l := by
  obtain ⟨i, b⟩ := l
  cases b <;> simp [literalOf, secOf]; omega

lemma secOf_literalOf (s : ℕ) : secOf (literalOf s) = s := by
  unfold secOf literalOf
  by_cases h : s % 2 = 0 <;> simp [h] <;> omega

lemma mem_zip_replicate (c : Clause) (k : ℕ) (l : Literal) (j : ℕ) :
    (l, j) ∈ c.zip (List.replicate c.length k) ↔ l ∈ c ∧ j = k := by
  induction c with
  | nil => simp
  | cons a t ih =>
    simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons, List.mem_cons,
      Prod.mk.injEq, ih]
    tauto

/-- A literal together with the number of its clause occurs in the flat form exactly when
it occurs in that clause. -/
lemma mem_zip (d : List Clause) (l : Literal) (j : ℕ) :
    (l, j) ∈ (lits d).zip (cn d) ↔ j < d.length ∧ l ∈ d.getD j [] := by
  induction d using List.reverseRecOn with
  | nil => simp [lits, cn]
  | append_singleton d c ih =>
    rw [lits_append, cn_append, List.zip_append (by rw [cn_length]), List.mem_append, ih]
    rw [mem_zip_replicate]
    constructor
    · rintro (⟨hj, hl⟩ | ⟨hl, rfl⟩)
      · exact ⟨by simp; omega, by rwa [List.getD_append _ _ _ _ hj]⟩
      · exact ⟨by simp, by simp [hl]⟩
    · rintro ⟨hj, hl⟩
      simp only [List.length_append, List.length_singleton] at hj
      rcases Nat.lt_or_ge j d.length with h | h
      · exact Or.inl ⟨h, by rwa [List.getD_append _ _ _ _ h] at hl⟩
      · have : j = d.length := by omega
        subst this
        exact Or.inr ⟨by simpa using hl, rfl⟩

lemma snd_lt_of_mem_zip (d : List Clause) {x : Literal × ℕ} (hx : x ∈ (lits d).zip (cn d)) :
    x.2 < d.length := ((mem_zip d x.1 x.2).mp hx).1

variable (F : Formula)

open Classical in
/-- The table: entry `s · m + j` says whether the clause block of clause `j` in section
`s` is active. -/
noncomputable def table (t : ℕ) : ℕ :=
  if ∃ x ∈ (lits F).zip (cn F), secOf x.1 * F.length + x.2 = t then 1 else 0

theorem table_eq (s j : ℕ) (hj : j < F.length) :
    table F (s * F.length + j) = if active F s j then 1 else 0 := by
  classical
  unfold table active
  have key : (∃ x ∈ (lits F).zip (cn F), secOf x.1 * F.length + x.2 = s * F.length + j) ↔
      literalOf s ∈ F.getD j [] := by
    constructor
    · rintro ⟨⟨l, j'⟩, hx, he⟩
      obtain ⟨hj', hl⟩ := (mem_zip F l j').mp hx
      simp only at he
      have h1 : secOf l = s := by
        have e1 : (secOf l * F.length + j') / F.length = secOf l := by
          rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj']; rfl
        have e2 : (s * F.length + j) / F.length = s := by
          rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj]; rfl
        rw [← e1, he, e2]
      have h2 : j' = j := by rw [h1] at he; omega
      rw [← h1, literalOf_secOf, ← h2]; exact hl
    · intro hl
      exact ⟨(literalOf s, j), (mem_zip F _ j).mpr ⟨hj, hl⟩, by rw [secOf_literalOf]⟩
  by_cases h : literalOf s ∈ F.getD j []
  · rw [if_pos (key.mpr h), if_pos (decide_eq_true h)]
  · rw [if_neg (fun hc => h (key.mp hc)), if_neg (by simpa using h)]

end Lax391470Proofs.L2Active
