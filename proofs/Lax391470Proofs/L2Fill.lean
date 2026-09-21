import Lax391470Proofs.ReadAll

/-!
Filling a table of marks: for every `i < K` the cell `(2·iv i + 1 − sv i)·m + cv i` is set
to one. Stated for arbitrary number sequences, so that nothing here knows about formulas.
-/

namespace Lax391470Proofs.L2Fill

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.bin .add (V s) (.lit 1))
abbrev add (e f : Expr) : Expr := .bin .add e f
abbrev sub (e f : Expr) : Expr := .bin .sub e f
abbrev mul (e f : Expr) : Expr := .bin .mul e f

def fillBody : Com :=
  .seq (.assign "t"
      (add (mul (sub (add (mul (.lit 2) (.get "vr" (V "i"))) (.lit 1)) (.get "sg" (V "i")))
        (V "m")) (.get "cl" (V "i"))))
    (.seq (.store "act" (V "t") (.lit 1)) (bump "i"))

def fillLoop : Com := .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "k")) fillBody)

variable {B : ℕ} (K m Lact : ℕ) (iv sv cv : ℕ → ℕ)

/-- The cell marked by entry `i`. -/
def cell (i : ℕ) : ℕ := (2 * iv i + 1 - sv i) * m + cv i

open Classical in
/-- The table after the first `i` entries. -/
noncomputable def pre (i t : ℕ) : ℕ := if ∃ i' < i, cell m iv sv cv i' = t then 1 else 0

lemma pre_succ (i t : ℕ) :
    pre m iv sv cv (i + 1) t = if cell m iv sv cv i = t then 1 else pre m iv sv cv i t := by
  classical
  unfold pre
  by_cases h : cell m iv sv cv i = t
  · rw [if_pos h, if_pos ⟨i, by omega, h⟩]
  · rw [if_neg h]
    congr 1
    refine propext ⟨?_, fun ⟨i', hi', he⟩ => ⟨i', by omega, he⟩⟩
    rintro ⟨i', hi', he⟩
    rcases Nat.lt_or_ge i' i with hlt | hge
    · exact ⟨i', hlt, he⟩
    · have : i' = i := by omega
      subst this; exact absurd he h

def FInv (σ : Env) : Prop :=
  σ.vars "m" = m ∧ σ.vars "k" = K ∧ σ.vars "i" ≤ K ∧
    K ≤ (σ.arrs "vr").length ∧ K ≤ (σ.arrs "sg").length ∧ K ≤ (σ.arrs "cl").length ∧
    (∀ i < K, (σ.arrs "vr").getD i 0 = iv i) ∧ (∀ i < K, (σ.arrs "sg").getD i 0 = sv i) ∧
    (∀ i < K, (σ.arrs "cl").getD i 0 = cv i) ∧
    (σ.arrs "act").length = Lact ∧
    (∀ t < Lact, (σ.arrs "act").getD t 0 = pre m iv sv cv (σ.vars "i") t) ∧ σ.out = []

theorem fillBody_spec (hcell : ∀ i < K, cell m iv sv cv i < Lact)
    (hval : ∀ i < K, 2 * iv i + 1 < B ∧ sv i < B ∧ cv i < B ∧ (2 * iv i + 1 - sv i) * m < B)
    (hB : Lact + 2 < B) (hK : K + 1 < B) (hm : m < B) :
    Spec B (fun σ => FInv K m Lact iv sv cv σ ∧ σ.vars "i" < K) fillBody
      (fun σ σ' => FInv K m Lact iv sv cv σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 40 := by
  refine Spec.pre (P := fun σ => FInv K m Lact iv sv cv σ ∧ σ.vars "i" < K ∧
      σ.vars "i" < (σ.arrs "vr").length ∧ σ.vars "i" < (σ.arrs "sg").length ∧
      σ.vars "i" < (σ.arrs "cl").length ∧
      (σ.arrs "vr").getD (σ.vars "i") 0 = iv (σ.vars "i") ∧
      (σ.arrs "sg").getD (σ.vars "i") 0 = sv (σ.vars "i") ∧
      (σ.arrs "cl").getD (σ.vars "i") 0 = cv (σ.vars "i") ∧
      σ.vars "m" = m ∧ cell m iv sv cv (σ.vars "i") < (σ.arrs "act").length) ?_ ?_
  · run_vcg
    all_goals have hi := ‹σ.vars "i" < K›
    all_goals have e1 := ‹(σ.arrs "vr").getD (σ.vars "i") 0 = iv (σ.vars "i")›
    all_goals have e2 := ‹(σ.arrs "sg").getD (σ.vars "i") 0 = sv (σ.vars "i")›
    all_goals have e3 := ‹(σ.arrs "cl").getD (σ.vars "i") 0 = cv (σ.vars "i")›
    all_goals have em := ‹σ.vars "m" = m›
    all_goals obtain ⟨v1, v2, v3, v4⟩ := hval _ hi
    all_goals have hc := hcell _ hi
    all_goals unfold cell at hc
    all_goals obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := ‹FInv K m Lact iv sv cv σ›
    · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
        simp only [Env.setVar, Env.setArr, e1, e2, e3, em] <;> try simp
      any_goals assumption
      intro t ht
      rw [pre_succ, ← h11 t ht, List.getElem?_set]
      unfold cell
      by_cases hct : (2 * iv (σ.vars "i") + 1 - sv (σ.vars "i")) * m + cv (σ.vars "i") = t
      · simp [hct, h10, ht]
      · simp [hct, List.getD_eq_getElem?_getD]
    all_goals simp only [Env.setVar, e1, e2, e3, em]
    all_goals try simp
    all_goals omega
  · rintro σ ⟨hI, hi⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hI
    exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩, hi, by omega, by omega, by omega,
      h7 _ hi, h8 _ hi, h9 _ hi, h1, by rw [h10]; exact hcell _ hi⟩

theorem fillLoop_spec (hcell : ∀ i < K, cell m iv sv cv i < Lact)
    (hval : ∀ i < K, 2 * iv i + 1 < B ∧ sv i < B ∧ cv i < B ∧ (2 * iv i + 1 - sv i) * m < B)
    (hB : Lact + 2 < B) (hK : K + 1 < B) (hm : m < B) :
    Spec B (fun σ => FInv K m Lact iv sv cv (σ.setVar "i" 0)) fillLoop
      (fun _ σ' => FInv K m Lact iv sv cv σ' ∧ σ'.vars "i" = K) (44 * K + 6) :=
  Spec.forRangeZero "i" "k" (FInv K m Lact iv sv cv) K 40 (by omega)
    (fun _ h => h.2.2.1) (fun _ h => h.2.1) (fillBody_spec K m Lact iv sv cv hcell hval hB hK hm)

end Lax391470Proofs.L2Fill
