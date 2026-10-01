import Lax391470Proofs.L1Ordered

/-!
What the verifier of `AUX p q` checks, on the values of the tokens, and what that means
for the instance and the schedule the tokens describe.
-/

namespace Lax391470Proofs.V2Sem

open Lax391470 Lax391470.Scheduling Lax391470.AuxiliaryProblem
open Lax391470Proofs.TokModel Lax391470Proofs.TokProg Lax391470Proofs.AuxFormat
open Lax391470Proofs.L1Model Lax391470Proofs.L1Ordered

variable (p q : ℕ) (tk : List ℕ)

/-- The position of the start time of job `j`. -/
abbrev iS (n N j : ℕ) : ℕ := 2 + (3 * n + 4 * N + j)

/-- The start time of job `j`. -/
def tOf (j : ℕ) : ℕ := tk.getD (iS (tk.getD 0 0) (tk.getD 1 0) j) 0

/-- The release time of job `j` of the underlying instance. -/
def rOf (j : ℕ) : ℕ := if j < tk.getD 0 0 then tk.getD (2 + (3 * j + 0)) 0 else 0

/-- The deadline of job `j` of the underlying instance. -/
def dOf (j : ℕ) : ℕ :=
  if j < tk.getD 0 0 then tk.getD (2 + (3 * j + 1)) 0
  else if j < tk.getD 0 0 + tk.getD 1 0 then ev tk (tk.getD 0 0) (j - tk.getD 0 0) 1
  else ev tk (tk.getD 0 0) (j - tk.getD 0 0 - tk.getD 1 0) 3

/-- The length of job `j` of the underlying instance. -/
def pOf (j : ℕ) : ℕ :=
  if j < tk.getD 0 0 then (if tk.getD (2 + (3 * j + 2)) 0 ≠ 0 then p else q)
  else if j < tk.getD 0 0 + tk.getD 1 0 then p
  else q

/-- Every job runs inside its interval. -/
def FE : Prop :=
  ∀ j < tk.getD 0 0 + 2 * tk.getD 1 0, rOf tk j ≤ tOf tk j ∧ tOf tk j + pOf p q tk j ≤ dOf tk j

/-- No two jobs overlap. -/
def OV : Prop :=
  ∀ i < tk.getD 0 0 + 2 * tk.getD 1 0, ∀ j < tk.getD 0 0 + 2 * tk.getD 1 0, i ≠ j →
    tOf tk i + pOf p q tk i ≤ tOf tk j ∨ tOf tk j + pOf p q tk j ≤ tOf tk i

/-- In every pair one job is early. -/
def EP : Prop :=
  ∀ i < tk.getD 1 0,
    tOf tk (tk.getD 0 0 + i) + p ≤ ev tk (tk.getD 0 0) i 0 ∨
    tOf tk (tk.getD 0 0 + tk.getD 1 0 + i) + q ≤ ev tk (tk.getD 0 0) i 2

/-- Everything the verifier checks. -/
def Sem : Prop := OrdOK tk ∧ FE p q tk ∧ OV p q tk ∧ EP p q tk

/-! ### The Token Values of an Instance, Followed by Anything -/

section
variable (A : AuxiliaryProblem.Instance) (rest : List ℕ)

lemma tkOf_length : (tkOf A).length = 2 + 3 * A.ordinary + 4 * A.pairs := by
  unfold tkOf; rw [List.length_map, toksOf_length]

lemma rd {k : ℕ} (hk : k < 2 + 3 * A.ordinary + 4 * A.pairs) :
    (tkOf A ++ rest).getD k 0 = (tkOf A).getD k 0 :=
  List.getD_append _ _ _ _ (by rw [tkOf_length]; exact hk)

lemma h0 : (tkOf A ++ rest).getD 0 0 = A.ordinary := by rw [rd A rest (by omega), tk_zero]
lemma h1 : (tkOf A ++ rest).getD 1 0 = A.pairs := by rw [rd A rest (by omega), tk_one]

lemma ev_app {i c : ℕ} (hi : i < A.pairs) (hc : c < 4) :
    ev (tkOf A ++ rest) A.ordinary i c = ev (tkOf A) A.ordinary i c := by
  unfold ev; exact rd A rest (by omega)

lemma ord_app : OrdOK (tkOf A ++ rest) ↔ OrdOK (tkOf A) := by
  unfold OrdOK PairOK
  rw [h0, h1, tk_zero, tk_one]
  refine forall₂_congr fun i hi => ?_
  rw [ev_app A rest hi (by omega), ev_app A rest hi (by omega), ev_app A rest hi (by omega),
    ev_app A rest hi (by omega)]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (imp_congr_right fun hi' => ?_)))
  rw [ev_app A rest hi' (by omega), ev_app A rest hi' (by omega)]

variable (j : Fin (A.toInstance p q).jobs)

lemma jlt : (j : ℕ) < A.ordinary + A.pairs + A.pairs := j.isLt

lemma rOf_eq : (rOf (tkOf A ++ rest) j : ℤ) = (A.toInstance p q).r j := by
  unfold rOf
  rw [h0]
  by_cases h : (j : ℕ) < A.ordinary
  · rw [if_pos h, rd A rest (by omega), tk_ord A j 0 h (by omega)]
    simp [Instance.toInstance, h, ordRec, Tok.val]
  · rw [if_neg h]; simp [Instance.toInstance, h]

lemma pOf_eq : pOf p q (tkOf A ++ rest) j = (A.toInstance p q).p j := by
  unfold pOf
  rw [h0, h1]
  by_cases h : (j : ℕ) < A.ordinary
  · rw [if_pos h, rd A rest (by omega), tk_ord A j 2 h (by omega)]
    simp only [Instance.toInstance, h, dif_pos, ordRec, List.getD_cons_succ, List.getD_cons_zero,
      Tok.val]
    cases A.long ⟨j, h⟩ <;> simp
  · rw [if_neg h]; simp [Instance.toInstance, h]

lemma dOf_eq : (dOf (tkOf A ++ rest) j : ℤ) = (A.toInstance p q).d j := by
  have hj := jlt p q A j
  unfold dOf
  rw [h0, h1]
  by_cases h : (j : ℕ) < A.ordinary
  · rw [if_pos h, rd A rest (by omega), tk_ord A j 1 h (by omega)]
    simp [Instance.toInstance, h, ordRec, Tok.val]
  · rw [if_neg h]
    by_cases h' : (j : ℕ) < A.ordinary + A.pairs
    · rw [if_pos h', ev_app A rest (by omega) (by omega), (ev_eq A _ (by omega)).2.1]
      simp [Instance.toInstance, h, h']
    · rw [if_neg h', ev_app A rest (by omega) (by omega), (ev_eq A _ (by omega)).2.2.2]
      simp [Instance.toInstance, h, h']

end

/-- **The verifier checks auxiliary-instance feasibility**: the token values of an instance, followed by
start times, pass exactly if the instance is ordered and the start times solve it. -/
theorem sem_iff (A : AuxiliaryProblem.Instance) (rest : List ℕ) :
    Sem p q (tkOf A ++ rest) ↔
      A.Ordered ∧ A.Solves p q (fun j => (tOf (tkOf A ++ rest) j : ℤ)) := by
  unfold Sem FE OV EP Instance.Solves Instance.Feasible
  rw [ord_app, ← ordered_iff, h0, h1]
  refine and_congr Iff.rfl ?_
  constructor
  · rintro ⟨hfe, hov, hep⟩
    refine ⟨⟨fun j => ?_, fun i j hij => ?_⟩, fun i => ?_⟩
    · have hj := jlt p q A j
      have := hfe j (by omega)
      rw [← rOf_eq p q A rest j, ← dOf_eq p q A rest j, ← pOf_eq p q A rest j]
      beta_reduce
      exact_mod_cast this
    · have hi := jlt p q A i
      have hj := jlt p q A j
      have := hov i (by omega) j (by omega) (fun h => hij (Fin.ext h))
      rw [← pOf_eq p q A rest i, ← pOf_eq p q A rest j]
      beta_reduce
      exact_mod_cast this
    · have := hep i i.isLt
      rw [ev_app A rest i.isLt (by omega), ev_app A rest i.isLt (by omega),
        (ev_eq A i i.isLt).1, (ev_eq A i i.isLt).2.2.1] at this
      simp only [Instance.longJob, Instance.shortJob]
      exact_mod_cast this
  · rintro ⟨⟨hfe, hov⟩, hep⟩
    refine ⟨fun j hj => ?_, fun i hi j hj hij => ?_, fun i hi => ?_⟩
    · have := hfe ⟨j, by show j < A.ordinary + A.pairs + A.pairs; omega⟩
      rw [← rOf_eq p q A rest, ← dOf_eq p q A rest, ← pOf_eq p q A rest] at this
      beta_reduce at this
      exact_mod_cast this
    · have := hov ⟨i, by show i < A.ordinary + A.pairs + A.pairs; omega⟩
        ⟨j, by show j < A.ordinary + A.pairs + A.pairs; omega⟩
        (fun h => hij (congrArg Fin.val h))
      rw [← pOf_eq p q A rest, ← pOf_eq p q A rest] at this
      beta_reduce at this
      exact_mod_cast this
    · have := hep ⟨i, hi⟩
      simp only [Instance.longJob, Instance.shortJob] at this
      rw [ev_app A rest hi (by omega), ev_app A rest hi (by omega),
        (ev_eq A i hi).1, (ev_eq A i hi).2.2.1]
      exact_mod_cast this

end Lax391470Proofs.V2Sem
