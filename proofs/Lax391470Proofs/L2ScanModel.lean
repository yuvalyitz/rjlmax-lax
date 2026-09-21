import Lax391470Proofs.CnfScan
import Lax391470Proofs.Bits

/-!
What the scan has collected, in the flat form a machine keeps it in: the literals in
order, the number of the clause of each, and one more than the largest index.
-/

namespace Lax391470Proofs.L2ScanModel

open Lax429075.CNF Lax434930.PolynomialTime Lax391470Proofs.CnfScan

/-- The literals of a list of clauses, in order. -/
def lits (d : List Clause) : List Literal := d.flatMap id

/-- The clause number of each of those literals. -/
def cn (d : List Clause) : List ℕ :=
  (List.range d.length).flatMap fun j => List.replicate (d.getD j []).length j

/-- One more than the largest index, and `1` for no literal. -/
def mxOf (l : List Literal) : ℕ := l.foldr (fun l n => max (l.index + 1) n) 1

lemma lits_append (d : List Clause) (c : Clause) : lits (d ++ [c]) = lits d ++ c := by
  simp [lits]

lemma cn_append (d : List Clause) (c : Clause) :
    cn (d ++ [c]) = cn d ++ List.replicate c.length d.length := by
  unfold cn
  rw [List.length_append, List.length_singleton, List.range_succ, List.flatMap_append]
  congr 1
  · refine List.flatMap_congr fun j hj => ?_
    have : j < d.length := List.mem_range.mp hj
    rw [List.getD_append _ _ _ _ this]
  · simp

lemma cn_length (d : List Clause) : (cn d).length = (lits d).length := by
  induction d using List.reverseRecOn with
  | nil => rfl
  | append_singleton d c ih => rw [cn_append, lits_append]; simp [ih]

lemma mxOf_append (l : List Literal) (x : Literal) :
    mxOf (l ++ [x]) = max (mxOf l) (x.index + 1) := by
  induction l with
  | nil => simp [mxOf]
  | cons a t ih =>
    simp only [mxOf, List.cons_append, List.foldr_cons] at ih ⊢
    rw [ih]; omega

lemma mxOf_pos (l : List Literal) : 1 ≤ mxOf l := by
  induction l with
  | nil => simp [mxOf]
  | cons a t ih => simp only [mxOf, List.foldr_cons]; omega

/-- The literals read so far. -/
def flat (s : St) : List Literal := lits s.done ++ s.cur

/-- Their clause numbers. -/
def nums (s : St) : List ℕ := cn s.done ++ List.replicate s.cur.length s.done.length

/-- Everything the scan counts is bounded by the number of bits it has read. -/
def size (s : St) : ℕ := max (max s.n (flat s).length) (max s.done.length (mxOf (flat s) - 1))

lemma size_step (s : St) (b : Bool) : size (step s b) ≤ size s + 1 := by
  obtain ⟨ph, n, d, c⟩ := s
  match ph with
  | 0 => cases b <;> simp [step, size, flat]
  | 1 => cases b <;> simp [step, size, flat, lits_append] <;> omega
  | 2 => cases b <;> simp [step, size, flat]; omega
  | 3 =>
    have := mxOf_pos (lits d ++ c)
    simp only [step, size, flat, ← List.append_assoc, mxOf_append, List.length_append,
      List.length_singleton]
    omega
  | k + 4 => simp [step, size, flat]

lemma size_run (w : Word) : size (run init w) ≤ w.length := by
  induction w using List.reverseRecOn with
  | nil => simp [size, init, flat, lits, mxOf]
  | append_singleton u b ih =>
      rw [run_append]; simp only [run_cons, run_nil, List.length_append, List.length_singleton]
      exact le_trans (size_step _ _) (by omega)

end Lax391470Proofs.L2ScanModel
