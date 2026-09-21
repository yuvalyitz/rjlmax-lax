import Lax391470Proofs.L2Model

/-!
List and encoding lemmas for the output of Lemma 1's reduction.
-/

namespace Lax391470Proofs.L1Lists

open Lax391470.BinaryEncoding Lax391470Proofs.Bits Lax391470Proofs.L2Model

/-- The zeros and ones of the integer `a - b`. -/
def intBits (a b : ℕ) : List ℕ :=
  [if a < b then 1 else 0] ++ bitsNat (if a < b then b - a else a - b)

lemma natBits_encodeInt (a b : ℕ) : natBits (encodeInt ((a : ℤ) - b)) = intBits a b := by
  unfold encodeInt intBits
  rw [show (decide ((a : ℤ) - b < 0) :: encodeNat ((a : ℤ) - b).natAbs) =
    [decide ((a : ℤ) - b < 0)] ++ encodeNat ((a : ℤ) - b).natAbs from rfl, natBits_append,
    natBits_encodeNat, natBits_singleton]
  by_cases h : a < b
  · have h1 : (a : ℤ) - b < 0 := by omega
    have h2 : ((a : ℤ) - b).natAbs = b - a := by omega
    simp [h, h1, h2]
  · have h1 : ¬ (a : ℤ) - b < 0 := by omega
    have h2 : ((a : ℤ) - b).natAbs = a - b := by omega
    simp [h, h1, h2]

/-- A list of `5 N` records, regrouped five at a time. -/
lemma flatMap_range_five {α : Type} (f : ℕ → List α) (N : ℕ) :
    (List.range (5 * N)).flatMap f =
      (List.range N).flatMap fun i =>
        f (5 * i) ++ f (5 * i + 1) ++ f (5 * i + 2) ++ f (5 * i + 3) ++ f (5 * i + 4) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 5 * (N + 1) = 5 * N + 1 + 1 + 1 + 1 + 1 by ring]
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    rw [ih]
    simp [List.append_assoc]

lemma flatMap_range_add {α : Type} (f : ℕ → List α) (a b : ℕ) :
    (List.range (a + b)).flatMap f =
      (List.range a).flatMap f ++ (List.range b).flatMap fun k => f (a + k) := by
  rw [List.range_add, List.flatMap_append, List.flatMap_map]

end Lax391470Proofs.L1Lists
