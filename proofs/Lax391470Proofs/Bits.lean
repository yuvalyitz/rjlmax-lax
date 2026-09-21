import Lax391470.BinaryEncoding
import Mathlib.Data.Nat.Size
import Lax759944.TuringRamPolytimeEquivalence

/-!
Binary words as lists of zeros and ones, the form in which a word RAM is handed them.
-/

namespace Lax391470Proofs.Bits

open Lax434930.PolynomialTime Lax391470.BinaryEncoding

/-- A binary word as a list of zeros and ones. -/
def natBits (w : Word) : List ℕ := w.map fun b => if b then 1 else 0

/-- A list of numbers as a binary word: which entries are nonzero. -/
def bitsOf (l : List ℕ) : Word := l.map fun n => decide (n ≠ 0)

@[simp] lemma bitsOf_natBits (w : Word) : bitsOf (natBits w) = w := by
  induction w with
  | nil => rfl
  | cons b t ih =>
      simp only [natBits, bitsOf, List.map_cons, List.map_map] at ih ⊢
      rw [ih]; cases b <;> simp

/-- The `i`-th binary digit of `n`. -/
def digit (n i : ℕ) : ℕ := n / 2 ^ i % 2

/-- The self-delimiting code of a number, as zeros and ones. -/
def bitsNat (n : ℕ) : List ℕ :=
  List.replicate n.size 1 ++ [0] ++ (List.range n.size).map (digit n)

lemma bits_eq_digits (n : ℕ) :
    n.bits.map (fun b => if b then 1 else 0) = (List.range n.size).map (digit n) := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n h ih =>
      by_cases hz : Nat.bit b n = 0
      · rw [hz]; simp
      · rw [Nat.bits_append_bit n b h, Nat.size_bit hz, List.range_succ_eq_map, List.map_cons,
          List.map_cons, List.map_map, ih]
        congr 1
        · cases b <;> simp [digit, Nat.bit_val]
        · refine List.map_congr_left fun i _ => ?_
          simp only [Function.comp, digit, pow_succ]
          rw [Nat.mul_comm, ← Nat.div_div_eq_div_mul]
          congr 2
          cases b <;> simp [Nat.bit_val]; omega

lemma natBits_encodeNat (n : ℕ) : natBits (encodeNat n) = bitsNat n := by
  simp only [natBits, encodeNat, bitsNat, List.map_append, List.map_replicate, List.map_cons,
    List.map_nil]
  rw [bits_eq_digits, Nat.size_eq_bits_len]
  simp

end Lax391470Proofs.Bits
