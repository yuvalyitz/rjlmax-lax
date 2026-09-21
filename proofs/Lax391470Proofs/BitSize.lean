import Lax759944.BinaryWordEncoding
import Mathlib.Data.Nat.Size

/-!
Bounds on the bit-size of a list of natural numbers, in the encoding of `lax-759944`: the
length of the list and every entry are below `2 ^ (bitSize + 1)`. The proofs are adapted
from `Lax759944Proofs.Encoding` (Szymon Toruńczyk, `lax-759944`).
-/

namespace Lax391470Proofs.BitSize

open Lax759944.BinaryWordEncoding

theorem bitSize_cons (a : ℕ) (x : List ℕ) :
    bitSize (a :: x) = a.bits.length + 1 + bitSize x := by
  simp [bitSize, encode, encodeNat, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem length_le_bitSize (x : List ℕ) : x.length ≤ bitSize x := by
  induction x with
  | nil => simp [bitSize, encode]
  | cons a x ih => rw [bitSize_cons]; simp only [List.length_cons]; omega

theorem bits_length_lt_bitSize {a : ℕ} {x : List ℕ} (ha : a ∈ x) :
    a.bits.length < bitSize x := by
  induction x with
  | nil => simp at ha
  | cons b x ih =>
    rw [bitSize_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · have := ih ha; omega

theorem mem_lt_two_pow_bitSize_add_one {a : ℕ} {x : List ℕ} (ha : a ∈ x) :
    a < 2 ^ (bitSize x + 1) := by
  have h : a < 2 ^ a.bits.length := by
    rw [Nat.size_eq_bits_len]; exact Nat.lt_size_self a
  exact h.trans_le (Nat.pow_le_pow_right (by omega) (by have := bits_length_lt_bitSize ha; omega))

theorem length_lt_two_pow_bitSize_add_one (x : List ℕ) :
    x.length < 2 ^ (bitSize x + 1) :=
  (length_le_bitSize x).trans_lt ((Nat.lt_two_pow_self).trans_le
    (Nat.pow_le_pow_right (by omega) (by omega)))

end Lax391470Proofs.BitSize
