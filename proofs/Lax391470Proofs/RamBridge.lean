import Lax808846.RamComputes
import Lax759944.RamPolytime
import Lax391470Proofs.BitSize

/-!
From a running-time statement in the archive's word RAM style to the polynomial-time
predicate of the RAM/Turing equivalence.

The two say the same thing in different currencies. `Lax808846` measures the input by
its length as a list of numbers and states an explicit bound at every word length that
admits the input; `Lax759944` measures it by its bit size, prefixes the physical input
with its length, and asks for a polynomial. This file converts one into the other once,
so that a program written and costed in the first style can be cited in the second.
-/

namespace Lax391470Proofs.RamBridge

open Lax808846.Ram Lax808846.RamComputes
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax391470Proofs.BitSize

lemma add_two_le_two_pow (s : ℕ) : s + 2 ≤ 2 ^ (s + 1) := by
  have h1 : s < 2 ^ s := Nat.lt_two_pow_self
  have h2 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  have h3 : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by ring
  omega

/-- **The bridge, for any polynomial running time.** The same change of currency with the
step count left as a polynomial in the bit size and the fitting condition raised to a
power `d`, which is what a program with nested loops — whose values and cost are
polynomial rather than linear in the length of its input — asks for. -/
theorem ramPolytime_of_poly {f : List ℕ → List ℕ} {prog : Program} {c d K : ℕ}
    (time : Polynomial ℕ)
    (hd : 1 ≤ d) (hK : c * 4 ^ d ≤ 2 ^ K)
    (hout : ∀ x, ∀ v ∈ f x, v < 2 ^ (d * bitSize x + K))
    (hrun : ∀ (w : ℕ) (x : List ℕ),
        (∀ v ∈ (x.length :: x), c * ((x.length + 1) + v + 1) ^ d ≤ 2 ^ w) →
        ∃ t ≤ time.eval (bitSize x), RunsTo w prog (x.length :: x) (f x) t) :
    RamPolytime f := by
  refine ⟨prog, Polynomial.C d * Polynomial.X + Polynomial.C (K + 1), time,
    fun x => ⟨?_, ?_⟩⟩
  · intro a ha
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    rcases List.mem_append.mp ha with hin | hin
    · have hlt : a < 2 ^ (bitSize x + 1) := by
        rcases List.mem_cons.mp hin with rfl | hin'
        · exact length_lt_two_pow_bitSize_add_one x
        · exact mem_lt_two_pow_bitSize_add_one hin'
      calc a < 2 ^ (bitSize x + 1) := hlt
        _ ≤ 2 ^ (d * bitSize x + (K + 1)) := Nat.pow_le_pow_right (by omega) (by
            have : bitSize x ≤ d * bitSize x := Nat.le_mul_of_pos_left _ hd
            omega)
    · calc a < 2 ^ (d * bitSize x + K) := hout x a hin
        _ ≤ 2 ^ (d * bitSize x + (K + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
  · intro w hw
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C] at hw
    refine hrun w x fun v hv => ?_
    have hvlt : v < 2 ^ (bitSize x + 1) := by
      rcases List.mem_cons.mp hv with rfl | hv'
      · exact length_lt_two_pow_bitSize_add_one x
      · exact mem_lt_two_pow_bitSize_add_one hv'
    have hlen := length_le_bitSize x
    have hs2 := add_two_le_two_pow (bitSize x)
    have hbase : x.length + 1 + v + 1 ≤ 4 * 2 ^ bitSize x := by
      have e1 : (2:ℕ) ^ (bitSize x + 1) = 2 * 2 ^ bitSize x := by ring
      omega
    calc c * (x.length + 1 + v + 1) ^ d
        ≤ c * (4 * 2 ^ bitSize x) ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase d)
      _ = c * 4 ^ d * 2 ^ (d * bitSize x) := by
          rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm (bitSize x) d, Nat.mul_assoc]
      _ ≤ 2 ^ K * 2 ^ (d * bitSize x) := Nat.mul_le_mul_right _ hK
      _ = 2 ^ (d * bitSize x + K) := by rw [← Nat.pow_add, Nat.add_comm]
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)

end Lax391470Proofs.RamBridge
