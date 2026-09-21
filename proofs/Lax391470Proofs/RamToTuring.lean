import Lax391470Proofs.TMCompose
import Lax391470Proofs.TMToNats
import Lax391470Proofs.TMToBits

/-!
A map on binary words that a word RAM computes in polynomial time, on the zeros and ones
of its input, is polynomial-time computable on a Turing machine.
-/

namespace Lax391470Proofs.RamToTuring

open Turing Lax434930.PolynomialTime Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax391470Proofs.Bits

theorem polyTime_of_ram {f : Word → Word} {g : List ℕ → List ℕ} (hg : RamPolytime g)
    (h : ∀ w, g (natBits w) = natBits (f w)) :
    Nonempty (TM2ComputableInPolyTime id id f) := by
  obtain ⟨t1⟩ := Lax391470Proofs.TMToNats.toNats
  obtain ⟨t2⟩ :=
    (Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime g).mp hg
  obtain ⟨t3⟩ := Lax391470Proofs.TMToBits.toBits
  obtain ⟨c12⟩ := Lax391470Proofs.TMCompose.comp t1 t2
  obtain ⟨c⟩ := Lax391470Proofs.TMCompose.comp c12 t3
  refine ⟨{ tm := c.tm, inputAlphabet := c.inputAlphabet, outputAlphabet := c.outputAlphabet,
            time := c.time, outputsFun := fun w => ?_ }⟩
  have hc := c.outputsFun w
  simp only [Function.comp_apply, h, bitsOf_natBits] at hc
  exact hc

end Lax391470Proofs.RamToTuring
