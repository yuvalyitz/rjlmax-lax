import Lax391470Proofs.RamToTuring
import Lax434930.PolynomialTime

/-!
A language decided by a polynomial-time word RAM program, on the zeros and ones of its
input and with a one-bit answer, belongs to P.
-/

namespace Lax391470Proofs.RamDecider

open Turing Lax434930.PolynomialTime Lax759944.RamPolytime Lax391470Proofs.Bits

theorem mem_P_of_ram {V : Language} (f : Word → Bool) (hf : ∀ w, f w = true ↔ w ∈ V)
    {g : List ℕ → List ℕ} (hg : RamPolytime g)
    (h : ∀ w, g (natBits w) = [if f w then 1 else 0]) : V ∈ P := by
  obtain ⟨c⟩ := RamToTuring.polyTime_of_ram (f := fun w => [f w]) hg (fun w => by
    rw [h w]; cases f w <;> rfl)
  refine ⟨f, hf, ⟨?_⟩⟩
  exact
    { tm := c.tm
      inputAlphabet := c.inputAlphabet
      outputAlphabet := c.outputAlphabet
      time := c.time
      outputsFun := fun w => c.outputsFun w }

end Lax391470Proofs.RamDecider
