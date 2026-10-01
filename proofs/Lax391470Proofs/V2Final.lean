import Lax391470Proofs.V2Main
import Lax391470Proofs.RamBridge2
import Lax391470Proofs.RamDecider
import Lax391470Proofs.L2Final
import Lax391470.Lemma2

/-!
The auxiliary problem belongs to NP: the verifier is a polynomial-time word RAM
program, hence a polynomial-time Turing machine.
-/

namespace Lax391470Proofs.V2Final

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax391470Proofs.Bits Lax391470Proofs.V2Main Lax391470Proofs.V2Dec
open Lax391470Proofs.L2Ram Lax391470Proofs.L2Final

variable (p q : ℕ)

open Classical in
/-- The answer of the verifier. -/
noncomputable def ans (z : List ℕ) : List ℕ := [if Dec p q z then 1 else 0]

def layout : Layout :=
  ⟨["L", "rt", "rv", "Ln", "st", "nx", "nw", "p", "c", "ph", "val", "pw", "i", "T", "kind", "tv",
    "j", "n3", "n34", "okx", "g", "ok", "nn", "N", "b3", "bS", "nN", "nj", "e0", "e1", "e2", "e3",
    "f0", "f2", "fj", "R", "D", "lg", "Tt", "P", "Ee", "tL", "tS", "EL", "ES", "vi", "vj", "x1",
    "y1", "u1", "v1"],
   ["a", "w", "TK", "TT", "PP"], 12⟩

theorem com_ok : Com.Ok layout (main p q) := by
  simp [main, front, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, V1Parts.initU,
    VUnpair.uLoop, VUnpair.uBody, TokRun.tokRun, TokRun.reset, V2Nk.nkB, V2Parts.bcheck,
    V1Parts.gate, TokLoop.scanLoop, TokLoop.scanBody, TokLoop.readBit, TokProg.dispatch,
    TokProg.put, TokProg.reset, TokProg.startDigits, TokProg.digit, V2Accept.acceptPart,
    V2Accept.setA, V2Accept.setB, L1Check.checkLoop, L1Check.checkBody, L1Check.load,
    L1Check.load2, L1Check.chk, V2Ord.ordLoop, V2Ord.ordBody, V2Ord.loadO, V2Ord.setLen,
    V2Ord.checks2, V1Front.stores, V2Pair.pairLoop, V2Pair.pairBody, V2Pair.loadP2,
    V2Pair.checksP, V2Pair.early, V2Pair.stores4, VPairs.pairsLoop, VPairs.outerBody,
    VPairs.innerLoop, VPairs.innerBody, VPairs.loadIJ, VPairs.ovl, layout, Com.Ok, Cond.Ok,
    condExpr, Expr.Ok]

/-- The value bound of an input. -/
def Bd (z : List ℕ) : ℕ :=
  (z.length + 16) * 2 ^ (z.length + 1) + 10 * z.length + p + q + 64 + Mx z

theorem solves : Solves layout (main p q) Shape (fun x => ans p q x.tail)
    (fun x => Bd p q x.tail) (fun x => Kmain x.tail.length) where
  ok := com_ok p q
  inp := by
    intro x hx v hv
    rw [shape_eq hx] at hv
    have hpow : x.tail.length < 2 ^ (x.tail.length + 1) :=
      lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by omega) (by omega))
    have hmul : 2 ^ (x.tail.length + 1) ≤ (x.tail.length + 16) * 2 ^ (x.tail.length + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    rcases List.mem_cons.mp hv with rfl | hv'
    · unfold Bd; omega
    · have := le_Mx hv'; unfold Bd; omega
  run := by
    intro x hx
    obtain ⟨σ', hrun, hout⟩ := main_spec (B := Bd p q x.tail) p q x.tail
      (fun v hv => by have := le_Mx hv; unfold Bd; omega) (by unfold Bd; omega)
    rw [← shape_eq hx] at hrun
    exact ⟨_, σ', hrun, hout⟩

def prog : Program := compileProgram layout (main p q)

theorem prog_runs (w : ℕ) (x : List ℕ) (hfit : 65 + 5 * Bd p q x ≤ 2 ^ w) :
    ∃ t ≤ 10 * Kmain x.length + 1,
      RunsTo w (prog p q) (x.length :: x) (ans p q x) t := by
  have hs : Solves layout (main p q) {z | z = x.length :: x} (fun z => ans p q z.tail)
      (fun z => Bd p q z.tail) (fun z => Kmain z.tail.length) :=
    ⟨(solves p q).ok, fun z hz => (solves p q).inp z (by rw [hz]; exact ⟨by simp, by simp⟩),
      fun z hz => (solves p q).run z (by rw [hz]; exact ⟨by simp, by simp⟩)⟩
  have h := computesInTime_of_solves (w := w)
    (T := fun z => 10 * Kmain z.tail.length + 1) hs
    (fun z hz => by
      rw [hz]; simp only [List.tail_cons]
      have hB : 64 ≤ Bd p q x := by unfold Bd; omega
      refine fitsWords_of_max_le (by omega) ?_
      simp only [Layout.span, layout, List.length_cons, List.length_nil, max_le_iff]
      omega)
    (fun z hz => by simp [Layout.const])
  obtain ⟨t, ht, hrun⟩ := h (x.length :: x) rfl
  exact ⟨t, by simpa using ht, by simpa [prog] using hrun⟩

/-! ### Word Length and Running Time -/

open Lax759944.BinaryWordEncoding Lax759944.RamPolytime Lax391470Proofs.BitSize

/-- The number of extra bits a word needs beyond twice the bit size of the input. -/
def Kx : ℕ := (5 * (p + q + 110) + 65).size

lemma Bd_lt (x : List ℕ) : 65 + 5 * Bd p q x < 2 ^ (2 * bitSize x + Kx p q) := by
  have hlen := length_le_bitSize x
  obtain ⟨S, hS⟩ : ∃ S, S = 2 ^ bitSize x := ⟨_, rfl⟩
  have hP : 2 ^ x.length ≤ S := by rw [hS]; exact Nat.pow_le_pow_right (by omega) hlen
  have hl : x.length < 2 ^ x.length := Nat.lt_two_pow_self
  have hM : Mx x < 2 * S := by
    have hp1 : (2 : ℕ) ^ (bitSize x + 1) = 2 * 2 ^ bitSize x := by ring
    rw [hS, ← hp1]
    rcases Mx_mem_or_zero x with hm | hm
    · exact mem_lt_two_pow_bitSize_add_one hm
    · rw [hm]; exact Nat.pos_of_ne_zero (by positivity)
  have hS1 : 1 ≤ S := by rw [hS]; exact Nat.one_le_two_pow
  have hSS : S ≤ S * S := Nat.le_mul_of_pos_left _ (by omega)
  have hp2 : (2 : ℕ) ^ (x.length + 1) = 2 * 2 ^ x.length := by ring
  have h1 : (x.length + 16) * 2 ^ (x.length + 1) ≤ (17 * S) * (2 * S) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e1 : (17 * S) * (2 * S) = 34 * (S * S) := by ring
  have hpq : p + q ≤ (p + q) * (S * S) := Nat.le_mul_of_pos_right _ (by omega)
  have hc : 5 * (p + q + 110) + 65 < 2 ^ Kx p q := Nat.lt_size_self _
  have hle : 65 + 5 * Bd p q x ≤ (5 * (p + q + 110) + 65) * (S * S) := by
    have e4 : (5 * (p + q + 110) + 65) * (S * S) = 5 * ((p + q) * (S * S)) + 615 * (S * S) := by
      ring
    unfold Bd
    rw [e4]; omega
  calc 65 + 5 * Bd p q x ≤ (5 * (p + q + 110) + 65) * (S * S) := hle
    _ < 2 ^ Kx p q * (S * S) := Nat.mul_lt_mul_of_pos_right hc (by omega)
    _ = 2 ^ (2 * bitSize x + Kx p q) := by rw [hS]; ring

lemma Kmain_eq (l : ℕ) : Kmain l = 422 + 898 * l + 666 * (l * l) := by
  unfold Kmain Kfront V2Accept.Kacc; ring

lemma Kmain_le (x : List ℕ) : 10 * Kmain x.length + 1 ≤ 8980 * (bitSize x + 1) ^ 2 := by
  have hlen := length_le_bitSize x
  have hprod : x.length * x.length ≤ bitSize x * bitSize x := Nat.mul_le_mul hlen hlen
  have e : (bitSize x + 1) ^ 2 = bitSize x * bitSize x + 2 * bitSize x + 1 := by ring
  rw [Kmain_eq, e]
  omega

/-- **The verifier is polynomial-time on a word RAM.** -/
theorem ramPolytime_ans : RamPolytime (ans p q) := by
  refine Lax391470Proofs.RamBridge2.ramPolytime_of_wordlen (d := 2) (K := Kx p q)
    (prog := prog p q)
    (Polynomial.C 8980 * (Polynomial.X + Polynomial.C 1) ^ 2) (by omega) ?_ ?_
  · intro x v hv
    have h1 : v ≤ 1 := by
      unfold ans at hv
      rw [List.mem_singleton] at hv
      rw [hv]; split <;> omega
    have hK : 1 ≤ Kx p q := by
      unfold Kx; exact Nat.size_pos.mpr (by omega)
    have h2 : 2 ≤ 2 ^ (2 * bitSize x + Kx p q) :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by omega)
        (show 1 ≤ 2 * bitSize x + Kx p q by omega))
    omega
  · intro w x hw
    have hfit : 65 + 5 * Bd p q x ≤ 2 ^ w :=
      le_trans (Bd_lt p q x).le (Nat.pow_le_pow_right (by omega) (by omega))
    obtain ⟨t, ht, hrun⟩ := prog_runs p q w x hfit
    refine ⟨t, ?_, hrun⟩
    have := Kmain_le x
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]
    omega

open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime
open Lax434930.Certificates Lax391470.BinaryEncoding

/-- The language of the verifier. -/
def V : Language := {w | Dec p q (natBits w)}

open Classical in
theorem V_mem_P : V p q ∈ P :=
  RamDecider.mem_P_of_ram (V := V p q) (fun w => decide (Dec p q (natBits w)))
    (fun w => by simp [V]) (ramPolytime_ans p q) (fun w => by
      unfold ans
      by_cases h : Dec p q (natBits w) <;> simp [h])

/--
---
conclusion: Lax391470.Lemma2.aux_mem_NP
---
A certificate is a schedule of the underlying instance: one start time for every ordinary
job, every long pending job and every short pending job, in the code of the instance. All
times of the auxiliary problem are natural numbers, and a job starts before its deadline,
so a solution takes at most quadratically more room than the instance. The verifier is a
word RAM program: it takes the pair of instance and certificate apart, reads both with a
one-pass tokenizer — once up to the end of the instance, to see that the instance is
complete, and once to the end — checks the conditions on the deadlines of the pending
jobs, checks every job against its availability interval, checks that in every connected
pair one job meets its early deadline, and compares all pairs of jobs for overlap.
Polynomial time on the word RAM transfers to a Turing machine.
-/
theorem aux_mem_NP (p q : ℕ) : AUX p q ∈ NP := by
  refine ⟨V p q, V_mem_P p q, Polynomial.X * (Polynomial.X + Polynomial.C 2),
    fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨y, hy, hd⟩ := dec_complete (p := p) (q := q) h
    exact ⟨y, by simpa using hy, hd⟩
  · obtain ⟨y, -, hd⟩ := h
    exact dec_sound hd

end Lax391470Proofs.V2Final
