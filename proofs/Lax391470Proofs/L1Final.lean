import Lax391470Proofs.L1Main
import Lax391470Proofs.RamBridge2
import Lax391470Proofs.RamToTuring
import Lax391470Proofs.L2Final

/-!
Lemma 1's reduction is polynomial-time computable: on the word RAM, and hence on a Turing
machine.
-/

namespace Lax391470Proofs.L1Final

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax391470Proofs.Bits Lax391470Proofs.L1Main

variable (p q : ℕ)

def layout : Layout :=
  ⟨["L", "rt", "rv", "Ln", "pw", "ph", "val", "i", "T", "p", "c", "kind", "j", "n3", "tv", "n",
    "N", "b3", "ok", "jobs", "e0", "e1", "e2", "e3", "f0", "f2", "v", "s", "u", "i2", "ix", "M"],
   ["a", "TK"], 12⟩

theorem com_ok : Com.Ok layout (main p q) := by
  simp [main, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, L1Parts.initS, AuxNk.nkA,
    TokLoop.scanLoop, TokLoop.scanBody, TokLoop.readBit, TokProg.dispatch, TokProg.put,
    TokProg.reset, TokProg.startDigits, TokProg.digit, L1Accept.acceptCom, L1Parts.setup1,
    L1Check.checkLoop, L1Check.checkBody, L1Check.load, L1Check.load2, L1Check.chk,
    L1Print.printPart, L1Print.rowLoop, L1Rows.ordRowCom, L1Rows.quadRowCom, L1Rows.ieOrd,
    L1Rows.ieQuad, OutSteps.emitTK, OutSteps.emitSel, OutSteps.selLen, OutSteps.emitInt,
    L1Parts.rejectCom, L2Parts.emitVar, L2Parts.emitLit, L2Print.emitAt, EmitNat.emitNat,
    EmitNat.sizeLoop, EmitNat.sizeBody, EmitNat.onesLoop, EmitNat.onesBody, EmitNat.digLoop,
    EmitNat.digBody, layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

/-! ### The output is zeros and ones -/

open Lax391470Proofs.L1Lists Lax391470Proofs.L1Model

/-- Every entry is a bit. -/
def Bin (l : List ℕ) : Prop := ∀ v ∈ l, v ≤ 1

@[simp] lemma bin_append (a b : List ℕ) : Bin (a ++ b) ↔ Bin a ∧ Bin b := by
  unfold Bin; simp only [List.mem_append]
  exact ⟨fun h => ⟨fun v hv => h v (Or.inl hv), fun v hv => h v (Or.inr hv)⟩,
    fun h v hv => hv.elim (h.1 v) (h.2 v)⟩

@[simp] lemma bin_bitsNat (n : ℕ) : Bin (bitsNat n) := fun _ hv => L2Final.bitsNat_le_one hv

@[simp] lemma bin_cons (a : ℕ) (l : List ℕ) : Bin (a :: l) ↔ a ≤ 1 ∧ Bin l := by
  unfold Bin; simp

@[simp] lemma bin_nil : Bin [] := fun _ hv => by simp at hv

@[simp] lemma bin_intBits (a b : ℕ) : Bin (intBits a b) := by
  unfold intBits
  rw [bin_append]
  refine ⟨?_, bin_bitsNat _⟩
  rw [bin_cons]; exact ⟨by split <;> omega, bin_nil⟩

lemma bin_flatMap (l : List ℕ) (f : ℕ → List ℕ) (h : ∀ i, Bin (f i)) : Bin (l.flatMap f) := by
  intro v hv
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hv
  exact h i v hi

lemma red_le_one {y : List ℕ} {v : ℕ} (hv : v ∈ L1Red.red p q y) : v ≤ 1 := by
  have h1 : Bin (L1Red.blockedBits p) := by simp [L1Red.blockedBits]
  have h2 : ∀ tk, Bin (outBits p q tk) := fun tk => by
    unfold outBits
    rw [bin_append, bin_append]
    exact ⟨⟨bin_bitsNat _, bin_flatMap _ _ fun i => by simp [ordRow]⟩,
      bin_flatMap _ _ fun i => by simp [quadRow]⟩
  unfold L1Red.red at hv
  split_ifs at hv
  · exact h2 _ v hv
  · exact h1 v hv

/-! ### The machine program -/

open Lax391470Proofs.L2Ram Lax391470Proofs.L2Final

/-- The value bound of an input. -/
def Bd (y : List ℕ) : ℕ :=
  16 * 2 ^ y.length + (p + 2 * q) * (y.length + 2) + 4 * y.length + p + 64 + Mx y

theorem solves : Solves layout (main p q) Shape (fun x => L1Red.red p q x.tail)
    (fun x => Bd p q x.tail) (fun x => Kmain x.tail.length (Bd p q x.tail).size) where
  ok := com_ok p q
  inp := by
    intro x hx v hv
    rw [shape_eq hx] at hv
    have hpow : x.tail.length < 2 ^ x.tail.length := Nat.lt_two_pow_self
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

theorem prog_runs (w : ℕ) (x : List ℕ) (hfit : 46 + 2 * Bd p q x ≤ 2 ^ w) :
    ∃ t ≤ 10 * Kmain x.length (Bd p q x).size + 1,
      RunsTo w (prog p q) (x.length :: x) (L1Red.red p q x) t := by
  have hs : Solves layout (main p q) {z | z = x.length :: x} (fun z => L1Red.red p q z.tail)
      (fun z => Bd p q z.tail) (fun z => Kmain z.tail.length (Bd p q z.tail).size) :=
    ⟨(solves p q).ok, fun z hz => (solves p q).inp z (by rw [hz]; exact ⟨by simp, by simp⟩),
      fun z hz => (solves p q).run z (by rw [hz]; exact ⟨by simp, by simp⟩)⟩
  have h := computesInTime_of_solves (w := w)
    (T := fun z => 10 * Kmain z.tail.length (Bd p q z.tail).size + 1) hs
    (fun z hz => by
      rw [hz]; simp only [List.tail_cons]
      have hB : 64 ≤ Bd p q x := by unfold Bd; omega
      refine fitsWords_of_max_le (by omega) ?_
      simp only [Layout.span, layout, List.length_cons, List.length_nil, max_le_iff]
      omega)
    (fun z hz => by simp [Layout.const])
  obtain ⟨t, ht, hrun⟩ := h (x.length :: x) rfl
  exact ⟨t, by simpa using ht, by simpa [prog] using hrun⟩

/-! ### Word length and running time -/

open Lax759944.BinaryWordEncoding Lax759944.RamPolytime Lax391470Proofs.BitSize

/-- The number of extra bits a word needs beyond the bit size of the input. -/
def Kx : ℕ := (2 * (86 + 3 * p + 4 * q) + 46).size

lemma Bd_lt (x : List ℕ) : 46 + 2 * Bd p q x < 2 ^ (bitSize x + Kx p q) := by
  have hlen := length_le_bitSize x
  have hP : 2 ^ x.length ≤ 2 ^ bitSize x := Nat.pow_le_pow_right (by omega) hlen
  have hl : x.length < 2 ^ x.length := Nat.lt_two_pow_self
  have hM : Mx x < 2 ^ (bitSize x + 1) := by
    rcases Mx_mem_or_zero x with hm | hm
    · exact mem_lt_two_pow_bitSize_add_one hm
    · rw [hm]; exact Nat.pos_of_ne_zero (by positivity)
  have hp1 : (2 : ℕ) ^ (bitSize x + 1) = 2 * 2 ^ bitSize x := by ring
  have hmul : (p + 2 * q) * (x.length + 2) ≤ (p + 2 * q) * (2 * 2 ^ bitSize x) :=
    Nat.mul_le_mul_left _ (by omega)
  have hone : 1 ≤ 2 ^ bitSize x := Nat.one_le_two_pow
  have hp64 : p + 64 ≤ (p + 64) * 2 ^ bitSize x := Nat.le_mul_of_pos_right _ (by omega)
  have hc : 2 * (86 + 3 * p + 4 * q) + 46 < 2 ^ Kx p q := Nat.lt_size_self _
  have e1 : (p + 2 * q) * (2 * 2 ^ bitSize x) = (2 * p + 4 * q) * 2 ^ bitSize x := by ring
  have e2 : (p + 64) * 2 ^ bitSize x = p * 2 ^ bitSize x + 64 * 2 ^ bitSize x := by ring
  have e3 : (2 * p + 4 * q) * 2 ^ bitSize x = 2 * (p * 2 ^ bitSize x) + 4 * (q * 2 ^ bitSize x) := by
    ring
  have hle : 46 + 2 * Bd p q x ≤ (2 * (86 + 3 * p + 4 * q) + 46) * 2 ^ bitSize x := by
    have e4 : (2 * (86 + 3 * p + 4 * q) + 46) * 2 ^ bitSize x =
        218 * 2 ^ bitSize x + 6 * (p * 2 ^ bitSize x) + 8 * (q * 2 ^ bitSize x) := by ring
    unfold Bd
    rw [e4]; omega
  calc 46 + 2 * Bd p q x ≤ (2 * (86 + 3 * p + 4 * q) + 46) * 2 ^ bitSize x := hle
    _ < 2 ^ Kx p q * 2 ^ bitSize x := Nat.mul_lt_mul_of_pos_right hc (by omega)
    _ = 2 ^ (bitSize x + Kx p q) := by rw [← Nat.pow_add, Nat.add_comm]

lemma Kmain_eq (l Sz : ℕ) : Kmain l Sz = 402 + 2078 * l + 240 * Sz + 1056 * (Sz * l) := by
  unfold Kmain L1Accept.Kacc1 L1Print.Kprint; ring

lemma Kmain_le (x : List ℕ) :
    10 * Kmain x.length (Bd p q x).size + 1 ≤ 37761 * ((Kx p q + 1) * (bitSize x + 1)) ^ 2 := by
  set Z := (Kx p q + 1) * (bitSize x + 1) with hZ
  have hlen := length_le_bitSize x
  have hSz : (Bd p q x).size ≤ bitSize x + Kx p q :=
    Nat.size_le.mpr (by have := Bd_lt p q x; omega)
  have hZe : Z = Kx p q * bitSize x + Kx p q + bitSize x + 1 := by rw [hZ]; ring
  have hSzZ : (Bd p q x).size ≤ Z := by omega
  have hlZ : x.length ≤ Z := by omega
  have hZ1 : 1 ≤ Z := by omega
  have hZZ : Z ≤ Z * Z := Nat.le_mul_of_pos_left _ (by omega)
  have hprod : (Bd p q x).size * x.length ≤ Z * Z := Nat.mul_le_mul hSzZ hlZ
  have e : Z ^ 2 = Z * Z := by ring
  rw [Kmain_eq, e]
  omega

/-- **The reduction, on zeros and ones, is polynomial-time on a word RAM.** -/
theorem ramPolytime_red : RamPolytime (L1Red.red p q) := by
  refine Lax391470Proofs.RamBridge2.ramPolytime_of_wordlen (d := 1) (K := Kx p q)
    (prog := prog p q)
    (Polynomial.C 37761 * (Polynomial.C (Kx p q + 1) * (Polynomial.X + Polynomial.C 1)) ^ 2)
    (by omega) ?_ ?_
  · intro x v hv
    have h1 := red_le_one p q hv
    have hK : 1 ≤ Kx p q := by
      unfold Kx; exact Nat.size_pos.mpr (by omega)
    have h2 : 2 ≤ 2 ^ (1 * bitSize x + Kx p q) :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by omega)
        (show 1 ≤ 1 * bitSize x + Kx p q by omega))
    omega
  · intro w x hw
    have hfit : 46 + 2 * Bd p q x ≤ 2 ^ w :=
      le_trans (Bd_lt p q x).le (Nat.pow_le_pow_right (by omega) (by omega))
    obtain ⟨t, ht, hrun⟩ := prog_runs p q w x hfit
    refine ⟨t, ?_, hrun⟩
    have := Kmain_le p q x
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]
    omega

open Lax434930.PolynomialTime in
/--
---
conclusion: Lax391470.Lemma1.reduce_polyTime
---
The reduction is a word RAM program on the zeros and ones of its input: a one-pass
tokenizer decodes the instance of the auxiliary problem, a second pass checks the
conditions on its deadlines, and a printer writes the binary codes of the jobs of the
stacked instance, signs included. Decoded numbers may be exponential in the length of the
input, which the word length of a polynomial-time word RAM accommodates. Polynomial time
on the word RAM transfers to a Turing machine.
-/
theorem reduce_polyTime (p q : ℕ) :
    Nonempty (Turing.TM2ComputableInPolyTime id id (Lax391470.Lemma1.reduce p q)) :=
  RamToTuring.polyTime_of_ram (ramPolytime_red p q) (L1Red.red_natBits p q)

end Lax391470Proofs.L1Final
