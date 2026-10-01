import Lax391470Proofs.L2Ram
import Lax391470Proofs.RamToTuring

/-!
Lemma 2's reduction is polynomial-time computable: on the word RAM, and hence on a Turing
machine.
-/

namespace Lax391470Proofs.L2Final

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax391470Proofs.L2Main Lax391470Proofs.L2Nums Lax391470Proofs.L2Ram Lax391470Proofs.Bits

variable (p q : ℕ)

/-! ### The Output Is Zeros and Ones -/

lemma bitsNat_le_one {n v : ℕ} (hv : v ∈ bitsNat n) : v ≤ 1 := by
  simp only [bitsNat, List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_range] at hv
  rcases hv with (⟨-, rfl⟩ | rfl) | ⟨i, -, rfl⟩
  · exact le_refl _
  · omega
  · unfold digit; omega

lemma red_le_one {y : List ℕ} {v : ℕ} (hv : v ∈ L2Model.red p q y) : v ≤ 1 := by
  unfold L2Model.red at hv
  simp only at hv
  split_ifs at hv
  · simp only [L2Model.outBits, L2Model.ordBits, L2Model.pairBits, List.mem_append,
      List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with ((h | h) | ⟨o, -, (h | h) | h⟩) | ⟨i, -, ((h | h) | h) | h⟩
    all_goals first
      | exact bitsNat_le_one h
      | (rw [h]; split <;> omega)
  · simp only [L2Model.blockedBits, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hv
    rcases hv with (h | h) | (h | h) | h
    all_goals first
      | exact bitsNat_le_one h
      | omega

/-! ### The Machine Program -/

/-- The physical inputs: a word preceded by its length. -/
def Shape : Set (List ℕ) := {y | y ≠ [] ∧ y.headD 0 = y.tail.length}

lemma shape_eq {y : List ℕ} (h : y ∈ Shape) : y = y.tail.length :: y.tail := by
  obtain ⟨hne, hh⟩ := h
  rcases y with _ | ⟨a, t⟩
  · exact absurd rfl hne
  · simp only [List.headD_cons, List.tail_cons] at hh ⊢
    rw [hh]

lemma len_lt_Bd (y : List ℕ) : y.length + 8 < Bd p q y := by
  have hX : y.length + 4 ≤ (y.length + 4) * (y.length + 4) := Nat.le_mul_of_pos_left _ (by omega)
  have hU : (y.length + 4) * (y.length + 4) ≤ (p + q + 1) * ((y.length + 4) * (y.length + 4)) :=
    Nat.le_mul_of_pos_left _ (by omega)
  unfold Bd bnd; omega

theorem solves : Solves layout (main p q) Shape (fun x => L2Model.red p q x.tail)
    (fun x => Bd p q x.tail) (fun x => Kfull p q x.tail) where
  ok := com_ok p q
  inp := by
    intro x hx v hv
    rw [shape_eq hx] at hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · have := len_lt_Bd p q x.tail; omega
    · have := le_Mx hv'; unfold Bd bnd; omega
  run := by
    intro x hx
    obtain ⟨σ', hrun, hout⟩ := run_main p q x.tail
    rw [← shape_eq hx] at hrun
    exact ⟨_, σ', hrun, hout⟩

def prog : Program := compileProgram layout (main p q)

theorem prog_runs (w : ℕ) (x : List ℕ)
    (hfit : 56 + 12 * Bd p q x ≤ 2 ^ w) :
    ∃ t ≤ 10 * Kfull p q x + 1, RunsTo w (prog p q) (x.length :: x) (L2Model.red p q x) t := by
  have hs : Solves layout (main p q) {z | z = x.length :: x} (fun z => L2Model.red p q z.tail)
      (fun z => Bd p q z.tail) (fun z => Kfull p q z.tail) :=
    ⟨(solves p q).ok, fun z hz => (solves p q).inp z (by rw [hz]; exact ⟨by simp, by simp⟩),
      fun z hz => (solves p q).run z (by rw [hz]; exact ⟨by simp, by simp⟩)⟩
  have h := computesInTime_of_solves (w := w) (T := fun z => 10 * Kfull p q z.tail + 1) hs
    (fun z hz => by
      rw [hz]; simp only [List.tail_cons]
      have hB := len_lt_Bd p q x
      refine fitsWords_of_max_le (by omega) ?_
      simp only [Layout.span, layout, List.length_cons, List.length_nil, max_le_iff]
      omega)
    (fun z hz => by simp [Layout.const])
  obtain ⟨t, ht, hrun⟩ := h (x.length :: x) rfl
  exact ⟨t, by simpa using ht, by simpa [prog] using hrun⟩

/-! ### Fitting Into a Word -/

lemma Mx_mem_or_zero (y : List ℕ) : Mx y ∈ y ∨ Mx y = 0 := by
  induction y with
  | nil => right; rfl
  | cons a t ih =>
    simp only [Mx, List.foldr_cons] at ih ⊢
    rcases Nat.le_total a (List.foldr max 0 t) with h | h
    · rw [Nat.max_eq_right h]
      rcases ih with h' | h'
      · exact Or.inl (List.mem_cons_of_mem _ h')
      · right; exact h'
    · rw [Nat.max_eq_left h]; exact Or.inl List.mem_cons_self

/-- The constant of the fitting condition. -/
def cfit : ℕ := 768 * (p + q + 1) + 836

lemma fit_of (w : ℕ) (x : List ℕ)
    (h : ∀ v ∈ (x.length :: x), cfit p q * ((x.length + 1) + v + 1) ^ 2 ≤ 2 ^ w) :
    56 + 12 * Bd p q x ≤ 2 ^ w := by
  obtain ⟨v, hv, hT⟩ : ∃ v ∈ (x.length :: x), x.length + Mx x + 2 ≤ (x.length + 1) + v + 1 := by
    rcases Mx_mem_or_zero x with hm | hm
    · exact ⟨Mx x, List.mem_cons_of_mem _ hm, by omega⟩
    · exact ⟨x.length, List.mem_cons_self, by omega⟩
  have hpow := Nat.pow_le_pow_left hT 2
  have hc := Nat.mul_le_mul_left (cfit p q) hpow
  refine le_trans ?_ (le_trans hc (h v hv))
  set T := x.length + Mx x + 2 with hTdef
  have hW : x.length + 4 ≤ 2 * T := by omega
  have hWW : (x.length + 4) * (x.length + 4) ≤ 2 * T * (2 * T) := Nat.mul_le_mul hW hW
  have h4 : 2 * T * (2 * T) = 4 * (T * T) := by ring
  have hTT : T ≤ T * T := Nat.le_mul_of_pos_left _ (by omega)
  have hc0 := Nat.mul_le_mul_left (p + q + 1) (hWW.trans h4.le)
  have h5 : (p + q + 1) * (4 * (T * T)) = 4 * ((p + q + 1) * (T * T)) := by ring
  have h6 : cfit p q * T ^ 2 = 768 * ((p + q + 1) * (T * T)) + 836 * (T * T) := by
    unfold cfit; ring
  rw [h6]
  unfold Bd bnd
  omega

/-! ### The Running Time Is Polynomial in the Bit Size -/

open Lax759944.BinaryWordEncoding Lax759944.RamPolytime Lax391470Proofs.BitSize

/-- The scale of the time bound: a constant times the bit size. -/
def sc : ℕ := (16 * (p + q + 1)).size + 8

lemma Bd_size_le (x : List ℕ) : (Bd p q x).size ≤ sc p q * (bitSize x + 1) := by
  set N := bitSize x + 1 with hN
  set s1 := (16 * (p + q + 1)).size with hs1
  have hlen := length_le_bitSize x
  have hNpow : N < 2 ^ N := Nat.lt_two_pow_self
  have hW : x.length + 4 ≤ 2 ^ (N + 2) := by
    have : (2 : ℕ) ^ (N + 2) = 4 * 2 ^ N := by ring
    omega
  have hWW : (x.length + 4) * (x.length + 4) ≤ 2 ^ (2 * N + 4) := by
    have := Nat.mul_le_mul hW hW
    rwa [← Nat.pow_add, show N + 2 + (N + 2) = 2 * N + 4 by ring] at this
  have hc : 16 * (p + q + 1) < 2 ^ s1 := Nat.lt_size_self _
  have hM : Mx x < 2 ^ N := by
    rcases Mx_mem_or_zero x with hm | hm
    · exact mem_lt_two_pow_bitSize_add_one hm
    · rw [hm]; exact Nat.pos_of_ne_zero (by positivity)
  have hprod : 16 * (p + q + 1) * ((x.length + 4) * (x.length + 4)) ≤
      2 ^ s1 * 2 ^ (2 * N + 4) := Nat.mul_le_mul hc.le hWW
  rw [← Nat.pow_add] at hprod
  have h64 : (64 : ℕ) ≤ 2 ^ (s1 + (2 * N + 4)) := by
    calc (64 : ℕ) = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ (s1 + (2 * N + 4)) := Nat.pow_le_pow_right (by omega) (by omega)
  have hMle : 2 ^ N ≤ 2 ^ (s1 + (2 * N + 4)) := Nat.pow_le_pow_right (by omega) (by omega)
  have hlt : Bd p q x < 2 ^ (s1 + 2 * N + 6) := by
    have e : (2 : ℕ) ^ (s1 + 2 * N + 6) = 4 * 2 ^ (s1 + (2 * N + 4)) := by
      rw [show s1 + 2 * N + 6 = (s1 + (2 * N + 4)) + 2 by ring, Nat.pow_add]; ring
    have e2 : 16 * ((p + q + 1) * ((x.length + 4) * (x.length + 4))) =
        16 * (p + q + 1) * ((x.length + 4) * (x.length + 4)) := by ring
    unfold Bd bnd
    rw [e, e2]; omega
  have h1 := Nat.size_le.mpr hlt
  have h2 : s1 ≤ s1 * N := Nat.le_mul_of_pos_right _ (by omega)
  have h3 : sc p q * N = s1 * N + 8 * N := by unfold sc; ring
  omega

lemma Kfull_le (x : List ℕ) :
    10 * Kfull p q x + 1 ≤ 55701 * (sc p q * (bitSize x + 1)) ^ 3 := by
  set Z := sc p q * (bitSize x + 1) with hZ
  have hSz := Bd_size_le p q x
  rw [← hZ] at hSz
  have hlen := length_le_bitSize x
  have hs : 8 ≤ sc p q := by unfold sc; omega
  have hZN : 8 * (bitSize x + 1) ≤ Z := Nat.mul_le_mul_right _ hs
  have hWZ : x.length + 4 ≤ Z := by omega
  have hZ1 : 1 ≤ Z := by omega
  have hZZ : Z ≤ Z * Z := Nat.le_mul_of_pos_left _ (by omega)
  have hZZZ : Z * Z ≤ Z * Z * Z := Nat.le_mul_of_pos_right _ (by omega)
  have hWW : (x.length + 4) * (x.length + 4) ≤ Z * Z := Nat.mul_le_mul hWZ hWZ
  have t1 : (Bd p q x).size * (8 * (x.length + 4)) ≤ Z * (8 * Z) :=
    Nat.mul_le_mul hSz (by omega)
  have t2 : (Bd p q x).size * ((x.length + 4) + 2 * ((x.length + 4) * (x.length + 4))) ≤
      Z * (Z + 2 * (Z * Z)) := Nat.mul_le_mul hSz (by omega)
  have e1 : Z * (8 * Z) = 8 * (Z * Z) := by ring
  have e2 : Z * (Z + 2 * (Z * Z)) = Z * Z + 2 * (Z * Z * Z) := by ring
  have e3 : Z ^ 3 = Z * Z * Z := by ring
  unfold Kfull Kmain
  rw [L2Accept.Kacc_eq, e3]
  omega

/-- **The reduction, on zeros and ones, is polynomial-time on a word RAM.** -/
theorem ramPolytime_red : RamPolytime (L2Model.red p q) := by
  have hK : cfit p q * 4 ^ 2 ≤ 2 ^ (16 * cfit p q).size := by
    have := Nat.lt_size_self (16 * cfit p q)
    omega
  have hKpos : 1 ≤ (16 * cfit p q).size := by
    have : 0 < 16 * cfit p q := by unfold cfit; omega
    exact Nat.size_pos.mpr this
  refine Lax391470Proofs.RamBridge.ramPolytime_of_poly (c := cfit p q) (d := 2)
    (K := (16 * cfit p q).size) (prog := prog p q)
    (Polynomial.C 55701 * (Polynomial.C (sc p q) * (Polynomial.X + Polynomial.C 1)) ^ 3)
    (by omega) hK ?_ ?_
  · intro x v hv
    have h1 := red_le_one p q hv
    have h2 : 2 ≤ 2 ^ (2 * bitSize x + (16 * cfit p q).size) :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by omega)
        (show 1 ≤ 2 * bitSize x + (16 * cfit p q).size by omega))
    omega
  · intro w x hfits
    obtain ⟨t, ht, hrun⟩ := prog_runs p q w x (fit_of p q w x hfits)
    refine ⟨t, ?_, hrun⟩
    have := Kfull_le p q x
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]
    omega

open Lax434930.PolynomialTime in
/--
---
conclusion: Lax391470.Lemma2.reduce_polyTime
---
The reduction is a word RAM program on the zeros and ones of its input: a finite-state scan
decodes the formula, the numbers of the constructed instance are computed into arrays, and
a printer writes their binary codes. Polynomial time on the word RAM transfers to a Turing
machine.
-/
theorem reduce_polyTime (p q : ℕ) :
    Nonempty (Turing.TM2ComputableInPolyTime id id (Lax391470.Lemma2.reduce p q)) :=
  RamToTuring.polyTime_of_ram (ramPolytime_red p q) (L2Model.red_natBits p q)

end Lax391470Proofs.L2Final
