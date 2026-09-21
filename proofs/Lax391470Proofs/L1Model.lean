import Lax391470Proofs.L1Lists
import Lax391470Proofs.AuxFormat
import Lax391470Proofs.StackedNumbering
import Lax391470Proofs.TokProg

/-!
The zeros and ones of the stacked instance, in terms of the token values of the encoding
of the auxiliary instance: what the machine has to write.
-/

namespace Lax391470Proofs.L1Model

open Lax391470 Lax391470.BinaryEncoding Lax391470Proofs.Bits Lax391470Proofs.L2Model
open Lax391470Proofs.L1Lists Lax391470Proofs.TokModel Lax391470Proofs.AuxFormat
open Lax391470Proofs.TokProg

variable (p q : ℕ)

lemma natBits_encodeInt_nat (a : ℕ) : natBits (encodeInt (a : ℤ)) = [0] ++ bitsNat a := by
  have := natBits_encodeInt a 0
  simpa [intBits] using this

/-- One job of an instance, as zeros and ones. -/
def jobBits (I : Scheduling.Instance) (j : ℕ) : List ℕ :=
  if h : j < I.jobs then
    natBits (encodeInt (I.r ⟨j, h⟩)) ++ natBits (encodeInt (I.d ⟨j, h⟩)) ++ bitsNat (I.p ⟨j, h⟩)
  else []

theorem natBits_encodeInstance (I : Scheduling.Instance) :
    natBits (encodeInstance I) = bitsNat I.jobs ++ (List.range I.jobs).flatMap (jobBits I) := by
  unfold encodeInstance
  rw [natBits_append, natBits_encodeNat, flatMap_finRange, natBits_flatMap]
  congr 1
  refine List.flatMap_congr fun j hj => ?_
  have h : j < I.jobs := List.mem_range.mp hj
  simp only [jobBits, dif_pos h, natBits_append, natBits_encodeNat]

/-- The values of the tokens of the encoding of `A`. -/
def tkOf (A : AuxiliaryProblem.Instance) : List ℕ := (toksOf A).map Tok.val

/-- The record of ordinary job `o`. -/
def ordRow (tk : List ℕ) (o : ℕ) : List ℕ :=
  ([0] ++ bitsNat (tk.getD (2 + (3 * o + 0)) 0)) ++ ([0] ++ bitsNat (tk.getD (2 + (3 * o + 1)) 0)) ++
    bitsNat (if tk.getD (2 + (3 * o + 2)) 0 = 0 then q else p)

/-- The five records of pair `i`, the bins having width `p + 2q`. -/
def quadRow (tk : List ℕ) (n i : ℕ) : List ℕ :=
  (intBits (p + q) ((p + 2 * q) * (i + 1)) ++ intBits (p + 2 * q) ((p + 2 * q) * (i + 1)) ++
      bitsNat q) ++
    (intBits q ((p + 2 * q) * (i + 1)) ++ ([0] ++ bitsNat (tk.getD (2 + (3 * n + (4 * i + 0))) 0)) ++
      bitsNat p) ++
    (intBits 0 ((p + 2 * q) * (i + 1)) ++ ([0] ++ bitsNat (tk.getD (2 + (3 * n + (4 * i + 1))) 0)) ++
      bitsNat p) ++
    (intBits p ((p + 2 * q) * (i + 1)) ++ ([0] ++ bitsNat (tk.getD (2 + (3 * n + (4 * i + 2))) 0)) ++
      bitsNat q) ++
    (intBits 0 ((p + 2 * q) * (i + 1)) ++ ([0] ++ bitsNat (tk.getD (2 + (3 * n + (4 * i + 3))) 0)) ++
      bitsNat q)

/-- The zeros and ones of the stacked instance. -/
def outBits (tk : List ℕ) : List ℕ :=
  bitsNat (tk.getD 0 0 + 5 * tk.getD 1 0) ++
    (List.range (tk.getD 0 0)).flatMap (ordRow p q tk) ++
    (List.range (tk.getD 1 0)).flatMap (quadRow p q tk (tk.getD 0 0))

variable (A : AuxiliaryProblem.Instance)

lemma tk_getD (k : ℕ) : (tkOf A).getD k 0 = Tok.val ((toksOf A).getD k (.bit false)) := by
  unfold tkOf
  have h : (0 : ℕ) = Tok.val (.bit false) := rfl
  rw [h, List.getD_map]

lemma tk_zero : (tkOf A).getD 0 0 = A.ordinary := by rw [tk_getD, toksOf_eq]; rfl
lemma tk_one : (tkOf A).getD 1 0 = A.pairs := by rw [tk_getD, toksOf_eq]; rfl

lemma tk_ord (o c : ℕ) (ho : o < A.ordinary) (hc : c < 3) :
    (tkOf A).getD (2 + (3 * o + c)) 0 = Tok.val ((ordRec A o).getD c (.bit false)) := by
  rw [tk_getD, toksOf_eq, show 2 + (3 * o + c) = (3 * o + c) + 1 + 1 by ring]
  simp only [List.getD_cons_succ]
  rw [body_ord A o c ho hc]

lemma tk_pair (i c : ℕ) (hi : i < A.pairs) (hc : c < 4) :
    (tkOf A).getD (2 + (3 * A.ordinary + (4 * i + c))) 0 =
      Tok.val ((pairRec A i).getD c (.bit false)) := by
  rw [tk_getD, toksOf_eq, show 2 + (3 * A.ordinary + (4 * i + c)) =
    (3 * A.ordinary + (4 * i + c)) + 1 + 1 by ring]
  simp only [List.getD_cons_succ]
  rw [body_pair A i c hi hc]

/-- An ordinary job's record. -/
lemma jobBits_ord (o : ℕ) (ho : o < A.ordinary) :
    jobBits (StackedConstruction.inst p q A) o = ordRow p q (tkOf A) o := by
  have hj : o < (StackedConstruction.inst p q A).jobs := by
    show o < A.ordinary + 5 * A.pairs; omega
  unfold jobBits ordRow
  rw [dif_pos hj, StackedNumbering.r_of_ord p q (j := ⟨o, hj⟩) ⟨o, ho⟩ rfl,
    StackedNumbering.d_of_ord p q (j := ⟨o, hj⟩) ⟨o, ho⟩ rfl,
    StackedNumbering.p_of_ord p q (j := ⟨o, hj⟩) ⟨o, ho⟩ rfl,
    natBits_encodeInt_nat, natBits_encodeInt_nat, tk_ord A o 0 ho (by omega),
    tk_ord A o 1 ho (by omega), tk_ord A o 2 ho (by omega)]
  simp only [ordRec, dif_pos ho, List.getD_cons_zero, List.getD_cons_succ, Tok.val]
  cases A.long ⟨o, ho⟩ <;> simp

open Lax391470Proofs.StackedNumbering in
lemma binStart_add (i x : ℕ) :
    StackedConstruction.binStart p q i + (x : ℤ) = (x : ℤ) - (((p + 2 * q) * (i + 1) : ℕ) : ℤ) := by
  unfold StackedConstruction.binStart; ring

open Lax391470Proofs.StackedNumbering in
/-- The record of part `c` of pair `i`. -/
lemma jobBits_quad (i c : ℕ) (hi : i < A.pairs) (hc : c < 5) :
    jobBits (StackedConstruction.inst p q A) (A.ordinary + (5 * i + c)) =
      natBits (encodeInt (StackedConstruction.binStart p q i + relPart p q c)) ++
        natBits (encodeInt (duePart p q A ⟨i, hi⟩ c)) ++ bitsNat (lenPart p q c) := by
  have hj : A.ordinary + (5 * i + c) < (StackedConstruction.inst p q A).jobs := by
    show _ < A.ordinary + 5 * A.pairs; omega
  have hidx : ((⟨A.ordinary + (5 * i + c), hj⟩ : Fin _) : ℕ) = A.ordinary + 5 * (⟨i, hi⟩ : Fin _) + c := by
    simp; ring
  unfold jobBits
  rw [dif_pos hj, r_of_quad p q ⟨i, hi⟩ c hc hidx, d_of_quad p q ⟨i, hi⟩ c hc hidx,
    p_of_quad p q ⟨i, hi⟩ c hc hidx]

open Lax391470Proofs.StackedNumbering in
lemma quadRow_eq (i : ℕ) (hi : i < A.pairs) :
    jobBits (StackedConstruction.inst p q A) (A.ordinary + (5 * i)) ++
      jobBits (StackedConstruction.inst p q A) (A.ordinary + (5 * i + 1)) ++
      jobBits (StackedConstruction.inst p q A) (A.ordinary + (5 * i + 2)) ++
      jobBits (StackedConstruction.inst p q A) (A.ordinary + (5 * i + 3)) ++
      jobBits (StackedConstruction.inst p q A) (A.ordinary + (5 * i + 4)) =
    quadRow p q (tkOf A) A.ordinary i := by
  have h0 := jobBits_quad p q A i 0 hi (by omega)
  have h1 := jobBits_quad p q A i 1 hi (by omega)
  have h2 := jobBits_quad p q A i 2 hi (by omega)
  have h3 := jobBits_quad p q A i 3 hi (by omega)
  have h4 := jobBits_quad p q A i 4 hi (by omega)
  rw [Nat.add_zero] at h0
  rw [h0, h1, h2, h3, h4]
  have b0 := binStart_add p q i (p + q)
  have b1 := binStart_add p q i q
  have b2 := binStart_add p q i 0
  have b3 := binStart_add p q i p
  have b5 := binStart_add p q i (p + 2 * q)
  simp only [relPart, duePart, lenPart]
  rw [b0, b1, b3, b5]
  have b2' : StackedConstruction.binStart p q i + 0 =
      ((0 : ℕ) : ℤ) - (((p + 2 * q) * (i + 1) : ℕ) : ℤ) := by simpa using b2
  rw [b2', natBits_encodeInt, natBits_encodeInt, natBits_encodeInt, natBits_encodeInt,
    natBits_encodeInt, natBits_encodeInt_nat, natBits_encodeInt_nat, natBits_encodeInt_nat,
    natBits_encodeInt_nat]
  unfold quadRow
  rw [tk_pair A i 0 hi (by omega), tk_pair A i 1 hi (by omega), tk_pair A i 2 hi (by omega),
    tk_pair A i 3 hi (by omega)]
  simp only [pairRec, dif_pos hi, List.getD_cons_zero, List.getD_cons_succ, Tok.val]

/-- **What the machine has to write.** -/
theorem natBits_stacked :
    natBits (encodeInstance (StackedConstruction.inst p q A)) = outBits p q (tkOf A) := by
  rw [natBits_encodeInstance]
  have hjobs : (StackedConstruction.inst p q A).jobs = A.ordinary + 5 * A.pairs := rfl
  rw [hjobs, flatMap_range_add, flatMap_range_five]
  unfold outBits
  rw [tk_zero, tk_one, List.append_assoc]
  congr 2
  · refine List.flatMap_congr fun o ho => jobBits_ord p q A o (List.mem_range.mp ho)
  · refine List.flatMap_congr fun i hi => ?_
    have := quadRow_eq p q A i (List.mem_range.mp hi)
    simpa [Nat.add_assoc] using this

end Lax391470Proofs.L1Model
