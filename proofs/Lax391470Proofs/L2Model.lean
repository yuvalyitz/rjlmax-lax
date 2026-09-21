import Lax391470.Lemma2
import Lax391470Proofs.Bits
import Lax391470Proofs.CnfScan

/-!
The reduction of Lemma 2 as a function on zeros and ones: what the machine has to write.
-/

namespace Lax391470Proofs.L2Model

open Lax391470 Lax391470.BinaryEncoding Lax391470.SatConstruction Lax429075
open Lax434930.PolynomialTime Lax391470Proofs.Bits

lemma natBits_append (u v : Word) : natBits (u ++ v) = natBits u ++ natBits v := by
  simp [natBits]

@[simp] lemma natBits_singleton (b : Bool) : natBits [b] = [if b then 1 else 0] := rfl

lemma flatMap_finRange {α : Type} : ∀ (n : ℕ) (f : Fin n → List α),
    (List.finRange n).flatMap f =
      (List.range n).flatMap fun i => if h : i < n then f ⟨i, h⟩ else []
  | 0, _ => by simp
  | n + 1, f => by
    rw [List.finRange_succ_last, List.range_succ, List.flatMap_append, List.flatMap_append,
      List.flatMap_map, flatMap_finRange n]
    congr 1
    · refine List.flatMap_congr fun i hi => ?_
      have hi' : i < n := List.mem_range.mp hi
      simp [hi', Nat.lt_succ_of_lt hi']
    · simp; rfl

lemma natBits_flatMap (l : List ℕ) (f : ℕ → Word) :
    natBits (l.flatMap f) = l.flatMap fun i => natBits (f i) := by
  simp [natBits, List.map_flatMap]

variable (p q : ℕ) (F : CNF.Formula)

/-- The zeros and ones of one ordinary job. -/
def ordBits (o : ℕ) : List ℕ :=
  bitsNat (ordRelease p q F o) ++ bitsNat (SatConstruction.ordDue p q F o) ++
    [if ordLong F o then 1 else 0]

/-- The zeros and ones of one connected pair. -/
def pairBits (i : ℕ) : List ℕ :=
  bitsNat (longEarly p q F i) ++ bitsNat (longDue p q F i) ++
    bitsNat (shortEarly p q F i) ++ bitsNat (shortDue p q F i)

/-- The zeros and ones of the constructed instance. -/
def outBits : List ℕ :=
  bitsNat (numOrdinary F) ++ bitsNat (SatConstruction.numPairs F) ++
    ((List.range (numOrdinary F)).flatMap (ordBits p q F)) ++
    (List.range (SatConstruction.numPairs F)).flatMap (pairBits p q F)

theorem natBits_encodeAux_inst : natBits (encodeAux (inst p q F)) = outBits p q F := by
  simp only [encodeAux, natBits_append, natBits_encodeNat, outBits, flatMap_finRange,
    natBits_flatMap]
  congr 1
  · congr 1
    refine List.flatMap_congr fun o ho => ?_
    have ho' : o < (inst p q F).ordinary := List.mem_range.mp ho
    rw [dif_pos ho']
    simp only [natBits_append, natBits_encodeNat, ordBits, natBits_singleton]
    rfl
  · refine List.flatMap_congr fun i hi => ?_
    have hi' : i < (inst p q F).pairs := List.mem_range.mp hi
    rw [dif_pos hi']
    simp only [natBits_append, natBits_encodeNat, pairBits]
    rfl

/-- The zeros and ones of the instance a malformed word is sent to. -/
def blockedBits : List ℕ := bitsNat 1 ++ bitsNat 0 ++ (bitsNat 0 ++ bitsNat 0 ++ [0])

theorem natBits_encodeAux_blocked : natBits (encodeAux Lemma2.blocked) = blockedBits := by
  simp only [encodeAux, Lemma2.blocked, natBits_append, natBits_encodeNat, blockedBits,
    List.finRange_succ, List.finRange_zero, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    natBits_singleton, List.append_nil]
  rfl

/-- **The reduction on zeros and ones.** -/
def red (y : List ℕ) : List ℕ :=
  let s := CnfScan.run CnfScan.init (bitsOf y)
  if s.ph = 4 then outBits p q s.done else blockedBits

theorem red_natBits (w : Word) : red p q (natBits w) = natBits (Lemma2.reduce p q w) := by
  unfold red Lemma2.reduce
  simp only [bitsOf_natBits, CnfScan.decodeCNF_eq]
  split
  · simp [natBits_encodeAux_inst]
  · simp [natBits_encodeAux_blocked]

end Lax391470Proofs.L2Model
