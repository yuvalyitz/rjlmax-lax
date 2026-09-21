import Lax391470.Lemma1
import Lax391470Proofs.L1Ordered

/-!
The reduction of Lemma 1 as a function on zeros and ones.
-/

namespace Lax391470Proofs.L1Red

open Lax391470 Lax391470.BinaryEncoding Lax434930.PolynomialTime
open Lax391470Proofs.Bits Lax391470Proofs.TokModel Lax391470Proofs.TokScan
open Lax391470Proofs.AuxFormat Lax391470Proofs.TokProg Lax391470Proofs.L1Model
open Lax391470Proofs.L1Ordered Lax391470Proofs.L2Model

variable (p q : ℕ)

/-- The zeros and ones of the fixed instance without a feasible schedule. -/
def blockedBits : List ℕ :=
  bitsNat 1 ++ (([0] ++ bitsNat 0) ++ ([0] ++ bitsNat 0) ++ bitsNat p)

theorem natBits_blocked : natBits (encodeInstance (Lemma1.blocked p)) = blockedBits p := by
  rw [natBits_encodeInstance]
  have hj : (Lemma1.blocked p).jobs = 1 := rfl
  rw [hj]
  simp only [List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil, jobBits,
    blockedBits]
  rw [dif_pos (by rw [hj]; omega)]
  have e0 : (Lemma1.blocked p).r ⟨0, by rw [hj]; omega⟩ = ((0 : ℕ) : ℤ) := rfl
  have e1 : (Lemma1.blocked p).d ⟨0, by rw [hj]; omega⟩ = ((0 : ℕ) : ℤ) := rfl
  have e2 : (Lemma1.blocked p).p ⟨0, by rw [hj]; omega⟩ = p := rfl
  rw [e0, e1, e2, natBits_encodeInt_nat]

/-- The token values the scan collects. -/
def tkScan (y : List ℕ) : List ℕ := (run EA init (bitsOf y)).toks.map Tok.val

open Classical in
/-- **The reduction on zeros and ones.** -/
noncomputable def red (y : List ℕ) : List ℕ :=
  if Accepts EA (run EA init (bitsOf y)) ∧ OrdOK (tkScan y) then outBits p q (tkScan y)
  else blockedBits p

theorem red_natBits (w : Word) : red p q (natBits w) = natBits (Lemma1.reduce p q w) := by
  classical
  unfold red Lemma1.reduce tkScan
  rw [bitsOf_natBits]
  obtain ⟨hdec1, hdec2⟩ := decode_iff w
  by_cases hacc : Accepts EA (run EA init w)
  · have henc := hdec1 hacc
    have hconf := (accept_sound EA hacc).2
    have htk : (run EA init w).toks.map Tok.val = tkOf (ofToks (run EA init w).toks) := by
      unfold tkOf; rw [toksOf_ofToks hconf]
    rw [htk]
    by_cases hord : (ofToks (run EA init w).toks).Ordered
    · have hex : ∃ A : AuxiliaryProblem.Instance, encodeAux A = w ∧ A.Ordered :=
        ⟨_, henc, hord⟩
      rw [if_pos ⟨hacc, (ordered_iff _).mp hord⟩, dif_pos hex]
      have hch : hex.choose = ofToks (run EA init w).toks := (hdec2 _ hex.choose_spec.1).2
      rw [hch, natBits_stacked]
    · have hnex : ¬ ∃ A : AuxiliaryProblem.Instance, encodeAux A = w ∧ A.Ordered := by
        rintro ⟨A, hA, hAo⟩
        rw [(hdec2 A hA).2] at hAo
        exact hord hAo
      rw [if_neg (fun h => hord ((ordered_iff _).mpr h.2)), dif_neg hnex, natBits_blocked]
  · have hnex : ¬ ∃ A : AuxiliaryProblem.Instance, encodeAux A = w ∧ A.Ordered := by
      rintro ⟨A, hA, -⟩
      exact hacc (hdec2 A hA).1
    rw [if_neg (fun h => hacc h.1), dif_neg hnex, natBits_blocked]

end Lax391470Proofs.L1Red
