import Lax391470Proofs.TokScan
import Lax391470Proofs.RecList
import Lax391470Proofs.L2Model
import Lax391470Proofs.AuxFormat

/-!
The encoding of a scheduling instance, as a stream of tokens.
-/

namespace Lax391470Proofs.InstFormat

open Lax391470 Lax391470.BinaryEncoding Lax391470Proofs.TokModel

variable (I : Scheduling.Instance)

/-- The five tokens of job `j`: sign and size of its release time, sign and size of its
deadline, and its processing time. -/
def jobRec (j : ℕ) : List Tok :=
  if h : j < I.jobs then
    [.bit (decide (I.r ⟨j, h⟩ < 0)), .num (I.r ⟨j, h⟩).natAbs,
      .bit (decide (I.d ⟨j, h⟩ < 0)), .num (I.d ⟨j, h⟩).natAbs, .num (I.p ⟨j, h⟩)]
  else [.bit false, .num 0, .bit false, .num 0, .num 0]

lemma jobRec_length (j : ℕ) : (jobRec I j).length = 5 := by unfold jobRec; split <;> rfl

/-- The tokens of the encoding of `I`. -/
def toksOf : List Tok := .num I.jobs :: (List.range I.jobs).flatMap (jobRec I)

theorem encodeInstance_eq : encodeInstance I = code (toksOf I) := by
  unfold encodeInstance toksOf
  rw [show (Tok.num I.jobs :: (List.range I.jobs).flatMap (jobRec I)) =
    [Tok.num I.jobs] ++ (List.range I.jobs).flatMap (jobRec I) from rfl, code_append,
    L2Model.flatMap_finRange]
  congr 1
  · simp [code, Tok.code]
  · simp only [code, List.flatMap_assoc]
    refine List.flatMap_congr fun j hj => ?_
    have h : j < I.jobs := List.mem_range.mp hj
    simp [jobRec, h, Tok.code, encodeInt]

lemma toksOf_length : (toksOf I).length = 1 + 5 * I.jobs := by
  unfold toksOf
  rw [List.length_cons, RecList.length_flatMap_const _ 5 (jobRec_length I)]; omega

/-- The kind of the token at position `j` after the count. -/
def kindAt (n j : ℕ) : Kind :=
  if j < 5 * n then (if j % 5 = 0 ∨ j % 5 = 2 then .bit else .num) else .done

/-- The format: the count, then `n` records of five tokens. -/
def EI : Format := fun ts =>
  match ts with
  | .num n :: rest => kindAt n rest.length
  | [] => .num
  | _ => .done

lemma EI_cons (n : ℕ) (rest : List Tok) : EI (.num n :: rest) = kindAt n rest.length := rfl

/-- The records after the count. -/
def body : List Tok := (List.range I.jobs).flatMap (jobRec I)

lemma body_length : (body I).length = 5 * I.jobs :=
  RecList.length_flatMap_const _ 5 (jobRec_length I) _

lemma body_get (j c : ℕ) (hj : j < I.jobs) (hc : c < 5) (d : Tok) :
    (body I).getD (5 * j + c) d = (jobRec I j).getD c d :=
  RecList.getD_flatMap_const _ 5 (jobRec_length I) _ _ _ hj hc d

lemma body_kind (k : ℕ) (hk : k < 5 * I.jobs) :
    ((body I).getD k (.bit false)).kind = kindAt I.jobs k := by
  unfold kindAt
  rw [if_pos hk]
  have e : k = 5 * (k / 5) + k % 5 := by omega
  have hj : k / 5 < I.jobs := by omega
  rw [e, body_get I _ _ hj (by omega), ← e]
  unfold jobRec; rw [dif_pos hj]
  have h5 : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
  rcases h5 with h | h | h | h | h <;> simp [h, Tok.kind]

/-! ### From a Conforming Stream Back to an Instance -/

open Lax391470Proofs.AuxFormat (numAt bitAt tok_of_num tok_of_bit numAt_of bitAt_of kind_ne_done)

/-- The integer with sign bit `b` and absolute value `v`. -/
def toInt (b : Bool) (v : ℕ) : ℤ := if b then -(v : ℤ) else v

lemma toInt_sign {b : Bool} {v : ℕ} (h : ¬ (b = true ∧ v = 0)) : decide (toInt b v < 0) = b := by
  cases b <;> simp [toInt] at h ⊢; omega

lemma toInt_abs (b : Bool) (v : ℕ) : (toInt b v).natAbs = v := by
  cases b <;> simp [toInt]

/-- The instance a stream of tokens describes. -/
def ofToks (ts : List Tok) : Scheduling.Instance where
  jobs := numAt ts 0
  r j := toInt (bitAt ts (1 + (5 * j + 0))) (numAt ts (1 + (5 * j + 1)))
  d j := toInt (bitAt ts (1 + (5 * j + 2))) (numAt ts (1 + (5 * j + 3)))
  p j := numAt ts (1 + (5 * j + 4))

/-- No integer of the stream is written as `-0`. -/
def NoNegZero (ts : List Tok) : Prop :=
  ∀ j < numAt ts 0,
    ¬ (bitAt ts (1 + (5 * j + 0)) = true ∧ numAt ts (1 + (5 * j + 1)) = 0) ∧
    ¬ (bitAt ts (1 + (5 * j + 2)) = true ∧ numAt ts (1 + (5 * j + 3)) = 0)

lemma numAt_cons1 (a : Tok) (rest : List Tok) (k : ℕ) :
    numAt (a :: rest) (1 + k) = numAt rest k := by
  unfold numAt; rw [show 1 + k = k + 1 by ring]; rfl

lemma bitAt_cons1 (a : Tok) (rest : List Tok) (k : ℕ) :
    bitAt (a :: rest) (1 + k) = bitAt rest k := by
  unfold bitAt; rw [show 1 + k = k + 1 by ring]; rfl

/-- The length of a conforming stream. -/
lemma conf_length {n : ℕ} {rest : List Tok} (hc : Conforms EI (.num n :: rest)) :
    rest.length = 5 * n := by
  obtain ⟨hf, hd⟩ := hc
  rw [EI_cons] at hd
  have h1 : ¬ rest.length < 5 * n := by
    intro hlt
    unfold kindAt at hd
    rw [if_pos hlt] at hd
    split_ifs at hd
  by_contra hne
  have hk := hf (1 + 5 * n) (by simp; omega)
  have e : (Tok.num n :: rest).take (1 + 5 * n) = .num n :: rest.take (5 * n) := by
    rw [show 1 + 5 * n = 5 * n + 1 by ring]; rfl
  rw [e, EI_cons, List.length_take, Nat.min_eq_left (by omega)] at hk
  have : kindAt n (5 * n) = .done := by simp [kindAt]
  rw [this] at hk
  exact kind_ne_done _ hk

lemma conf_head {ts : List Tok} (hc : Conforms EI ts) : ∃ n rest, ts = .num n :: rest := by
  obtain ⟨hf, hd⟩ := hc
  rcases ts with _ | ⟨a, rest⟩
  · simp [EI] at hd
  have ha : a.kind = .num := by simpa [EI] using hf 0 (by simp)
  exact ⟨_, rest, by rw [tok_of_num ha]⟩

/-- **A conforming stream without `-0` is the encoding of the instance it describes.** -/
theorem toksOf_ofToks {ts : List Tok} (hc : Conforms EI ts) (hz : NoNegZero ts) :
    toksOf (ofToks ts) = ts := by
  obtain ⟨n, rest, rfl⟩ := conf_head hc
  have hlen := conf_length hc
  obtain ⟨hf, -⟩ := hc
  have hkind : ∀ j < 5 * n, (rest.getD j (.bit false)).kind = kindAt n j := by
    intro j hj
    have hk := hf (j + 1) (by simp; omega)
    have e : (Tok.num n :: rest).take (j + 1) = .num n :: rest.take j := rfl
    rw [e, EI_cons, List.length_take, Nat.min_eq_left (by omega)] at hk
    simpa using hk
  have hbit : ∀ j < 5 * n, j % 5 = 0 ∨ j % 5 = 2 → ∃ b, rest.getD j (.bit false) = .bit b := by
    intro j hj h5
    have := hkind j hj
    unfold kindAt at this
    rw [if_pos hj, if_pos h5] at this
    exact ⟨_, tok_of_bit this⟩
  have hnum : ∀ j < 5 * n, ¬ (j % 5 = 0 ∨ j % 5 = 2) → ∃ v, rest.getD j (.bit false) = .num v := by
    intro j hj h5
    have := hkind j hj
    unfold kindAt at this
    rw [if_pos hj, if_neg h5] at this
    exact ⟨_, tok_of_num this⟩
  set I := ofToks (Tok.num n :: rest) with hI
  have hIn : I.jobs = n := rfl
  unfold toksOf
  rw [hIn]
  congr 1
  refine List.ext_getElem (by
    rw [RecList.length_flatMap_const _ 5 (jobRec_length I), hlen]) fun j h1 h2 => ?_
  have hj : j < 5 * n := by rw [← hlen]; exact h2
  have e : j = 5 * (j / 5) + j % 5 := by omega
  have hjn : j / 5 < n := by omega
  have hz' := hz (j / 5) hjn
  simp only [numAt_cons1, bitAt_cons1] at hz'
  have hg : ((List.range n).flatMap (jobRec I)).getD j (.bit false) = rest.getD j (.bit false) := by
    rw [e, RecList.getD_flatMap_const _ 5 (jobRec_length I) _ _ _ hjn (by omega), ← e]
    unfold jobRec; rw [dif_pos (show j / 5 < I.jobs from hjn)]
    obtain ⟨b0, hb0⟩ := hbit (5 * (j / 5) + 0) (by omega) (by omega)
    obtain ⟨v1, hv1⟩ := hnum (5 * (j / 5) + 1) (by omega) (by omega)
    obtain ⟨b2, hb2⟩ := hbit (5 * (j / 5) + 2) (by omega) (by omega)
    obtain ⟨v3, hv3⟩ := hnum (5 * (j / 5) + 3) (by omega) (by omega)
    obtain ⟨v4, hv4⟩ := hnum (5 * (j / 5) + 4) (by omega) (by omega)
    rw [bitAt_of hb0, numAt_of hv1, bitAt_of hb2, numAt_of hv3] at hz'
    have hr : I.r ⟨j / 5, hjn⟩ = toInt b0 v1 := by
      show toInt (bitAt _ (1 + _)) (numAt _ (1 + _)) = _
      rw [bitAt_cons1, numAt_cons1, bitAt_of hb0, numAt_of hv1]
    have hd : I.d ⟨j / 5, hjn⟩ = toInt b2 v3 := by
      show toInt (bitAt _ (1 + _)) (numAt _ (1 + _)) = _
      rw [bitAt_cons1, numAt_cons1, bitAt_of hb2, numAt_of hv3]
    have hp : I.p ⟨j / 5, hjn⟩ = v4 := by
      show numAt _ (1 + _) = _
      rw [numAt_cons1, numAt_of hv4]
    rw [hr, hd, hp, toInt_sign hz'.1, toInt_sign hz'.2, toInt_abs, toInt_abs]
    have h5 : j % 5 = 0 ∨ j % 5 = 1 ∨ j % 5 = 2 ∨ j % 5 = 3 ∨ j % 5 = 4 := by omega
    rcases h5 with h | h | h | h | h <;> rw [h] at e ⊢ <;> rw [e]
    · rw [hb0]; rfl
    · rw [hv1]; rfl
    · rw [hb2]; rfl
    · rw [hv3]; rfl
    · rw [hv4]; rfl
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at hg
  exact hg

end Lax391470Proofs.InstFormat
