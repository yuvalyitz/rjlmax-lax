import Lax391470Proofs.V1Sem

/-!
The token values of an instance followed by a schedule describe them, in both directions.
-/

namespace Lax391470Proofs.V1Reads

open Lax391470 Lax391470.Scheduling Lax391470Proofs.TokModel Lax391470Proofs.TokProg
open Lax391470Proofs.InstFormat Lax391470Proofs.V1Format Lax391470Proofs.V1Sem
open Lax391470Proofs.AuxFormat (numAt bitAt tok_of_num tok_of_bit numAt_of bitAt_of)

lemma toInt_self (z : ℤ) : toInt (decide (z < 0)) z.natAbs = z := by
  unfold toInt
  by_cases h : z < 0
  · simp only [h, decide_true, if_true]; omega
  · simp only [h, decide_false, Bool.false_eq_true, if_false]; omega

/-! ### From an instance and a schedule to token values -/

/-- A schedule as a function on all numbers. -/
def ext {I : Scheduling.Instance} (t : I.Schedule) (j : ℕ) : ℤ :=
  if h : j < I.jobs then t ⟨j, h⟩ else 0

variable (I : Scheduling.Instance) (t : ℕ → ℤ)

lemma get_job (j c : ℕ) (hj : j < I.jobs) (hc : c < 5) :
    (toks2 I t).getD (iJ j c) (.bit false) = (jobRec I j).getD c (.bit false) := by
  rw [toks2_eq, show iJ j c = (5 * j + c) + 1 by unfold iJ; ring, List.getD_cons_succ,
    List.getD_append _ _ _ _ (by rw [body_length]; omega), body_get I j c hj hc]

lemma get_sched (j c : ℕ) (hj : j < I.jobs) (hc : c < 2) :
    (toks2 I t).getD (iT I.jobs j c) (.bit false) = (schedRec t j).getD c (.bit false) := by
  rw [toks2_eq, show iT I.jobs j c = (5 * I.jobs + (2 * j + c)) + 1 by unfold iT; ring,
    List.getD_cons_succ, List.getD_append_right _ _ _ _ (by rw [body_length]; omega), body_length,
    show 5 * I.jobs + (2 * j + c) - 5 * I.jobs = 2 * j + c by omega]
  exact RecList.getD_flatMap_const _ 2 (schedRec_length t) _ _ _ hj hc _

lemma val_zero : ((toks2 I t).map Tok.val).getD 0 0 = I.jobs := by
  rw [val_getD, toks2_eq]; rfl

/-- **The token values of an instance and a schedule describe them.** -/
theorem reads_toks2 (s : I.Schedule) : Reads I s ((toks2 I (ext s)).map Tok.val) := by
  refine ⟨val_zero I _, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_⟩
  · rw [zv_toks (b := decide (I.r j < 0)) (v := (I.r j).natAbs), toInt_self]
    · rw [get_job I _ j 0 j.isLt (by omega)]; unfold jobRec; rw [dif_pos j.isLt]; rfl
    · rw [get_job I _ j 1 j.isLt (by omega)]; unfold jobRec; rw [dif_pos j.isLt]; rfl
  · rw [zv_toks (b := decide (I.d j < 0)) (v := (I.d j).natAbs), toInt_self]
    · rw [get_job I _ j 2 j.isLt (by omega)]; unfold jobRec; rw [dif_pos j.isLt]; rfl
    · rw [get_job I _ j 3 j.isLt (by omega)]; unfold jobRec; rw [dif_pos j.isLt]; rfl
  · rw [val_getD, get_job I _ j 4 j.isLt (by omega)]; unfold jobRec; rw [dif_pos j.isLt]; rfl
  · have e : ext s j = s j := by unfold ext; rw [dif_pos j.isLt]
    rw [zv_toks (b := decide (ext s j < 0)) (v := (ext s j).natAbs), toInt_self, e]
    · rw [get_sched I _ j 0 j.isLt (by omega)]; rfl
    · rw [get_sched I _ j 1 j.isLt (by omega)]; rfl

/-- The encoding of an instance never writes `-0`. -/
theorem nz_toks2 : NZ ((toks2 I t).map Tok.val) := by
  intro j hj
  rw [val_zero] at hj
  have h0 := get_job I t j 0 hj (by omega)
  have h1 := get_job I t j 1 hj (by omega)
  have h2 := get_job I t j 2 hj (by omega)
  have h3 := get_job I t j 3 hj (by omega)
  unfold jobRec at h0 h1 h2 h3
  rw [dif_pos hj] at h0 h1 h2 h3
  rw [val_getD, val_getD, val_getD, val_getD, h0, h1, h2, h3]
  simp only [List.getD_cons_zero, List.getD_cons_succ, Tok.val]
  constructor
  · rintro ⟨ha, hb⟩
    by_cases hz : I.r ⟨j, hj⟩ < 0 <;> simp [hz] at ha; omega
  · rintro ⟨ha, hb⟩
    by_cases hz : I.d ⟨j, hj⟩ < 0 <;> simp [hz] at ha; omega

/-! ### From token values to an instance and a schedule -/

lemma conf_toks {n : ℕ} {rest : List Tok} (hc : Conforms EI (.num n :: rest)) (j : ℕ)
    (hj : j < n) :
    ∃ b0 v1 b2 v3 v4,
      (Tok.num n :: rest).getD (iJ j 0) (.bit false) = .bit b0 ∧
      (Tok.num n :: rest).getD (iJ j 1) (.bit false) = .num v1 ∧
      (Tok.num n :: rest).getD (iJ j 2) (.bit false) = .bit b2 ∧
      (Tok.num n :: rest).getD (iJ j 3) (.bit false) = .num v3 ∧
      (Tok.num n :: rest).getD (iJ j 4) (.bit false) = .num v4 := by
  have hlen := conf_length hc
  obtain ⟨hf, -⟩ := hc
  have hkind : ∀ k < 5 * n,
      ((Tok.num n :: rest).getD (1 + k) (.bit false)).kind = kindAt n k := by
    intro k hk
    have h := hf (k + 1) (by simp; omega)
    have e : (Tok.num n :: rest).take (k + 1) = .num n :: rest.take k := rfl
    rw [e, EI_cons, List.length_take, Nat.min_eq_left (by omega)] at h
    rw [show 1 + k = k + 1 by ring]; exact h
  have hb : ∀ k < 5 * n, k % 5 = 0 ∨ k % 5 = 2 →
      ∃ b, (Tok.num n :: rest).getD (1 + k) (.bit false) = .bit b := by
    intro k hk h5
    have := hkind k hk
    unfold kindAt at this
    rw [if_pos hk, if_pos h5] at this
    exact ⟨_, tok_of_bit this⟩
  have hn : ∀ k < 5 * n, ¬ (k % 5 = 0 ∨ k % 5 = 2) →
      ∃ v, (Tok.num n :: rest).getD (1 + k) (.bit false) = .num v := by
    intro k hk h5
    have := hkind k hk
    unfold kindAt at this
    rw [if_pos hk, if_neg h5] at this
    exact ⟨_, tok_of_num this⟩
  obtain ⟨b0, h0⟩ := hb (5 * j + 0) (by omega) (by omega)
  obtain ⟨v1, h1⟩ := hn (5 * j + 1) (by omega) (by omega)
  obtain ⟨b2, h2⟩ := hb (5 * j + 2) (by omega) (by omega)
  obtain ⟨v3, h3⟩ := hn (5 * j + 3) (by omega) (by omega)
  obtain ⟨v4, h4⟩ := hn (5 * j + 4) (by omega) (by omega)
  exact ⟨b0, v1, b2, v3, v4, h0, h1, h2, h3, h4⟩

/-- **Token values that begin with a conforming instance describe it**, with the
schedule read off the values. -/
theorem reads_of_toks {ts1 l : List Tok} (hc1 : Conforms EI ts1)
    (hnz : NZ ((ts1 ++ l).map Tok.val)) :
    NoNegZero ts1 ∧
    Reads (ofToks ts1)
      (fun j => zv ((ts1 ++ l).map Tok.val) (iT (ofToks ts1).jobs j 0) (iT (ofToks ts1).jobs j 1))
      ((ts1 ++ l).map Tok.val) := by
  obtain ⟨n, rest, rfl⟩ := conf_head hc1
  have hlen := conf_length hc1
  have hn0 : ((Tok.num n :: rest ++ l).map Tok.val).getD 0 0 = n := by
    rw [val_getD]; rfl
  have tr : ∀ k < 1 + 5 * n, (Tok.num n :: rest ++ l).getD k (.bit false) =
      (Tok.num n :: rest).getD k (.bit false) := fun k hk =>
    List.getD_append _ _ _ _ (by simp; omega)
  have hJ : (ofToks (Tok.num n :: rest)).jobs = n := rfl
  refine ⟨fun j hj => ?_, hn0, fun j => ?_, fun j => ?_, fun j => ?_, fun j => rfl⟩
  · have hj' : j < n := hj
    obtain ⟨b0, v1, b2, v3, v4, h0, h1, h2, h3, h4⟩ := conf_toks hc1 j hj'
    have := hnz j (by rw [hn0]; exact hj')
    rw [val_getD, val_getD, val_getD, val_getD, tr _ (by unfold iJ; omega),
      tr _ (by unfold iJ; omega), tr _ (by unfold iJ; omega), tr _ (by unfold iJ; omega),
      h0, h1, h2, h3] at this
    rw [bitAt_of h0, numAt_of h1, bitAt_of h2, numAt_of h3]
    cases b0 <;> cases b2 <;> simp [Tok.val] at this ⊢ <;> omega
  · have hj' : (j : ℕ) < n := j.isLt
    obtain ⟨b0, v1, b2, v3, v4, h0, h1, h2, h3, h4⟩ := conf_toks hc1 j hj'
    rw [zv_toks (by rw [tr _ (by unfold iJ; omega)]; exact h0)
      (by rw [tr _ (by unfold iJ; omega)]; exact h1)]
    show _ = toInt (bitAt _ _) (numAt _ _)
    rw [bitAt_of h0, numAt_of h1]
  · have hj' : (j : ℕ) < n := j.isLt
    obtain ⟨b0, v1, b2, v3, v4, h0, h1, h2, h3, h4⟩ := conf_toks hc1 j hj'
    rw [zv_toks (by rw [tr _ (by unfold iJ; omega)]; exact h2)
      (by rw [tr _ (by unfold iJ; omega)]; exact h3)]
    show _ = toInt (bitAt _ _) (numAt _ _)
    rw [bitAt_of h2, numAt_of h3]
  · have hj' : (j : ℕ) < n := j.isLt
    obtain ⟨b0, v1, b2, v3, v4, h0, h1, h2, h3, h4⟩ := conf_toks hc1 j hj'
    rw [val_getD, tr _ (by unfold iJ; omega), h4]
    show _ = numAt _ _
    rw [numAt_of h4]; rfl

end Lax391470Proofs.V1Reads
