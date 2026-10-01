import Lax391470Proofs.L1Check
import Lax391470Proofs.Bits
import Lax391470Proofs.TokProg
import Lax434930.Certificates

/-!
Taking a pair of words apart: one pass over `pair x y` that writes `x ++ y` into the
array `w` and counts the two lengths.
-/

namespace Lax391470Proofs.VUnpair

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.L1Check (V add)
open Lax391470Proofs.Bits Lax434930.Certificates

/-! ### The Model -/

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The state of the pass: `0` before a marker, `1` before a bit of the first word, `2` in
the second word. -/
structure U where
  st : ℕ
  xs : List ℕ
  ys : List ℕ

def ustep (u : U) (c : ℕ) : U :=
  if u.st = 0 then (if c = 0 then { u with st := 1 } else { u with st := 2 })
  else if u.st = 1 then ⟨0, u.xs ++ [c], u.ys⟩
  else ⟨u.st, u.xs, u.ys ++ [c]⟩

def urun (u : U) (z : List ℕ) : U := z.foldl ustep u

def uinit : U := ⟨0, [], []⟩

lemma urun_append (u : U) (a b : List ℕ) : urun u (a ++ b) = urun (urun u a) b := by
  simp [urun, List.foldl_append]

lemma urun_second (xs ys z : List ℕ) : urun ⟨2, xs, ys⟩ z = ⟨2, xs, ys ++ z⟩ := by
  induction z generalizing ys with
  | nil => simp [urun]
  | cons c t ih =>
    have : urun ⟨2, xs, ys⟩ (c :: t) = urun ⟨2, xs, ys ++ [c]⟩ t := by simp [urun, ustep]
    rw [this, ih]; simp

lemma urun_pair_aux (x y : Lax434930.PolynomialTime.Word) (xs : List ℕ) :
    urun ⟨0, xs, []⟩ (natBits (pair x y)) = ⟨2, xs ++ natBits x, natBits y⟩ := by
  induction x generalizing xs with
  | nil =>
    have : urun ⟨0, xs, []⟩ (natBits (pair [] y)) = urun ⟨2, xs, []⟩ (natBits y) := by
      simp [pair, natBits, urun, ustep]
    rw [this, urun_second]; simp [natBits]
  | cons b t ih =>
    have : urun ⟨0, xs, []⟩ (natBits (pair (b :: t) y)) =
        urun ⟨0, xs ++ [if b then 1 else 0], []⟩ (natBits (pair t y)) := by
      simp [pair, natBits, urun, ustep]
    rw [this, ih]; simp [natBits]

/-- **The pass takes a pair apart.** -/
theorem urun_pair (x y : Lax434930.PolynomialTime.Word) :
    urun uinit (natBits (pair x y)) = ⟨2, natBits x, natBits y⟩ := by
  have := urun_pair_aux x y []
  simpa [uinit] using this

/-- In the first word nothing of the second has been seen; the lengths are bounded. -/
inductive UGood (u : U) (k : ℕ) : Prop where
  | mk
    (st : u.st ≤ 2)
    (ys : u.st ≠ 2 → u.ys = [])
    (len : u.xs.length + u.ys.length ≤ k)

theorem UGood.len
    {u : U} {k : ℕ}
    (h : UGood u k) : u.xs.length + u.ys.length ≤ k :=
  match h with | ⟨_, _, x⟩ => x

lemma ugood_step {u : U} {k : ℕ} (h : UGood u k) (c : ℕ) : UGood (ustep u c) (k + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold ustep
  split_ifs with a b c
  · exact ⟨by simp, fun _ => h2 (by omega), by simp; omega⟩
  · exact ⟨by simp, fun h => absurd rfl h, by simp; omega⟩
  · exact ⟨by simp, fun _ => h2 (by omega), by simp; omega⟩
  · exact ⟨h1, fun h => by simp at h; omega, by simp; omega⟩

def uAt (z : List ℕ) (t : ℕ) : U := urun uinit (z.take t)

lemma uAt_succ {z : List ℕ} {t : ℕ} (ht : t < z.length) :
    uAt z (t + 1) = ustep (uAt z t) (z.getD t 0) := by
  unfold uAt
  rw [List.take_add_one, urun_append, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
  simp [urun]

lemma ugood_uAt (z : List ℕ) : ∀ t ≤ z.length, UGood (uAt z t) t
  | 0, _ => ⟨by simp [uAt, urun, uinit], fun _ => by simp [uAt, urun, uinit],
      by simp [uAt, urun, uinit]⟩
  | t + 1, h => by
    rw [uAt_succ (by omega)]
    exact ugood_step (ugood_uAt z t (by omega)) _

/-- Everything the pass collects comes from its input. -/
lemma urun_mem (z : List ℕ) : ∀ (u : U) (v : ℕ), v ∈ (urun u z).xs ++ (urun u z).ys →
    v ∈ u.xs ++ u.ys ∨ v ∈ z := by
  induction z with
  | nil => intro u v h; exact Or.inl h
  | cons c t ih =>
    intro u v h
    have h' : v ∈ (urun (ustep u c) t).xs ++ (urun (ustep u c) t).ys := h
    rcases ih (ustep u c) v h' with h1 | h1
    · have : v ∈ u.xs ++ u.ys ∨ v = c := by
        unfold ustep at h1
        split_ifs at h1 <;> simp at h1 ⊢ <;> tauto
      rcases this with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (by rw [h2]; exact List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem _ h1)

lemma urun_mem_init {z : List ℕ} {v : ℕ} (h : v ∈ (urun uinit z).xs ++ (urun uinit z).ys) :
    v ∈ z := by
  rcases urun_mem z uinit v h with h1 | h1
  · simp [uinit] at h1
  · exact h1

/-! ### The Program -/

variable {B : ℕ}

def uBody : Com :=
  .seq (.assign "c" (.get "a" (V "p")))
    (.seq (.ite (.eq (V "st") (.lit 0))
        (.ite (.eq (V "c") (.lit 0)) (.assign "st" (.lit 1)) (.assign "st" (.lit 2)))
        (.seq (.store "w" (V "nw") (V "c")) (.seq (.assign "nw" (add (V "nw") (.lit 1)))
          (.ite (.eq (V "st") (.lit 1))
            (.seq (.assign "nx" (add (V "nx") (.lit 1))) (.assign "st" (.lit 0))) .skip))))
      (.assign "p" (add (V "p") (.lit 1))))

theorem uBody_spec (z wa : List ℕ) (p0 s nx nw : ℕ) (hp : p0 < z.length) (hs : s ≤ 2)
    (hnw : nw < wa.length) (hB : z.length + 4 < B) (hnwB : nw ≤ z.length) (hnxB : nx ≤ z.length)
    (hz : ∀ v ∈ z, v < B) :
    Spec B (fun σ => σ.arrs "a" = z ∧ σ.arrs "w" = wa ∧ σ.vars "p" = p0 ∧ σ.vars "st" = s ∧
        σ.vars "nx" = nx ∧ σ.vars "nw" = nw) uBody
      (fun σ σ' => σ'.arrs "a" = z ∧
        σ'.arrs "w" = (if s = 0 then wa else wa.set nw (z.getD p0 0)) ∧
        σ'.vars "p" = p0 + 1 ∧
        σ'.vars "st" = (if s = 0 then (if z.getD p0 0 = 0 then 1 else 2)
          else if s = 1 then 0 else s) ∧
        σ'.vars "nx" = (if s = 1 then nx + 1 else nx) ∧
        σ'.vars "nw" = (if s = 0 then nw else nw + 1) ∧
        σ'.vars "Ln" = σ.vars "Ln" ∧ σ'.out = σ.out) 40 := by
  have hc : z.getD p0 0 < B := by
    rw [List.getD_eq_getElem _ _ hp]; exact hz _ (List.getElem_mem hp)
  run_vcg
  all_goals have hA := ‹σ.arrs "a" = z›
  all_goals have hW := ‹σ.arrs "w" = wa›
  all_goals have hP := ‹σ.vars "p" = p0›
  all_goals have hS := ‹σ.vars "st" = s›
  all_goals have hX := ‹σ.vars "nx" = nx›
  all_goals have hN := ‹σ.vars "nw" = nw›
  all_goals try simp [Env.setVar, Env.setArr, hA, hW, hP, hS, hX, hN] at *
  all_goals try omega
  all_goals try simp_all

def uLoop : Com := .seq (.assign "p" (.lit 0)) (.while (.lt (V "p") (V "Ln")) uBody)

/-- The invariant: the variables and the array `w` reflect the model. -/
inductive UInv (z : List ℕ) (σ : Env) : Prop where
  | mk
    (ha : σ.arrs "a" = z)
    (hLn : σ.vars "Ln" = z.length)
    (hp : σ.vars "p" ≤ z.length)
    (hst : σ.vars "st" = (uAt z (σ.vars "p")).st)
    (hnx : σ.vars "nx" = (uAt z (σ.vars "p")).xs.length)
    (hnw : σ.vars "nw" = (uAt z (σ.vars "p")).xs.length + (uAt z (σ.vars "p")).ys.length)
    (hw : (σ.arrs "w").take (σ.vars "nw") = (uAt z (σ.vars "p")).xs ++ (uAt z (σ.vars "p")).ys)
    (hwl : z.length ≤ (σ.arrs "w").length)
    (hout : σ.out = [])

theorem UInv.hLn
    {z : List ℕ} {σ : Env}
    (h : UInv z σ) : σ.vars "Ln" = z.length :=
  match h with | ⟨_, x, _, _, _, _, _, _, _⟩ => x

theorem UInv.hp
    {z : List ℕ} {σ : Env}
    (h : UInv z σ) : σ.vars "p" ≤ z.length :=
  match h with | ⟨_, _, x, _, _, _, _, _, _⟩ => x

theorem uLoop_spec (z : List ℕ) (hB : z.length + 4 < B) (hz : ∀ v ∈ z, v < B) :
    Spec B (fun σ => UInv z (σ.setVar "p" 0)) uLoop
      (fun _ σ' => UInv z σ' ∧ σ'.vars "p" = z.length) ((40 + 4) * z.length + 6) := by
  refine Spec.forRangeZero "p" "Ln" (UInv z) z.length 40 (by omega) (fun _ h => h.hp)
    (fun _ h => h.hLn) ?_
  intro σ ⟨⟨ha, hLn, hple, hst, hnx, hnw, hw, hwl, hout⟩, hlt⟩
  set u := uAt z (σ.vars "p") with hu
  have hg := ugood_uAt z (σ.vars "p") hple
  rw [← hu] at hg
  obtain ⟨g1, g2, g3⟩ := hg
  obtain ⟨σ', r, q1, q2, q3, q4, q5, q6, q7, q8⟩ := uBody_spec (B := B) z (σ.arrs "w")
    (σ.vars "p") u.st u.xs.length (u.xs.length + u.ys.length) hlt g1 (by omega) hB (by omega)
    (by omega) hz σ ⟨ha, rfl, rfl, hst, hnx, hnw⟩
  refine ⟨σ', r, ⟨q1, by rw [q7]; exact hLn, by omega, ?_, ?_, ?_, ?_, ?_, by rw [q8]; exact hout⟩,
    q3⟩
  all_goals try rw [q3, uAt_succ hlt, ← hu]
  · rw [q4]; unfold ustep; split_ifs <;> simp_all
  · rw [q5]; unfold ustep; split_ifs <;> simp_all
  · rw [q6]; unfold ustep; split_ifs <;> simp_all; omega
  · rw [q6, q2]
    rw [hnw] at hw
    unfold ustep
    by_cases h0 : u.st = 0
    · simp only [h0, if_true]
      split_ifs <;> exact hw
    · have hys : u.st = 1 → u.ys = [] := fun h => g2 (by omega)
      simp only [h0, if_false]
      rw [TokProg.take_set_succ _ _ _ (by omega), hw]
      split_ifs with h1
      · simp [hys h1]
      · simp
  · rw [q2]; split_ifs
    · exact hwl
    · rw [List.length_set]; exact hwl

end Lax391470Proofs.VUnpair
