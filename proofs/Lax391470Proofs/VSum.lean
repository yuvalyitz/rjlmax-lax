import Lax391470Proofs.L1Check

/-!
The sum of the first `T` tokens: an offset that exceeds every number in sight.
-/

namespace Lax391470Proofs.VSum

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.L1Check (V add)

def sumTo (t : List ℕ) (k : ℕ) : ℕ := (t.take k).sum

lemma sumTo_zero (t : List ℕ) : sumTo t 0 = 0 := by simp [sumTo]

lemma sumTo_succ {t : List ℕ} {k : ℕ} (hk : k < t.length) :
    sumTo t (k + 1) = sumTo t k + t.getD k 0 := by
  unfold sumTo
  rw [List.take_add_one, List.sum_append, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hk]
  simp

lemma sumTo_mono (t : List ℕ) {k k' : ℕ} (h : k ≤ k') (hk' : k' ≤ t.length) :
    sumTo t k ≤ sumTo t k' := by
  induction k', h using Nat.le_induction with
  | base => exact le_refl _
  | succ m hm ih =>
    rw [sumTo_succ (by omega)]
    have := ih (by omega)
    omega

lemma getD_le_sumTo (t : List ℕ) {k T : ℕ} (hk : k < T) (hT : T ≤ t.length) :
    t.getD k 0 ≤ sumTo t T := by
  have h1 := sumTo_succ (t := t) (k := k) (by omega)
  have h2 := sumTo_mono t (k := k + 1) (k' := T) (by omega) hT
  omega

variable {B : ℕ}

def sumBody : Com :=
  .seq (.assign "O" (add (V "O") (.get "TK" (V "sk")))) (.assign "sk" (add (V "sk") (.lit 1)))

theorem sumBody_spec (t : List ℕ) (k o : ℕ) (hk : k < t.length) (hB : o + t.getD k 0 < B)
    (hkB : k + 1 < B) :
    Spec B (fun σ => σ.arrs "TK" = t ∧ σ.vars "sk" = k ∧ σ.vars "O" = o) sumBody
      (fun σ σ' => σ'.vars "O" = o + t.getD k 0 ∧ σ'.vars "sk" = k + 1 ∧ σ'.arrs = σ.arrs ∧
        σ'.vars "T" = σ.vars "T" ∧ σ'.out = σ.out) 10 := by
  run_vcg
  all_goals have e0 := ‹σ.arrs "TK" = t›
  all_goals have e1 := ‹σ.vars "sk" = k›
  all_goals have e2 := ‹σ.vars "O" = o›
  all_goals try simp [Env.setVar, e0, e1, e2] at *
  all_goals omega

def sumLoop : Com := .seq (.assign "sk" (.lit 0)) (.while (.lt (V "sk") (V "T")) sumBody)

def SInv (t : List ℕ) (Tn : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.arrs "TK" = t ∧ σ.vars "T" = Tn ∧ σ.vars "sk" ≤ Tn ∧ σ.vars "O" = sumTo t (σ.vars "sk") ∧
    σ.out = out0

theorem sumLoop_spec (t : List ℕ) (Tn : ℕ) (out0 : List ℕ) (hT : Tn ≤ t.length)
    (hB : sumTo t Tn + Tn + 2 < B) :
    Spec B (fun σ => SInv t Tn out0 (σ.setVar "sk" 0)) sumLoop
      (fun _ σ' => SInv t Tn out0 σ' ∧ σ'.vars "sk" = Tn) ((10 + 4) * Tn + 6) := by
  refine Spec.forRangeZero "sk" "T" (SInv t Tn out0) Tn 10 (by omega) (fun _ h => h.2.2.1)
    (fun _ h => h.2.1) ?_
  intro σ ⟨⟨hTK, hTv, hle, hO, hout⟩, hlt⟩
  have h1 := sumTo_succ (t := t) (k := σ.vars "sk") (by omega)
  have h2 := sumTo_mono t (k := σ.vars "sk" + 1) (k' := Tn) (by omega) hT
  obtain ⟨σ', r, q1, q2, q3, q4, q5⟩ := sumBody_spec (B := B) t (σ.vars "sk") _ (by omega)
    (by omega) (by omega) σ ⟨hTK, rfl, hO⟩
  exact ⟨σ', r, ⟨by rw [q3]; exact hTK, by rw [q4]; exact hTv, by omega, by rw [q1, q2, h1],
    by rw [q5]; exact hout⟩, q2⟩

end Lax391470Proofs.VSum
