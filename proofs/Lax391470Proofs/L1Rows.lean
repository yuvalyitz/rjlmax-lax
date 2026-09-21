import Lax391470Proofs.OutSteps
import Lax391470Proofs.L1Model

/-!
The rows of the stacked instance, as output steps.
-/

namespace Lax391470Proofs.L1Rows

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.Bits Lax391470Proofs.OutSteps Lax391470Proofs.L1Lists
open Lax391470Proofs.L1Model

variable {B : ℕ} (p q : ℕ)

/-- Index `2 + (3 i + c)`. -/
def ieOrd (c : ℕ) : Expr := .bin .add (.lit (2 + c)) (.bin .mul (.lit 3) (V "i"))

/-- Index `b3 + (4 i + c)`. -/
def ieQuad (c : ℕ) : Expr := .bin .add (V "b3") (.bin .add (.bin .mul (.lit 4) (V "i")) (.lit c))

lemma eval_ieOrd (c : ℕ) (σ : Env) (h : 3 * σ.vars "i" + c + 4 < B) :
    (ieOrd c).evalB B σ = some (2 + (3 * σ.vars "i" + c)) := by
  have e := evalB_bin (op := .add) (evalB_lit (B := B) (σ := σ) (n := 2 + c) (by omega))
    (evalB_bin (op := .mul) (evalB_lit (B := B) (σ := σ) (n := 3) (by omega))
      (evalB_var (x := "i") (by omega)) (by simp; omega)) (by simp; omega)
  rw [ieOrd, e]; congr 1; simp; omega

lemma eval_ieQuad (c : ℕ) (σ : Env) (h : σ.vars "b3" + 4 * σ.vars "i" + c + 4 < B) :
    (ieQuad c).evalB B σ = some (σ.vars "b3" + (4 * σ.vars "i" + c)) := by
  have e := evalB_bin (op := .add) (evalB_var (B := B) (σ := σ) (x := "b3") (by omega))
    (evalB_bin (op := .add) (evalB_bin (op := .mul) (evalB_lit (B := B) (σ := σ) (n := 4)
      (by omega)) (evalB_var (x := "i") (by omega)) (by simp; omega))
      (evalB_lit (n := c) (by omega)) (by simp; omega)) (by simp; omega)
  rw [ieQuad, e]; simp

/-- Every token is small. -/
def TokOK (B Sz T : ℕ) (t : List ℕ) : Prop :=
  T ≤ t.length ∧ ∀ k < T, t.getD k 0 + 4 < B ∧ (t.getD k 0).size ≤ Sz

variable (Sz T : ℕ)

theorem tkOrd (c : ℕ) :
    OStep B (emitTK (ieOrd c))
      (fun t i _ => TokOK B Sz T t ∧ 2 + (3 * i + c) < T ∧ 3 * i + c + 4 < B)
      (fun t i _ => bitsNat (t.getD (2 + (3 * i + c)) 0)) (1 + (ieOrd c).size + (48 * Sz + 50)) :=
  oEmitTK (ieOrd c) (fun i _ => 2 + (3 * i + c)) Sz _
    (fun σ h => eval_ieOrd c σ h.2.2)
    (fun t i _ h => ⟨lt_of_lt_of_le h.2.1 h.1.1, by omega, (h.1.2 _ h.2.1).1, (h.1.2 _ h.2.1).2⟩)

theorem tkQuad (c : ℕ) :
    OStep B (emitTK (ieQuad c))
      (fun t i b3 => TokOK B Sz T t ∧ b3 + (4 * i + c) < T ∧ b3 + 4 * i + c + 4 < B)
      (fun t i b3 => bitsNat (t.getD (b3 + (4 * i + c)) 0))
      (1 + (ieQuad c).size + (48 * Sz + 50)) :=
  oEmitTK (ieQuad c) (fun i b3 => b3 + (4 * i + c)) Sz _
    (fun σ h => eval_ieQuad c σ h.2.2)
    (fun t i _ h => ⟨lt_of_lt_of_le h.2.1 h.1.1, by omega, (h.1.2 _ h.2.1).1, (h.1.2 _ h.2.1).2⟩)

theorem selOrd (hp : p + 4 < B) (hq : q + 4 < B) (hs : ∀ v, v + 4 < B → v.size ≤ Sz) :
    OStep B (emitSel p q (ieOrd 2))
      (fun t i _ => TokOK B Sz T t ∧ 2 + (3 * i + 2) < T ∧ 3 * i + 2 + 4 < B)
      (fun t i _ => bitsNat (if t.getD (2 + (3 * i + 2)) 0 = 0 then q else p))
      (1 + (ieOrd 2).size + (48 * Sz + 60)) :=
  oEmitSel p q (ieOrd 2) (fun i _ => 2 + (3 * i + 2)) Sz _ hp hq hs
    (fun σ h => eval_ieOrd 2 σ h.2.2)
    (fun t i _ h => ⟨lt_of_lt_of_le h.2.1 h.1.1, by omega,
      by have := (h.1.2 (2 + (3 * i + 2)) h.2.1).1; omega⟩)

/-- The record of an ordinary job. -/
def ordRowCom : Com :=
  .seq (.write (.lit 0)) (.seq (emitTK (ieOrd 0)) (.seq (.write (.lit 0))
    (.seq (emitTK (ieOrd 1)) (emitSel p q (ieOrd 2)))))

theorem ordRow_step (hp : p + 4 < B) (hq : q + 4 < B) (hs : ∀ v, v + 4 < B → v.size ≤ Sz) :
    OStep B (ordRowCom p q)
      (fun t i _ => TokOK B Sz T t ∧ 2 + (3 * i + 2) < T ∧ 3 * i + 8 < B)
      (fun t i _ => ordRow p q t i) (3 * (48 * Sz + 70) + 20) := by
  refine ((oWrite (B := B) 0 (by omega)).seq ((tkOrd Sz T 0).seq ((oWrite (B := B) 0 (by omega)).seq
    ((tkOrd Sz T 1).seq (selOrd p q Sz T hp hq hs))))).weaken ?_ ?_ ?_
  · intro t i b3 ⟨h1, h2, h3⟩
    exact ⟨trivial, ⟨h1, by omega, by omega⟩, trivial, ⟨h1, by omega, by omega⟩, h1, h2, by omega⟩
  · intro t i b3 _
    simp [ordRow, List.append_assoc]
  · simp [ieOrd, Expr.size]; omega

open Lax391470Proofs.L2Parts in
/-- The five records of a pair. -/
def quadRowCom : Com :=
  .seq (emitInt p q (p + q)) (.seq (emitInt p q (p + 2 * q)) (.seq (emitLit q)
  (.seq (emitInt p q q) (.seq (.write (.lit 0)) (.seq (emitTK (ieQuad 0)) (.seq (emitLit p)
  (.seq (emitInt p q 0) (.seq (.write (.lit 0)) (.seq (emitTK (ieQuad 1)) (.seq (emitLit p)
  (.seq (emitInt p q p) (.seq (.write (.lit 0)) (.seq (emitTK (ieQuad 2)) (.seq (emitLit q)
  (.seq (emitInt p q 0) (.seq (.write (.lit 0)) (.seq (emitTK (ieQuad 3)) (emitLit q))))))))))))))))))

/-- What the pair row needs. -/
def PQuad (B Sz T p q : ℕ) (t : List ℕ) (i b3 : ℕ) : Prop :=
  TokOK B Sz T t ∧ b3 = 2 + 3 * t.getD 0 0 ∧ b3 + (4 * i + 3) < T ∧ b3 + 4 * i + 8 < B ∧
    (p + 2 * q) * (i + 1) + (p + 2 * q) + 8 < B ∧ i + 2 < B

theorem quadRow_step (hpq : p + 2 * q + 4 < B) (hs : ∀ v, v + 4 < B → v.size ≤ Sz) :
    OStep B (quadRowCom p q) (PQuad B Sz T p q)
      (fun t i _ => quadRow p q t (t.getD 0 0) i) (19 * (48 * Sz + 80)) := by
  have hps : p.size ≤ Sz := hs p (by omega)
  have hqs : q.size ≤ Sz := hs q (by omega)
  have I := fun a => oEmitInt (B := B) p q a Sz (by omega) hs
  have W := oWrite (B := B) 0 (by omega)
  have Lp := oEmitLit (B := B) p Sz (by omega) hps
  have Lq := oEmitLit (B := B) q Sz (by omega) hqs
  refine ((I (p + q)).seq ((I (p + 2 * q)).seq (Lq.seq
    ((I q).seq (W.seq ((tkQuad Sz T 0).seq (Lp.seq
    ((I 0).seq (W.seq ((tkQuad Sz T 1).seq (Lp.seq
    ((I p).seq (W.seq ((tkQuad Sz T 2).seq (Lq.seq
    ((I 0).seq (W.seq ((tkQuad Sz T 3).seq Lq)))))))))))))))))).weaken ?_ ?_ ?_
  · intro t i b3 ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨⟨by omega, h6⟩, ⟨by omega, h6⟩, trivial,
      ⟨by omega, h6⟩, trivial, ⟨h1, by omega, by omega⟩, trivial,
      ⟨by omega, h6⟩, trivial, ⟨h1, by omega, by omega⟩, trivial,
      ⟨by omega, h6⟩, trivial, ⟨h1, by omega, by omega⟩, trivial,
      ⟨by omega, h6⟩, trivial, ⟨h1, by omega, by omega⟩, trivial⟩
  · rintro t i b3 ⟨-, h2, -⟩
    have e0 : b3 + (4 * i + 0) = 2 + (3 * t.getD 0 0 + (4 * i + 0)) := by omega
    have e1 : b3 + (4 * i + 1) = 2 + (3 * t.getD 0 0 + (4 * i + 1)) := by omega
    have e2 : b3 + (4 * i + 2) = 2 + (3 * t.getD 0 0 + (4 * i + 2)) := by omega
    have e3 : b3 + (4 * i + 3) = 2 + (3 * t.getD 0 0 + (4 * i + 3)) := by omega
    simp only [e0, e1, e2, e3, quadRow, List.append_assoc]
  · clear I W Lp Lq hs hps hqs hpq
    have hsz : ∀ c, (ieQuad c).size ≤ 8 := fun c => by simp [ieQuad, Expr.size]
    have h0 := hsz 0; have h1 := hsz 1; have h2 := hsz 2; have h3 := hsz 3
    generalize (ieQuad 0).size = a0 at *
    generalize (ieQuad 1).size = a1 at *
    generalize (ieQuad 2).size = a2 at *
    generalize (ieQuad 3).size = a3 at *
    linarith

end Lax391470Proofs.L1Rows
