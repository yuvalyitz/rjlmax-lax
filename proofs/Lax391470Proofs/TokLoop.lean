import Lax391470Proofs.TokBound
import Lax391470Proofs.Bits

/-!
The tokenizer loop: one bit of the input array a step.
-/

namespace Lax391470Proofs.TokLoop

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.TokModel Lax391470Proofs.TokScan Lax391470Proofs.TokProg
open Lax391470Proofs.TokBound Lax391470Proofs.Bits Lax434930.PolynomialTime

variable (E : Format)

/-- The state after the first `t` entries. -/
def stAt (y : List ℕ) (t : ℕ) : St := run E init (bitsOf (y.take t))

lemma stAt_succ {y : List ℕ} {t : ℕ} (ht : t < y.length) :
    stAt E y (t + 1) = step E (stAt E y t) (decide (y.getD t 0 ≠ 0)) := by
  unfold stAt
  rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some]
  simp only [bitsOf, List.map_append, List.map_cons, List.map_nil]
  rw [run_append, run_cons, run_nil, List.getD_eq_getElem _ _ ht]

lemma bd_stAt (y : List ℕ) : ∀ t ≤ y.length, Bd (stAt E y t) t
  | 0, _ => by simpa [stAt, bitsOf] using bd_init
  | t + 1, ht => by
    rw [stAt_succ E (by omega)]
    exact bd_step E (bd_stAt y t (by omega)) _

/-- Read entry `p` of the input, normalised to a bit. -/
def readBit (arr : String) : Com :=
  .seq (.assign "c" (.get arr (V "p"))) (.ite (.eq (V "c") (.lit 0)) .skip (set "c" 1))

variable {B : ℕ}

theorem readBit_spec (arr : String) :
    Spec B (fun σ => σ.vars "p" < (σ.arrs arr).length ∧ σ.vars "p" < B ∧
        (σ.arrs arr).getD (σ.vars "p") 0 < B ∧ 1 < B) (readBit arr)
      (fun σ σ' => σ'.vars "c" = (if (σ.arrs arr).getD (σ.vars "p") 0 ≠ 0 then 1 else 0) ∧
        (∀ y, y ≠ "c" → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
        σ'.inp = σ.inp) 10 := by
  run_vcg
  all_goals try simp only [Env.setVar] at *
  all_goals try simp_all

variable (arr : String) (nk : Com)

def scanBody : Com := .seq (readBit arr) (.seq (dispatch nk) (bump "p"))

def scanLoop : Com := .seq (set "p" 0) (.while (.lt (V "p") (V "Ln")) (scanBody arr nk))

variable {E} {cap Knk : ℕ}

/-- The invariant of the loop. -/
inductive TInv (arr : String) (y : List ℕ) (cap : ℕ) (σ : Env) : Prop where
  | mk
    (refl : Refl E (stAt E y (σ.vars "p")) σ)
    (ha : (σ.arrs arr).take y.length = y)
    (hLn : σ.vars "Ln" = y.length)
    (hp : σ.vars "p" ≤ y.length)
    (hTK : cap ≤ (σ.arrs "TK").length)
    (hout : σ.out = [])

theorem TInv.refl
    {arr : String} {y : List ℕ} {cap : ℕ} {σ : Env}
    (h : TInv (E := E) arr y cap σ) : Refl E (stAt E y (σ.vars "p")) σ :=
  match h with | ⟨x, _, _, _, _, _⟩ => x

theorem TInv.hLn
    {arr : String} {y : List ℕ} {cap : ℕ} {σ : Env}
    (h : TInv (E := E) arr y cap σ) : σ.vars "Ln" = y.length :=
  match h with | ⟨_, _, x, _, _, _⟩ => x

theorem TInv.hp
    {arr : String} {y : List ℕ} {cap : ℕ} {σ : Env}
    (h : TInv (E := E) arr y cap σ) : σ.vars "p" ≤ y.length :=
  match h with | ⟨_, _, _, x, _, _⟩ => x

theorem TInv.hTK
    {arr : String} {y : List ℕ} {cap : ℕ} {σ : Env}
    (h : TInv (E := E) arr y cap σ) : cap ≤ (σ.arrs "TK").length :=
  match h with | ⟨_, _, _, _, x, _⟩ => x

theorem TInv.hout
    {arr : String} {y : List ℕ} {cap : ℕ} {σ : Env}
    (h : TInv (E := E) arr y cap σ) : σ.out = [] :=
  match h with | ⟨_, _, _, _, _, x⟩ => x

theorem scanBody_spec (harr : arr ≠ "TK") (y : List ℕ) (cap : ℕ) (hcap : y.length ≤ cap) (hnk : NkSpec B (2 ^ y.length) E y.length nk Knk)
    (hB : 2 ^ (y.length + 1) + y.length + 8 ≤ B) (hy : ∀ v ∈ y, v < B) :
    Spec B (fun σ => TInv (E := E) arr y cap σ ∧ σ.vars "p" < y.length) (scanBody arr nk)
      (fun σ σ' => TInv (E := E) arr y cap σ' ∧ σ'.vars "p" = σ.vars "p" + 1) (100 + Knk) := by
  intro σ ⟨hI, hp⟩
  obtain ⟨hR, ha, hLn, hple, hTK, hout⟩ := hI
  set s := stAt E y (σ.vars "p") with hs
  have hbd := bd_stAt E y (σ.vars "p") hple
  rw [← hs] at hbd
  have hpow : 2 ^ (σ.vars "p" + 1) ≤ 2 ^ y.length := Nat.pow_le_pow_right (by omega) (by omega)
  have hpow2 : (2 : ℕ) ^ (y.length + 1) = 2 * 2 ^ y.length := by ring
  have hdgp : 2 ^ s.dg.length ≤ 2 ^ (σ.vars "p") := Nat.pow_le_pow_right (by omega) hbd.dg
  have hpp : (2 : ℕ) ^ (σ.vars "p" + 1) = 2 * 2 ^ σ.vars "p" := by ring
  have hvlt := ofBits_lt s.dg
  -- read the bit
  have hal : y.length ≤ (σ.arrs arr).length := by
    have := congrArg List.length ha
    rw [List.length_take] at this; omega
  have hag : (σ.arrs arr).getD (σ.vars "p") 0 = y.getD (σ.vars "p") 0 := by
    conv_rhs => rw [← ha]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hp]
  obtain ⟨σ1, r1, c1, v1, a1, o1, i1⟩ := readBit_spec (B := B) arr σ
    ⟨by omega, by omega, by
      rw [hag, List.getD_eq_getElem _ _ hp]; exact hy _ (List.getElem_mem hp), by omega⟩
  have hR1 : Refl E s σ1 :=
    ⟨by rw [v1 _ (by decide)]; exact hR.ph, by rw [v1 _ (by decide)]; exact hR.L,
      by rw [v1 _ (by decide)]; exact hR.val, by rw [v1 _ (by decide)]; exact hR.pw,
      by rw [v1 _ (by decide)]; exact hR.i,
      ⟨by rw [v1 _ (by decide)]; exact hR.tok.1, by rw [a1]; exact hR.tok.2⟩,
      by rw [v1 _ (by decide)]; exact hR.kind⟩
  -- the step
  have h2y : 2 ≤ 2 ^ y.length := by
    calc (2 : ℕ) = 2 ^ 1 := rfl
      _ ≤ 2 ^ y.length := Nat.pow_le_pow_right (by omega) (by omega)
  have hstepB : StepB B (2 ^ y.length) y.length s :=
    ⟨by omega, by omega, h2y, by rw [hbd.val, hbd.pw]; omega, by have := hbd.ph; omega, by have := hbd.L; omega, by have := hbd.dg; omega,
      by rw [hbd.val, hbd.pw]; omega, by rw [hbd.pw]; omega, by have := hbd.T; omega,
      by have := hbd.T; omega, fun t ht => by have := hbd.tok t ht; omega⟩
  obtain ⟨σ2, r2, hR2, f1, f2, f3, f4, f5, f6, f7⟩ :=
    dispatch_spec nk hnk s (decide (y.getD (σ.vars "p") 0 ≠ 0)) hstepB
      (fun h => (run_inv E (bitsOf (y.take (σ.vars "p"))) h).1.fol)
      (fun h => (run_inv E (bitsOf (y.take (σ.vars "p"))) (le_of_eq h)).1.num (Or.inl h)) σ1
      ⟨hR1, by rw [c1, hag]; by_cases h0 : y.getD (σ.vars "p") 0 = 0 <;> simp,
        by rw [a1]; have := hbd.T; omega⟩
  -- advance
  have hp2 : σ2.vars "p" = σ.vars "p" := by rw [f1, v1 _ (by decide)]
  have r3 : Run B (bump "p") σ2 (σ2.setVar "p" (σ2.vars "p" + 1))
      (1 + (add (V "p") (.lit 1)).size) :=
    Run.assign (evalB_bin (evalB_var (by rw [hp2]; omega)) (evalB_lit (by omega))
      (by simp [hp2]; omega))
  refine ⟨_, (r1.seq (r2.seq r3)).mono (by simp [Expr.size]; omega), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have hst : stAt E y ((σ2.setVar "p" (σ2.vars "p" + 1)).vars "p") =
        step E s (decide (y.getD (σ.vars "p") 0 ≠ 0)) := by
      simp only [Env.setVar, if_true, hp2]
      rw [stAt_succ E hp]
    rw [hst]
    obtain ⟨g1, g2, g3, g4, g5, ⟨g6, g7⟩, g8⟩ := hR2
    exact ⟨by simpa [Env.setVar] using g1, by simpa [Env.setVar] using g2,
      by simpa [Env.setVar] using g3, by simpa [Env.setVar] using g4,
      by simpa [Env.setVar] using g5, ⟨by simpa [Env.setVar] using g6,
        by simpa [Env.setVar] using g7⟩, by simpa [Env.setVar] using g8⟩
  · simp only [Env.setVar]; rw [f4 arr harr, a1, ha]
  · simp [Env.setVar]; rw [f2, v1 _ (by decide), hLn]
  · simp [Env.setVar, hp2]; omega
  · simp only [Env.setVar]; rw [f7, a1]; exact hTK
  · simp only [Env.setVar]; rw [f5, o1, hout]
  · simp [Env.setVar, hp2]

theorem scanLoop_spec (harr : arr ≠ "TK") (y : List ℕ) (cap : ℕ) (hcap : y.length ≤ cap) (hnk : NkSpec B (2 ^ y.length) E y.length nk Knk)
    (hB : 2 ^ (y.length + 1) + y.length + 8 ≤ B) (hy : ∀ v ∈ y, v < B) :
    Spec B (fun σ => TInv (E := E) arr y cap (σ.setVar "p" 0)) (scanLoop arr nk)
      (fun _ σ' => TInv (E := E) arr y cap σ' ∧ σ'.vars "p" = y.length)
      ((100 + Knk + 4) * y.length + 6) :=
  Spec.forRangeZero "p" "Ln" (TInv (E := E) arr y cap) y.length (100 + Knk) (by
    have : y.length < 2 ^ (y.length + 1) := Nat.lt_of_lt_of_le Nat.lt_two_pow_self
      (Nat.pow_le_pow_right (by omega) (by omega))
    omega) (fun _ h => h.hp) (fun _ h => h.hLn) (scanBody_spec arr nk harr y cap hcap hnk hB hy)

end Lax391470Proofs.TokLoop
