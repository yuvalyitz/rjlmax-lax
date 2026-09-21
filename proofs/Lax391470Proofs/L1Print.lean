import Lax391470Proofs.L1Rows
import Lax391470Proofs.L1Parts

/-!
Printing the stacked instance: the number of jobs, the ordinary rows, the pair rows.
-/

namespace Lax391470Proofs.L1Print

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.Bits Lax391470Proofs.OutSteps Lax391470Proofs.L2Parts
open Lax391470Proofs.L1Rows Lax391470Proofs.L1Model

variable {B : ℕ} (p q : ℕ)

def rowLoop (mv : String) (c : Com) : Com :=
  .seq (.assign "i" (.lit 0))
    (.while (.lt (.var "i") (.var mv)) (.seq c (.assign "i" (.bin .add (V "i") (.lit 1)))))

def printPart : Com :=
  .seq (emitVar "jobs") (.seq (rowLoop "n" (ordRowCom p q)) (rowLoop "N" (quadRowCom p q)))

/-- The cost of printing. -/
def Kprint (Sz n N : ℕ) : ℕ :=
  (48 * Sz + 50) + ((3 * (48 * Sz + 70) + 20 + 10 + 4) * n + 6) +
    ((19 * (48 * Sz + 80) + 10 + 4) * N + 6)

theorem printPart_spec (arr : List ℕ) (n N T Sz : ℕ) (out0 : List ℕ)
    (hT : T = 2 + 3 * n + 4 * N) (htok : TokOK B Sz T arr) (h0 : arr.getD 0 0 = n)
    (hB : 4 * T + (p + 2 * q) * (N + 2) + 16 < B) (hs : ∀ v, v + 4 < B → v.size ≤ Sz) :
    Spec B (fun σ => σ.arrs "TK" = arr ∧ σ.vars "n" = n ∧ σ.vars "N" = N ∧
        σ.vars "b3" = 2 + 3 * n ∧ σ.vars "jobs" = n + 5 * N ∧ σ.out = out0) (printPart p q)
      (fun _ σ' => σ'.out = out0 ++ (bitsNat (n + 5 * N) ++
        (List.range n).flatMap (ordRow p q arr) ++
        (List.range N).flatMap (quadRow p q arr n))) (Kprint Sz n N) := by
  intro σ ⟨hA, hn, hN, hb3, hj, ho⟩
  have hpq : (p + 2 * q) * 2 ≤ (p + 2 * q) * (N + 2) := Nat.mul_le_mul_left _ (by omega)
  -- the number of jobs
  obtain ⟨σ1, r1, o1, v1, a1⟩ := emitVar_spec (B := B) "jobs" Sz σ
    ⟨by rw [hj]; omega, by rw [hj]; exact hs _ (by omega)⟩
  have A1 : σ1.arrs "TK" = arr := by rw [a1]; exact hA
  -- the ordinary rows
  obtain ⟨σ2, r2, ⟨a2, v2, -, o2⟩, i2⟩ := oLoop (B := B) "n" (ordRowCom p q) _ _ _
    (ordRow_step (B := B) p q Sz T (by omega) (by omega) hs) σ1.arrs σ1.vars n σ1.out (by decide)
    (by decide) ((v1 "n" (by decide)).trans hn) (by omega)
    (fun i hi => ⟨by rw [A1]; exact htok, by omega, by omega⟩) σ1
    ⟨rfl, fun y _ hyi => by simp [Env.setVar, hyi], by simp [Env.setVar], by simp [Env.setVar]⟩
  -- the pair rows
  have A2 : σ2.arrs "TK" = arr := by rw [a2]; exact A1
  have vN2 : σ2.vars "N" = N := by
    rw [v2 "N" (by decide) (by decide), v1 "N" (by decide)]; exact hN
  have vb2 : σ2.vars "b3" = 2 + 3 * n := by
    rw [v2 "b3" (by decide) (by decide), v1 "b3" (by decide)]; exact hb3
  obtain ⟨σ3, r3, ⟨-, -, -, o3⟩, i3⟩ := oLoop (B := B) "N" (quadRowCom p q) _ _ _
    (quadRow_step (B := B) p q Sz T (by omega) hs) σ2.arrs σ2.vars N σ2.out (by decide)
    (by decide) vN2 (by omega)
    (fun i hi => by
      have hm : (p + 2 * q) * (i + 1) + (p + 2 * q) ≤ (p + 2 * q) * (N + 2) := by
        have := Nat.mul_le_mul_left (p + 2 * q) (show i + 2 ≤ N + 2 by omega)
        rw [show i + 2 = (i + 1) + 1 by ring, Nat.mul_succ] at this
        exact this
      exact ⟨by rw [A2]; exact htok, by rw [A2, h0, vb2], by rw [vb2]; omega,
        by rw [vb2]; omega, by omega, by omega⟩) σ2
    ⟨rfl, fun y _ hyi => by simp [Env.setVar, hyi], by simp [Env.setVar], by simp [Env.setVar]⟩
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by unfold Kprint; omega), ?_⟩
  show σ3.out = _
  rw [o3, o2, o1, ho, hj, A2, A1, i2, i3]
  simp only [h0, List.append_assoc]

end Lax391470Proofs.L1Print
