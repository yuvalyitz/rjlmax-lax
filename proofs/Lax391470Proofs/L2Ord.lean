import Lax391470Proofs.ReadAll

/-!
The numbers of one ordinary job, computed from the dimensions of the construction and the
table of active blocks. Stated against pure mirror functions of the program.
-/

namespace Lax391470Proofs.L2Ord

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

abbrev V (s : String) : Expr := .var s
abbrev add (e f : Expr) : Expr := .bin .add e f
abbrev sub (e f : Expr) : Expr := .bin .sub e f
abbrev mul (e f : Expr) : Expr := .bin .mul e f
abbrev div (e f : Expr) : Expr := .bin .div e f

variable (p q : ℕ)

/-- Release time, deadline and length bit of ordinary job `o`, as the program computes
them from `nn` variables, `m` clauses, section length `S` and the table `act`. -/
def rVal (nn S o : ℕ) : ℕ :=
  if o < 6 * nn then
    if o - 3 * (o / 3) = 0 then
      (if o / 3 - o / 3 / 2 * 2 = 0 then S * (o / 3) + 1 else S * (o / 3) + (q + 1))
    else if o - 3 * (o / 3) = 1 then S * (o / 3)
    else S * (o / 3) + S - q
  else 0

def dVal (nn m S : ℕ) (act : ℕ → ℕ) (o : ℕ) : ℕ :=
  if o < 6 * nn then
    if o - 3 * (o / 3) = 0 then
      (if o / 3 - o / 3 / 2 * 2 = 0 then S * (o / 3) + 2 * q else S * (o / 3) + (p + q))
    else if o - 3 * (o / 3) = 1 then S * (o / 3) + (p + 2 * q + 1)
    else S * (o / 3) + S
  else if o < 6 * nn + m then
    (if act ((2 * nn - 1) * m + (o - 6 * nn)) = 0
      then S * (2 * nn - 1) + (p + 2 * q) + (o - 6 * nn) * (p + q) + (p + q - 1)
      else S * (2 * nn - 1) + (p + 2 * q) + (o - 6 * nn) * (p + q) + (p + q))
  else
    (if act (o - 6 * nn - m) = 0
      then (p + 2 * q) + (o - 6 * nn - m) * (p + q) + (p + q - 1)
      else (p + 2 * q) + (o - 6 * nn - m) * (p + q) + (p + q))

def lgVal (nn m o : ℕ) : ℕ :=
  if o < 6 * nn then
    (if o - 3 * (o / 3) = 1 then o / 3 - o / 3 / 2 * 2 else 0)
  else if o < 6 * nn + m then 1 else 0

/-- The section part: job `o < 6·nn`. -/
def calcSec : Com :=
  .seq (.assign "s" (div (V "o") (.lit 3)))
  (.seq (.assign "c" (sub (V "o") (mul (.lit 3) (V "s"))))
  (.seq (.assign "par" (sub (V "s") (mul (div (V "s") (.lit 2)) (.lit 2))))
  (.seq (.assign "base" (mul (V "S") (V "s")))
    (.ite (.eq (V "c") (.lit 0))
      (.seq (.assign "lg" (.lit 0))
        (.ite (.eq (V "par") (.lit 0))
          (.seq (.assign "r" (add (V "base") (.lit 1))) (.assign "d" (add (V "base") (.lit (2 * q)))))
          (.seq (.assign "r" (add (V "base") (.lit (q + 1))))
            (.assign "d" (add (V "base") (.lit (p + q)))))))
      (.ite (.eq (V "c") (.lit 1))
        (.seq (.assign "lg" (V "par"))
          (.seq (.assign "r" (V "base")) (.assign "d" (add (V "base") (.lit (p + 2 * q + 1))))))
        (.seq (.assign "lg" (.lit 0))
          (.seq (.assign "r" (sub (add (V "base") (V "S")) (.lit q)))
            (.assign "d" (add (V "base") (V "S"))))))))))

variable {B : ℕ} (nn m S : ℕ) (act : ℕ → ℕ)

set_option maxHeartbeats 2000000 in
theorem calcSec_spec :
    Spec B (fun σ => σ.vars "S" = S ∧ σ.vars "o" < 6 * nn ∧
        S * (σ.vars "o" / 3) + S + p + 2 * q + 4 < B ∧ σ.vars "o" < B ∧ 3 * (σ.vars "o" / 3) < B ∧
        S < B) (calcSec p q)
      (fun σ σ' => σ'.vars "r" = rVal q nn S (σ.vars "o") ∧
        σ'.vars "d" = dVal p q nn m S act (σ.vars "o") ∧ σ'.vars "lg" = lgVal nn m (σ.vars "o"))
      60 := by
  run_vcg
  all_goals have hS := ‹σ.vars "S" = S›
  all_goals try simp [Env.setVar] at *
  all_goals try (rw [hS]; omega)
  all_goals try simp_all [rVal, dVal, lgVal]

/-- The tail part: job `o ≥ 6·nn`, one of the unconnected pending jobs. -/
def calcTail : Com :=
  .seq (.assign "r" (.lit 0))
  (.seq (.ite (.lt (V "o") (V "n6m"))
      (.seq (.assign "j" (sub (V "o") (V "n6")))
        (.seq (.assign "sec" (sub (mul (.lit 2) (V "nn")) (.lit 1))) (.assign "lg" (.lit 1))))
      (.seq (.assign "j" (sub (sub (V "o") (V "n6")) (V "m")))
        (.seq (.assign "sec" (.lit 0)) (.assign "lg" (.lit 0)))))
  (.seq (.assign "cs" (add (add (mul (V "S") (V "sec")) (.lit (p + 2 * q)))
      (mul (V "j") (.lit (p + q)))))
    (.ite (.eq (.get "act" (add (mul (V "sec") (V "m")) (V "j"))) (.lit 0))
      (.assign "d" (add (V "cs") (.lit (p + q - 1))))
      (.assign "d" (add (V "cs") (.lit (p + q)))))))

set_option maxHeartbeats 2000000 in
theorem calcTail_spec :
    Spec B (fun σ => σ.vars "S" = S ∧ σ.vars "nn" = nn ∧ σ.vars "m" = m ∧
        σ.vars "n6" = 6 * nn ∧ σ.vars "n6m" = 6 * nn + m ∧
        ¬ σ.vars "o" < 6 * nn ∧ σ.vars "o" < 6 * nn + 2 * m ∧
        (2 * nn - 1) * m + m ≤ (σ.arrs "act").length ∧
        (σ.arrs "act").getD ((2 * nn - 1) * m + (σ.vars "o" - 6 * nn)) 0 =
          act ((2 * nn - 1) * m + (σ.vars "o" - 6 * nn)) ∧
        (σ.arrs "act").getD (σ.vars "o" - 6 * nn - m) 0 = act (σ.vars "o" - 6 * nn - m) ∧
        S * (2 * nn - 1) + (p + 2 * q) + 2 * (m * (p + q)) + (p + q) + 4 < B ∧
        (σ.vars "o" - 6 * nn) * (p + q) ≤ 2 * (m * (p + q)) ∧
        (σ.vars "o" - 6 * nn - m) * (p + q) ≤ 2 * (m * (p + q)) ∧
        6 * nn + 2 * m < B ∧ (2 * nn - 1) * m + m < B ∧ S < B ∧
        (∀ t, (σ.arrs "act").getD t 0 < B)) (calcTail p q)
      (fun σ σ' => σ'.vars "r" = rVal q nn S (σ.vars "o") ∧
        σ'.vars "d" = dVal p q nn m S act (σ.vars "o") ∧ σ'.vars "lg" = lgVal nn m (σ.vars "o"))
      60 := by
  run_vcg
  all_goals have hS := ‹σ.vars "S" = S›
  all_goals have hnn := ‹σ.vars "nn" = nn›
  all_goals have hm := ‹σ.vars "m" = m›
  all_goals have h6 := ‹σ.vars "n6" = 6 * nn›
  all_goals have h6m := ‹σ.vars "n6m" = 6 * nn + m›
  all_goals have hact := ‹∀ t, (σ.arrs "act").getD t 0 < B›
  all_goals try simp [Env.setVar] at *
  all_goals try simp only [hS, hnn, hm, h6, h6m] at *
  all_goals try omega
  all_goals try (simp_all [rVal, dVal, lgVal]; done)
  all_goals try exact hact _
  all_goals (
    have h1 : ¬ σ.vars "o" < 6 * nn := by omega
    have h2 : ¬ σ.vars "o" < 6 * nn + m := by omega
    simp only [rVal, dVal, lgVal, if_neg h1, if_neg h2]
    simp_all)

end Lax391470Proofs.L2Ord
