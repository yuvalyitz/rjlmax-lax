import Lax391470Proofs.TokLoop

/-!
One complete run of the tokenizer over a prefix of an array: reset, ask the format, scan.
-/

namespace Lax391470Proofs.TokRun

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.Bits Lax391470Proofs.TokModel Lax391470Proofs.TokScan
open Lax391470Proofs.TokProg Lax391470Proofs.TokLoop

/-- Start over, on the first `len` cells. -/
def reset (len : String) : Com :=
  .seq (.assign "Ln" (V len)) (.seq (set "ph" 0) (.seq (set "L" 0) (.seq (set "val" 0)
    (.seq (set "pw" 1) (.seq (set "i" 0) (set "T" 0))))))

variable {B : ℕ}

theorem reset_spec (len : String) (n : ℕ) (hB : n + 2 < B) :
    Spec B (fun σ => σ.vars len = n) (reset len)
      (fun σ σ' => σ'.vars "Ln" = n ∧ σ'.vars "ph" = 0 ∧ σ'.vars "L" = 0 ∧ σ'.vars "val" = 0 ∧
        σ'.vars "pw" = 1 ∧ σ'.vars "i" = 0 ∧ σ'.vars "T" = 0 ∧ σ'.arrs = σ.arrs ∧
        σ'.out = σ.out) 20 := by
  run_vcg
  all_goals try simp_all [Env.setVar]

def tokRun (arr len : String) (nk : Com) : Com :=
  .seq (reset len) (.seq nk (scanLoop arr nk))

variable {E : Format} {Knk : ℕ}

/-- **A run of the tokenizer** over the word `y` at the start of the array `arr`. -/
theorem tokRun_spec (arr len : String) (nk : Com) (harr : arr ≠ "TK") (y : List ℕ) (cap : ℕ)
    (hcap : y.length ≤ cap)
    (hnk : NkSpec B (2 ^ y.length) E y.length nk Knk)
    (hB : 2 ^ (y.length + 1) + y.length + 8 ≤ B) (hy : ∀ v ∈ y, v < B) :
    Spec B (fun σ => (σ.arrs arr).take y.length = y ∧ σ.vars len = y.length ∧
        cap ≤ (σ.arrs "TK").length ∧ σ.out = []) (tokRun arr len nk)
      (fun _ σ' => Refl E (run E init (bitsOf y)) σ' ∧ σ'.out = [] ∧
        cap ≤ (σ'.arrs "TK").length)
      (20 + Knk + ((100 + Knk + 4) * y.length + 6)) := by
  intro σ ⟨ha, hl, hTK, hout⟩
  have hpow : y.length < 2 ^ (y.length + 1) := Nat.lt_of_lt_of_le Nat.lt_two_pow_self
    (Nat.pow_le_pow_right (by omega) (by omega))
  obtain ⟨σ1, r1, e1, e2, e3, e4, e5, e6, e7, ea, eo⟩ :=
    reset_spec (B := B) len y.length (by omega) σ hl
  obtain ⟨σ2, r2, k2, v2, a2, o2, -⟩ := hnk [] (fun k hk => by simp at hk) (by simp) σ1
    ⟨⟨by simpa using e7, by simp⟩, fun t ht => by simp at ht⟩
  have sv : ∀ x ∈ scanVars, σ2.vars x = σ1.vars x := v2
  obtain ⟨σ3, r3, I3, p3⟩ := scanLoop_spec (B := B) arr nk harr y cap hcap hnk hB hy σ2 (by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [Env.setVar]
    all_goals try simp [stAt, bitsOf, init]
    · rw [sv "ph" (by simp [scanVars])]; exact e2
    · rw [sv "L" (by simp [scanVars])]; exact e3
    · rw [sv "val" (by simp [scanVars])]; exact e4
    · rw [sv "pw" (by simp [scanVars])]; exact e5
    · rw [sv "i" (by simp [scanVars])]; exact e6
    · rw [sv "T" (by simp [scanVars])]; exact e7
    · exact k2
    · rw [a2, ea]; exact ha
    · rw [sv "Ln" (by simp [scanVars])]; exact e1
    · rw [a2, ea]; exact hTK
    · rw [o2, eo]; exact hout)
  have hst : stAt E y (σ3.vars "p") = run E init (bitsOf y) := by
    rw [p3]; unfold stAt; rw [List.take_length]
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by omega), ?_, I3.hout, I3.hTK⟩
  rw [← hst]; exact I3.refl

end Lax391470Proofs.TokRun
