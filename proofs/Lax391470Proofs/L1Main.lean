import Lax391470Proofs.L1Accept
import Lax391470Proofs.AuxNk

/-!
The whole reduction of Lemma 1 as one IMP+ program, and what it computes.
-/

namespace Lax391470Proofs.L1Main

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.Bits Lax391470Proofs.TokModel Lax391470Proofs.TokScan
open Lax391470Proofs.TokProg Lax391470Proofs.TokLoop Lax391470Proofs.TokBound
open Lax391470Proofs.AuxFormat Lax391470Proofs.AuxNk Lax391470Proofs.L1Parts
open Lax391470Proofs.L1Accept

variable (p q : ℕ)

def main : Com :=
  .seq ReadAll.readAll (.seq initS (.seq nkA (.seq (scanLoop "a" nkA)
    (.ite (.eq (.var "ph") (.lit 0))
      (.ite (.eq (.var "L") (.lit 0))
        (.ite (.eq (.var "kind") (.lit 2)) (acceptCom p q) (rejectCom p)) (rejectCom p))
      (rejectCom p)))))

lemma Kacc1_mono (Sz : ℕ) {n n' N N' : ℕ} (hn : n ≤ n') (hN : N ≤ N') :
    Kacc1 Sz n N ≤ Kacc1 Sz n' N' := by
  unfold Kacc1 L1Print.Kprint
  have h1 := Nat.mul_le_mul_left (3 * (48 * Sz + 70) + 20 + 10 + 4) hn
  have h2 := Nat.mul_le_mul_left (19 * (48 * Sz + 80) + 10 + 4) hN
  omega

/-- The cost of the whole program on an input of length `l`. -/
def Kmain (l Sz : ℕ) : ℕ :=
  (12 * l + 10) + 8 + 60 + ((100 + 60 + 4) * l + 6) + (12 + Kacc1 Sz l l)

lemma wvars_readAll : ReadAll.readAll.wvars = ["L", "rt", "rv", "rt"] := by
  simp [ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, Com.wvars]
lemma warrs_readAll : ReadAll.readAll.warrs = ["a"] := by
  simp [ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, Com.warrs]

variable {B : ℕ} (y : List ℕ)

theorem main_spec (hyB : ∀ v ∈ y, v < B)
    (hB : 16 * 2 ^ y.length + (p + 2 * q) * (y.length + 2) + 4 * y.length + p + 64 ≤ B) :
    ∃ σ', Run B (main p q) (initEnv (fun _ => y.length) (y.length :: y)) σ'
        (Kmain y.length B.size) ∧ σ'.out = L1Red.red p q y := by
  have hpow : y.length < 2 ^ y.length := Nat.lt_two_pow_self
  have hpow1 : (2 : ℕ) ^ (y.length + 1) = 2 * 2 ^ y.length := by ring
  have hs : ∀ v, v + 4 < B → v.size ≤ B.size := fun v hv => Nat.size_le_size (by omega)
  set σ0 := initEnv (fun _ => y.length) (y.length :: y) with hσ0
  -- read
  obtain ⟨σ1, r1, ⟨hL1, ha1, ho1, -⟩, fv1, fa1, -, -⟩ :=
    (ReadAll.readAll_spec (B := B) (y := y) hyB (by omega)).frame σ0
      ⟨rfl, rfl, by simp [hσ0, initEnv]⟩
  have z1 : ∀ x, x ∉ ["L", "rt", "rv"] → σ1.vars x = 0 := fun x hx => by
    rw [fv1 x (by rw [wvars_readAll]; simp only [List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hx ⊢; tauto)]
    rfl
  have tk1 : σ1.arrs "TK" = List.replicate y.length 0 := by
    rw [fa1 "TK" (by simp [warrs_readAll])]; rfl
  -- initialise the tokenizer
  obtain ⟨σ2, r2, i1, i2, i3, iv, ia, io, -⟩ := initS_spec (B := B) (by omega) σ1
    (by show σ1.vars "L" < B; rw [hL1]; omega)
  have z2 : ∀ x, x ∉ ["L", "rt", "rv", "Ln", "pw"] → σ2.vars x = 0 := fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rw [iv x (by simp; tauto), z1 x (by simp; tauto)]
  -- the first expectation
  have hnk : NkSpec B (2 ^ y.length) EA y.length nkA 60 := nkA_spec (B := B) _ _ (by omega)
  obtain ⟨σ3, r3, k3, v3, a3, o3, -⟩ := hnk [] (fun k hk => by simp at hk) (by simp) σ2
    ⟨⟨by simpa using z2 "T" (by decide), by simp⟩, fun t ht => by simp at ht⟩
  -- the scan
  have sv : ∀ x ∈ scanVars, σ3.vars x = σ2.vars x := v3
  obtain ⟨σ4, r4, ⟨I4, p4⟩, -, -, -, -⟩ :=
    (scanLoop_spec (B := B) "a" nkA (by decide) y y.length (le_refl _) hnk (by omega) hyB).frame σ3 (by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [Env.setVar]
    all_goals try simp [stAt, bitsOf, init]
    · rw [sv "ph" (by simp [scanVars])]; exact z2 "ph" (by decide)
    · rw [sv "L" (by simp [scanVars])]; exact i2
    · rw [sv "val" (by simp [scanVars])]; exact z2 "val" (by decide)
    · rw [sv "pw" (by simp [scanVars])]; exact i3
    · rw [sv "i" (by simp [scanVars])]; exact z2 "i" (by decide)
    · rw [sv "T" (by simp [scanVars])]; exact z2 "T" (by decide)
    · exact k3
    · rw [a3, ia, ha1, List.take_length]
    · rw [sv "Ln" (by simp [scanVars]), i1]; exact hL1
    · rw [a3, ia, tk1]; simp
    · rw [o3, io]; exact ho1)
  obtain ⟨hR, -, -, -, hTKl, hout4⟩ := I4
  have hst : stAt EA y (σ4.vars "p") = run EA init (bitsOf y) := by
    rw [p4]; unfold stAt; rw [List.take_length]
  rw [hst] at hR
  have hbd := bd_stAt EA y y.length (le_refl _)
  have hst' : stAt EA y y.length = run EA init (bitsOf y) := by
    unfold stAt; rw [List.take_length]
  rw [hst'] at hbd
  have hphB : σ4.vars "ph" < B := by rw [hR.ph]; have := hbd.ph; omega
  have hLB : σ4.vars "L" < B := by rw [hR.L]; have := hbd.L; omega
  have hkB : σ4.vars "kind" < B := by
    rw [hR.kind]; cases EA (run EA init (bitsOf y)).toks <;> simp [kcode] <;> omega
  have hp8 : p + 8 < B := by omega
  have hseq : ∀ {σ' K}, Run B (.ite (.eq (.var "ph") (.lit 0))
      (.ite (.eq (.var "L") (.lit 0))
        (.ite (.eq (.var "kind") (.lit 2)) (acceptCom p q) (rejectCom p)) (rejectCom p))
      (rejectCom p)) σ4 σ' K → Run B (main p q) σ0 σ' ((12 * y.length + 10) + (8 + (60 +
        (((100 + 60 + 4) * y.length + 6) + K)))) := fun h => r1.seq (r2.seq (r3.seq (r4.seq h)))
  have rejectRun := rejectCom_spec (B := B) p B.size hp8 hs σ4 trivial
  obtain ⟨σr, rr, orr⟩ := rejectRun
  have houtr : σr.out = L1Red.blockedBits p := by rw [orr, hout4, List.nil_append]
  have hKrej : 4 * (48 * B.size + 50) + 4 ≤ Kacc1 B.size y.length y.length := by
    unfold Kacc1; omega
  by_cases hacc : Accepts EA (run EA init (bitsOf y))
  · obtain ⟨h0, hL0, hk⟩ := hacc
    have hconf := (accept_sound EA ⟨h0, hL0, hk⟩).2
    have hlenT := conf_length hconf
    have hT := hbd.T
    have hmul : (p + 2 * q) * (((run EA init (bitsOf y)).toks.map Tok.val).getD 1 0 + 2) ≤
        (p + 2 * q) * (y.length + 2) := Nat.mul_le_mul_left _ (by omega)
    obtain ⟨σa, ra, oa⟩ := accept_spec (B := B) p q _ hconf (2 ^ (y.length + 1)) B.size
      hbd.tok (by omega) (by omega) hp8 hs σ4 ⟨hR.tok, by omega, hout4⟩
    have rite := Run.ite_true (d := rejectCom p) (cond_lit_true (B := B) (hR.ph.trans h0) (by omega))
      (Run.ite_true (d := rejectCom p) (cond_lit_true (B := B) (hR.L.trans hL0) (by omega))
        (Run.ite_true (d := rejectCom p) (cond_lit_true (B := B)
          (show σ4.vars "kind" = 2 by rw [hR.kind, hk]; rfl) (by omega)) ra))
    have hmono := Kacc1_mono B.size (show ((run EA init (bitsOf y)).toks.map Tok.val).getD 0 0 ≤
      y.length by omega) (show ((run EA init (bitsOf y)).toks.map Tok.val).getD 1 0 ≤ y.length
      by omega)
    refine ⟨σa, (hseq rite).mono (by unfold Kmain; simp only [Cond.size, Expr.size]; omega), ?_⟩
    rw [oa]
    unfold L1Red.red L1Red.tkScan
    by_cases hord : L1Ordered.OrdOK ((run EA init (bitsOf y)).toks.map Tok.val)
    · rw [if_pos hord, if_pos ⟨⟨h0, hL0, hk⟩, hord⟩]
    · rw [if_neg hord, if_neg (fun h => hord h.2)]
  · have hred : L1Red.red p q y = L1Red.blockedBits p := by
      unfold L1Red.red; rw [if_neg (fun h => hacc h.1)]
    rw [hred]
    by_cases h0 : (run EA init (bitsOf y)).ph = 0
    · by_cases hL0 : (run EA init (bitsOf y)).L = 0
      · have hk : EA (run EA init (bitsOf y)).toks ≠ .done := fun hk => hacc ⟨h0, hL0, hk⟩
        have rite := Run.ite_true (d := rejectCom p)
          (cond_lit_true (B := B) (hR.ph.trans h0) (by omega))
          (Run.ite_true (d := rejectCom p) (cond_lit_true (B := B) (hR.L.trans hL0) (by omega))
            (Run.ite_false (c := acceptCom p q) (cond_lit_false (B := B)
              (by rw [hR.kind]; exact fun h => hk (kcode_done.mp h)) hkB (by omega)) rr))
        exact ⟨σr, (hseq rite).mono (by unfold Kmain; simp only [Cond.size, Expr.size]; omega), houtr⟩
      · have rite := Run.ite_true (d := rejectCom p)
          (cond_lit_true (B := B) (hR.ph.trans h0) (by omega))
          (Run.ite_false (c := Com.ite (.eq (.var "kind") (.lit 2)) (acceptCom p q) (rejectCom p))
            (cond_lit_false (B := B) (by rw [hR.L]; exact hL0) hLB (by omega)) rr)
        exact ⟨σr, (hseq rite).mono (by unfold Kmain; simp only [Cond.size, Expr.size]; omega), houtr⟩
    · have rite := Run.ite_false
        (c := Com.ite (.eq (.var "L") (.lit 0))
          (.ite (.eq (.var "kind") (.lit 2)) (acceptCom p q) (rejectCom p)) (rejectCom p))
        (cond_lit_false (B := B) (by rw [hR.ph]; exact h0) hphB (by omega)) rr
      exact ⟨σr, (hseq rite).mono (by unfold Kmain; simp only [Cond.size, Expr.size]; omega), houtr⟩

end Lax391470Proofs.L1Main
