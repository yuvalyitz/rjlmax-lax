import Lax391470Proofs.V1Main
import Lax391470Proofs.V2Parts
import Lax391470Proofs.V2Accept
import Lax391470Proofs.V2Nk
import Lax391470Proofs.V2Dec
import Lax391470Proofs.TokBound
import Lax391470Proofs.L1Agree
import Lax391470Proofs.ReadAll

/-!
The verifier of `AUX p q` as one IMP+ program, and what it computes.
-/

namespace Lax391470Proofs.V2Main

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.Bits Lax391470Proofs.TokModel Lax391470Proofs.TokScan
open Lax391470Proofs.TokProg Lax391470Proofs.TokLoop Lax391470Proofs.TokBound
open Lax391470Proofs.TokRun Lax391470Proofs.V2Nk Lax391470Proofs.V2Format
open Lax391470Proofs.VUnpair Lax391470Proofs.V2Accept
open Lax391470Proofs.V1Parts (initU initU_spec gate gate_spec)
open Lax391470Proofs.V2Parts
open Lax391470Proofs.V1Main (tok_getD)
open Lax391470Proofs.V2Dec Lax391470Proofs.V2Sem Lax391470Proofs.V2Link

variable (p q : ℕ)

def front : Com :=
  .seq ReadAll.readAll (.seq initU (.seq uLoop (.seq (tokRun "w" "nx" nkB) (.seq bcheck
    (.seq (tokRun "w" "nw" nkB) gate)))))

def main : Com :=
  .seq front (.ite (.eq (.var "g") (.lit 1)) (acceptPart p q) (.write (.lit 0)))

lemma warrs_readAll : ReadAll.readAll.warrs = ["a"] := by
  simp [ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, Com.warrs]

lemma warrs_uLoop : uLoop.warrs = ["w"] := by
  simp [uLoop, uBody, Com.warrs]

lemma wvars_tokRun (len x : String) (hx : x = "st" ∨ x = "nx" ∨ x = "nw" ∨ x = "okx") :
    x ∉ (tokRun "w" len nkB).wvars := by
  rcases hx with rfl | rfl | rfl | rfl <;>
  simp [tokRun, TokRun.reset, nkB, scanLoop, scanBody, readBit, dispatch, put, TokProg.reset,
    startDigits, TokProg.digit, Com.wvars]

lemma warrs_tokRun (len a : String) (ha : a ≠ "TK") : a ∉ (tokRun "w" len nkB).warrs := by
  simp [ha, tokRun, TokRun.reset, nkB, scanLoop, scanBody, readBit, dispatch, put, TokProg.reset,
    startDigits, TokProg.digit, Com.warrs]

variable {B : ℕ} (z : List ℕ)

open Classical

/-- The cost of everything before the arithmetic, on an input of length `l`. -/
def Kfront (l : ℕ) : ℕ :=
  (12 * l + 10) + (10 + (((40 + 4) * l + 6) + ((20 + 90 + ((100 + 90 + 4) * l + 6)) +
    (50 + ((20 + 90 + ((100 + 90 + 4) * l + 6)) + 40)))))

theorem front_spec (hzB : ∀ v ∈ z, v < B) (hB : 16 * 2 ^ (z.length + 1) + z.length + 64 ≤ B) :
    ∃ σ', Run B front (initEnv (fun _ => z.length) (z.length :: z)) σ' (Kfront z.length) ∧
      σ'.vars "g" = (if Gate z then 1 else 0) ∧ TokRefl (s2 z).toks σ' ∧
      z.length ≤ (σ'.arrs "TT").length ∧ z.length ≤ (σ'.arrs "PP").length ∧ σ'.out = [] := by
  set l := z.length with hl
  set σ0 := initEnv (fun _ => l) (l :: z) with hσ0
  set u := urun uinit z with hu
  have hug := ugood_uAt z l (le_refl _)
  have huAt : uAt z l = u := by unfold uAt; rw [hl, List.take_length]
  rw [huAt] at hug
  obtain ⟨ug1, ug2, ug3⟩ := hug
  have hpl : ∀ k, k ≤ l → (2 : ℕ) ^ (k + 1) ≤ 2 ^ (l + 1) := fun k hk =>
    Nat.pow_le_pow_right (by omega) (by omega)
  have hp2 : ∀ k, (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := fun k => by ring
  -- read
  obtain ⟨σ1, r1, ⟨hL1, ha1, ho1, -⟩, fv1, fa1, -, -⟩ :=
    (ReadAll.readAll_spec (B := B) (y := z) hzB (by omega)).frame σ0
      ⟨rfl, rfl, by simp [hσ0, initEnv, hl]⟩
  have len1 : ∀ a, a ≠ "a" → (σ1.arrs a).length = l := fun a ha => by
    rw [fa1 a (by rw [warrs_readAll]; simpa using ha)]; simp [hσ0, initEnv]
  -- take the pair apart
  obtain ⟨σ2, r2, i1, i2, i3, i4, ia, io⟩ := initU_spec (B := B) l (by omega) σ1 hL1
  obtain ⟨σ3, r3, ⟨I3, p3⟩, fv3, fa3, -, -⟩ := (uLoop_spec (B := B) z (by omega) hzB).frame σ2
    ⟨by simp only [Env.setVar]; rw [ia]; exact ha1,
      by simp only [Env.setVar]; rw [if_neg (by decide)]; exact i1,
      by simp [Env.setVar],
      by simp only [Env.setVar, if_true]; rw [if_neg (by decide), i2]; simp [uAt, urun, uinit],
      by simp only [Env.setVar, if_true]; rw [if_neg (by decide), i3]; simp [uAt, urun, uinit],
      by simp only [Env.setVar, if_true]; rw [if_neg (by decide), i4]; simp [uAt, urun, uinit],
      by simp only [Env.setVar, if_true]; rw [if_neg (by decide), i4]; simp [uAt, urun, uinit],
      by simp only [Env.setVar]; rw [ia, len1 _ (by decide)],
      by simp only [Env.setVar]; rw [io]; exact ho1⟩
  obtain ⟨-, -, -, hst3, hnx3, hnw3, hw3, -, hout3⟩ := I3
  rw [p3, huAt] at hst3 hnx3 hnw3 hw3
  have len3 : ∀ a, a ≠ "a" → a ≠ "w" → (σ3.arrs a).length = l := fun a h1 h2 => by
    rw [fa3 a (by rw [warrs_uLoop]; simpa using h2), ia, len1 a h1]
  have hmem : ∀ v ∈ u.xs ++ u.ys, v < B := fun v hv => hzB v (urun_mem_init hv)
  -- the first scan
  have hxl : u.xs.length ≤ l := by omega
  have hnk1 : NkSpec B (2 ^ u.xs.length) E2 u.xs.length nkB 90 := nkB_spec (B := B) _ _ (by
    have := hpl _ hxl; have := hp2 u.xs.length; omega)
  obtain ⟨σ4, r4, ⟨hR4, ho4, hc4⟩, fv4, fa4, -, -⟩ :=
    (tokRun_spec (B := B) "w" "nx" nkB (by decide) u.xs l hxl hnk1
      (by have := hpl _ hxl; omega) (fun v hv => hmem v (List.mem_append_left _ hv))).frame σ3
    ⟨by
        have := congrArg (List.take u.xs.length) hw3
        rw [List.take_take, hnw3, Nat.min_eq_left (by omega), List.take_left'] at this
        · exact this
        · rfl,
      hnx3, by rw [len3 _ (by decide) (by decide)], hout3⟩
  have hbd1 := bd_stAt E2 u.xs u.xs.length (le_refl _)
  have e1 : stAt E2 u.xs u.xs.length = s1 z := by unfold stAt s1; rw [List.take_length]
  rw [e1] at hbd1
  have hR4' : Refl E2 (s1 z) σ4 := hR4
  -- the boundary
  obtain ⟨σ5, r5, c5, v5, a5, o5⟩ : ∃ σ5, Run B bcheck σ4 σ5 50 ∧
      σ5.vars "okx" = (if (s1 z).ph = 0 ∧ (s1 z).L = 0 ∧ (s1 z).toks.length =
        2 + 3 * ((s1 z).toks.map Tok.val).getD 0 0 +
          4 * ((s1 z).toks.map Tok.val).getD 1 0 then 1 else 0) ∧
      (∀ x, x ≠ "okx" → σ5.vars x = σ4.vars x) ∧ σ5.arrs = σ4.arrs ∧ σ5.out = σ4.out := by
    have hph : σ4.vars "ph" < B := by rw [hR4'.ph]; have := hbd1.ph; omega
    have hLv : σ4.vars "L" < B := by rw [hR4'.L]; have := hbd1.L; omega
    by_cases hT0 : (s1 z).toks.length < 2
    · obtain ⟨σ5, r5, c5, v5, a5, o5⟩ := bcheck_small (B := B) (by omega) σ4
        ⟨hph, hLv, by rw [hR4'.tok.1]; exact hT0⟩
      refine ⟨σ5, r5, ?_, v5, a5, o5⟩
      rw [c5, if_neg (fun h => by omega)]
    · have hg0 := tok_getD hR4'.tok.2 (show 0 < (s1 z).toks.length by omega)
      have hg1 := tok_getD hR4'.tok.2 (show 1 < (s1 z).toks.length by omega)
      have hn0 : ((s1 z).toks.map Tok.val).getD 0 0 < 2 ^ (u.xs.length + 1) := by
        rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; omega), List.getElem_map]
        exact hbd1.tok _ (List.getElem_mem _)
      have hn1 : ((s1 z).toks.map Tok.val).getD 1 0 < 2 ^ (u.xs.length + 1) := by
        rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; omega), List.getElem_map]
        exact hbd1.tok _ (List.getElem_mem _)
      have hTl : (s1 z).toks.length ≤ (σ4.arrs "TK").length := by
        have := congrArg List.length hR4'.tok.2
        rw [List.length_take, List.length_map] at this; omega
      obtain ⟨σ5, r5, c5, v5, a5, o5⟩ := bcheck_flat (B := B) _ _ (by
          have := hpl _ hxl; omega) σ4
        ⟨hph, hLv, by rw [hR4'.tok.1]; have := hbd1.T; omega, hg0, hg1, by omega⟩
      refine ⟨σ5, r5, ?_, v5, a5, o5⟩
      rw [c5, hR4'.ph, hR4'.L, hR4'.tok.1]
  -- the second scan
  have hyl : (u.xs ++ u.ys).length ≤ l := by rw [List.length_append]; omega
  have hnkB : NkSpec B (2 ^ (u.xs ++ u.ys).length) E2 (u.xs ++ u.ys).length nkB 90 :=
    nkB_spec (B := B) _ _ (by have := hpl _ hyl; have := hp2 (u.xs ++ u.ys).length; omega)
  have w5 : σ5.arrs "w" = σ3.arrs "w" := by rw [a5, fa4 "w" (warrs_tokRun _ _ (by decide))]
  obtain ⟨σ6, r6, ⟨hR6, ho6, -⟩, fv6, fa6, -, -⟩ :=
    (tokRun_spec (B := B) "w" "nw" nkB (by decide) (u.xs ++ u.ys) l hyl hnkB
      (by have := hpl _ hyl; omega) hmem).frame σ5
    ⟨by rw [w5, List.length_append, ← hnw3]; exact hw3,
      by rw [v5 _ (by decide), fv4 _ (wvars_tokRun _ _ (by simp)), hnw3, List.length_append],
      by rw [a5]; exact hc4, by rw [o5]; exact ho4⟩
  have hbd2 := bd_stAt E2 (u.xs ++ u.ys) (u.xs ++ u.ys).length (le_refl _)
  have e2 : stAt E2 (u.xs ++ u.ys) (u.xs ++ u.ys).length = s2 z := by
    unfold stAt s2; rw [List.take_length]
  rw [e2] at hbd2
  have hR6' : Refl E2 (s2 z) σ6 := hR6
  have st6 : σ6.vars "st" = u.st := by
    rw [fv6 _ (wvars_tokRun _ _ (by simp)), v5 _ (by decide), fv4 _ (wvars_tokRun _ _ (by simp)),
      hst3]
  have okx6 : σ6.vars "okx" = σ5.vars "okx" := fv6 _ (wvars_tokRun _ _ (by simp))
  have hkB : σ6.vars "kind" < B := by
    rw [hR6'.kind]; cases E2 (s2 z).toks <;> simp [kcode] <;> omega
  -- the gate
  obtain ⟨σ7, r7, c7, v7, a7, o7⟩ := gate_spec (B := B) (by omega) σ6
    ⟨by rw [st6]; omega, by rw [hR6'.ph]; have := hbd2.ph; omega,
      by rw [hR6'.L]; have := hbd2.L; omega, hkB, by rw [okx6, c5]; split <;> omega⟩
  have len6 : ∀ a, a ≠ "a" → a ≠ "w" → a ≠ "TK" → (σ7.arrs a).length = l := fun a h1 h2 h3 => by
    rw [a7, fa6 a (warrs_tokRun _ _ h3), a5, fa4 a (warrs_tokRun _ _ h3), len3 a h1 h2]
  refine ⟨σ7, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))).mono (by
      unfold Kfront; omega), ?_, ⟨by rw [v7 _ (by decide)]; exact hR6'.tok.1,
      by rw [a7]; exact hR6'.tok.2⟩, by rw [len6 _ (by decide) (by decide) (by decide)],
    by rw [len6 _ (by decide) (by decide) (by decide)], by rw [o7]; exact ho6⟩
  rw [c7, st6, hR6'.ph, hR6'.L, hR6'.kind, okx6, c5]
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have h5' : (s1 z).ph = 0 ∧ (s1 z).L = 0 ∧ (s1 z).toks.length =
        2 + 3 * ((s1 z).toks.map Tok.val).getD 0 0 +
          4 * ((s1 z).toks.map Tok.val).getD 1 0 := by
      by_contra hc; rw [if_neg hc] at h5; omega
    exact ⟨h1, h5'.1, h5'.2.1, h5'.2.2, h2, h3, kcode_done.mp h4⟩
  · rintro ⟨g1, g2, g3, g4, g5, g6, g7⟩
    exact ⟨g1, g5, g6, by rw [g7]; rfl, by rw [if_pos ⟨g2, g3, g4⟩]⟩

/-- The cost of the whole verifier on an input of length `l`. -/
def Kmain (l : ℕ) : ℕ := Kfront l + (8 + Kacc l l)

lemma Kacc_mono {n N l : ℕ} (hn : n ≤ l) (hN : N ≤ l) : Kacc n N ≤ Kacc l l := by
  unfold Kacc
  have h1 : ((70 + 4) * (n + 2 * N) + 6 + 4 + 4) * (n + 2 * N) ≤
      ((70 + 4) * (l + 2 * l) + 6 + 4 + 4) * (l + 2 * l) := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- **The verifier decides `Dec p q`.** -/
theorem main_spec (hzB : ∀ v ∈ z, v < B)
    (hB : (z.length + 16) * 2 ^ (z.length + 1) + 10 * z.length + p + q + 64 ≤ B) :
    ∃ σ', Run B (main p q) (initEnv (fun _ => z.length) (z.length :: z)) σ' (Kmain z.length) ∧
      σ'.out = [if Dec p q z then 1 else 0] := by
  have hmul : (z.length + 16) * 2 ^ (z.length + 1) =
      z.length * 2 ^ (z.length + 1) + 16 * 2 ^ (z.length + 1) := by ring
  obtain ⟨σ7, r7, hg, hTR, hTT, hPP, hout⟩ := front_spec (B := B) z hzB (by omega)
  by_cases hG : Gate z
  · rw [if_pos hG] at hg
    have hconf : Conforms E2 (s2 z).toks := (accept_sound E2 hG.acc).2
    have hlenT : (s2 z).toks.length = 2 + (3 * ((s2 z).toks.map Tok.val).getD 0 0 +
        4 * ((s2 z).toks.map Tok.val).getD 1 0 + (((s2 z).toks.map Tok.val).getD 0 0 +
          2 * ((s2 z).toks.map Tok.val).getD 1 0)) := conf2_length hconf
    have hug := ugood_uAt z z.length (le_refl _)
    have huAt : uAt z z.length = urun uinit z := by unfold uAt; rw [List.take_length]
    rw [huAt] at hug
    have hyl : ((urun uinit z).xs ++ (urun uinit z).ys).length ≤ z.length := by
      rw [List.length_append]; exact hug.len
    have hbd2 := bd_stAt E2 ((urun uinit z).xs ++ (urun uinit z).ys) _ (le_refl _)
    have e2 : stAt E2 ((urun uinit z).xs ++ (urun uinit z).ys)
        ((urun uinit z).xs ++ (urun uinit z).ys).length = s2 z := by
      unfold stAt s2; rw [List.take_length]
    rw [e2] at hbd2
    have hpw : (2 : ℕ) ^ (((urun uinit z).xs ++ (urun uinit z).ys).length + 1) ≤
        2 ^ (z.length + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    obtain ⟨hT1, hT2⟩ := hTR
    obtain ⟨t, ht⟩ : ∃ t, t = σ7.arrs "TK" := ⟨_, rfl⟩
    obtain ⟨Tn, hTn⟩ : ∃ Tn, Tn = (s2 z).toks.length := ⟨_, rfl⟩
    obtain ⟨n, hn⟩ : ∃ n, n = ((s2 z).toks.map Tok.val).getD 0 0 := ⟨_, rfl⟩
    obtain ⟨N, hN⟩ : ∃ N, N = ((s2 z).toks.map Tok.val).getD 1 0 := ⟨_, rfl⟩
    rw [← hTn, ← hn, ← hN] at hlenT
    rw [← ht, ← hTn] at hT2
    have hTle := hbd2.T
    rw [← hTn] at hTle
    have hget : ∀ k < Tn, t.getD k 0 = ((s2 z).toks.map Tok.val).getD k 0 := fun k hk => by
      rw [← hT2, L1Agree.getD_take t Tn hk]
    have hTl : Tn ≤ t.length := by
      have := congrArg List.length hT2
      rw [List.length_take, List.length_map, ← hTn] at this; omega
    have hTz : Tn ≤ z.length := le_trans hTle hyl
    have htB : ∀ k < Tn, t.getD k 0 < 2 ^ (z.length + 1) := fun k hk => by
      rw [hget k hk, List.getD_eq_getElem _ _ (by rw [List.length_map, ← hTn]; exact hk),
        List.getElem_map]
      exact lt_of_lt_of_le (hbd2.tok _ (List.getElem_mem _)) hpw
    have h16 : 16 * 2 ^ (z.length + 1) = 2 * 2 ^ (z.length + 1) + 14 * 2 ^ (z.length + 1) := by
      ring
    obtain ⟨σ8, r8, o8⟩ := accept_spec (B := B) p q t n N Tn (2 ^ (z.length + 1))
      (by rw [hget 0 (by omega), hn]) (by rw [hget 1 (by omega), hN]) hlenT hTl htB (by omega) σ7
      ⟨ht.symm, by omega, by omega, hout⟩
    have rite := Run.ite_true (d := Com.write (.lit 0))
      (cond_lit_true (B := B) hg (by omega)) r8
    refine ⟨σ8, (r7.seq rite).mono (by
      have := Kacc_mono (n := n) (N := N) (l := z.length) (by omega) (by omega)
      unfold Kmain; simp only [Cond.size, Expr.size]; omega), ?_⟩
    rw [o8]
    congr 1
    refine if_congr ?_ rfl rfl
    have := sem_congr p q n N (tk := (s2 z).toks.map Tok.val) (tk' := t) hn.symm hN.symm
      (fun k hk => hget k (by omega))
    unfold Dec tk2
    exact ⟨fun h => ⟨hG, this.mp h⟩, fun h => this.mpr h.2⟩
  · rw [if_neg hG] at hg
    have rw0 := Run.write (B := B) (σ := σ7) (e := .lit 0) (v := 0) (evalB_lit (by omega))
    have rite := Run.ite_false (c := acceptPart p q)
      (cond_lit_false (B := B) (x := "g") (n := 1) (by rw [hg]; decide) (by rw [hg]; omega)
        (by omega)) rw0
    refine ⟨_, (r7.seq rite).mono (by
      unfold Kmain Kacc; simp only [Cond.size, Expr.size]; omega), ?_⟩
    show σ7.out ++ [0] = _
    rw [hout, if_neg (fun h => hG h.1)]
    rfl

end Lax391470Proofs.V2Main
