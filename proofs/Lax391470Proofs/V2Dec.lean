import Lax391470Proofs.V2Sem
import Lax391470Proofs.V2Format
import Lax391470Proofs.V1Dec

/-!
The decision the verifier of `AUX p q` makes, as a predicate on its input, and the two
halves of its correctness.
-/

namespace Lax391470Proofs.V2Dec

open Lax391470 Lax391470.Scheduling Lax391470.BinaryEncoding Lax391470.AuxiliaryProblem
open Lax391470Proofs.TokModel Lax391470Proofs.TokProg Lax391470Proofs.TokScan
open Lax391470Proofs.AuxFormat Lax391470Proofs.V2Format Lax391470Proofs.V2Sem
open Lax391470Proofs.VUnpair Lax391470Proofs.Bits Lax391470Proofs.L1Model
open Lax434930.Certificates Lax434930.PolynomialTime

/-- The scan of the first word. -/
def s1 (z : List ℕ) : St := run E2 init (bitsOf (urun uinit z).xs)
/-- The scan of both words. -/
def s2 (z : List ℕ) : St := run E2 init (bitsOf ((urun uinit z).xs ++ (urun uinit z).ys))
/-- The values of all tokens. -/
def tk2 (z : List ℕ) : List ℕ := (s2 z).toks.map Tok.val

/-- The part of the decision made before the arithmetic. -/
inductive Gate (z : List ℕ) : Prop where
  | mk
    (st : (urun uinit z).st = 2)
    (ph : (s1 z).ph = 0)
    (L : (s1 z).L = 0)
    (T : (s1 z).toks.length = 2 + 3 * ((s1 z).toks.map Tok.val).getD 0 0 +
      4 * ((s1 z).toks.map Tok.val).getD 1 0)
    (acc : Accepts E2 (s2 z))

theorem Gate.acc
    {z : List ℕ}
    (h : Gate z) : Accepts E2 (s2 z) :=
  match h with | ⟨_, _, _, _, x⟩ => x

/-- **What the verifier accepts.** -/
def Dec (p q : ℕ) (z : List ℕ) : Prop := Gate z ∧ Sem p q (tk2 z)

lemma s1_pair (x y : Word) : s1 (natBits (pair x y)) = run E2 init x := by
  unfold s1; rw [urun_pair]; simp

lemma s2_pair (x y : Word) : s2 (natBits (pair x y)) = run E2 init (x ++ y) := by
  unfold s2; rw [urun_pair]; simp [V1Dec.bitsOf_append]

variable {p q : ℕ}

/-- **Soundness**: an accepted pair begins with an ordered, solvable instance. -/
theorem dec_sound {x y : Word} (h : Dec p q (natBits (pair x y))) : x ∈ AUX p q := by
  obtain ⟨⟨-, h0, hL, hT, -⟩, hsem⟩ := h
  unfold tk2 at hsem
  rw [s1_pair] at h0 hL hT
  rw [s2_pair] at hsem
  obtain ⟨hcode, hc1⟩ := boundary h0 hL hT
  obtain ⟨l, hl⟩ := V1Format.run_toks_prefix E2 (run E2 init x) y
  rw [← run_append] at hl
  have hA := toksOf_ofToks hc1
  rw [hl, ← hA, List.map_append] at hsem
  obtain ⟨hord, hsol⟩ := (sem_iff p q _ _).mp hsem
  exact ⟨ofToks _, by rw [encodeAux_eq, hA, hcode], hord, _, hsol⟩

/-! ### Completeness -/

/-- A schedule as natural numbers, on all indices. -/
def ext {A : AuxiliaryProblem.Instance} (t : (A.toInstance p q).Schedule) (j : ℕ) : ℕ :=
  if h : j < (A.toInstance p q).jobs then (t ⟨j, h⟩).toNat else 0

lemma code_sched_le (t : ℕ → ℕ) (c : ℕ) : ∀ m, (∀ j < m, (encodeNat (t j)).length ≤ c) →
    (code (schedToks t m)).length ≤ m * c
  | 0, _ => by simp [schedToks, code]
  | m + 1, h => by
    have ih := code_sched_le t c m fun j hj => h j (by omega)
    have hm := h m (by omega)
    unfold schedToks at ih ⊢
    rw [List.range_succ, List.map_append, code_append, List.length_append, Nat.succ_mul]
    simp only [List.map_cons, List.map_nil, code, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, Tok.code] at ih ⊢
    omega

lemma tok_code_bound (t : Tok) : (encodeNat (Tok.val t)).length ≤ t.code.length + 2 := by
  cases t with
  | num v => simp [Tok.val, Tok.code]
  | bit b => cases b <;> simp [Tok.val, Tok.code, encodeNat]

lemma code_mem_le {ts : List Tok} {t : Tok} (h : t ∈ ts) : t.code.length ≤ (code ts).length := by
  induction ts with
  | nil => simp at h
  | cons a r ih =>
    simp only [code, List.flatMap_cons, List.length_append]
    rcases List.mem_cons.mp h with rfl | h'
    · omega
    · have := ih h'; simp only [code] at this; omega

lemma toks_le_code (ts : List Tok) : ts.length ≤ (code ts).length := by
  induction ts with
  | nil => simp [code]
  | cons a r ih =>
    simp only [code, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    have : 1 ≤ a.code.length := by
      cases a <;> simp [Tok.code, encodeNat]; omega
    omega

lemma dOf_index (tk : List ℕ) (j : ℕ) (hj : j < tk.getD 0 0 + 2 * tk.getD 1 0) :
    ∃ k < 2 + 3 * tk.getD 0 0 + 4 * tk.getD 1 0, dOf tk j = tk.getD k 0 := by
  unfold dOf L1Ordered.ev
  split_ifs
  · exact ⟨_, by omega, rfl⟩
  · exact ⟨_, by omega, rfl⟩
  · exact ⟨_, by omega, rfl⟩

/-- **Completeness**: an ordered, solvable instance has a short accepted certificate. -/
theorem dec_complete {x : Word} (h : x ∈ AUX p q) :
    ∃ y : Word, y.length ≤ x.length * (x.length + 2) ∧ Dec p q (natBits (pair x y)) := by
  obtain ⟨A, rfl, hord, t, ht⟩ := h
  set l := schedToks (ext t) (A.ordinary + 2 * A.pairs) with hl
  have hx : encodeAux A = code (toksOf A) := encodeAux_eq A
  have hc := conforms_toks2 A (ext t)
  -- the token values
  have hval : (toks2 A (ext t)).map Tok.val = tkOf A ++ l.map Tok.val := by
    unfold toks2 tkOf; rw [List.map_append]
  have htn : ∀ j : Fin (A.toInstance p q).jobs,
      (tOf (tkOf A ++ l.map Tok.val) j : ℤ) = t j := by
    intro j
    have hj : (j : ℕ) < A.ordinary + A.pairs + A.pairs := j.isLt
    have hr := (ht.1.1 j).1
    have hr0 : (0 : ℤ) ≤ (A.toInstance p q).r j := by
      rw [← rOf_eq p q A [] j]; exact Int.natCast_nonneg _
    unfold tOf
    rw [h0, h1, List.getD_append_right _ _ _ _ (by rw [tkOf_length]; unfold iS; omega), tkOf_length,
      show iS A.ordinary A.pairs j - (2 + 3 * A.ordinary + 4 * A.pairs) = j by
        unfold iS; omega]
    have hg : (l.map Tok.val).getD j 0 = ext t j := by
      rw [V1Sem.val_getD, hl, schedToks_get _ _ _ (by omega)]; rfl
    rw [hg]
    unfold ext
    rw [dif_pos j.isLt]
    exact Int.toNat_of_nonneg (le_trans hr0 hr)
  have hsem : Sem p q (tkOf A ++ l.map Tok.val) := by
    refine (sem_iff p q A _).mpr ⟨hord, ?_⟩
    have e : (fun j : Fin (A.toInstance p q).jobs =>
        (tOf (tkOf A ++ l.map Tok.val) j : ℤ)) = t := funext htn
    rw [e]; exact ht
  refine ⟨code l, ?_, ⟨by rw [urun_pair], ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- the certificate is short
    have hcnt : A.ordinary + 2 * A.pairs ≤ (encodeAux A).length := by
      have := toks_le_code (toksOf A)
      rw [toksOf_length, ← hx] at this; omega
    refine le_trans (code_sched_le (ext t) ((encodeAux A).length + 2) _ fun j hj => ?_)
      (Nat.mul_le_mul_right _ hcnt)
    have hj' : j < (A.toInstance p q).jobs := by
      show j < A.ordinary + A.pairs + A.pairs; omega
    obtain ⟨k, hk, hdk⟩ := dOf_index (tkOf A ++ l.map Tok.val) j (by rw [h0, h1]; exact hj)
    rw [h0, h1] at hk
    have hfe := ((sem_iff p q A _).mp hsem).2.1.1 ⟨j, hj'⟩
    have hle : ext t j ≤ dOf (tkOf A ++ l.map Tok.val) j := by
      have h2 : ((tOf (tkOf A ++ l.map Tok.val) j : ℕ) : ℤ) +
          ((A.toInstance p q).p ⟨j, hj'⟩ : ℤ) ≤ (A.toInstance p q).d ⟨j, hj'⟩ := hfe.2
      have hd : ((dOf (tkOf A ++ l.map Tok.val) j : ℕ) : ℤ) = (A.toInstance p q).d ⟨j, hj'⟩ :=
        dOf_eq p q A (l.map Tok.val) ⟨j, hj'⟩
      rw [← hd] at h2
      have h3 : ((tOf (tkOf A ++ l.map Tok.val) j : ℕ) : ℤ) = t ⟨j, hj'⟩ := htn ⟨j, hj'⟩
      have h4 : (tOf (tkOf A ++ l.map Tok.val) j : ℤ) ≤ dOf (tkOf A ++ l.map Tok.val) j := by
        have : (0 : ℤ) ≤ ((A.toInstance p q).p ⟨j, hj'⟩ : ℤ) := Int.natCast_nonneg _
        omega
      have h5 : tOf (tkOf A ++ l.map Tok.val) j ≤ dOf (tkOf A ++ l.map Tok.val) j := by
        exact_mod_cast h4
      have h6 : tOf (tkOf A ++ l.map Tok.val) j = ext t j := by
        have : ((tOf (tkOf A ++ l.map Tok.val) j : ℕ) : ℤ) = ((ext t j : ℕ) : ℤ) := by
          rw [h3]; unfold ext; rw [dif_pos hj']
          have hr := (ht.1.1 ⟨j, hj'⟩).1
          have hr0 : (0 : ℤ) ≤ (A.toInstance p q).r ⟨j, hj'⟩ := by
            rw [← rOf_eq p q A [] ⟨j, hj'⟩]; exact Int.natCast_nonneg _
          exact (Int.toNat_of_nonneg (le_trans hr0 hr)).symm
        exact_mod_cast this
      omega
    rw [hdk, rd A _ hk, tk_getD] at hle
    have hmem : (toksOf A).getD k (.bit false) ∈ toksOf A := by
      rw [List.getD_eq_getElem _ _ (by rw [toksOf_length]; omega)]
      exact List.getElem_mem _
    have b1 := V1Dec.encodeNat_mono hle
    have b2 := tok_code_bound ((toksOf A).getD k (.bit false))
    have b3 := code_mem_le hmem
    rw [← hx] at b3
    omega
  · have e1 : run E2 init (code (toksOf A)) = bd (toksOf A) := by
      have := run_toks E2 (toksOf A) [] (fun k hk => by
        have h := hc.1 k (by unfold toks2; rw [List.length_append]; omega)
        unfold toks2 at h
        rw [List.getD_append _ _ _ _ hk, List.take_append_of_le_length (by omega)] at h
        simpa using h) []
      simpa [init, bd] using this
    rw [s1_pair, hx, e1]; rfl
  · have e1 : run E2 init (code (toksOf A)) = bd (toksOf A) := by
      have := run_toks E2 (toksOf A) [] (fun k hk => by
        have h := hc.1 k (by unfold toks2; rw [List.length_append]; omega)
        unfold toks2 at h
        rw [List.getD_append _ _ _ _ hk, List.take_append_of_le_length (by omega)] at h
        simpa using h) []
      simpa [init, bd] using this
    rw [s1_pair, hx, e1]; rfl
  · have e1 : run E2 init (code (toksOf A)) = bd (toksOf A) := by
      have := run_toks E2 (toksOf A) [] (fun k hk => by
        have h := hc.1 k (by unfold toks2; rw [List.length_append]; omega)
        unfold toks2 at h
        rw [List.getD_append _ _ _ _ hk, List.take_append_of_le_length (by omega)] at h
        simpa using h) []
      simpa [init, bd] using this
    rw [s1_pair, hx, e1]
    show (toksOf A).length = 2 + 3 * (tkOf A).getD 0 0 + 4 * (tkOf A).getD 1 0
    rw [toksOf_length, tk_zero, tk_one]
  · have e2 := accept_complete E2 _ hc
    have hcode : code (toks2 A (ext t)) = encodeAux A ++ code l := by
      unfold toks2; rw [code_append, hx]
    rw [hcode] at e2
    rw [s2_pair]; exact e2.1
  · have e2 := accept_complete E2 _ hc
    have hcode : code (toks2 A (ext t)) = encodeAux A ++ code l := by
      unfold toks2; rw [code_append, hx]
    rw [hcode] at e2
    unfold tk2; rw [s2_pair, e2.2, hval]; exact hsem

end Lax391470Proofs.V2Dec
