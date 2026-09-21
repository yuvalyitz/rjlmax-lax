import Lax391470Proofs.V1Reads
import Lax391470Proofs.VUnpair

/-!
The decision the verifier of `TwoLengths p q` makes, as a predicate on its input, and the
two halves of its correctness.
-/

namespace Lax391470Proofs.V1Dec

open Lax391470 Lax391470.Scheduling Lax391470.BinaryEncoding
open Lax391470Proofs.TokModel Lax391470Proofs.TokProg Lax391470Proofs.TokScan
open Lax391470Proofs.InstFormat Lax391470Proofs.V1Format Lax391470Proofs.V1Sem
open Lax391470Proofs.V1Reads Lax391470Proofs.VUnpair Lax391470Proofs.Bits
open Lax434930.Certificates Lax434930.PolynomialTime

/-- The scan of the first word. -/
def s1 (z : List ℕ) : St := run E2 init (bitsOf (urun uinit z).xs)
/-- The scan of both words. -/
def s2 (z : List ℕ) : St := run E2 init (bitsOf ((urun uinit z).xs ++ (urun uinit z).ys))
/-- The values of all tokens. -/
def tk2 (z : List ℕ) : List ℕ := (s2 z).toks.map Tok.val

/-- **What the verifier accepts.** -/
inductive Dec (p q : ℕ) (z : List ℕ) : Prop where
  | mk
    (st : (urun uinit z).st = 2)
    (ph : (s1 z).ph = 0)
    (L : (s1 z).L = 0)
    (T : (s1 z).toks.length = 1 + 5 * ((s1 z).toks.map Tok.val).getD 0 0)
    (acc : Accepts E2 (s2 z))
    (nz : NZ (tk2 z))
    (av : AV p q (tk2 z))
    (ov : OV (tk2 z))
/-- The part of the decision made before the arithmetic. -/
inductive Gate (z : List ℕ) : Prop where
  | mk
    (st : (urun uinit z).st = 2)
    (ph : (s1 z).ph = 0)
    (L : (s1 z).L = 0)
    (T : (s1 z).toks.length = 1 + 5 * ((s1 z).toks.map Tok.val).getD 0 0)
    (acc : Accepts E2 (s2 z))

theorem Gate.acc
    {z : List ℕ}
    (h : Gate z) : Accepts E2 (s2 z) :=
  match h with | ⟨_, _, _, _, x⟩ => x

lemma dec_iff (p q : ℕ) (z : List ℕ) :
    Dec p q z ↔ Gate z ∧ NZ (tk2 z) ∧ AV p q (tk2 z) ∧ OV (tk2 z) :=
  ⟨fun ⟨a, b, c, d, e, f, g, h⟩ => ⟨⟨a, b, c, d, e⟩, f, g, h⟩,
    fun ⟨⟨a, b, c, d, e⟩, f, g, h⟩ => ⟨a, b, c, d, e, f, g, h⟩⟩

lemma bitsOf_append (a b : List ℕ) : bitsOf (a ++ b) = bitsOf a ++ bitsOf b := by
  simp [bitsOf]

lemma s1_pair (x y : Word) : s1 (natBits (pair x y)) = run E2 init x := by
  unfold s1; rw [urun_pair]; simp

lemma s2_pair (x y : Word) : s2 (natBits (pair x y)) = run E2 init (x ++ y) := by
  unfold s2; rw [urun_pair]; simp [bitsOf_append]

variable {p q : ℕ}

/-- **Soundness**: an accepted pair begins with a schedulable instance on `{p, q}`. -/
theorem dec_sound {x y : Word} (h : Dec p q (natBits (pair x y))) : x ∈ TwoLengths p q := by
  obtain ⟨-, h0, hL, hT, -, hnz, hav, hov⟩ := h
  unfold tk2 at hnz hav hov
  rw [s1_pair] at h0 hL hT
  rw [s2_pair] at hnz hav hov
  obtain ⟨hcode, hc1⟩ := boundary h0 hL hT
  obtain ⟨l, hl⟩ := run_toks_prefix E2 (run E2 init x) y
  rw [← run_append] at hl
  rw [hl] at hnz hav hov
  obtain ⟨hnn, hreads⟩ := reads_of_toks hc1 hnz
  have hI := toksOf_ofToks hc1 hnn
  obtain ⟨ha, hb⟩ := (feas_iff hreads p q).mp ⟨hav, hov⟩
  exact ⟨ofToks _, by rw [encodeInstance_eq, hI, hcode], ha, _, hb⟩

/-! ### Completeness -/

lemma flatMap_len_le {α : Type} (l : List ℕ) (f g : ℕ → List α)
    (h : ∀ j ∈ l, (f j).length ≤ (g j).length) :
    (l.flatMap f).length ≤ (l.flatMap g).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have h1 := h a List.mem_cons_self
    have h2 := ih fun j hj => h j (List.mem_cons_of_mem _ hj)
    simp only [List.flatMap_cons, List.length_append]; omega

lemma encodeNat_length (v : ℕ) : (encodeNat v).length = 2 * v.size + 1 := by
  simp [encodeNat, Nat.size_eq_bits_len]; omega

lemma encodeNat_mono {v w : ℕ} (h : v ≤ w) : (encodeNat v).length ≤ (encodeNat w).length := by
  rw [encodeNat_length, encodeNat_length]
  have := Nat.size_le_size h
  omega

/-- A feasible schedule is no longer to write down than the instance. -/
lemma sched_short {I : Scheduling.Instance} {t : I.Schedule} (ht : Instance.Feasible t) :
    (code (schedToks (ext t) I.jobs)).length ≤ (encodeInstance I).length := by
  rw [encodeInstance_eq]
  unfold toksOf schedToks
  rw [show (Tok.num I.jobs :: (List.range I.jobs).flatMap (jobRec I)) =
    [Tok.num I.jobs] ++ (List.range I.jobs).flatMap (jobRec I) from rfl, code_append,
    List.length_append, AuxFormat.code_flatMap, AuxFormat.code_flatMap]
  refine le_trans (flatMap_len_le _ _ _ fun j hj => ?_) (Nat.le_add_left _ _)
  have hj' : j < I.jobs := List.mem_range.mp hj
  have h1 := (ht.1 ⟨j, hj'⟩).1
  have h2 := (ht.1 ⟨j, hj'⟩).2
  have e : ext t j = t ⟨j, hj'⟩ := by unfold ext; rw [dif_pos hj']
  unfold schedRec jobRec
  rw [dif_pos hj', e]
  simp only [code, List.flatMap_cons, List.flatMap_nil, Tok.code, List.length_append,
    List.length_cons, List.length_nil, List.append_nil]
  rcases le_total 0 (t ⟨j, hj'⟩) with hs | hs
  · have := encodeNat_mono (v := (t ⟨j, hj'⟩).natAbs) (w := (I.d ⟨j, hj'⟩).natAbs) (by omega)
    omega
  · have := encodeNat_mono (v := (t ⟨j, hj'⟩).natAbs) (w := (I.r ⟨j, hj'⟩).natAbs) (by omega)
    omega

/-- **Completeness**: a schedulable instance on `{p, q}` has a short accepted certificate. -/
theorem dec_complete {x : Word} (h : x ∈ TwoLengths p q) :
    ∃ y : Word, y.length ≤ x.length ∧ Dec p q (natBits (pair x y)) := by
  obtain ⟨I, rfl, hlen, t, ht⟩ := h
  refine ⟨code (schedToks (ext t) I.jobs), sched_short ht, ?_⟩
  have hc := conforms_toks2 I (ext t)
  have hx : encodeInstance I = code (toksOf I) := encodeInstance_eq I
  have e1 : run E2 init (code (toksOf I)) = bd (toksOf I) := by
    have := run_toks E2 (toksOf I) [] (fun k hk => by
      have h := hc.1 k (by unfold toks2; rw [List.length_append]; omega)
      unfold toks2 at h
      rw [List.getD_append _ _ _ _ hk, List.take_append_of_le_length (by omega)] at h
      simpa using h) []
    simpa [init, bd] using this
  have e2 := accept_complete E2 _ hc
  have hcode : code (toks2 I (ext t)) = encodeInstance I ++ code (schedToks (ext t) I.jobs) := by
    unfold toks2; rw [code_append, hx]
  rw [hcode] at e2
  have hr := reads_toks2 I t
  have hfe := (feas_iff hr p q).mpr ⟨hlen, ht⟩
  refine ⟨by rw [urun_pair], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [s1_pair, hx, e1]; rfl
  · rw [s1_pair, hx, e1]; rfl
  · rw [s1_pair, hx, e1]
    show (toksOf I).length = 1 + 5 * ((toksOf I).map Tok.val).getD 0 0
    rw [toksOf_length]; rfl
  · rw [s2_pair]; exact e2.1
  · unfold tk2; rw [s2_pair, e2.2]; exact nz_toks2 I _
  · unfold tk2; rw [s2_pair, e2.2]; exact hfe.1
  · unfold tk2; rw [s2_pair, e2.2]; exact hfe.2

end Lax391470Proofs.V1Dec
