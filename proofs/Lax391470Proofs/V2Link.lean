import Lax391470Proofs.V2Pair
import Lax391470Proofs.V2Sem
import Lax391470Proofs.VPairs

/-!
What the loops of the verifier of `AUX p q` compute is what the conditions ask for.
-/

namespace Lax391470Proofs.V2Link

open Lax391470Proofs.V2Ord Lax391470Proofs.V2Pair Lax391470Proofs.V2Sem
open Lax391470Proofs.VPairs Lax391470Proofs.L1Ordered

lemma split3 (n N : ℕ) (Q : ℕ → Prop) :
    (∀ j < n + 2 * N, Q j) ↔
      (∀ o < n, Q o) ∧ (∀ i < N, Q (n + i)) ∧ (∀ i < N, Q (n + N + i)) := by
  constructor
  · intro h
    exact ⟨fun o ho => h o (by omega), fun i hi => h _ (by omega), fun i hi => h _ (by omega)⟩
  · rintro ⟨h1, h2, h3⟩ j hj
    by_cases a : j < n
    · exact h1 j a
    · by_cases b : j < n + N
      · have := h2 (j - n) (by omega)
        rwa [show n + (j - n) = j by omega] at this
      · have := h3 (j - n - N) (by omega)
        rwa [show n + N + (j - n - N) = j by omega] at this

variable (p q : ℕ) (t : List ℕ) (n N : ℕ)

/-- **What the two passes leave in the arrays** are the start times and lengths of all
jobs of the underlying instance. -/
theorem values (tt pp : List ℕ) (hn : t.getD 0 0 = n) (hN : t.getD 1 0 = N)
    (ho : ∀ o < n, tt.getD o 0 = t.getD (2 + 3 * n + 4 * N + o) 0 ∧
      pp.getD o 0 = lenO p q t o)
    (hp : ∀ i < N, tt.getD (n + i) 0 = t.getD (2 + 3 * n + 4 * N + (n + i)) 0 ∧
      pp.getD (n + i) 0 = p ∧
      tt.getD (n + N + i) 0 = t.getD (2 + 3 * n + 4 * N + (n + N + i)) 0 ∧
      pp.getD (n + N + i) 0 = q) :
    ∀ j < n + 2 * N, tt.getD j 0 = tOf t j ∧ pp.getD j 0 = pOf p q t j := by
  have eS : ∀ j, 2 + 3 * n + 4 * N + j = iS n N j := fun j => by unfold iS; omega
  have hT : ∀ j, tOf t j = t.getD (2 + 3 * n + 4 * N + j) 0 := fun j => by
    unfold tOf; rw [hn, hN, eS]
  refine (split3 n N _).mpr ⟨fun o h => ?_, fun i h => ?_, fun i h => ?_⟩
  · refine ⟨by rw [(ho o h).1, hT], ?_⟩
    rw [(ho o h).2]; unfold lenO pOf; rw [hn, if_pos h]
  · refine ⟨by rw [(hp i h).1, hT], ?_⟩
    rw [(hp i h).2.1]; unfold pOf; rw [hn, hN]; split_ifs <;> first | omega
  · refine ⟨by rw [(hp i h).2.2.1, hT], ?_⟩
    rw [(hp i h).2.2.2]; unfold pOf; rw [hn, hN]; split_ifs <;> first | omega

/-- **The two passes check feasibility and the early deadlines.** -/
theorem link_fe (hn : t.getD 0 0 = n) (hN : t.getD 1 0 = N) :
    ((∀ o < n, FO p q t (2 + 3 * n + 4 * N) o) ∧
      ∀ i < N, FP p q t (2 + 3 * n) (2 + 3 * n + 4 * N) n (n + N) i) ↔
      FE p q t ∧ EP p q t := by
  have eS : ∀ j, 2 + 3 * n + 4 * N + j = iS n N j := fun j => by unfold iS; omega
  have eE : ∀ i c, 2 + 3 * n + (4 * i + c) = 2 + (3 * n + (4 * i + c)) := fun i c => by omega
  unfold FE EP
  rw [hn, hN, split3]
  have hA : ∀ o < n, (rOf t o ≤ tOf t o ∧ tOf t o + pOf p q t o ≤ dOf t o) ↔
      FO p q t (2 + 3 * n + 4 * N) o := by
    intro o ho
    unfold rOf tOf pOf dOf FO
    rw [hn, hN, if_pos ho, if_pos ho, if_pos ho, eS]
  have r1 : ∀ i, rOf t (n + i) = 0 := fun i => by
    unfold rOf; rw [hn]; split_ifs with h
    · omega
    · rfl
  have p1 : ∀ i < N, pOf p q t (n + i) = p := fun i hi => by
    unfold pOf; rw [hn, hN]; split_ifs <;> first | omega
  have p2 : ∀ i, pOf p q t (n + N + i) = q := fun i => by
    unfold pOf; rw [hn, hN]; split_ifs <;> first | omega
  have d1 : ∀ i < N, dOf t (n + i) = ev t n i 1 := fun i hi => by
    unfold dOf; rw [hn, hN]; split_ifs
    · omega
    · rw [Nat.add_sub_cancel_left]
    · omega
  have d2 : ∀ i, dOf t (n + N + i) = ev t n i 3 := fun i => by
    unfold dOf; rw [hn, hN]; split_ifs
    · omega
    · omega
    · rw [show n + N + i - n - N = i by omega]
  have hB : ∀ i < N, (rOf t (n + i) ≤ tOf t (n + i) ∧
      tOf t (n + i) + pOf p q t (n + i) ≤ dOf t (n + i)) ↔
      t.getD (2 + 3 * n + 4 * N + (n + i)) 0 + p ≤ t.getD (2 + 3 * n + (4 * i + 1)) 0 := by
    intro i hi
    rw [r1, p1 i hi, d1 i hi]
    unfold tOf ev
    rw [hn, hN, eS, eE]
    exact ⟨fun h => h.2, fun h => ⟨Nat.zero_le _, h⟩⟩
  have hC : ∀ i < N, (rOf t (n + N + i) ≤ tOf t (n + N + i) ∧
      tOf t (n + N + i) + pOf p q t (n + N + i) ≤ dOf t (n + N + i)) ↔
      t.getD (2 + 3 * n + 4 * N + (n + N + i)) 0 + q ≤ t.getD (2 + 3 * n + (4 * i + 3)) 0 := by
    intro i hi
    rw [show n + N + i = n + (N + i) by omega, r1, ← show n + N + i = n + (N + i) by omega,
      p2, d2]
    unfold tOf ev
    rw [hn, hN, eS, eE]
    exact ⟨fun h => h.2, fun h => ⟨Nat.zero_le _, h⟩⟩
  have hE : ∀ i < N, (tOf t (n + i) + p ≤ ev t n i 0 ∨ tOf t (n + N + i) + q ≤ ev t n i 2) ↔
      (t.getD (2 + 3 * n + 4 * N + (n + i)) 0 + p ≤ t.getD (2 + 3 * n + (4 * i + 0)) 0 ∨
        t.getD (2 + 3 * n + 4 * N + (n + N + i)) 0 + q ≤
          t.getD (2 + 3 * n + (4 * i + 2)) 0) := by
    intro i hi
    unfold tOf ev
    rw [hn, hN, eS, eS, eE, eE]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun o ho => (hA o ho).mpr (h1 o ho), fun i hi => (hB i hi).mpr (h2 i hi).1,
      fun i hi => (hC i hi).mpr (h2 i hi).2.1⟩, fun i hi => (hE i hi).mpr (h2 i hi).2.2⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    exact ⟨fun o ho => (hA o ho).mp (h1 o ho),
      fun i hi => ⟨(hB i hi).mp (h2 i hi), (hC i hi).mp (h3 i hi), (hE i hi).mp (h4 i hi)⟩⟩

/-- **The double loop checks that no two jobs overlap.** -/
theorem link_ov (tt pp : List ℕ) (hn : t.getD 0 0 = n) (hN : t.getD 1 0 = N)
    (hv : ∀ j < n + 2 * N, tt.getD j 0 = tOf t j ∧ pp.getD j 0 = pOf p q t j) :
    (∀ i < n + 2 * N, ∀ j < n + 2 * N, fine tt pp i j) ↔ OV p q t := by
  unfold OV
  rw [hn, hN]
  refine forall₂_congr fun i hi => forall₂_congr fun j hj => ?_
  unfold fine
  rw [(hv i hi).1, (hv i hi).2, (hv j hj).1, (hv j hj).2]
  tauto

/-- The conditions only look at the first `2 + 3n + 4N + (n + 2N)` values. -/
theorem sem_congr {tk tk' : List ℕ} (h0 : tk.getD 0 0 = n) (h1 : tk.getD 1 0 = N)
    (hk : ∀ k < 2 + (3 * n + 4 * N + (n + 2 * N)), tk'.getD k 0 = tk.getD k 0) :
    Sem p q tk' ↔ Sem p q tk := by
  have h0' : tk'.getD 0 0 = n := by rw [hk 0 (by omega), h0]
  have h1' : tk'.getD 1 0 = N := by rw [hk 1 (by omega), h1]
  have hr : ∀ j < n + 2 * N, rOf tk' j = rOf tk j := fun j hj => by
    unfold rOf; rw [h0', h0]; split_ifs
    · exact hk _ (by omega)
    · rfl
  have ht : ∀ j < n + 2 * N, tOf tk' j = tOf tk j := fun j hj => by
    unfold tOf; rw [h0', h0, h1', h1]; exact hk _ (by unfold iS; omega)
  have hp : ∀ j < n + 2 * N, pOf p q tk' j = pOf p q tk j := fun j hj => by
    unfold pOf; rw [h0', h0, h1', h1]
    by_cases hj' : j < n
    · rw [if_pos hj', if_pos hj', hk _ (by omega)]
    · rw [if_neg hj', if_neg hj']
  have he : ∀ i < N, ∀ c < 4, ev tk' n i c = ev tk n i c := fun i hi c hc => by
    unfold ev; exact hk _ (by omega)
  have hd : ∀ j < n + 2 * N, dOf tk' j = dOf tk j := fun j hj => by
    unfold dOf; rw [h0', h0, h1', h1]; split_ifs
    · exact hk _ (by omega)
    · exact he _ (by omega) _ (by omega)
    · exact he _ (by omega) _ (by omega)
  unfold Sem
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · unfold OrdOK PairOK
    rw [h0', h0, h1', h1]
    refine forall₂_congr fun i hi => ?_
    rw [he i hi 0 (by omega), he i hi 1 (by omega), he i hi 2 (by omega), he i hi 3 (by omega)]
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
      (imp_congr_right fun hi' => ?_)))
    rw [he _ hi' 0 (by omega), he _ hi' 2 (by omega)]
  · unfold FE
    rw [h0', h0, h1', h1]
    refine forall₂_congr fun j hj => ?_
    rw [hr j hj, ht j hj, hp j hj, hd j hj]
  · unfold OV
    rw [h0', h0, h1', h1]
    refine forall₂_congr fun i hi => forall₂_congr fun j hj => ?_
    rw [ht i hi, ht j hj, hp i hi, hp j hj]
  · unfold EP
    rw [h0', h0, h1', h1]
    refine forall₂_congr fun i hi => ?_
    rw [ht _ (show n + i < n + 2 * N by omega), ht _ (show n + N + i < n + 2 * N by omega),
      he i hi 0 (by omega), he i hi 2 (by omega)]

end Lax391470Proofs.V2Link
