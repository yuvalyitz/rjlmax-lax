import Lax391470Proofs.V1Front
import Lax391470Proofs.VPairs
import Lax391470Proofs.V1Sem

/-!
What the two loops of the verifier compute on shifted natural numbers is what the
conditions on integers ask for.
-/

namespace Lax391470Proofs.V1Link

open Lax391470Proofs.V1Front Lax391470Proofs.VPairs Lax391470Proofs.V1Sem

/-- The integer with sign `s` and absolute value `a`. -/
def zz (s a : ℕ) : ℤ := if s = 0 then (a : ℤ) else -(a : ℤ)

lemma sh_le_iff {O s a s' a' : ℕ} (ha : a ≤ O) (ha' : a' ≤ O) :
    sh O s a ≤ sh O s' a' ↔ zz s a ≤ zz s' a' := by
  unfold sh zz; split_ifs <;> omega

lemma sh_add_le_iff {O s a s' a' : ℕ} (P : ℕ) (ha : a ≤ O) (ha' : a' ≤ O) :
    sh O s a + P ≤ sh O s' a' ↔ zz s a + P ≤ zz s' a' := by
  unfold sh zz; split_ifs <;> omega

variable (p q : ℕ) (tk tt pp : List ℕ) (Ov n : ℕ)

/-- **The link.** -/
theorem link (hn : tk.getD 0 0 = n) (hO : ∀ k < 1 + 7 * n, tk.getD k 0 ≤ Ov)
    (hv : ∀ j < n, tt.getD j 0 = ttv Ov tk n j ∧ pp.getD j 0 = ppv tk j) :
    ((∀ j < n, FOK p q Ov tk n j) ∧ ∀ i < n, ∀ j < n, fine tt pp i j) ↔
      NZ tk ∧ AV p q tk ∧ OV tk := by
  unfold NZ AV OV
  rw [hn]
  have hA : ∀ j < n, FOK p q Ov tk n j ↔
      ((¬ (tk.getD (iJ j 0) 0 ≠ 0 ∧ tk.getD (iJ j 1) 0 = 0) ∧
        ¬ (tk.getD (iJ j 2) 0 ≠ 0 ∧ tk.getD (iJ j 3) 0 = 0)) ∧
      ((tk.getD (iJ j 4) 0 = p ∨ tk.getD (iJ j 4) 0 = q) ∧
        zv tk (iJ j 0) (iJ j 1) ≤ zv tk (iT n j 0) (iT n j 1) ∧
        zv tk (iT n j 0) (iT n j 1) + tk.getD (iJ j 4) 0 ≤ zv tk (iJ j 2) (iJ j 3))) := by
    intro j hj
    unfold FOK
    rw [sh_le_iff (hO _ (by omega)) (hO _ (by omega)),
      sh_add_le_iff _ (hO _ (by omega)) (hO _ (by omega))]
    simp only [zv, zz]
    tauto
  have hF : ∀ i < n, ∀ j < n, fine tt pp i j ↔ (i ≠ j →
      zv tk (iT n i 0) (iT n i 1) + tk.getD (iJ i 4) 0 ≤ zv tk (iT n j 0) (iT n j 1) ∨
      zv tk (iT n j 0) (iT n j 1) + tk.getD (iJ j 4) 0 ≤ zv tk (iT n i 0) (iT n i 1)) := by
    intro i hi j hj
    unfold fine
    rw [(hv i hi).1, (hv i hi).2, (hv j hj).1, (hv j hj).2]
    unfold ttv ppv
    rw [sh_add_le_iff _ (hO _ (by omega)) (hO _ (by omega)),
      sh_add_le_iff _ (hO _ (by omega)) (hO _ (by omega))]
    simp only [zv, zz]
    tauto
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun j hj => ((hA j hj).mp (h1 j hj)).1, fun j hj => ((hA j hj).mp (h1 j hj)).2,
      fun i hi j hj => (hF i hi j hj).mp (h2 i hi j hj)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun j hj => (hA j hj).mpr ⟨h1 j hj, h2 j hj⟩,
      fun i hi j hj => (hF i hi j hj).mpr (h3 i hi j hj)⟩

/-- The conditions only look at the first `1 + 7 n` values. -/
theorem sem_congr {tk tk' : List ℕ} (h0 : tk.getD 0 0 = n)
    (hk : ∀ k < 1 + 7 * n, tk'.getD k 0 = tk.getD k 0) :
    (NZ tk' ∧ AV p q tk' ∧ OV tk') ↔ (NZ tk ∧ AV p q tk ∧ OV tk) := by
  have h0' : tk'.getD 0 0 = n := by rw [hk 0 (by omega), h0]
  unfold NZ AV OV zv
  rw [h0', h0]
  refine and_congr (forall₂_congr fun j hj => ?_) (and_congr (forall₂_congr fun j hj => ?_)
    (forall₂_congr fun i hi => forall₂_congr fun j hj => ?_))
  · rw [hk (iJ j 0) (by unfold iJ; omega), hk (iJ j 1) (by unfold iJ; omega), hk (iJ j 2) (by unfold iJ; omega),
      hk (iJ j 3) (by unfold iJ; omega)]
  · rw [hk (iJ j 0) (by unfold iJ; omega), hk (iJ j 1) (by unfold iJ; omega), hk (iJ j 2) (by unfold iJ; omega),
      hk (iJ j 3) (by unfold iJ; omega), hk (iJ j 4) (by unfold iJ; omega), hk (iT n j 0) (by unfold iT; omega),
      hk (iT n j 1) (by unfold iT; omega)]
  · rw [hk (iJ j 4) (by unfold iJ; omega), hk (iT n j 0) (by unfold iT; omega), hk (iT n j 1) (by unfold iT; omega),
      hk (iJ i 4) (by unfold iJ; omega), hk (iT n i 0) (by unfold iT; omega), hk (iT n i 1) (by unfold iT; omega)]

end Lax391470Proofs.V1Link
