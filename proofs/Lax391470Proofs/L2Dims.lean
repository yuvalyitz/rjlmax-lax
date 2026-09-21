import Lax391470Proofs.L2Fill
import Lax391470Proofs.L2Active
import Lax391470Proofs.SatBridge

/-!
The table the fill loop leaves is the table of active blocks, and its cells are in range.
-/

namespace Lax391470Proofs.L2Dims

open Lax429075.CNF Lax391470.SatConstruction
open Lax391470Proofs.L2ScanModel Lax391470Proofs.L2Active Lax391470Proofs.L2Fill

variable (F : Formula)

def dflt : Literal := ⟨0, false⟩

def ivF (i : ℕ) : ℕ := ((lits F).getD i dflt).index
def svF (i : ℕ) : ℕ := if ((lits F).getD i dflt).positive then 1 else 0
def cvF (i : ℕ) : ℕ := (cn F).getD i 0

lemma cell_eq (i : ℕ) :
    cell F.length (ivF F) (svF F) (cvF F) i =
      secOf ((lits F).getD i dflt) * F.length + (cn F).getD i 0 := by
  unfold cell ivF svF cvF secOf
  cases ((lits F).getD i dflt).positive <;> simp

lemma mem_zip_iff (x : Literal × ℕ) :
    x ∈ (lits F).zip (cn F) ↔
      ∃ i < (lits F).length, x = ((lits F).getD i dflt, (cn F).getD i 0) := by
  have hl := cn_length F
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hi' : i < (lits F).length := by simpa [hl] using hi
    refine ⟨i, hi', ?_⟩
    rw [List.getElem_zip, List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ (by omega)]
  · rintro ⟨i, hi, rfl⟩
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by omega : i < (cn F).length)]
    rw [← List.getElem_zip (l := lits F) (l' := cn F) (h := by simp [hl, hi])]
    exact List.getElem_mem _

theorem pre_eq_table (t : ℕ) :
    pre F.length (ivF F) (svF F) (cvF F) (lits F).length t = table F t := by
  classical
  unfold pre table
  congr 1
  refine propext ⟨?_, ?_⟩
  · rintro ⟨i, hi, he⟩
    exact ⟨_, (mem_zip_iff F _).mpr ⟨i, hi, rfl⟩, by rw [← he, cell_eq]⟩
  · rintro ⟨x, hx, he⟩
    obtain ⟨i, hi, rfl⟩ := (mem_zip_iff F x).mp hx
    exact ⟨i, hi, by rw [cell_eq]; exact he⟩

lemma table_le_one (t : ℕ) : table F t ≤ 1 := by
  classical
  unfold table; split <;> omega

/-- Every marked cell lies below `2 · n · m`. -/
lemma cell_lt (i : ℕ) (hi : i < (lits F).length) :
    cell F.length (ivF F) (svF F) (cvF F) i < 2 * numVars F * F.length := by
  rw [cell_eq]
  have hmem : ((lits F).getD i dflt, (cn F).getD i 0) ∈ (lits F).zip (cn F) :=
    (mem_zip_iff F _).mpr ⟨i, hi, rfl⟩
  have hj := snd_lt_of_mem_zip F hmem
  have hl : (lits F).getD i dflt ∈ lits F := by
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
  have hidx : ((lits F).getD i dflt).index < numVars F := SatBridge.index_lt_foldr _ hl
  have hsec : secOf ((lits F).getD i dflt) + 1 ≤ 2 * numVars F := by
    unfold secOf; split <;> omega
  have := Nat.mul_le_mul_right F.length hsec
  simp only at hj
  rw [Nat.add_mul] at this
  omega

lemma table_zero (t : ℕ) (ht : 2 * numVars F * F.length ≤ t) : table F t = 0 := by
  rw [← pre_eq_table]
  classical
  unfold pre
  rw [if_neg]
  rintro ⟨i, hi, he⟩
  have := cell_lt F i hi
  omega

end Lax391470Proofs.L2Dims
