import Lax391470.SatConstruction
import Lax391470Proofs.TypedSat

/-!
A formula of the archive read as a formula of the typed development.
-/

namespace Lax391470Proofs.SatBridge

open Lax391470 Lax391470.SatConstruction Lax429075

lemma index_lt_foldr (L : List CNF.Literal) {l : CNF.Literal} (hl : l ∈ L) :
    l.index < L.foldr (fun l n => max (l.index + 1) n) 1 := by
  induction L with
  | nil => cases hl
  | cons a L ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hl with rfl | h
    · omega
    · have := ih h; omega

lemma index_lt (F : CNF.Formula) {C : CNF.Clause} (hC : C ∈ F) {l : CNF.Literal}
    (hl : l ∈ C) : l.index < numVars F :=
  index_lt_foldr _ (List.mem_flatMap.mpr ⟨C, hC, hl⟩)

/-- The archive's formula as a typed one. -/
def toCnf (F : CNF.Formula) : Sat.Cnf where
  n := numVars F
  m := F.length
  clause j := Finset.univ.filter fun l : Sat.Literal (numVars F) =>
    (⟨l.var, l.pos⟩ : CNF.Literal) ∈ F.getD j []

theorem satisfiable_iff (F : CNF.Formula) : CNF.Satisfiable F ↔ (toCnf F).Satisfiable := by
  constructor
  · rintro ⟨ρ, hρ⟩
    refine ⟨fun i => ρ i, fun j => ?_⟩
    have hj : (j : ℕ) < F.length := j.isLt
    simp only [CNF.eval, List.all_eq_true, List.any_eq_true] at hρ
    obtain ⟨l, hl, hev⟩ := hρ F[j] (List.getElem_mem hj)
    have hlt := index_lt F (List.getElem_mem hj) hl
    refine ⟨⟨⟨l.index, hlt⟩, l.positive⟩, ?_, ?_⟩
    · have hg : F.getD (j : ℕ) [] = F[j] := List.getD_eq_getElem _ _ hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hg]; exact hl⟩
    · obtain ⟨idx, pos⟩ := l
      cases pos <;> simp_all [Sat.Literal.Holds, CNF.Literal.eval]
  · rintro ⟨v, hv⟩
    refine ⟨fun i => if h : i < numVars F then v ⟨i, h⟩ else false, ?_⟩
    simp only [CNF.eval, List.all_eq_true, List.any_eq_true]
    intro C hC
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hC
    obtain ⟨l, hl, hholds⟩ := hv ⟨j, hj⟩
    have hg : F.getD j [] = F[j] := List.getD_eq_getElem _ _ hj
    have hl' : (⟨l.var, l.pos⟩ : CNF.Literal) ∈ F[j] := by
      have := (Finset.mem_filter.mp hl).2
      rwa [hg] at this
    refine ⟨_, hl', ?_⟩
    obtain ⟨⟨idx, hidx⟩, pos⟩ := l
    have hidx' : idx < numVars F := hidx
    simp only [Sat.Literal.Holds] at hholds
    cases pos <;> simp_all [CNF.Literal.eval]

end Lax391470Proofs.SatBridge
