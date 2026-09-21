import Lax391470Proofs.V1Format

/-!
What the verifier of `TwoLengths p q` checks, on the values of the tokens, and what that
means for the instance and the schedule the tokens describe.
-/

namespace Lax391470Proofs.V1Sem

open Lax391470 Lax391470.Scheduling Lax391470Proofs.TokModel Lax391470Proofs.TokProg
open Lax391470Proofs.InstFormat Lax391470Proofs.V1Format

/-- The integer with sign at position `ks` and absolute value at position `ka`. -/
def zv (tk : List ℕ) (ks ka : ℕ) : ℤ :=
  if tk.getD ks 0 = 0 then (tk.getD ka 0 : ℤ) else -(tk.getD ka 0 : ℤ)

/-- The positions of the data of job `j`. -/
abbrev iJ (j c : ℕ) : ℕ := 1 + (5 * j + c)
/-- The positions of the start time of job `j`. -/
abbrev iT (n j c : ℕ) : ℕ := 1 + (5 * n + (2 * j + c))

/-- No release time or deadline is written as `-0`. -/
def NZ (tk : List ℕ) : Prop :=
  ∀ j < tk.getD 0 0,
    ¬ (tk.getD (iJ j 0) 0 ≠ 0 ∧ tk.getD (iJ j 1) 0 = 0) ∧
    ¬ (tk.getD (iJ j 2) 0 ≠ 0 ∧ tk.getD (iJ j 3) 0 = 0)

/-- Every length is `p` or `q`, and every job runs inside its interval. -/
def AV (p q : ℕ) (tk : List ℕ) : Prop :=
  ∀ j < tk.getD 0 0,
    (tk.getD (iJ j 4) 0 = p ∨ tk.getD (iJ j 4) 0 = q) ∧
    zv tk (iJ j 0) (iJ j 1) ≤ zv tk (iT (tk.getD 0 0) j 0) (iT (tk.getD 0 0) j 1) ∧
    zv tk (iT (tk.getD 0 0) j 0) (iT (tk.getD 0 0) j 1) + tk.getD (iJ j 4) 0 ≤
      zv tk (iJ j 2) (iJ j 3)

/-- No two jobs overlap. -/
def OV (tk : List ℕ) : Prop :=
  ∀ i < tk.getD 0 0, ∀ j < tk.getD 0 0, i ≠ j →
    zv tk (iT (tk.getD 0 0) i 0) (iT (tk.getD 0 0) i 1) + tk.getD (iJ i 4) 0 ≤
        zv tk (iT (tk.getD 0 0) j 0) (iT (tk.getD 0 0) j 1) ∨
      zv tk (iT (tk.getD 0 0) j 0) (iT (tk.getD 0 0) j 1) + tk.getD (iJ j 4) 0 ≤
        zv tk (iT (tk.getD 0 0) i 0) (iT (tk.getD 0 0) i 1)

/-- The token values describe the instance `I` and the schedule `t`. -/
inductive Reads (I : Scheduling.Instance) (t : I.Schedule) (tk : List ℕ) : Prop where
  | mk
    (n : tk.getD 0 0 = I.jobs)
    (r : ∀ j : Fin I.jobs, zv tk (iJ j 0) (iJ j 1) = I.r j)
    (d : ∀ j : Fin I.jobs, zv tk (iJ j 2) (iJ j 3) = I.d j)
    (p : ∀ j : Fin I.jobs, tk.getD (iJ j 4) 0 = I.p j)
    (t : ∀ j : Fin I.jobs, zv tk (iT I.jobs j 0) (iT I.jobs j 1) = t j)
/-- **The checks mean what they should.** -/
theorem feas_iff {I : Scheduling.Instance} {t : I.Schedule} {tk : List ℕ} (h : Reads I t tk)
    (p q : ℕ) : AV p q tk ∧ OV tk ↔ I.LengthsIn p q ∧ Instance.Feasible t := by
  obtain ⟨hn, hr, hd, hp, ht⟩ := h
  unfold AV OV
  rw [hn]
  constructor
  · rintro ⟨hav, hov⟩
    refine ⟨fun j => ?_, fun j => ?_, fun i j hij => ?_⟩
    · have := (hav j j.isLt).1
      rw [hp j] at this; exact this
    · have := (hav j j.isLt).2
      rw [hr j, hd j, hp j, ht j] at this; exact this
    · have := hov i i.isLt j j.isLt (fun h => hij (Fin.ext h))
      rw [ht i, ht j, hp i, hp j] at this; exact this
  · rintro ⟨hl, hav, hov⟩
    refine ⟨fun j hj => ?_, fun i hi j hj hij => ?_⟩
    · have h1 := hl ⟨j, hj⟩
      have h2 := hav ⟨j, hj⟩
      rw [← hp ⟨j, hj⟩] at h1
      rw [← hr ⟨j, hj⟩, ← hd ⟨j, hj⟩, ← hp ⟨j, hj⟩, ← ht ⟨j, hj⟩] at h2
      exact ⟨h1, h2⟩
    · have := hov ⟨i, hi⟩ ⟨j, hj⟩ (fun h => hij (congrArg Fin.val h))
      rw [← ht ⟨i, hi⟩, ← ht ⟨j, hj⟩, ← hp ⟨i, hi⟩, ← hp ⟨j, hj⟩] at this
      exact this

/-! ### Reading values off tokens -/

lemma val_getD (ts : List Tok) (k : ℕ) :
    (ts.map Tok.val).getD k 0 = Tok.val (ts.getD k (.bit false)) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ts[k]? <;> rfl

lemma zv_toks {ts : List Tok} {ks ka : ℕ} {b : Bool} {v : ℕ}
    (hs : ts.getD ks (.bit false) = .bit b) (ha : ts.getD ka (.bit false) = .num v) :
    zv (ts.map Tok.val) ks ka = toInt b v := by
  unfold zv toInt
  rw [val_getD, val_getD, hs, ha]
  cases b <;> simp [Tok.val]

end Lax391470Proofs.V1Sem
