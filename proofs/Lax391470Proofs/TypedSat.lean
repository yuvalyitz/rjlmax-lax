import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.DeriveFintype

namespace Lax391470Proofs

/-!
# Boolean satisfiability

CNF-SAT, the source of most NP-hardness proofs and of the reduction in
`RjLmax.FromSat`. A formula has `n` variables and `m` clauses; a clause is a finite set
of literals, and a literal is a variable together with a sign.

Both the variables and the clauses are *indexed* — `Fin n` and `Fin m` rather than
abstract finite types — because a reduction that lays gadgets out on a time line needs to
put them in an order, and the order is part of the construction rather than an artifact of
it. `Fin` supplies one canonically.
-/

namespace Sat

set_option genSizeOfSpec false in
/-- A literal over `n` Boolean variables: a variable index and a sign. `pos = false`
is the negated literal `¬xᵢ`. -/
structure Literal (n : ℕ) where
  /-- The variable the literal refers to. -/
  var : Fin n
  /-- `true` for `xᵢ`, `false` for `¬xᵢ`. -/
  pos : Bool
deriving DecidableEq, Fintype

namespace Literal

variable {n : ℕ}

/-- The negation of a literal. -/
def neg (l : Literal n) : Literal n := ⟨l.var, !l.pos⟩

/-- The assignment `v` makes the literal true. -/
def Holds (v : Fin n → Bool) (l : Literal n) : Prop := v l.var = l.pos

instance (v : Fin n → Bool) (l : Literal n) : Decidable (Holds v l) := by
  unfold Holds; infer_instance

/-- Exactly one of `l` and `¬l` holds. -/
lemma holds_neg_iff (v : Fin n → Bool) (l : Literal n) : Holds v l.neg ↔ ¬ Holds v l := by
  simp only [Holds, neg]
  cases v l.var <;> cases l.pos <;> simp

end Literal

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- **Definition 5 (Boolean Satisfiability).** A formula in conjunctive normal form:
`n` variables, `m` clauses, each clause a finite set of literals. -/
structure Cnf where
  /-- The number of variables. -/
  n : ℕ
  /-- The number of clauses. -/
  m : ℕ
  /-- The literals of each clause. -/
  clause : Fin m → Finset (Literal n)

namespace Cnf

variable (φ : Cnf)

/-- An assignment of a truth value to every variable. -/
abbrev Assignment : Type := Fin φ.n → Bool

variable {φ}

/-- `v` satisfies `φ`: every clause contains a literal that holds. -/
def Satisfies (v : φ.Assignment) : Prop := ∀ j, ∃ l ∈ φ.clause j, Literal.Holds v l

variable (φ)

/-- **The question of Definition 5**: is there a satisfying assignment? -/
def Satisfiable : Prop := ∃ v : φ.Assignment, Satisfies v

end Cnf

end Sat

end Lax391470Proofs
