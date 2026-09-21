import Lax391470Proofs.TypedSat
import Lax391470Proofs.TypedBlocks

namespace Lax391470Proofs

namespace RjLmax

/-- `AUX(p, q)`. -/
def auxProblem (p q : ℕ) : Aux p q → Prop := fun A => A.Yes

/-- CNF-SAT. -/
def satProblem : Sat.Cnf → Prop := fun φ => φ.Satisfiable

end RjLmax

end Lax391470Proofs
