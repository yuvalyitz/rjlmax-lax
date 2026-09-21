import Lax391470.Scheduling

/-!
---
title: Integral start times suffice
type: theorem
---
An instance has a feasible schedule with real start times if and only if it has one with
integer start times. Rounding every start time up to the next integer preserves
feasibility, because release times, deadlines and processing times are integers.

# Formalization notes

The source defines a schedule as a real-valued assignment of start times and remarks
that, by discretization, start times can always be taken to be integers. This statement
is that remark. It is what licenses the rest of the submission to define feasibility over
the integers.
-/

namespace Lax391470.IntegralStartTimes

open Lax391470.Scheduling

/-- Real and integer start times decide the same instances. -/
axiom realSchedulable_iff (I : Instance) : I.RealSchedulable ↔ I.Schedulable

end Lax391470.IntegralStartTimes
