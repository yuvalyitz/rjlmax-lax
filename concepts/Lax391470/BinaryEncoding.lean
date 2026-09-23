import Lax391470.AuxiliaryProblem
import Lax434930.PolynomialTime
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits

/-!
---
title: Binary encodings and the two languages
type: definition
---
Scheduling instances and instances of the auxiliary problem as binary words, the
representation against which classical complexity measures running time, and the two
decision problems of this submission as languages of such words.

A natural number is written as its binary digits preceded by their number in unary,
which makes the code self-delimiting; an integer is a sign bit followed by its absolute
value. A scheduling instance is the number of jobs followed by the release time, the
deadline and the processing time of every job in turn. An instance of the auxiliary
problem is the number of ordinary jobs, the number of connected pairs, then for every
ordinary job its release time, its deadline and one bit telling whether it is long, then
for every connected pair its four deadlines.

For fixed job lengths $p$ and $q$, the language of *scheduling on the lengths
$\{p, q\}$* consists of the encodings of the instances on those lengths that have a
feasible schedule, and the language $\mathrm{AUX}(p, q)$ consists of the encodings of the
ordered instances of the auxiliary problem that have a solution at those lengths.

# Formalization notes

Numbers are written in binary, the usual convention, under which NP-hardness is the
usual claim. Hardness under a unary encoding of the scheduling instance would be the
stronger claim, strong NP-hardness: the reduction would then have to produce numbers
bounded by a polynomial in its input, since a unary word must stay polynomially long. That
this reduction does produce such numbers, which is what the source's claim of strong
NP-completeness rests on, is recorded separately.

The job lengths $p$ and $q$ are parameters of the language and not part of the input:
the theorem is about every fixed pair of lengths. A word that encodes no instance, or an
instance with a processing time outside $\{p, q\}$, or an instance of the auxiliary
problem whose deadlines are not ordered, belongs to neither language.
-/

namespace Lax391470.BinaryEncoding

open Lax434930.PolynomialTime

/-- A natural number as a binary word: its digits, least significant first, preceded by
their number in unary. -/
def encodeNat (n : ℕ) : Word :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

/-- An integer as a binary word: one bit for the sign, then the absolute value. -/
def encodeInt (z : ℤ) : Word := decide (z < 0) :: encodeNat z.natAbs

/-- A scheduling instance as a binary word. -/
def encodeInstance (I : Scheduling.Instance) : Word :=
  encodeNat I.jobs ++
    (List.finRange I.jobs).flatMap fun j =>
      encodeInt (I.r j) ++ encodeInt (I.d j) ++ encodeNat (I.p j)

/-- An instance of the auxiliary problem as a binary word. -/
def encodeAux (A : AuxiliaryProblem.Instance) : Word :=
  encodeNat A.ordinary ++ encodeNat A.pairs ++
    ((List.finRange A.ordinary).flatMap fun o =>
      encodeNat (A.r o) ++ encodeNat (A.d o) ++ [A.long o]) ++
    (List.finRange A.pairs).flatMap fun i =>
      encodeNat (A.longEarly i) ++ encodeNat (A.longDue i) ++
        encodeNat (A.shortEarly i) ++ encodeNat (A.shortDue i)

/-- **Scheduling on the lengths `{p, q}`**, as a language. -/
def TwoLengths (p q : ℕ) : Language :=
  {w | ∃ I : Scheduling.Instance, encodeInstance I = w ∧ I.LengthsIn p q ∧ I.Schedulable}

/-- **The auxiliary problem `AUX(p, q)`**, as a language. -/
def AUX (p q : ℕ) : Language :=
  {w | ∃ A : AuxiliaryProblem.Instance, encodeAux A = w ∧ A.Ordered ∧ A.Solvable p q}

end Lax391470.BinaryEncoding
