# Scheduling with Two Non-Unit Job Lengths Is NP-Complete

A [Lax archive](https://github.com/lax-archive/lax) submission (`lax-391470`) formalizing the theorem of
Elffers and de Weerdt ([arXiv:1412.3095](https://arxiv.org/abs/1412.3095)): for every fixed
pair of integer job lengths `p > q > 1`, single-machine scheduling with release times and
deadlines restricted to the job lengths `{p, q}` is NP-complete. The polynomial bound on the
reduction's numbers, the basis of the paper's strong NP-completeness, is proved as well.

**Status: complete.** All 19 statements are proved, with no `sorry`. Besides Lean's three
standard axioms, the proofs assume only statements of other archive submissions, each of
which the archive records as proved (see Dependencies). See `abstract.md` for the
mathematics.

## Prerequisites

Lean `v4.33.0` via [elan](https://github.com/leanprover/elan), and the
[`lax` CLI](https://github.com/lax-archive/lax). The mathlib revision is pinned in `manifest.yaml`; Lake
fetches it on first build.

## Verification

Run the archive validation:

    lax build .

The final stage, *Inspecting the statements*, pairs each statement with its proof and
reports `9 concepts · 19 proofs`. The external assumptions are listed under Dependencies.

To check a single module while editing, from `proofs/`:

    lake build Lax391470Proofs.V1Final

To audit axioms yourself, write a scratch file **outside** the package:

    cat > /tmp/ax.lean <<'LEAN'
    import Lax391470Proofs
    #print axioms Lax391470Proofs.V1Final.twoLengths_mem_NP
    LEAN

and run `lake env lean /tmp/ax.lean` from `proofs/`. Expect `propext`, `Classical.choice`,
`Quot.sound`, and the cited statement
`Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime`.

> Anything placed inside `proofs/Lax391470Proofs/` must also be imported by
> `Lax391470Proofs.lean`, or the build is rejected. Keep scratch work elsewhere.

## Reading Guide

The `concepts/` directory contains the definitions and theorem statements; `proofs/`
contains their Lean proofs. Start with the definitions, encodings, and main theorems.

Suggested order:

1. `abstract.md` — the argument in prose.
2. `concepts/Lax391470/Scheduling.lean` — the problem: instances, feasibility, schedulability.
3. `concepts/Lax391470/BinaryEncoding.lean` — how an instance becomes a word, and the
   languages `TwoLengths p q` and `AUX p q`. This is where a scheduling problem becomes a
   formal language, so it deserves the closest reading.
4. `concepts/Lax391470/Theorem1.lean` — the main NP-completeness theorem.
5. The machinery: `AuxiliaryProblem`, `SatConstruction`, `StackedConstruction`, `Lemma2`,
   `Lemma1`.

In `proofs/`, the readable entry point is `Hardness.lean`;
`V1Final.lean` and `V2Final.lean` carry the two NP-membership arguments.

## Layout

    manifest.yaml     id, title, authors, pinned Lean + mathlib, bibliography
    abstract.md       the prose account, rendered on the archive website
    concepts/         statements only, as axioms — 9 modules
    proofs/           the proofs, each tagged with the statement it discharges — 103 modules

A concept module states results as `axiom`s. A proof is a `theorem` whose docstring carries
`conclusion: <that axiom's full name>`; the build checks the pairing.

## Dependencies

Beyond mathlib, this submission builds on four others in the archive, all listed in the
bibliography of `manifest.yaml`:

- `lax-434930`, *Classical Complexity Classes* (Édouard Bonnet): P, NP, and NP-completeness.
- `lax-429075`, *The Cook–Levin Theorem* (Édouard Bonnet): satisfiability, its encoding,
  and its NP-hardness.
- `lax-808846`, *The Word RAM* (Jan Dreier): the machine model, the IMP+ language and its
  verified compiler.
- `lax-759944`, *Computability and Polynomial-Time Equivalence of Turing Machines and Word
  RAMs* (Szymon Toruńczyk).

Results of other submissions are cited through their statements: Cook–Levin
(`SATHard.hardness`) and the round trip of the formula encoding (`EncodingCorrect.roundtrip`)
from `lax-429075`, and the equivalence of polynomial time on the word RAM and on Turing
machines (`ramPolytime_iff_turingPolytime`) from `lax-759944`. The archive's proof network
counts a statement here as proved once those are.

Two packages are required with their proofs, and the build warns about each
(`proof-dependency`). From `lax-808846` come the IMP+ language, its verified compiler to the
word RAM and the `run_vcg` tactic, in which every polynomial-time bound here is proved. From
`lax-434930` comes the composition of polynomial-time Turing machines. Neither is stated as
a result in its submission, so there is no statement to cite instead.

The archive itself is described in `lax-242665`, *An Introduction to Lax* (Édouard Bonnet,
Jan Dreier, Clemens Kuske).

## License

Apache 2.0, as required by the archive. See `LICENSE`.
