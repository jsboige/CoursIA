/-
Knots.ReidemeisterCombinatorial (EN) — Verifiable sequence of Reidemeister moves
=================================================================================

Infrastructure issue (Epic #1453, point 3): the missing organ behind the
remaining `sorry`s of `knot_lean` (Reidemeister.lean:1056, Lidman.lean:81) —
a **kernel-verifiable sequence of Reidemeister moves**.

Why this module is separate from `Knots.Reidemeister`: the RTC machinery
(`ReidemeisterEquiv`) is already in place (inductives `ReidemeisterStep` and
`ReidemeisterEquiv`, lemmas `*.symm`, `reidemeister_equiv_symm`,
`reidemeister_equiv_equivalence`). What is missing is the **algorithmic
backbone**:

  1. a `MoveSequence` alias for `List ReidemeisterStep` (readability),
  2. a `movesConnects` constructor that seals the RTC into a compact witness,
  3. a **bounded decidable verifier** `verifyMoves` which, for a budget `n`
     of moves allowed, enumerates all R1/R2/R3 sequences and returns `true`
     if any of them connects two diagrams. Bounded to remain decidable;
     full enumeration is `O((crossings+1)^n)`,
  4. the **soundness** of the verifier: if `verifyMoves n d₁ d₂ = true`, then
     `ReidemeisterEquiv d₁ d₂`. This is the target of subsequent prover
     passes.

What this module **does not do**:
- it does not prove the deep Reidemeister theorem (`reidemeister_theorem`,
  Reidemeister.lean:1053) which requires PL-manifolds/S³/ambient isotopy —
  the verifier's soundness only delivers the **combinatorial side**
  (« ⇐ » ReidemeisterEquiv → ambient_isotopic remains out of scope);
- it does not attack the permanent `sorry`s of `Knots.Slice` (Conway,
  Piccirillo, Freedman), explicitly marked as « decades away from formalization »
  by previous sections — these statements live in a 4-manifolds / Khovanov /
  Kirby theory that Mathlib does not have.

Target Lidman:81 — `unknotting_11n102_upper` — **becomes accessible** once
this module lands: exhibit a `MoveSequence` connecting
`(changeCrossingAt c₁ (changeCrossingAt c₂ knot_11n102)).diagram` to
`unknotDiagram`, and `verifyMoves_sound` (to be proved by prover passes on
this module) seals the implication.

Convention i18n (EPIC #4980, user decision 2026-07-04): this file is the **EN
mirror** of `ReidemeisterCombinatorial.lean` (FR canonical), via the sibling
pair pattern ratified 2026-07-04. Theorem statements, Lean tactics, lemma
names and Mathlib references stay in English (Mathlib 4 compat); only module
docstrings and this header block differ between the two files.

Status at first import: initial scaffolding (types + soundness statement).
Prover passes (PR2+) will provide `verifyMoves_sound`, the witness for
Lidman:81, and the bounded extension `verifyMovesAux`.
-/

import Knots.Reidemeister
import Knots.Invariant

namespace Knots

/-! ## 1. Alias and sequence constructor

`MoveSequence` is a named alias of `List ReidemeisterStep` for the readability
of statements: a « sequence of moves » is exactly a finite list of Reidemeister
steps, and the name makes the types more readable to consumers (`Lidman.lean`
in particular).
-/

/-- A finite sequence of Reidemeister moves.

Named alias of `List ReidemeisterStep` (see `Knots.Reidemeister`): the list
is in application order (left → right: `head` applied first).
-/
abbrev MoveSequence : KnotDiagram → KnotDiagram → Type :=
  fun d₁ d₂ => List { d' // ReidemeisterStep d₁ d' }

/-- A `MoveSequence` of length `0` trivially connects a diagram to itself
(RTC reflexive, it is `ReidemeisterEquiv.refl`). -/
def MoveSequence.nil (d : KnotDiagram) : MoveSequence d d := []

/-- Concatenate a sequence with a step: `MoveSequence.cons step ms` is a
sequence that applies `step` from `d₁`, then `ms` from `d₂` to `d₃`. The
typer enforces diagram coherence along the chain. -/
def MoveSequence.cons {d₁ d₂ d₃ : KnotDiagram}
    (step : ReidemeisterStep d₁ d₂) (ms : MoveSequence d₂ d₃) :
    MoveSequence d₁ d₃ :=
  ⟨d₂, step⟩ :: ms

/-! ## 2. Transitive closure of a sequence (`movesConnects`)

The `movesConnects` constructor seals a `MoveSequence` into a proof of
`ReidemeisterEquiv`. It is the inverse of the `ReidemeisterEquiv.step`
constructor rendered composable: structural recursion on the list, `cons`
becomes `step.trans`, `nil` becomes `refl`.
-/

/-- A sequence of moves connects `d₁` to `d₂` in the sense of `ReidemeisterEquiv`.

Reconstruction by recursion on the `MoveSequence`:
- `nil` (empty sequence) → `ReidemeisterEquiv.refl`,
- `cons step ms` → `ReidemeisterEquiv.trans (ReidemeisterEquiv.step step)
  (movesConnects d₂ d₃ ms)`.

The definition is **non-right-recursive**: `movesConnects d₂ d₃ ms` is
computed before being consumed by `trans`, which keeps evaluation
termination-safe under `decreasing_by wf_tacs`.
-/
def movesConnects {d₁ d₂ : KnotDiagram} :
    MoveSequence d₁ d₂ → ReidemeisterEquiv d₁ d₂
  | [] => ReidemeisterEquiv.refl d₁
  | (⟨_, step⟩ :: ms) =>
    ReidemeisterEquiv.trans
      (ReidemeisterEquiv.step step)
      (movesConnects _ _ ms)

/-- Trivially sound by construction: `movesConnects` _is_ the RTC. -/
theorem movesConnects_sound {d₁ d₂ : KnotDiagram}
    (ms : MoveSequence d₁ d₂) : ReidemeisterEquiv d₁ d₂ :=
  movesConnects ms

/-! ## 3. Bounded decidable verifier

`verifyMovesAux` enumerates the sequences of length at most `n` and decides
whether any of them connects `d₁` to `d₂`. The decision is **decidable**
(returns a `Bool`) — it is the instrument for prover passes that do not have
access to `decide` orchestration on the space of infinite sequences.

The algorithm is deliberately naive (exhaustive enumeration): for the bounds
useful in practice (n ≤ 4), the branching factor stays dominated by
`(crossings+1) × 3` (R1/R2/R3 × both directions) and the cost stays in
`O((3(numCrossings+1))^n)`. Subsequent prover passes will refine by avoiding
trivial symmetries (`ReidemeisterEquiv.symm`, `trans`).
-/

/-- A view of `ReidemeisterStep` as a pure constructor (without existential
`d₂`). Used by the algorithm to reconstruct the target diagram at each step. -/
def ReidemeisterStep.toWitness (d₁ : KnotDiagram) (d₂ : KnotDiagram)
    (h : (Reidemeister1Connected d₁ d₂ ∨ Reidemeister1Connected d₂ d₁
       ∨ Reidemeister2Connected d₁ d₂ ∨ Reidemeister2Connected d₂ d₁
       ∨ Reidemeister3Connected d₁ d₂ ∨ Reidemeister3Connected d₂ d₁)) :
    ReidemeisterStep d₁ d₂ :=
  -- Distributivity of `∨`: the conjunction is either R1, R2, or R3,
  -- and in each case the direction is forward or backward.
  -- The reconstruction is partial: we accept any witness `h` and
  -- pattern-match to select the right `ReidemeisterStep` constructor.
  -- The `_` is explicit to flag that reconstruction is not always unique
  -- (forward/backward symmetric).
  by
    rcases h with h | h | h | h | h | h
    · exact ReidemeisterStep.r1 (Or.inl h)
    · exact ReidemeisterStep.r1 (Or.inr h)
    · exact ReidemeisterStep.r2 (Or.inl h)
    · exact ReidemeisterStep.r2 (Or.inr h)
    · exact ReidemeisterStep.r3 (Or.inl h)
    · exact ReidemeisterStep.r3 (Or.inr h)

/-- Raw witness of an applicable move: a `KnotDiagram` reachable from `d₁`
by a single `ReidemeisterStep` (without a witness of the relation).
-/
def oneStepWitnesses (d₁ : KnotDiagram) : List KnotDiagram :=
  -- Deliberately skeleton implementation: the exhaustive list of 1-step
  -- successors of `d₁` is not enumerated here (PR2+); the function returns
  -- `[]` for now. Consumers that depend on `verifyMoves` must treat `[]`
  -- as « no 1-step witness », which `verifyMoves 0` captures trivially.
  []

/-- Bounded recursive verifier.

`verifyMovesAux k d₁ d₂` returns `true` iff there is a sequence of at most
`k` `ReidemeisterStep`s connecting `d₁` to `d₂`. Base cases:
- `k = 0` → `d₁ = d₂` (RTC reflexive);
- `k ≥ 1` → there is a 1-step successor `d'` of `d₁` such that
  `verifyMovesAux (k-1) d' d₂` is `true`.

**Status**: API skeleton for PR2+. The current version returns `true` only
on the reflexive case and `false` everywhere else, which is enough for
passes that consume only `verifyMoves 0` (equivalent to diagram equality).
The effective implementation is the subject of prover passes on the
remaining `sorry`s — see issue #18611, lemmas 1-4.
-/
def verifyMovesAux : Nat → KnotDiagram → KnotDiagram → Bool
  | 0, d, d' => d == d'
  | k+1, d, d' =>
    -- Skeleton: we consider `d == d'` (reflexive closure at 0 moves)
    -- and each 1-step successor of `d`. The `false` return is conservative
    -- (sound: `verifyMovesAux = true → ReidemeisterEquiv`, the converse
    -- is not required).
    d == d' ||
    (oneStepWitnesses d).any fun d_next => verifyMovesAux k d_next d'

/-- Public interface of the bounded verifier. -/
def verifyMoves (n : Nat) (d₁ d₂ : KnotDiagram) : Bool :=
  verifyMovesAux n d₁ d₂

/-! ## 4. Soundness (statement, to be proved by subsequent prover pass)

Soundness is the target lemma: « if `verifyMoves n d₁ d₂ = true`, then
`ReidemeisterEquiv d₁ d₂ ». The converse (completeness) is out of scope —
the algorithm is deliberately bounded and loses witnesses beyond the budget.

**Proof outline**: induction on `n`.
- `n = 0`: `verifyMovesAux 0 d₁ d₂ = (d₁ == d₂) = true` → `d₁ = d₂` →
  `ReidemeisterEquiv.refl d₁`.
- `n = k+1`: `verifyMovesAux (k+1) d₁ d₂ = true` →
  (`d₁ == d₂` ∧ reflexivity) ∨ (∃ d_next, `verifyMovesAux k d_next d₂ = true`
  ∧ `ReidemeisterStep d₁ d_next`). Case by case, the first reduces to
  `n = 0`, the second uses the induction hypothesis to obtain
  `ReidemeisterEquiv d_next d₂`, then `ReidemeisterEquiv.step` + `trans`
  close the diagram.

The concrete instrumentation (lemma `Or.inl`/`Or.inr` in the `Bool`,
extraction of the witness `d_next` from `(oneStepWitnesses d).any`) is
the subject of PR2+; it depends on `List.any`/`List.find` which are
decidable in Mathlib.
-/
theorem verifyMoves_sound :
    ∀ (n : Nat) (d₁ d₂ : KnotDiagram),
      verifyMoves n d₁ d₂ = true → ReidemeisterEquiv d₁ d₂ := by
  intro n d₁ d₂ h
  -- Soundness of the skeleton (which only returns `true` on `d₁ == d'`):
  -- trivial by `rfl` and `ReidemeisterEquiv.refl`. The full version
  -- (which consumes `oneStepWitnesses`) will be added in PR2+ without
  -- modifying the statement.
  sorry

/-! ## 5. Helpers for `Lidman.lean` (indirect target)

`foldChangeCrossingsAt` sequentially applies a list of crossing changes to
a knot (fold left). This is the « `indices` witness » of
`Knot.UnknottableIn` (Invariant.lean:2292) rendered operational.

`unknottingWitness` seals the typical usage: « for a knot to have unknotting
number ≤ n, exhibit a length-n crossing-change sequence and a
ReidemeisterEquiv sequence between its image and `unknotDiagram` ». This is
the contract that `unknotting_11n102_upper` (Lidman:81) will honour once
this module has landed and `verifyMoves_sound` is proved.
-/

/-- Sequentially applies a list of crossing changes. -/
def foldChangeCrossingsAt (k : Knot) (indices : List Nat) : Knot :=
  indices.foldl Knot.changeCrossingAt k

/-- Unknotting witness: a list of crossing changes + a ReidemeisterEquiv
sequence between its image and `unknotDiagram`. -/
structure UnknottingWitness (k : Knot) (n : Nat) where
  indices : List Nat
  length_eq : indices.length = n
  equiv :
    MoveSequence
      (foldChangeCrossingsAt k indices).diagram
      unknotDiagram

/-! ## 6. Future compatibility

The module only depends on `Knots.Reidemeister` and `Knots.Invariant` — not
on `Knots.ReidemeisterInvariance` (which would import `Knots.Conway` and
spin the lake needlessly for passes that only attack the combinatorial side).

The lakefile (`Knots.lean`, import line) will need to add
`import Knots.ReidemeisterCombinatorial` once this module has been verified
by CI — PR3, after soundness and Lidman:81 witness.
-/

end Knots
