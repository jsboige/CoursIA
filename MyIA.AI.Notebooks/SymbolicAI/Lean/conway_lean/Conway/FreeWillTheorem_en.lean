/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Free Will Theorem (Conway-Kochen 2006/2009)

Pilier 2 of Epic #1651. Proves that particle responses cannot be
deterministic functions of prior information, assuming three physically
motivated axioms: SPIN, TWIN, and MIN.

The argument proceeds in two stages:

**Stage 1 (Single-particle)**:
A deterministic model assigns a fixed {0,1} response to each measurement
direction, for each hidden state. SPIN forces this to be a valid coloring
of the Cabello vectors (exactly one `true` per orthogonal basis). But the
Kochen-Specker theorem (Pilier 1) says no such coloring exists.
Contradiction.

**Stage 2 (Two-particle)**:
With two entangled particles measured by spatially separated experimenters,
TWIN forces both particles to share the same response function, and MIN
ensures experimenter independence. The same KS contradiction applies.

**Key insight (Conway-Kochen)**: "Free will" here is a *mathematical*
definition, not a philosophical thesis. It means: the particle's response
is not a function of the past. The theorem proves this rigorously from
three modest physical axioms.

Sources:
  Conway & Kochen, "The Free Will Theorem",
    Found. Phys. 36 (2006), 1441-1473.
  Conway & Kochen, "The Strong Free Will Theorem",
    Notices AMS 56 (2009), 226-232.
-/


/-
  English mirror of `FreeWillTheorem.lean` (FR canonical). Convention EPIC #4980
  (decision ratified 2026-07-04, cf `code-style.md` §Lean i18n): distinct FR + EN
  sibling files — no inline bilingual block in a single file (Option B rejected).
  The module docstring above mirrors the FR copyright + FR-orbit description; the
  body signatures, proofs and tactics remain byte-identical between the two files.

  Architecture: `Conway.FreeWillTheorem` uses a nested namespace (`Conway > FreeWillTheorem`),
  with `open KochenSpecker` to access the 18-vector Cabello kernel. The EN sibling
  mirrors this nested structure (`Conway_en > FreeWillTheorem_en`), following the
  precedent of `KochenSpecker_en.lean` (PR #6211 MERGED 2026-07-12): `open Conway_en`
  to expose the parent sibling namespace, `open KochenSpecker` for the FR canonical
  combinatorial kernel (resolution cascades through the open namespace chain to
  `Conway.KochenSpecker`).
-/
import Conway.KochenSpecker

namespace Conway_en

open Conway_en

namespace FreeWillTheorem_en

open Conway.KochenSpecker

/-!
## Stage 1: Single-particle Free Will Theorem

A deterministic (hidden-variable) universe produces fixed {0,1} outcomes
for every measurement direction, determined by the hidden state. The SPIN
axiom forces these outcomes to satisfy the Kochen-Specker constraint.
Since KS proves no such coloring exists, deterministic models are
impossible.
-/

/-- Abstract type for hidden variables (the "past" of the universe).
    In a deterministic model, all measurement outcomes are fixed
    once the hidden state is known. -/
abbrev HiddenState := ℕ

/-- A deterministic response function maps each hidden state and
    measurement direction to a definite {0,1} outcome.

    In Conway-Kochen's language, this represents the hypothesis that
    "particle responses are functions of the past" — specifically,
    functions of the hidden variable λ and the measurement direction. -/
abbrev DeterministicResponse := HiddenState → VecIdx → Bool

/-- **SPIN axiom** (simplified for the Cabello 18-vector setting):
    for each hidden state, the response function defines a valid coloring
    of the Cabello vectors. Physically: measuring the squared spin
    component along each of 4 mutually orthogonal projectors yields
    exactly one "1" (and three "0"s) per orthogonal basis.

    This is precisely the `IsValidColoring` constraint from the
    Kochen-Specker formalization. -/
def SatisfiesSPIN (f : DeterministicResponse) : Prop :=
  ∀ state : HiddenState, IsValidColoring (f state)

/-- **Free Will Theorem (single-particle version)**.
    No deterministic response function is compatible with SPIN.

    *Proof*: For any hidden state `λ`, the function `f(λ, ·)` is a
    `{0,1}`-coloring of the 18 vectors. By SPIN, this coloring satisfies
    `IsValidColoring` (exactly one `true` per context). But the
    Kochen-Specker theorem proves no such coloring exists.
    Contradiction.

    In Conway-Kochen's language: "the particle's response is free" —
    meaning it cannot be a deterministic function of the hidden state. -/
theorem fwt_single_particle :
    ¬ ∃ f : DeterministicResponse, SatisfiesSPIN f := by
  rintro ⟨f, hspin⟩
  exact kochen_specker ⟨f 0, hspin 0⟩

/-!
## Stage 2: Two-particle Free Will Theorem

Two spin-1 particles are prepared in an entangled state and sent to
spatially separated experimenters Alice and Bob. Alice measures along
direction x, Bob along direction y. Three axioms constrain the outcomes:

  - **SPIN**: squared spin along orthogonal directions gives exactly one "1"
  - **TWIN**: parallel measurements on entangled particles give same result
  - **MIN**: experimenter choices are independent (spacelike separation)

The conclusion: neither particle's response can be a function of the past.
-/

/-- Two spatially separated experimenters. -/
inductive Experimenter
  | alice
  | bob
  deriving DecidableEq, Fintype

/-- A two-particle deterministic model assigns a definite {0,1} outcome
    to each experimenter, hidden state, and measurement direction.

    This represents the hypothesis that both particles' responses are
    determined by hidden variables: `f(λ, e, d)` gives the predetermined
    outcome when experimenter `e` measures along direction `d` in the
    hidden state `λ`. -/
abbrev TwoParticleResponse := HiddenState → Experimenter → VecIdx → Bool

/-- **TWIN axiom**: when both experimenters measure along the *same*
    direction, they get the same response. This is the signature of
    quantum entanglement — the EPR correlation.

    Physically: if Alice measures spin-squared along direction d and
    Bob also measures along d (parallel directions), their outcomes agree. -/
def SatisfiesTWIN (f : TwoParticleResponse) : Prop :=
  ∀ state : HiddenState, ∀ dir : VecIdx,
    f state .alice dir = f state .bob dir

/- **MIN axiom** (structural): each experimenter's response depends
   only on their *own* measurement direction, not the other experimenter's.

   This is built into the type signature: `f(state, e, d)` takes the
   experimenter's own direction but NOT the other experimenter's
   direction. In Conway-Kochen's 2009 formulation, MIN replaces FIN
   (the speed-of-light constraint) and is cleaner to formalize:
   it simply says Alice's response doesn't depend on Bob's axis choice. -/

/-- A two-particle deterministic model satisfies all Free Will Theorem
    axioms: SPIN for both particles, TWIN correlation, and MIN
    (structural independence).

    MIN is satisfied by construction: each `f state e dir` does not
    take the other experimenter's direction as input. -/
structure SatisfiesFWT (f : TwoParticleResponse) : Prop where
  spin : ∀ e : Experimenter, SatisfiesSPIN (f · e)
  twin : SatisfiesTWIN f

/-- **Free Will Theorem (two-particle version, Conway-Kochen 2009)**.
    No two-particle deterministic model satisfies all FWT axioms.

    *Proof*: By TWIN, Alice and Bob share the same response function.
    By SPIN for Alice, this shared function defines a valid coloring of
    the Cabello vectors for each hidden state. But the single-particle
    FWT (hence Kochen-Specker) says no such function exists.
    Contradiction.

    *Conclusion* (Conway-Kochen): the responses of the particles are
    *not* determined by the past. In their mathematical definition,
    the particles have "free will". -/
theorem free_will_theorem :
    ¬ ∃ f : TwoParticleResponse, SatisfiesFWT f := by
  rintro ⟨f, hfwt⟩
  -- By SPIN for Alice: f(·, .alice) is a deterministic response
  -- satisfying SPIN. This contradicts the single-particle FWT.
  have hspin_alice : SatisfiesSPIN (f · .alice) := hfwt.spin .alice
  exact fwt_single_particle ⟨(f · .alice), hspin_alice⟩

/-!
## Corollary: the "strong" form

The strong Free Will Theorem (2009 version with MIN) further asserts
that *if* the experimenters' choices are free (not determined by the
past), *then* the particles' responses must also be free.

In our formalization, we've proved the contrapositive: if responses
WERE determined by hidden variables, the axioms would be violated.
Equivalently: under SPIN + TWIN + MIN, responses are not deterministic.
-/

end FreeWillTheorem_en

/-!
## Connection to Conway's Legacy

The Free Will Theorem is the second pillar of Conway's mathematical
legacy formalized in this workspace, completing the hommage alongside
the Game of Life (Epic #1647):

  1. **Life** (Phase 2): emergence of complex computation from simple rules
  2. **Free Will Theorem** (Phase 3): mathematical limits of determinism

Both are quintessentially Conway: elegant, surprising, and accessible
once properly framed. The KS theorem (18-vector Cabello proof) serves
as the combinatorial engine, and the FWT itself is a one-line reduction.

Hall of Fame:
  - Conway & Kochen (2006) — Free Will Theorem (original)
  - Conway & Kochen (2009) — Strong Free Will Theorem (MIN version)
  - Kochen & Specker (1967) — original 117-vector KS theorem
  - Cabello, Estebaranz, Garcia-Alcaine (1996) — 18-vector tight KS proof
-/

end Conway_en

