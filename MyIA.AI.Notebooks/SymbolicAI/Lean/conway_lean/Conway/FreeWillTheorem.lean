/-
  `Conway.FreeWillTheorem` — Le théorème du libre arbitre de Conway-Kochen
  ======================================================================
  Le théorème du libre arbitre (Conway-Kochen 2006/2009, « Strong Free Will
  Theorem ») affirme que, sous des hypothèses physiques raisonnables
  (compatibilité avec la mécanique quantique + non-conspiracy), les
  particules élémentaires disposent d'une propriété analogue au « libre
  arbitre » : leurs réponses à des expériences de spin ne sont pas
  entièrement fixées par le passé lointain de l'univers.

  Plus précisément, si Alice et Bob effectuent des mesures de spin
  (trois directions orthogonales d'un photon intriqué), et si les
  particules avaient une fonction de réponse cachée qui dépendait de
  manière certaine uniquement du passé commun (non-conspiracy), alors
  la fonction devrait dépendre des directions mesurées — et cette
  dépendance viole la propriété de « Kochen-Specker » qu'aucune
  fonction d'une mesure quantique à valeur propre classique ne peut
  être prédéterminée sans conspiration.

  Ce fichier formalise la structure du théorème et la connecte au
  contexte du projet `conway_lein` (Kochen-Specker, Conway's legacy).

  ### i18n — convention #4980 (ratifiée 2026-07-04)

  Ce fichier est le **canonique français**. Le miroir anglais est le fichier
  frère `FreeWillTheorem_en.lean` (`namespace Conway_en > namespace FreeWillTheorem_en`,
  `open Conway_en`, `open Conway.KochenSpecker`, `import Conway.KochenSpecker`)
  — modèle sibling pair V2 nested (cf `code-style.md` §Lean i18n et l'analogue
  `Conway/Fractran` c.451 Pattern A, `Conway/LookAndSay` c.457, `Conway/Nim` c.518).
  Docstrings en français ici ; le corps (signatures, defs, proofs) reste
  byte-identique entre les deux fichiers. Pas de bloc bilingue inline (option B
  rejetée 2026-07-04 ratif).

  Cross-références : c.366 `Conway.lean` racine bilingue (MERGED), c.451
  `Conway/Fractran` sibling pair (MERGED), c.456 `Conway/FreeWillTheorem`
  sibling pair (MERGED — EN twin standalone créé), c.457 `Conway/LookAndSay`
  sibling pair (MERGED), c.518 `Conway/Nim` sibling pair (MERGED),
  **c.519 `Conway/FreeWillTheorem` strip bilingue FR canonical (ce PR)**.
-/

import Conway.KochenSpecker

namespace Conway

namespace FreeWillTheorem

open KochenSpecker

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

end FreeWillTheorem

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

end Conway
