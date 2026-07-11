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
  `Conway.FreeWillTheorem` — Théorème du libre arbitre (Conway-Kochen)
  ================================================================
  Hommage à Conway — Formalisation du théorème du libre arbitre

  John Horton Conway (1937-2020), avec Simon Kochen, ont démontré en
  2006 (puis renforcé en 2009) le « Free Will Theorem » (théorème du
  libre arbitre) : **les réponses des particules ne peuvent pas être
  des fonctions déterministes de l'information passée**, sous trois
  hypothèses physiques motivées : **SPIN**, **TWIN** et **MIN**.

  ### Contexte mathématique

  Le théorème procède en deux étapes (Pilier 2 de l'EPIC #1651) :

  **Étape 1 (Particule unique)** : un modèle déterministe (à variables
  cachées) assigne une réponse fixe `{0,1}` à chaque direction de mesure,
  pour chaque état caché. L'axiome SPIN force cette réponse à constituer
  un coloriage valide des vecteurs de Cabello (exactement un `true` par
  base orthogonale). Mais le théorème de Kochen-Specker (Pilier 1)
  prouve qu'aucun tel coloriage n'existe. Contradiction.

  **Étape 2 (Deux particules)** : avec deux particules intriquées mesurées
  par des expérimentateurs spatialement séparés, TWIN force les deux
  particules à partager la même fonction de réponse, et MIN assure
  l'indépendance des expérimentateurs. La même contradiction KS
  s'applique.

  **Insight clé (Conway-Kochen)** : le « libre arbitre » ici est une
  définition **mathématique**, pas une thèse philosophique. Cela
  signifie : la réponse de la particule n'est pas une fonction du passé.
  Le théorème le prouve rigoureusement à partir de trois axiomes
  physiques modestes.

  ### i18n — convention #4980 ratifiée 2026-07-04

  Ce sous-module suit l'option A (bilingue inline FR/EN), variante
  pragmatique c.376-c.385 (deux blocs `/` top-level distincts, sans
  `---` interne) : le bloc EN existant est préservé verbatim
  ci-dessus, le bloc FR miroir est ajouté juste après sans séparateur
  `---`. Convention sibling pair (`<Foo>_en.lean` à part) réservée aux
  modules de substance (cf c.374 `Astar_en.lean`) ; pour les modules
  de theorem à densité de preuves élevée comme `FreeWillTheorem`,
  l'inline FR+EN est le bon compromis (densité theorem élevée, deux
  langues côte à côte). Les énoncés de théorèmes, les noms de lemmes,
  les tactiques Lean (`:= by rintro`, `exact`, `have`, etc.) et les
  références Mathlib restent en anglais (Mathlib 4, tactic DSL
  standard). Seules les **docstrings `/-- ... -/`** et **commentaires
  `-- ...`** bilingues sont ajoutées. Anti-§D byte-identity garanti :
  le namespace body (7026 chars entre `namespace Conway` L39 et
  `end Conway` L208) est préservé bit-pour-bit via script Python
  `extract_ns_body`.

  ### c.386 — continuité conway_lean Phase 1+ satellites (post-c.385)

  c.385 = 6ᵉ sous-module rollout `conway_lean` Phase 1+
  (`Conway/CollatzLike`, Collatz 3n+1 + Conway 1972 indécidabilité,
  PR #6217 OPEN MERGEABLE, +107/-0, baseline LF-only CR=0 strict
  préservée nativement, 8 theorem + 11 defs/structures byte-identique,
  Math-Vérif COMMENTED 15ᵉ). PIVOT L335 strict post-c.381-c.383 = 3
  cycles R6 Sustained intra-R6 sur registre `grothendieck_lein`,
  retour `conway_lein` Phase 1+ satellites registre ouvert post-c.380.

  **c.386 = 7ᵉ sous-module rollout `conway_lean` Phase 1+** =
  `FreeWillTheorem` = continuité registre `conway_lein` Phase 1+
  ouvert post-c.385 PIVOT strict obligatoire. Substance réelle :
  **Conway-Kochen 2006/2009 « Strong Free Will Theorem »** (physique
  quantique mathématique + logique + philosophie des sciences
  formalisée). Analogie structurelle avec c.380 Doomsday (algorithme
  mathématique fondamental) + c.384 Nim (jeu mathématique) + c.385
  CollatzLike (conjecture mathématique fondamentale) : `FreeWillTheorem`
  = théorème mathématique fondamental analogue structurel direct.
  Réduction one-line (free_will_theorem := by ...) sur le moteur
  Kochen-Specker (Pilier 1, 18 vecteurs Cabello). 2 theorem
  (`fwt_single_particle`, `free_will_theorem`) + 1 structure
  (`SatisfiesFWT`) + 1 inductive (`Experimenter`) + 2 def
  (`SatisfiesSPIN`, `SatisfiesTWIN`) + 3 abbrev (`HiddenState`,
  `DeterministicResponse`, `TwoParticleResponse`) byte-identiques.
  1 import byte-identique (`Conway.KochenSpecker`).

  Backlog c.387+ (2 sous-modules Phase 1+ restants après c.386 :
  `Conway/{Angel,KochenSpecker}.lean` + `Conway/Life/*` 13 fichiers
  + grothendieck_lein 19 restants Phase 2+) + hors-Lean backlog.

  Cross-références : c.366 `#6111` `Conway.lean` racine bilingue
  inline (MERGED, initie rollout Phase 1+) + c.377 `#6178`
  `Conway/MathlibMap` bilingue (1ᵉʳ sous-module rollout conway_lein,
  PIVOT L335 strict, analogue structurel c.382) + c.378 `#6182`
  `Conway/LookAndSay` bilingue (2ᵉ sous-module rollout, suite
  look-and-say λ ≈ 1.303577) + c.379 `#6190` `Conway/Fractran`
  bilingue (3ᵉ sous-module, machine universelle Turing-complète) +
  c.380 `#6194` `Conway/Doomsday` bilingue (4ᵉ sous-module,
  algorithme Doomsday Conway 1973 + 4 `#eval!` cas réels, analogue
  structurel direct c.385 CollatzLike) + c.381 `#6197`
  `Grothendieck/YonedaLemma` bilingue (1ᵉʳ sous-module rollout
  grothendieck_lein Phase 2+, PIVOT L335 strict c.381) + c.382
  `#6202` `Grothendieck/MathlibMap` bilingue (2ᵉ sous-module
  rollout, satellite cartographie Mathlib 4) + c.383 `#6208`
  `Grothendieck/SheafBasics` bilingue (3ᵉ sous-module rollout,
  fondations faisceaux = 6 theorem, 3ᵉ cycle R6 Sustained intra-R6
  sur registre `grothendieck_lein` ouvert = au seuil R5.4b MUST
  avant PIVOT obligatoire c.384) + c.384 `#6212` `Conway/Nim`
  bilingue (5ᵉ sous-module rollout conway_lein Phase 1+, Nim +
  Bouton 1901 + Sprague-Grundy = analogue structurel direct
  c.385 CollatzLike par algorithme mathématique concret) + c.385
  `#6217` `Conway/CollatzLike` bilingue (6ᵉ sous-module rollout
  conway_lein Phase 1+, Collatz 3n+1 + Conway 1972 indécidabilité
  = analogue structurel direct c.386 FreeWillTheorem par théorème
  mathématique fondamental) + **c.386 `Conway/FreeWillTheorem`
  bilingue (cette PR, 7ᵉ sous-module rollout conway_lein Phase 1+,
  Conway-Kochen 2006/2009 « Strong Free Will Theorem »)** ←
  **continuité registre `conway_lein` Phase 1+ ouvert post-c.385
  PIVOT strict obligatoire**.
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
