/-
  Knots — racine du sous-lac `knot_lean`
  =====================================

  * Racine du sous-lac `knot_lean` (namespace `Knots`)
    présentée selon la convention i18n #4980 (sibling pair / agrégateur
    bilingue inline : `Knots.lean` canonique + `Knots_en.lean` jumeau,
    via `globs := #[.submodules \`Knots]` dans `lakefile.lean`).

  * Cible EPIC #2874 (Phase 1) — formalisation de la théorie des
    nœuds en Lean 4 / Mathlib 4, briques :
    - `Knots.Basic` — fondations combinatoires (croisements,
      diagrammes, PD-codes, Gauss codes, Dowker-Thistlethwaite)
    - `Knots.Reidemeister` — mouvements de Reidemeister (RI, RII,
      RIII) et invariance des invariants
    - `Knots.Invariant` — invariants polynomiaux (Alexander,
      Jones), tricoloriabilité, genre
    - `Knots.Conway` — notations et conventions de Conway
    - `Knots.Lidman` — contribution de Joshua Lidman (collaboration
      externe), orientation des variétés
    - `Knots.MathlibPrerequisites` — compat Mathlib 4

  * Inspiration : `shua/leanknot` (https://github.com/shua/leanknot)
    et Prathamesh (2015), *Formalising Knot Theory in Isabelle/HOL*.

  * Convention : espace de noms `Knots`, preuves en langue anglaise
    (compatibilité Mathlib 4 et tactic DSL), commentaires et chaînes
    de documentation en français par défaut (cf `#4980` ratifié
    2026-07-04).

---

The `knot_lean` sub-lake root (`namespace Knots`).
Aggregates the six modules below, following the i18n convention
ratified in #4980 (sibling pair via `globs := #[.submodules
\`Knots]` in `lakefile.lean`; this file is the canonical FR root,
mirrored by `Knots_en.lean`).

EPIC #2874 (Phase 1) — formalisation of knot theory in Lean 4 /
Mathlib 4, structured into six bricks:

- `Knots.Basic` — combinatorial foundations (crossings,
  diagrams, PD-codes, Gauss codes, Dowker-Thistlethwaite notation)
- `Knots.Reidemeister` — Reidemeister moves (RI, RII, RIII) and
  invariance of the polynomial / combinatorial invariants
- `Knots.Invariant` — polynomial invariants (Alexander, Jones),
  tricolourability, genus
- `Knots.Conway` — Conway notations and conventions
- `Knots.Lidman` — external collaboration layer (Joshua Lidman),
  orientation of knot varieties
- `Knots.MathlibPrerequisites` — Mathlib 4 compatibility shim

Inspired by `shua/leanknot` (https://github.com/shua/leanknot)
and Prathamesh (2015), *Formalising Knot Theory in Isabelle/HOL*.

Convention: `namespace Knots`, proofs and theorem statements in
English (Mathlib 4 / tactic DSL compatibility); default language
for documentation strings and prose comments is French per #4980
(ratified 2026-07-04).
-/

import Knots.Basic
import Knots.Reidemeister
import Knots.Invariant
import Knots.Conway
import Knots.Lidman
import Knots.MathlibPrerequisites
