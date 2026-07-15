/-
  Knots — racine du sous-lac `knot_lean`
  =====================================

  * Racine du sous-lac `knot_lean` (namespace `Knots`)
    présentée selon la convention i18n #4980 (sibling pair : `Knots.lean`
    canonique FR + `Knots_en.lean` jumeau EN, via
    `globs := #[.submodules \`Knots, \`Knots_en]` dans `lakefile.lean`).

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
-/

import Knots.Basic
import Knots.Reidemeister
import Knots.Invariant
import Knots.Conway
import Knots.Lidman
import Knots.MathlibPrerequisites
