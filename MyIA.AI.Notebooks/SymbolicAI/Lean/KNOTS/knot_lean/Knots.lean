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
    - `Knots.Tangle` — tangles à quatre extrémités (convention
      Conway : tangle nul/infini/1, rotation, compositions
      verticale/horizontale, clôtures numérateur/dénominateur)
    - `Knots.Reidemeister` — mouvements de Reidemeister (RI, RII,
      RIII) et invariance des invariants
    - `Knots.ReidemeisterMoves` — suite de mouvements vérifiable par le
      noyau (organe #18611 : inductif data + vérificateurs Bool +
      soundness vers `ReidemeisterEquiv`)
    - `Knots.ReidemeisterAny` — langue de moves étendue (organe #22359 :
      kink/bigon sans fraîcheur, forme canonique `canon` à renommage près,
      embedding R1/R3 de la langue connectée, cadre de décision borné)
    - `Knots.Invariant` — invariants polynomiaux (Alexander,
      Jones), tricoloriabilité, genre
    - `Knots.Conway` — notations et conventions de Conway
    - `Knots.Slice` — nœuds slice, théorèmes de Piccirillo et Freedman,
      dichotomie lisse/topologique (extrait de Conway, #18397)
    - `Knots.Jones` — bracket de Kauffman sur codes PD (somme d'états,
      évaluations trèfle / noeud en huit / noeud trivial)
    - `Knots.Khovanov` — complexe de Khovanov du trèfle (cube des
      lissages, m/Δ, d∘d = 0, table graduée `q + q³ + q⁵t² + q⁹t³`,
      χ|_{q=−1} = −2)
    - `Knots.FigureEight` — invariants du noeud en huit sur son code PD
      plan (Alexander signé classique à une unité près, déterminant 5,
      non-tricoloriabilité, 4 croisements — définition provisoire)
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
import Knots.Tangle
import Knots.Reidemeister
import Knots.Invariant
import Knots.Mutation
import Knots.ConwayPD
import Knots.Conway
import Knots.ConwayNotation
import Knots.Slice
import Knots.ReidemeisterInvariance
import Knots.ReidemeisterMoves
import Knots.ReidemeisterCombinatorial
import Knots.ReidemeisterAny
import Knots.Jones
import Knots.Khovanov
import Knots.FigureEight
import Knots.Lidman
import Knots.MathlibPrerequisites
