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
## Étape 1 : Théorème du libre arbitre à une particule

Un univers déterministe (à variables cachées) produit des résultats {0,1} fixés
pour chaque direction de mesure, déterminés par l'état caché. L'axiome
SPIN force ces résultats à satisfaire la contrainte de Kochen-Specker.
Puisque KS prouve qu'aucune telle coloration n'existe, les modèles
déterministes sont impossibles.
-/

/-- Type abstrait pour les variables cachées (le « passé » de l'univers).
    Dans un modèle déterministe, tous les résultats de mesure sont fixés
    une fois l'état caché connu. -/
abbrev HiddenState := ℕ

/-- Une fonction de réponse déterministe associe à chaque état caché et
    chaque direction de mesure un résultat {0,1} défini.

    Dans le langage de Conway-Kochen, cela représente l'hypothèse selon
    laquelle « les réponses des particules sont des fonctions du passé » —
    plus précisément, des fonctions de la variable cachée λ et de la direction de mesure. -/
abbrev DeterministicResponse := HiddenState → VecIdx → Bool

/-- **Axiome SPIN** (simplifié pour le cadre à 18 vecteurs de Cabello) :
    pour chaque état caché, la fonction de réponse définit une coloration
    valide des vecteurs de Cabello. Physiquement : mesurer la composante
    du carré du spin selon chacun de 4 projecteurs mutuellement orthogonaux
    donne exactement un « 1 » (et trois « 0 ») par base orthogonale.

    C'est précisément la contrainte `IsValidColoring` de la
    formalisation de Kochen-Specker. -/
def SatisfiesSPIN (f : DeterministicResponse) : Prop :=
  ∀ state : HiddenState, IsValidColoring (f state)

/-- **Théorème du libre arbitre (version à une particule)**.
    Aucune fonction de réponse déterministe n'est compatible avec SPIN.

    *Preuve* : Pour tout état caché `λ`, la fonction `f(λ, ·)` est une
    coloration `{0,1}` des 18 vecteurs. Par SPIN, cette coloration satisfait
    `IsValidColoring` (exactement un `true` par contexte). Mais le
    théorème de Kochen-Specker prouve qu'aucune telle coloration n'existe.
    Contradiction.

    Dans le langage de Conway-Kochen : « la réponse de la particule est libre » —
    c'est-à-dire qu'elle ne peut pas être une fonction déterministe de l'état caché. -/
theorem fwt_single_particle :
    ¬ ∃ f : DeterministicResponse, SatisfiesSPIN f := by
  rintro ⟨f, hspin⟩
  exact kochen_specker ⟨f 0, hspin 0⟩

/-!
## Étape 2 : Théorème du libre arbitre à deux particules

Deux particules de spin 1 sont préparées dans un état intriqué et envoyées à
deux expérimentateurs spatialement séparés, Alice et Bob. Alice mesure selon
la direction x, Bob selon la direction y. Trois axiomes contraignent les résultats :

  - **SPIN** : le carré du spin selon des directions orthogonales donne exactement un « 1 »
  - **TWIN** : les mesures parallèles sur des particules intriquées donnent le même résultat
  - **MIN** : les choix des expérimentateurs sont indépendants (séparation de type espace)

La conclusion : la réponse d'aucune des deux particules ne peut être une fonction du passé.
-/

/-- Deux expérimentateurs spatialement séparés. -/
inductive Experimenter
  | alice
  | bob
  deriving DecidableEq, Fintype

/-- Un modèle déterministe à deux particules associe un résultat {0,1} défini
    à chaque expérimentateur, état caché et direction de mesure.

    Cela représente l'hypothèse selon laquelle les réponses des deux particules sont
    déterminées par des variables cachées : `f(λ, e, d)` donne le résultat
    prédéterminé lorsque l'expérimentateur `e` mesure selon la direction `d` dans
    l'état caché `λ`. -/
abbrev TwoParticleResponse := HiddenState → Experimenter → VecIdx → Bool

/-- **Axiome TWIN** : lorsque les deux expérimentateurs mesurent selon la *même*
    direction, ils obtiennent la même réponse. C'est la signature de
    l'intrication quantique — la corrélation EPR.

    Physiquement : si Alice mesure le carré du spin selon la direction d et
    Bob mesure aussi selon d (directions parallèles), leurs résultats coïncident. -/
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

/-- Un modèle déterministe à deux particules satisfait tous les axiomes du théorème
    du libre arbitre : SPIN pour les deux particules, corrélation TWIN, et MIN
    (indépendance structurelle).

    MIN est satisfait par construction : chaque `f state e dir` ne prend pas
    la direction de l'autre expérimentateur en entrée. -/
structure SatisfiesFWT (f : TwoParticleResponse) : Prop where
  spin : ∀ e : Experimenter, SatisfiesSPIN (f · e)
  twin : SatisfiesTWIN f

/-- **Théorème du libre arbitre (version à deux particules, Conway-Kochen 2009)**.
    Aucun modèle déterministe à deux particules ne satisfait tous les axiomes du FWT.

    *Preuve* : Par TWIN, Alice et Bob partagent la même fonction de réponse.
    Par SPIN pour Alice, cette fonction partagée définit une coloration valide des
    vecteurs de Cabello pour chaque état caché. Mais le FWT à une particule
    (donc Kochen-Specker) dit qu'aucune telle fonction n'existe.
    Contradiction.

    *Conclusion* (Conway-Kochen) : les réponses des particules ne sont
    *pas* déterminées par le passé. Dans leur définition mathématique,
    les particules ont le « libre arbitre ». -/
theorem free_will_theorem :
    ¬ ∃ f : TwoParticleResponse, SatisfiesFWT f := by
  rintro ⟨f, hfwt⟩
  -- By SPIN for Alice: f(·, .alice) is a deterministic response
  -- satisfying SPIN. This contradicts the single-particle FWT.
  have hspin_alice : SatisfiesSPIN (f · .alice) := hfwt.spin .alice
  exact fwt_single_particle ⟨(f · .alice), hspin_alice⟩

/-!
## Corollaire : la forme « forte »

Le théorème du libre arbitre fort (version 2009 avec MIN) affirme de plus
que *si* les choix des expérimentateurs sont libres (non déterminés par le
passé), *alors* les réponses des particules doivent aussi être libres.

Dans notre formalisation, nous avons prouvé la contraposée : si les réponses
ÉTAIENT déterminées par des variables cachées, les axiomes seraient violés.
De façon équivalente : sous SPIN + TWIN + MIN, les réponses ne sont pas déterministes.
-/

end FreeWillTheorem

/-!
## Connexion à l'héritage de Conway

Le théorème du libre arbitre est le deuxième pilier de l'héritage mathématique
de Conway formalisé dans cet espace de travail, complétant l'hommage aux
côtés du Jeu de la Vie (Epic #1647) :

  1. **Life** (Phase 2) : émergence du calcul complexe à partir de règles simples
  2. **Free Will Theorem** (Phase 3) : limites mathématiques du déterminisme

Les deux sont Conway dans sa quintessence : élégants, surprenants, et accessibles
une fois correctement cadrés. Le théorème KS (preuve de Cabello à 18 vecteurs) sert
de moteur combinatoire, et le FWT lui-même est une réduction en une ligne.

Palmarès :
  - Conway & Kochen (2006) — Théorème du libre arbitre (original)
  - Conway & Kochen (2009) — Théorème du libre arbitre fort (version MIN)
  - Kochen & Specker (1967) — théorème KS original à 117 vecteurs
  - Cabello, Estebaranz, Garcia-Alcaine (1996) — preuve KS serrée à 18 vecteurs
-/

end Conway
