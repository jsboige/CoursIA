/-
Knots.ReidemeisterCombinatorial — Suite de mouvements de Reidemeister vérifiable
================================================================================

Issue d'infrastructure (Epic #1453, point 3) : organe manquant derrière les
`sorry` restants de `knot_lean` (Reidemeister.lean:1056, Lidman.lean:81) —
une **suite de mouvements de Reidemeister vérifiable par le noyau**.

Pourquoi ce module est séparé de `Knots.Reidemeister` : la machinerie RTC
(`ReidemeisterEquiv`) est déjà en place (inductifs `ReidemeisterStep` et
`ReidemeisterEquiv`, lemmes `*.symm`, `reidemeister_equiv_symm`,
`reidemeister_equiv_equivalence`). Ce qu'il manque, c'est la **colonne
vertébrale algorithmique** :

  1. un alias `MoveSequence` pour `List ReidemeisterStep` (lisibilité),
  2. un constructeur `movesConnects` qui scelle la RTC en un témoin compact,
  3. un vérificateur **décidable borné** `verifyMoves` qui, pour un budget `n`
     de mouvements autorisés, énumère toutes les suites de R1/R2/R3 et
     retourne `true` si l'une d'elles relie deux diagrammes. Borné pour rester
     décidable ; l'énumération complète est `O((crossings+1)^n)`,
  4. la **soundness** du vérificateur : si `verifyMoves n d₁ d₂ = true`, alors
     `ReidemeisterEquiv d₁ d₂`. C'est la cible des passes prouveur subséquentes.

Ce que ce module **ne fait pas** :
- il ne prouve pas le théorème de Reidemeister profond (`reidemeister_theorem`,
  Reidemeister.lean:1053) qui exige PL-manifolds/S³/abs.isotopie — la
  soundness du vérificateur donne seulement le côté **combinatoire** (« ⇐ »
  ReidemeisterEquiv → ambient_isotopic reste hors juridiction) ;
- il ne s'attaque pas aux `sorry` permanents de `Knots.Slice` (Conway,
  Piccirillo, Freedman), marqués explicitement « decades away from formalization »
  par les sections précédentes — ces énoncés vivent dans une théorie
  4-manifolds / Khovanov / Kirby que Mathlib n'a pas.

Cible Lidman:81 — `unknotting_11n102_upper` — **devient accessible** une fois
ce module en place : on exhibe une `MoveSequence` reliant
`(changeCrossingAt c₁ (changeCrossingAt c₂ knot_11n102)).diagram` au
`unknotDiagram`, et `verifyMoves_sound` (à prouver par passe prouveur sur ce
module) scelle l'implication.

Convention i18n (EPIC #4980, décision user 2026-07-04) : ce fichier est **FR
canonique**, avec son miroir anglais dans le sibling `ReidemeisterCombinatorial_en.lean`
(modèle sibling pair ratifié 2026-07-04). Les énoncés de théorèmes, les
tactiques Lean, les noms de lemmes et les références Mathlib restent en anglais
(compat Mathlib 4) ; seules les docstrings de module et ce bloc d'en-tête
diffèrent entre les deux fichiers.

Statut au premier import : scaffolding initial (types + soundness énoncé).
Les passes prouveur (PR2+) fourniront `verifyMoves_sound`, le témoin pour
Lidman:81, et l'extension bornée `verifyMovesAux`.
-/

import Knots.Reidemeister
import Knots.Invariant

namespace Knots

/-! ## 1. Alias et constructeur de suite de mouvements

`MoveSequence` est un alias nommé de `List ReidemeisterStep` pour la lisibilité
des énoncés : une « suite de mouvements » est exactement une liste finie de pas
de Reidemeister, et le nom rend les types plus parlants aux consommateurs
(`Lidman.lean`, en particulier).
-/

/-- Une suite finie de mouvements de Reidemeister.

Alias nommé de `List ReidemeisterStep` (voir `Knots.Reidemeister`) : la liste
est dans l'ordre d'application (gauche → droite : `head` appliqué d'abord).
-/
abbrev MoveSequence : KnotDiagram → KnotDiagram → Type :=
  fun d₁ d₂ => List { d' // ReidemeisterStep d₁ d' }

/-- Une `MoveSequence` de longueur `0` connecte trivialement un diagramme à
lui-même (RTC réflexive, c'est `ReidemeisterEquiv.refl`). -/
def MoveSequence.nil (d : KnotDiagram) : MoveSequence d d := []

/-- Concaténer une suite avec un pas : `movesConnects d₁ d₂ ms ms' step` est
une suite qui applique `ms` de `d₁` à un diagramme intermédiaire, puis le pas
`step`. Le typeur impose la cohérence des diagrammes en bout de chaîne. -/
def MoveSequence.cons {d₁ d₂ d₃ : KnotDiagram}
    (step : ReidemeisterStep d₁ d₂) (ms : MoveSequence d₂ d₃) :
    MoveSequence d₁ d₃ :=
  ⟨d₂, step⟩ :: ms

/-! ## 2. Fermeture transitive d'une suite (`movesConnects`)

Le constructeur `movesConnects` scelle une `MoveSequence` en une preuve de
`ReidemeisterEquiv`. C'est l'inverse du constructeur `ReidemeisterEquiv.step`
rendu composable : récurrence structurelle sur la liste, `cons` devient
`step.trans`, `nil` devient `refl`.
-/

/-- Une suite de mouvements connecte `d₁` à `d₂` au sens de `ReidemeisterEquiv`.

Reconstruction par récurrence sur la `MoveSequence` :
- `nil` (suite vide) → `ReidemeisterEquiv.refl`,
- `cons step ms` → `ReidemeisterEquiv.trans (ReidemeisterEquiv.step step)
  (movesConnects d₂ d₃ ms)`.

La définition est **non-récursive à droite** : `movesConnects d₂ d₃ ms` est
calculé avant d'être consommé par le `trans`, ce qui rend l'évaluation
terminaison-safe sous `decreasing_by wf_tacs`.
-/
def movesConnects {d₁ d₂ : KnotDiagram} :
    MoveSequence d₁ d₂ → ReidemeisterEquiv d₁ d₂
  | [] => ReidemeisterEquiv.refl d₁
  | (⟨_, step⟩ :: ms) =>
    ReidemeisterEquiv.trans
      (ReidemeisterEquiv.step step)
      (movesConnects _ _ ms)

/-- Soundness triviale par construction : `movesConnects` _est_ la RTC. -/
theorem movesConnects_sound {d₁ d₂ : KnotDiagram}
    (ms : MoveSequence d₁ d₂) : ReidemeisterEquiv d₁ d₂ :=
  movesConnects ms

/-! ## 3. Vérificateur décidable borné

`verifyMovesAux` énumère les suites de longueur au plus `n` et décide si
l'une d'elles relie `d₁` à `d₂`. La décision est **décidable** (retourne un
`Bool`) — c'est l'instrument des passes prouveur qui n'ont pas accès à
l'orchestration tactic `decide` sur l'espace des suites infinies.

L'algorithme est volontairement naïf (énumération exhaustive) : pour les
bornes utiles en pratique (n ≤ 4), le branching factor reste dominé par
`(crossings+1) × 3` (R1/R2/R3 × double-sens) et le coût reste en
`O((3(numCrossings+1))^n)`. Les passes prouveur ultérieures raffineront en
évitant les symétries triviales (`ReidemeisterEquiv.symm`, `trans`).
-/

/-- Vue d'un `ReidemeisterStep` sous forme de constructeur pur (sans `d₂`
existentiel). Utilisée par l'algorithme pour reconstruire le diagramme cible
à chaque pas. -/
def ReidemeisterStep.toWitness (d₁ : KnotDiagram) (d₂ : KnotDiagram)
    (h : (Reidemeister1Connected d₁ d₂ ∨ Reidemeister1Connected d₂ d₁
       ∨ Reidemeister2Connected d₁ d₂ ∨ Reidemeister2Connected d₂ d₁
       ∨ Reidemeister3Connected d₁ d₂ ∨ Reidemeister3Connected d₂ d₁)) :
    ReidemeisterStep d₁ d₂ :=
  -- Distributivité du `∨` : la conjonction est soit R1, R2, soit R3,
  -- et dans chaque cas la direction est forward ou backward.
  -- La reconstruction est partielle : on accepte n'importe quel témoin
  -- `h` et on pattern-match pour choisir le bon constructeur de
  -- `ReidemeisterStep`. Le `_` est explicite pour signaler que la
  -- reconstruction n'est pas toujours unique (forward/backward symétriques).
  by
    rcases h with h | h | h | h | h | h
    · exact ReidemeisterStep.r1 (Or.inl h)
    · exact ReidemeisterStep.r1 (Or.inr h)
    · exact ReidemeisterStep.r2 (Or.inl h)
    · exact ReidemeisterStep.r2 (Or.inr h)
    · exact ReidemeisterStep.r3 (Or.inl h)
    · exact ReidemeisterStep.r3 (Or.inr h)

/-- Témoin brut d'un mouvement applicable : un `KnotDiagram` accessible depuis
`d₁` par un seul `ReidemeisterStep` (sans témoin de la relation).
-/
def oneStepWitnesses (d₁ : KnotDiagram) : List KnotDiagram :=
  -- Implémentation volontairement squelette : la liste exhaustive des
  -- successeurs à 1 mouvement de `d₁` n'est pas énumérée ici (PR2+) ; la
  -- fonction retourne `[]` en attendant. Les consommateurs qui dépendent de
  -- `verifyMoves` doivent traiter `[]` comme « aucun témoin à 1 mouvement »,
  -- ce que `verifyMoves 0` capture trivialement.
  []

/-- Vérificateur récursif borné.

`verifyMovesAux k d₁ d₂` retourne `true` ssi il existe une suite d'au plus
`k` `ReidemeisterStep` reliant `d₁` à `d₂`. Cas de base :
- `k = 0` → `d₁ = d₂` (RTC réflexive) ;
- `k ≥ 1` → il existe un successeur `d'` de `d₁` à 1 mouvement tel que
  `verifyMovesAux (k-1) d' d₂` est `true`.

**Statut** : squelette d'API pour PR2+. La version courante retourne `true`
uniquement sur le cas réflexif et `false` partout ailleurs, ce qui suffit
aux passes qui ne consomment que `verifyMoves 0` (équivalent à l'égalité
diagramme). L'implémentation effective est l'objet des passes prouveur
sur les `sorry` restants — voir issue #18611, lemmes 1-4.
-/
def verifyMovesAux : Nat → KnotDiagram → KnotDiagram → Bool
  | 0, d, d' => d == d'
  | k+1, d, d' =>
    -- Squelette : on considére `d == d'` (clôture réflexive à 0 mouvement)
    -- et chaque successeur à 1 mouvement de `d`. Le retour `false` est
    -- conservative (sound : `verifyMovesAux = true → ReidemeisterEquiv`,
    -- l'inverse n'est pas demandée).
    d == d' ||
    (oneStepWitnesses d).any fun d_next => verifyMovesAux k d_next d'

/-- Interface publique du vérificateur borné. -/
def verifyMoves (n : Nat) (d₁ d₂ : KnotDiagram) : Bool :=
  verifyMovesAux n d₁ d₂

/-! ## 4. Soundness (énoncé, à prouver par passe prouveur subséquente)

La soundness est le lemme-cible : « si `verifyMoves n d₁ d₂ = true`, alors
`ReidemeisterEquiv d₁ d₂ ». La réciproque (complétude) est hors scope —
l'algorithme est volontairement borné et perd des témoins au-delà du budget.

**Preuve visée** : récurrence sur `n`.
- `n = 0` : `verifyMovesAux 0 d₁ d₂ = (d₁ == d₂) = true` → `d₁ = d₂` →
  `ReidemeisterEquiv.refl d₁`.
- `n = k+1` : `verifyMovesAux (k+1) d₁ d₂ = true` →
  (`d₁ == d₂` ∧ réflexivité) ∨ (∃ d_next, `verifyMovesAux k d_next d₂ = true`
  ∧ `ReidemeisterStep d₁ d_next`). Cas par cas, le premier se ramène à
  `n = 0`, le second utilise l'hypothèse d'induction pour obtenir
  `ReidemeisterEquiv d_next d₂`, puis `ReidemeisterEquiv.step` + `trans`
  ferment le diagramme.

L'instrumentation concrète (lemme `Or.inl`/`Or.inr` dans le `Bool`, extraction
du témoin `d_next` depuis `(oneStepWitnesses d).any`) est l'objet de la
PR2+ ; elle dépend de `List.any`/`List.find` qui sont décidable dans Mathlib.
-/
theorem verifyMoves_sound :
    ∀ (n : Nat) (d₁ d₂ : KnotDiagram),
      verifyMoves n d₁ d₂ = true → ReidemeisterEquiv d₁ d₂ := by
  intro n d₁ d₂ h
  -- La soundness du squelette (qui ne retourne `true` que sur `d₁ == d'`) :
  -- trivial par `rfl` et `ReidemeisterEquiv.refl`. La version pleine (qui
  -- consomme `oneStepWitnesses`) sera ajoutée en PR2+ sans modifier
  -- l'énoncé.
  sorry

/-! ## 5. Helpers pour `Lidman.lean` (cible indirecte)

`foldChangeCrossingsAt` applique séquentiellement une liste de changements de
croisement à un nœud (fold left). C'est le « témoin `indices` » de
`Knot.UnknottableIn` (Invariant.lean:2292) rendu opérationnel.

`unknottingWitness` scelle l'usage typique : « pour qu'un nœud ait un nombre
de dénouement ≤ n, exhiber une suite de changements de croisement de longueur
n et une suite de ReidemeisterEquiv entre l'image et `unknotDiagram` ».
C'est le contrat que `unknotting_11n102_upper` (Lidman:81) honorera une fois
ce module landed et `verifyMoves_sound` prouvé.
-/

/-- Applique séquentiellement une liste de changements de croisement. -/
def foldChangeCrossingsAt (k : Knot) (indices : List Nat) : Knot :=
  indices.foldl Knot.changeCrossingAt k

/-- Témoin de dénouement : liste de changements + suite de ReidemeisterEquiv
entre l'image et `unknotDiagram`. -/
structure UnknottingWitness (k : Knot) (n : Nat) where
  indices : List Nat
  length_eq : indices.length = n
  equiv :
    MoveSequence
      (foldChangeCrossingsAt k indices).diagram
      unknotDiagram

/-! ## 6. Compatibilité future

Le module ne dépend que de `Knots.Reidemeister` et `Knots.Invariant` — pas de
`Knots.ReidemeisterInvariance` (qui importerait `Knots.Conway` et ferait
tourner le lac inutilement pour les passes qui n'attaquent que la
combinatoire). Le sibling `_en` sera ajouté en PR2 avec le miroir anglais
des docstrings (convention i18n EPIC #4980).

Le lakefile (`Knots.lean`, ligne d'import) devra ajouter
`import Knots.ReidemeisterCombinatorial` une fois ce module vérifié par CI —
PR3, après soundness et witness `Lidman:81`.
-/

end Knots
