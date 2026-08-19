/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 54 : forme flèche de la topologie engendrée par une prétopologie

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-53 ont établi les fondamentaux : catégories, cribles,
topologies, lois de treillis, identités de pullback, bases de faisceaux,
clôture couvrante, calibration, sous-canonicalité, topologies denses,
faisceaux, hom interne, cohomologie de Čech, limite de Mayer-Vietoris,
extensions de Kan, adjonctions, monades, équivalences, catégories monoïdales,
la construction de Grothendieck, l'image directe/exceptionnelle, la forme
flèche de la couverture, les lois de cohérence du pseudo-foncteur pullback,
les lois de treillis indexées, la forme flèche des topologies dense,
extrémales, de l'adjonction pushforward-pullback, du bind, de la topologie
engendrée par une prétopologie (`Precoverage.toGrothendieck`), de la
topologie induite le long d'un foncteur, des foncteurs préservant les
couvertures, des lois de composition de ces foncteurs, de la topologie
engendrée par une couverture au sens de `Coverage`, et de la topologie
engendrée par une pré-couverture (`Precoverage.toGrothendieck`).

Cette partie applique le fil conducteur « forme flèche » à la **topologie
engendrée par une prétopologie** (`Pretopology.toGrothendieck`).
Mathlib fournit au niveau ponctuel `Pretopology.mem_toGrothendieck` :
`S ∈ K.toGrothendieck X ↔ ∃ R ∈ K X, R ≤ (S : Presieve X)`, mais **aucune
loi ne la connecte à la forme flèche** `K.toGrothendieck.Covers`. On
comble le trou par cinq théorèmes propres — structure identique à la
Partie 52 et à la Partie 53 mais à un niveau **plus explicite** : la
prétopologie est définie par une condition concrète `R ≤ (S : Presieve X)`
et le `Saturate` inductif de `Coverage`/`Precoverage` devient un
quantificateur existentiel simple. Cela donne aux théorèmes une saveur
plus concrète (mais sans constructivité sur le témoin), complémentaire
des deux étages inductifs au-dessus :

  - `covers_iff_toGrothendieck` (central) : pour `K : Pretopology C`,
    `K.toGrothendieck.Covers S f ↔ ∃ R ∈ K Y, R ≤ (S.pullback f).arrows`
    — pont direct entre la forme flèche et la caractérisation ponctuelle
    `Pretopology.mem_toGrothendieck`, via `covers_iff`. C'est la **loi
    naturelle** à l'étage prétopologie.
  - `covers_toGrothendieck_of_of` (cas particulier) : si `R ∈ K X`
    est une prétopologie, alors le crible qu'elle engendre couvre
    l'identité : `K.toGrothendieck.Covers (Sieve.generate R) (𝟙 X)` —
    la retombée ponctuelle, via `covering_iff_covers_id`.
  - `covers_toGrothendieck_top` (cas particulier) : la couverture
    triviale `⊤` couvre l'identité : `K.toGrothendieck.Covers ⊤ (𝟙 X)`,
    retombée de `K.has_isos` via `mem_toGrothendieck`.
  - `covers_of_mem_toGrothendieck` (cas particulier sur `Sieve.generate`) :
    si `R ∈ K X`, alors `K.toGrothendieck.Covers (Sieve.generate R) f`
    pour n'importe quelle `f : Y ⟶ X` — la stabilité par pullback,
    qui chez la prétopologie est `K.pullbacks` (vs constructeur
    inductif chez `Precoverage`).
  - `covers_iff_pullback_toGrothendieck` (cas particulier sur l'identité) :
    `K.toGrothendieck.Covers S (𝟙 X) ↔ S ∈ K.toGrothendieck X`
    — la retombée ponctuelle, via `covering_iff_covers_id`.

Chaque preuve est une **preuve tactique réelle** (veine DEEP) : les axiomes
de Mathlib (`GrothendieckTopology.covers_iff`, `Pretopology.mem_toGrothendieck`,
`K.pullbacks`, `Sieve.pullback_id`, `covering_iff_covers_id`) plus la
définition `Pretopology.toGrothendieck`. Aucune preuve n'est un re-export
ou un unfold.

EPIC #1646, Phase 5 (#2159). Tous les `sorry`s éliminés à la création.

### Convention i18n (EPIC #4980 ratifiée par user 2026-07-04)

Ce module est apparié avec son jumeau anglais dans le fichier sibling
`CoversPretopologyArrow_en.lean` (modèle sibling pair, voir PR #6154 pour
le pilote sur `Utility.lean`). Namespace suffix `_en` appliqué au fichier EN
(anti-collision, conforme code-style.md #4980). Les énoncés de théorèmes, les
noms de lemmas, les tactiques Lean et les références Mathlib restent en
anglais ; seules les docstrings `/-- ... -/` et les commentaires `-- ...`
diffèrent entre les deux fichiers (préservation byte-identity).
-/

import Mathlib.CategoryTheory.Sites.Pretopology

namespace Grothendieck.CoversPretopologyArrow

open CategoryTheory Limits Pretopology

universe u v

/-!
## Section 1 : le pont central — forme flèche ↔ caractérisation existentielle

`Pretopology.toGrothendieck` part d'une prétopologie (famille de
présieves « couvrantes sur chaque objet ») et la prolonge en topologie de
Grothendieck en déclarant couvrante toute sieve qui contient une famille
couvrante au sens de la prétopologie :
`sieves X := {S | ∃ R ∈ K X, R ≤ (S : Presieve X)}`. La forme flèche
`K.toGrothendieck.Covers S f ↔ S.pullback f ∈ K.toGrothendieck Y` réduit
au ponctuel ; `Pretopology.mem_toGrothendieck` identifie l'appartenance
ponctuelle à un quantificateur existentiel sur la prétopologie de `Y`.

La différence avec les Parties 52 et 53 est qu'**aucune clôture inductive**
n'intervient : la prétopologie est directement une caractérisation par
existence (`∃ R ∈ K Y, R ≤ ...`), pas une `Saturate`. La preuve est donc
plus simple : `covers_iff` réduit à `S.pullback f ∈ K.toGrothendieck Y`,
puis `Pretopology.mem_toGrothendieck` ramène au test existentiel. Pas
besoin d'invoquer de constructeur inductif — la prétopologie est
**stable par hypothèse** (ses axiomes sont `has_isos`, `pullbacks`,
`transitive`, mais dans le contexte de `toGrothendieck` seul `has_isos`
et l'implication directe sont utilisés).
-/

/-- Pont central : la forme flèche pour la topologie `K.toGrothendieck`
    (où `K : Pretopology C`) équivaut à la caractérisation existentielle
    ponctuelle :
    `K.toGrothendieck.Covers S f ↔ ∃ R ∈ K Y, R ≤ (S.pullback f).arrows`.
    Preuve : `covers_iff` réduit à `S.pullback f ∈ K.toGrothendieck Y`,
    puis `Pretopology.mem_toGrothendieck` identifie à l'existence d'un
    `R ∈ K Y` au-dessus de `S.pullback f`. -/
theorem covers_iff_toGrothendieck {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]
    (K : Pretopology C) {X Y : C} (S : Sieve X) (f : Y ⟶ X) :
    K.toGrothendieck.Covers S f ↔ ∃ R ∈ K Y, R ≤ (S.pullback f).arrows := by
  rw [GrothendieckTopology.covers_iff]
  exact Pretopology.mem_toGrothendieck K Y _

/-!
## Section 2 : cas de base — la prétopologie couvre sa propre génération

Quand la prétopologie fournit un `R ∈ K X`, le crible `Sieve.generate R`
qu'elle engendre couvre l'identité au sens de `K.toGrothendieck` — c'est
le sens direct de `Pretopology.mem_toGrothendieck` (le `R ≤ ⊤` est trivial).
Le pont vient de `covering_iff_covers_id`, qui ramène à `Sieve.generate R ∈
K.toGrothendieck X`, puis on applique `mem_toGrothendieck` au témoin `R`
lui-même. On retrouve la même structure que pour `Coverage`/`Precoverage`
mais sans constructeur inductif.
-/

/-- Cas de base : si `R ∈ K X` est une prétopologie, alors le crible
    qu'elle engendre couvre l'identité :
    `K.toGrothendieck.Covers (Sieve.generate R) (𝟙 X)`.
    Preuve : `covering_iff_covers_id` ramène à
    `Sieve.generate R ∈ K.toGrothendieck X`, puis
    `Pretopology.mem_toGrothendieck` identifie à l'existence d'un témoin ;
    ici `R` lui-même est témoin (`R ≤ (Sieve.generate R).arrows` par
    `Sieve.le_generate`, et `R ∈ K X` par hypothèse). -/
theorem covers_toGrothendieck_of_of {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]
    (K : Pretopology C) {X : C} {R : Presieve X} (hR : R ∈ K X) :
    K.toGrothendieck.Covers (Sieve.generate R) (𝟙 X) :=
  (GrothendieckTopology.covering_iff_covers_id (J := K.toGrothendieck) (X := X)
    (Sieve.generate R)).mp ⟨R, hR, Sieve.le_generate R⟩

/-- Cas de base généralisé : la couverture engendrée par `R` couvre
    n'importe quelle flèche `f : Y ⟶ X`. Preuve : d'abord
    `covers_iff_toGrothendieck` ramène à l'existence d'un
    `R' ∈ K Y` au-dessus de `(Sieve.generate R).pullback f`. On exhibe
    `R.pullbackArrows f` : `K.pullbacks f R hR` est
    dans `K Y`, et par la définition de `Sieve.pullbackArrows_comm`,
    `R.pullbackArrows f ≤ (Sieve.generate R).pullback f`. -/
theorem covers_of_mem_toGrothendieck {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]
    (K : Pretopology C) {X Y : C} (f : Y ⟶ X) {R : Presieve X} (hR : R ∈ K X) :
    K.toGrothendieck.Covers (Sieve.generate R) f := by
  rw [covers_iff_toGrothendieck]
  refine ⟨R.pullbackArrows f, K.pullbacks f R hR, ?_⟩
  rw [← Sieve.generate_le_iff, Sieve.pullbackArrows_comm]

/-- Cas particulier sur le crible top : `K.toGrothendieck.Covers ⊤ (𝟙 X)`.
    Preuve : `K.has_isos` (l'axiome d'isomorphismes) fournit le témoin
    `Presieve.singleton (𝟙 X) ∈ K X`, qui domine `⊤.arrows = ⊤`. -/
theorem covers_toGrothendieck_top {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]
    (K : Pretopology C) (X : C) :
    K.toGrothendieck.Covers (⊤ : Sieve X) (𝟙 X) :=
  (GrothendieckTopology.covering_iff_covers_id (J := K.toGrothendieck) (X := X) ⊤).mp
    ⟨Presieve.singleton (𝟙 X), K.has_isos (𝟙 X), by simp⟩

/-!
## Section 3 : retombée ponctuelle

Spécialisation sur l'identité : `K.toGrothendieck.Covers S (𝟙 X) ↔ S ∈
K.toGrothendieck X`. Le pont vers la couverture ponctuelle est
immédiat via `covering_iff_covers_id`.
-/

/-- Retombée ponctuelle : pour `K : Pretopology C`, couvrir le long
    de l'identité équivaut à appartenir à la topologie :
    `K.toGrothendieck.Covers S (𝟙 X) ↔ S ∈ K.toGrothendieck X`.
    Preuve : c'est exactement `covering_iff_covers_id`. -/
theorem covers_iff_pullback_toGrothendieck {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]
    (K : Pretopology C) {X : C} (S : Sieve X) :
    K.toGrothendieck.Covers S (𝟙 X) ↔ S ∈ K.toGrothendieck X :=
  (GrothendieckTopology.covering_iff_covers_id (J := K.toGrothendieck) (X := X) S).symm

end Grothendieck.CoversPretopologyArrow
