/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 56 : forme flèche de la topologie de Zariski

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-55 ont établi les fondamentaux : catégories, cribles,
topologies, lois de treillis, identités de pullback, bases de faisceaux,
clôture couvrante, calibration, sous-canonicalité, topologies denses,
faisceaux, hom interne, cohomologie de Čech, limite de Mayer-Vietoris,
extensions de Kan, adjonctions, monades, équivalences, catégories monoïdales,
la construction de Grothendieck, l'image directe/exceptionnelle, la forme
flèche de la couverture, les lois de cohérence du pseudo-foncteur pullback,
les lois de treillis indexées, la forme flèche des topologies dense,
extrémales, de l'adjonction pushforward-pullback, du bind, de la topologie
engendrée par une prétopologie, de la topologie induite le long d'un
foncteur, des foncteurs préservant les couvertures, des lois de
composition de ces foncteurs, de la topologie engendrée par une couverture
au sens de `Coverage`, et de la topologie engendrée par une pré-couverture.

Cette partie applique le fil conducteur « forme flèche » à la **topologie
de Zariski sur la catégorie des schémas** — la première topologie *nommée*
concrète de la série (après la topologie dense de la Partie 44, définie sur
une catégorie abstraite). Mathlib fournit `Scheme.zariskiPretopology :=
pretopology @IsOpenImmersion`, le pont `Scheme.zariskiTopology_eq`
(`zariskiTopology = zariskiPretopology.toGrothendieck`) et la
caractérisation ponctuelle `Pretopology.mem_toGrothendieck`, mais
**aucune loi ne connecte la topologie de Zariski à la forme flèche**
`J.Covers`. On comble le trou par six théorèmes propres :

  - `covers_iff_zariski` (central, moule P54 instancié) : pour des
    schémas `X Y`, une flèche `f : Y ⟶ X` et un crible `S` sur `X`,
    `Scheme.zariskiTopology.Covers S f ↔ ∃ R ∈ Scheme.zariskiPretopology Y,
    R ≤ (S.pullback f).arrows` — la couverture flèche se teste sur `Y`
    par l'existence d'une famille d'immersions ouvertes couvrantes
    raffinant le pullback.
  - `covers_iff_exists_cover` (spécificité Zariski, théorème signature) :
    `Scheme.zariskiTopology.Covers S f ↔ ∃ 𝒰 : Y.Cover (precoverage
    IsOpenImmersion), Presieve.ofArrows 𝒰.X 𝒰.f ≤ S.pullback f` — dans
    le monde des schémas, couvrir c'est **être raffiné par un
    recouvrement ouvert concret** (`Scheme.Cover`). C'est la
    caractérisation géométrique de la forme flèche, inexistante au niveau
    générique des Parties 52-54 (qui opèrent sur une prétopologie
    abstraite, sans objet « recouvrement » concret).
  - `covers_zariski_of_mem` (cas de base) : si `R` est une famille
    couvrante au sens de la prétopologie de Zariski, le crible qu'elle
    engendre couvre l'identité.
  - `covers_zariski_of_mem_arrow` (cas généralisé) : la couverture
    engendrée par `R ∈ zariskiPretopology X` couvre n'importe quelle
    flèche `f : Y ⟶ X` — le raffinement descend sur `Y` par
    `pullbackArrows`, la stabilité par changement de base de la
    prétopologie.
  - `covers_zariski_top` : la couverture triviale `⊤` couvre n'importe
    quelle flèche — le témoin est `Presieve.singleton (𝟙 Y)`, admis par
    l'axiome `has_isos` des prétopologies (l'identité est une immersion
    ouverte).
  - `covers_iff_pullback_zariski` (retombée ponctuelle) : couvrir le long
    de l'identité équivaut à appartenir à la topologie.

Chaque preuve est une **preuve tactique réelle** (veine MED) : les axiomes
de Mathlib (`GrothendieckTopology.covers_iff`, `Scheme.zariskiTopology_eq`,
`Pretopology.mem_toGrothendieck`, `Scheme.mem_grothendieckTopology_iff`,
`Sieve.pullback_id`, `Sieve.le_generate`, `Sieve.generate_le_iff`,
`Sieve.pullbackArrows_comm`, `Pretopology.pullbacks`, `Pretopology.has_isos`,
`GrothendieckTopology.covering_iff_covers_id`) composés en instanciation
concrète. Aucune preuve n'est un re-export ou un unfold.

### Autonomie vis-à-vis de la Partie 54

La Partie 54 (`CoversPretopologyArrow`, forme flèche générique pour
`Pretopology.toGrothendieck`) n'est pas mergée au moment de l'écriture :
ce module est **autonome sur `main`** — il n'importe aucune branche
feature et réinstalle localement les trois tactiques du moule, instanciées
à `K := Scheme.zariskiPretopology`. Quand la Partie 54 mergera, les
théorèmes 1 et 3-6 s'en dériveront en une réécriture ; le théorème 2
(`covers_iff_exists_cover`) restera spécifique, car `Scheme.Cover` n'a
pas d'analogue au niveau générique.

EPIC #1646, Phase 5 (#2159). Tous les `sorry`s éliminés à la création.

### Convention i18n (EPIC #4980 ratifiée par user 2026-07-04)

Ce module est apparié avec son jumeau anglais dans le fichier sibling
`CoversZariskiArrow_en.lean` (modèle sibling pair, voir PR #6154 pour
le pilote sur `Utility.lean`). Namespace suffix `_en` appliqué au fichier EN
(anti-collision, conforme code-style.md #4980). Les énoncés de théorèmes, les
noms de lemmes, les tactiques Lean et les références Mathlib restent en
anglais ; seules les docstrings `/-- ... -/` et les commentaires `-- ...`
diffèrent entre les deux fichiers (préservation byte-identity).
-/

import Mathlib.AlgebraicGeometry.Sites.BigZariski

namespace Grothendieck.CoversZariskiArrow

open CategoryTheory Limits AlgebraicGeometry

universe u

/-!
## Section 1 : le pont central — forme flèche ↔ test sur le but du pullback

La topologie de Zariski est l'exemple fondamental de topologie de
Grothendieck issue d'une prétopologie : `Scheme.zariskiPretopology :=
pretopology @IsOpenImmersion` (les familles couvrantes sont les familles
d'immersions ouvertes conjointement surjectives), et
`Scheme.zariskiTopology_eq` identifie la topologie engendrée. La forme
flèche `J.Covers S f ↔ S.pullback f ∈ J Y` (`covers_iff` Mathlib) se
combine avec `Pretopology.mem_toGrothendieck` (qui dit qu'appartenir à la
topologie engendrée, c'est contenir une famille couvrante) pour donner le
test concret : `Covers S f` ssi il existe une famille d'immersions ouvertes
couvrantes de `Y` raffinant le pullback de `S` le long de `f`.
-/

/-- Pont central : la forme flèche pour la topologie de Zariski équivaut
    au test existentiel sur la prétopologie du but :
    `Scheme.zariskiTopology.Covers S f ↔ ∃ R ∈ Scheme.zariskiPretopology Y,
    R ≤ (S.pullback f).arrows`.
    Preuve : `covers_iff` réduit à `S.pullback f ∈ zariskiTopology Y`,
    `zariskiTopology_eq` ramène à `zariskiPretopology.toGrothendieck`,
    puis `Pretopology.mem_toGrothendieck` identifie à l'existence d'une
    famille couvrante `R` au-dessus du pullback. -/
theorem covers_iff_zariski {X Y : Scheme.{u}} (S : Sieve X) (f : Y ⟶ X) :
    Scheme.zariskiTopology.Covers S f ↔
      ∃ R ∈ Scheme.zariskiPretopology Y, R ≤ (S.pullback f).arrows := by
  rw [GrothendieckTopology.covers_iff, Scheme.zariskiTopology_eq]
  exact Pretopology.mem_toGrothendieck _ _ _

/-!
## Section 2 : spécificité Zariski — la caractérisation par recouvrements ouverts

C'est la contribution qui n'existe pas au niveau générique des Parties
52-54 : dans la catégorie des schémas, la prétopologie de Zariski
provient d'une propriété de morphismes (`IsOpenImmersion`), et Mathlib
caractérise l'appartenance à la topologie engendrée par l'existence d'un
**recouvrement concret** (`Scheme.Cover`, famille indexée d'immersions
ouvertes conjointement surjectives) dont le crible engendré raffine `S`.
En forme flèche : `Covers S f` ssi un recouvrement ouvert de `Y` raffine
le pullback. C'est la formulation qu'utilise un géomètre : couvrir un
schéma, c'est exhiber un recouvrement ouvert.
-/

/-- Spécificité Zariski (théorème signature) : la forme flèche pour la
    topologie de Zariski équivaut à l'existence d'un recouvrement ouvert
    concret du but :
    `Scheme.zariskiTopology.Covers S f ↔ ∃ 𝒰 : Y.Cover (precoverage
    IsOpenImmersion), Presieve.ofArrows 𝒰.X 𝒰.f ≤ S.pullback f`.
    Preuve : `covers_iff` réduit au ponctuel sur `Y`, puis
    `Scheme.mem_grothendieckTopology_iff` (Mathlib,
    `AlgebraicGeometry.Sites.Pretopology`) identifie l'appartenance à
    l'existence d'un `Scheme.Cover` par immersions ouvertes raffinant le
    crible. -/
theorem covers_iff_exists_cover {X Y : Scheme.{u}} (S : Sieve X) (f : Y ⟶ X) :
    Scheme.zariskiTopology.Covers S f ↔
      ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage IsOpenImmersion) Y,
        Presieve.ofArrows 𝒰.X 𝒰.f ≤ S.pullback f := by
  rw [GrothendieckTopology.covers_iff]
  exact Scheme.mem_grothendieckTopology_iff (P := IsOpenImmersion)

/-!
## Section 3 : cas de base — familles couvrantes et crible engendré

Quand la prétopologie fournit une famille `R` d'immersions ouvertes
couvrantes de `X`, le crible `Sieve.generate R` qu'elle engendre couvre.
Sur l'identité, le pullback est trivial (`Sieve.pullback_id`) et `R`
lui-même est le témoin (`Sieve.le_generate`). Pour une flèche générale,
le raffinement descend sur `Y` par `pullbackArrows`, admis dans la
prétopologie par l'axiome de stabilité par changement de base
(`Pretopology.pullbacks`) ; la commutation
`generate ∘ pullbackArrows = pullback ∘ generate`
(`Sieve.pullbackArrows_comm`) referme le but.
-/

/-- Cas de base : si `R` est une famille d'immersions ouvertes
    couvrantes de `X` (au sens de `zariskiPretopology`), alors le crible
    qu'elle engendre couvre l'identité :
    `Scheme.zariskiTopology.Covers (Sieve.generate R) (𝟙 X)`.
    Preuve : `covers_iff_zariski` ramène au test existentiel sur `X`,
    `Sieve.pullback_id` trivialise le pullback, et `R` est son propre
    témoin par `Sieve.le_generate`. -/
theorem covers_zariski_of_mem {X : Scheme.{u}} {R : Presieve X}
    (hR : R ∈ Scheme.zariskiPretopology X) :
    Scheme.zariskiTopology.Covers (Sieve.generate R) (𝟙 X) := by
  rw [covers_iff_zariski, Sieve.pullback_id]
  exact ⟨R, hR, Sieve.le_generate R⟩

/-- Cas de base généralisé : la couverture engendrée par `R` couvre
    n'importe quelle flèche `f : Y ⟶ X`. Preuve : le témoin sur `Y` est
    `R.pullbackArrows f`, admis dans la prétopologie par
    `Pretopology.pullbacks` (stabilité par changement de base — la
    préimage d'un recouvrement ouvert par une flèche de schémas est un
    recouvrement ouvert), et `Sieve.pullbackArrows_comm` commute
    génération et pullback. -/
theorem covers_zariski_of_mem_arrow {X Y : Scheme.{u}} (f : Y ⟶ X)
    {R : Presieve X} (hR : R ∈ Scheme.zariskiPretopology X) :
    Scheme.zariskiTopology.Covers (Sieve.generate R) f := by
  rw [covers_iff_zariski]
  refine ⟨R.pullbackArrows f, Scheme.zariskiPretopology.pullbacks f R hR, ?_⟩
  rw [← Sieve.generate_le_iff, Sieve.pullbackArrows_comm]

/-- Cas particulier sur le crible top : `Scheme.zariskiTopology.Covers ⊤ f`
    pour toute flèche `f : Y ⟶ X`. Preuve : le témoin est
    `Presieve.singleton (𝟙 Y)`, admis par l'axiome `Pretopology.has_isos`
    (l'identité est un isomorphisme, donc une immersion ouverte
    triviale), qui domine `⊤`. -/
theorem covers_zariski_top {X Y : Scheme.{u}} (f : Y ⟶ X) :
    Scheme.zariskiTopology.Covers (⊤ : Sieve X) f := by
  rw [covers_iff_zariski]
  exact ⟨Presieve.singleton (𝟙 Y), Scheme.zariskiPretopology.has_isos (𝟙 Y), by simp⟩

/-!
## Section 4 : retombée ponctuelle

Spécialisation sur l'identité : couvrir le long de l'identité équivaut
à appartenir à la topologie — c'est `covering_iff_covers_id` Mathlib,
relié à `zariskiTopology` par `zariskiTopology_eq`.
-/

/-- Retombée ponctuelle : couvrir le long de l'identité équivaut à
    appartenir à la topologie de Zariski :
    `Scheme.zariskiTopology.Covers S (𝟙 X) ↔ S ∈ Scheme.zariskiTopology X`.
    Preuve : `zariskiTopology_eq` ramène au ponctuel, puis c'est
    exactement `GrothendieckTopology.covering_iff_covers_id`. -/
theorem covers_iff_pullback_zariski {X : Scheme.{u}} (S : Sieve X) :
    Scheme.zariskiTopology.Covers S (𝟙 X) ↔ S ∈ Scheme.zariskiTopology X := by
  rw [Scheme.zariskiTopology_eq]
  exact (GrothendieckTopology.covering_iff_covers_id
    (J := Scheme.zariskiPretopology.toGrothendieck) S).symm

end Grothendieck.CoversZariskiArrow
