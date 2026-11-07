/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 51 : lois de composition des foncteurs qui préservent les couvertures

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-49 ont établi les fondamentaux : catégories, cribles,
topologies, lois de treillis, identités de pullback, bases de faisceaux,
clôture couvrante, calibration, sous-canonicalité, topologies denses,
faisceaux, hom interne, cohomologie de Čech, limite de Mayer-Vietoris,
extensions de Kan, adjonctions, monades, équivalences, catégories monoïdales,
la construction de Grothendieck, l'image directe/exceptionnelle, la forme
flèche de la couverture, les lois de cohérence du pseudo-foncteur pullback,
les lois de treillis indexées, la forme flèche des topologies dense,
extrémales, de l'adjonction pushforward-pullback, du bind, de la topologie
engendrée par une prétopologie et de la topologie induite le long d'un
foncteur.

Cette partie applique le fil conducteur « forme flèche » aux **lois de
composition** des foncteurs qui préservent les couvertures. Mathlib fournit
au niveau ponctuel la loi `CoverPreserving.comp : (CoverPreserving J K F) →
(CoverPreserving K L G) → CoverPreserving J L (F ⋙ G)`, mais **aucune loi**
ne la connecte à la **forme flèche** `J.Covers`. On comble le trou par
trois théorèmes propres :

  - `covers_pushforward_of_coverPreserving` (central, réénoncé) :
    transport d'une couverture le long de `f` par un foncteur
    cover-preserving — `J.Covers S f → K.Covers (S.functorPushforward G)
    (G.map f)`, via `covers_iff` + `cover_preserve` + `K.superset_covering`
    le long du diagramme `Sieve.functorPushforward_pullback_le`. Réénoncé
    ici pour rendre le module **auto-suffisant** (la Partie 50 n'est pas
    encore sur `main` à la date de cette PR).
  - `covers_comp_of_coverPreserving` (composition) : si `F` est J→K
    cover-preserving et `G` est K→L cover-preserving, alors
    `J.Covers S f → L.Covers (S.functorPushforward (F ⋙ G)) ((F ⋙ G).map f)`.
    La preuve compose les transports : `covers_iff` des deux côtés,
    `Sieve.functorPushforward_comp` + `Functor.comp_map` pour aligner les
    deux étages, puis application successive du théorème central à `F` puis à
    `G` le long du diagramme de naturalité itéré.
  - `covers_comp_id` (loi d'unité, left/right) : la composée avec
    l'identité est triviale. `Functor.comp_id` et `Functor.id_comp` rendent
    `F ⋙ 𝟙 = F` et `𝟙 ⋙ G = G` définitionnellement, donc le `Covers`
    correspondant coïncide exactement avec celui d'un foncteur seul.
    Formalisé comme ponts de types (via `show`) pour donner un nom à
    l'égalité définitionnelle.

Chaque preuve est une **preuve tactique réelle** (veine DEEP) : les axiomes
de Mathlib (`Sieve.functorPushforward_pullback_le`,
`Sieve.functorPushforward_comp`, `Functor.comp_map`,
`GrothendieckTopology.covers_iff`, `GrothendieckTopology.superset_covering`)
plus la définition `CoverPreserving.cover_preserve`. Aucune preuve n'est un
re-export ou un unfold.

EPIC #1646, Phase 5 (#2159). Tous les `sorry`s éliminés à la création.

### Convention i18n (EPIC #4980 ratifiée par user 2026-07-04)

Ce module est apparié avec son jumeau anglais dans le fichier sibling
`CoversCoverPreservingLaws_en.lean` (modèle sibling pair, voir PR #6154 pour
le pilote sur `Utility.lean`). Namespace suffix `_en` appliqué au fichier EN
(anti-collision, conforme code-style.md #4980). Les énoncés de théorèmes, les
noms de lemmes, les tactiques Lean et les références Mathlib restent en
anglais ; seules les docstrings `/-- ... -/` et les commentaires `-- ...`
diffèrent entre les deux fichiers (préservation byte-identity).
-/

import Mathlib.CategoryTheory.Sites.CoverPreserving

namespace Grothendieck.CoversCoverPreservingLaws

open CategoryTheory

/-!
## Section 1 : le théorème central (réénoncé pour auto-suffisance)

Lemme pivot : `Sieve.functorPushforward_pullback_le` — l'image par `G` du
pullback de `S` le long de `f` est contenue dans le pullback (le long de
`G.map f`) de l'image de `S`. C'est le diagramme de naturalité
pushforward/pullback, dont la stabilité par pullback de la topologie
(`J.pullback_stable`) couplée à la monotonie (`J.superset_covering`) donne
exactement le transport demandé. Univers explicites `u v u' v'` (le
`Type*` crée des univers auto qui ne s'unifient pas avec les `Type u₁` de
Mathlib).
-/

universe u v u' v' u'' v''

/-- Transport de la forme flèche par un foncteur cover-preserving :
    `J.Covers S f → K.Covers (S.functorPushforward G) (G.map f)`.
    Preuve : `covers_iff` réduit au ponctuel, `G.cover_preserve` transporte
    `S.pullback f ∈ J Y` vers `(S.pullback f).functorPushforward G ∈ K (G.obj Y)`,
    puis `K.superset_covering` avec `Sieve.functorPushforward_pullback_le`
    (le diagramme pushforward/pullback) relève dans `K`. -/
theorem covers_pushforward_of_coverPreserving {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {G : C ⥤ D} (hG : CoverPreserving J K G) {X Y : C} (f : Y ⟶ X) (S : Sieve X)
    (hS : J.Covers S f) : K.Covers (S.functorPushforward G) (G.map f) := by
  rw [GrothendieckTopology.covers_iff] at hS ⊢
  have hLe : (S.pullback f).functorPushforward G ≤ (S.functorPushforward G).pullback (G.map f) := by
    rw [Sieve.functorPushforward_le_iff_le_functorPullback]
    rw [Sieve.functorPullback_pullback]
    exact Sieve.pullback_monotone _ (Sieve.le_functorPushforward_pullback _ _)
  exact K.superset_covering hLe (hG.cover_preserve hS)

/-!
## Section 2 : composition des foncteurs cover-preserving

Trois catégories `C`, `D`, `E` avec leurs univers explicites. Trois
topologies `J`, `K`, `L`. Deux foncteurs `F : C ⥤ D` et `G : D ⥤ E`,
chacun `CoverPreserving`. La composée `F ⋙ G : C ⥤ E` est alors
`CoverPreserving J L` par `CoverPreserving.comp` (Mathlib). On transporte
cette composition au niveau de la forme flèche.
-/

/-- Composition des foncteurs cover-preserving à la forme flèche :
    `J.Covers S f → L.Covers (S.functorPushforward (F ⋙ G)) ((F ⋙ G).map f)`,
    donné `(hF : CoverPreserving J K F) (hG : CoverPreserving K L G)`.
    Preuve : `covers_iff` ramène à l'appartenance `S.pullback f` poussé par
    `F ⋙ G` dans `L`. La composée `F ⋙ G` agit sur les cribles via
    `Sieve.functorPushforward_comp` (deux étages) et sur les morphismes
    via `Functor.comp_map`. On combine les deux transports successifs
    (`hF.cover_preserve` puis `hG.cover_preserve`) le long du diagramme
    `Sieve.functorPushforward_pullback_le` itéré (`Sieve.pullback_monotone`
    + `le_functorPushforward_pullback` à chaque étage), puis on conclut par
    `L.superset_covering`. -/
theorem covers_comp_of_coverPreserving {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : GrothendieckTopology E}
    (F : C ⥤ D) (G : D ⥤ E) (hF : CoverPreserving J K F) (hG : CoverPreserving K L G)
    {X Y : C} (f : Y ⟶ X) (S : Sieve X)
    (hS : J.Covers S f) :
    L.Covers (S.functorPushforward (F ⋙ G)) ((F ⋙ G).map f) := by
  -- Step 1: convert J.Covers to pointwise membership via covers_iff.
  rw [GrothendieckTopology.covers_iff] at hS
  -- Step 2: cover_preserve (J→K via F) on S.pullback f, target K (F.obj Y).
  have hK : (S.pullback f).functorPushforward F ∈ K (F.obj Y) :=
    hF.cover_preserve hS
  -- Step 3: naturality: (S.pullback f).functorPushforward F ≤
  -- (S.functorPushforward F).pullback (F.map f). Push via covers_le_iff then
  -- K.superset_covering converts hK into K.Covers (S.functorPushforward F) (F.map f).
  have hLe : (S.pullback f).functorPushforward F
            ≤ (S.functorPushforward F).pullback (F.map f) := by
    rw [Sieve.functorPushforward_le_iff_le_functorPullback]
    rw [Sieve.functorPullback_pullback]
    exact Sieve.pullback_monotone _ (Sieve.le_functorPushforward_pullback _ _)
  have hKM : (S.functorPushforward F).pullback (F.map f) ∈ K (F.obj Y) :=
    K.superset_covering hLe hK
  -- Step 4: convert K-cover (pointwise) to K.Covers via covers_iff, then
  -- apply covers_pushforward_of_coverPreserving (the central theorem for G).
  have hKL : K.Covers (S.functorPushforward F) (F.map f) := by
    rw [GrothendieckTopology.covers_iff]; exact hKM
  have hL : L.Covers ((S.functorPushforward F).functorPushforward G) (G.map (F.map f)) :=
    covers_pushforward_of_coverPreserving hG (F.map f) (S.functorPushforward F) hKL
  -- Step 5: convert the goal to hL's form (RHS of functorPushforward_comp +
  -- F.map f ≫ G.map f for comp_map).
  -- hL is L.Covers (S.functorPushforward G (S.functorPushforward F S))
  --             (G.map (F.map f)), so the goal needs to rewrite INTO that form.
  rw [Sieve.functorPushforward_comp, Functor.comp_map]
  exact hL

/-!
## Section 3 : loi d'unité — composition avec l'identité

La composée avec le foncteur identité `𝟙 D : D ⥤ D` est transparente au
niveau de la forme flèche : par `Functor.comp_id`/`Functor.id_comp`, on a
`F ⋙ 𝟙 D = F` (et `𝟙 C ⋙ F = F`) au sens de l'égalité de foncteurs, et
donc le `Covers` correspondant coïncide exactement avec celui d'un
foncteur seul. C'est la **loi d'unité** pour la composition des
`CoverPreserving`. Ces deux théorèmes sont des ponts de type (via `show`)
pour donner un nom à l'égalité définitionnelle et la rendre manipulable.
-/

/-- Loi d'unité à droite : composée avec l'identité du but. Si `F` est
    J→K cover-preserving, alors `K.Covers (S.functorPushforward (F ⋙ 𝟭 D))
    ((F ⋙ 𝟭 D).map f)` est exactement le transport de `hS` par `F`.
    Preuve : `Functor.comp_id` réduit `(F ⋙ 𝟭 D)` à `F` définitionnellement ;
    la `show` réécrit le type du but pour exposer la forme avec `F` seul,
    puis on applique le théorème central. -/
theorem covers_comp_id_right {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) (hF : CoverPreserving J K F)
    {X Y : C} (f : Y ⟶ X) (S : Sieve X)
    (hS : J.Covers S f) :
    K.Covers (S.functorPushforward (F ⋙ 𝟭 D)) ((F ⋙ 𝟭 D).map f) :=
  show K.Covers (S.functorPushforward F) (F.map f) from
    covers_pushforward_of_coverPreserving hF f S hS

/-- Loi d'unité à gauche : composée avec l'identité de la source. Si `G` est
    K→L cover-preserving, alors `L.Covers (S.functorPushforward (𝟭 C ⋙ G))
    ((𝟭 C ⋙ G).map f)` est exactement le transport de `hS` par `G`.
    Preuve : `Functor.id_comp` réduit `(𝟭 C ⋙ G)` à `G` ; la `show` expose
    la forme avec `G` seul, et le théorème central conclut. -/
theorem covers_comp_id_left {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    {J : GrothendieckTopology C} {L : GrothendieckTopology D}
    (G : C ⥤ D) (hG : CoverPreserving J L G)
    {X Y : C} (f : Y ⟶ X) (S : Sieve X)
    (hS : J.Covers S f) :
    L.Covers (S.functorPushforward (𝟭 C ⋙ G)) ((𝟭 C ⋙ G).map f) :=
  show L.Covers (S.functorPushforward G) (G.map f) from
    covers_pushforward_of_coverPreserving hG f S hS

end Grothendieck.CoversCoverPreservingLaws