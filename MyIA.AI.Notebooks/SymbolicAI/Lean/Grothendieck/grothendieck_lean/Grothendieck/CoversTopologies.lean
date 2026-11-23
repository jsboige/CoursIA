/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 44 : forme flèche de la topologie dense

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-43 ont établi les fondamentaux : catégories, cribles,
topologies, lois de treillis, identités de pullback, bases de faisceaux,
clôture couvrante, calibration, sous-canonicalité, topologies denses,
faisceaux, hom interne, cohomologie de Čech, limite de Mayer-Vietoris,
extensions de Kan, adjonctions, monades, équivalences, catégories monoïdales,
la construction de Grothendieck, l'image directe/exceptionnelle, la forme
flèche de la couverture, les lois de cohérence du pseudo-foncteur pullback
et les lois de treillis indexées.

Cette partie complète la forme flèche `J.Covers` pour les topologies
extrémales. Pour les topologies **discrète** (`discrete = ⊤`) et **triviale**
(`trivial = ⊥`), Mathlib fournit déjà les formes flèche :
`top_covers : (⊤ : GrothendieckTopology C).Covers S f` et
`bot_covers : (⊥ : GrothendieckTopology C).Covers S f ↔ S f`. Le vrai
manque est la forme flèche de la topologie **dense** : `dense_covering`
n'est qu'un énoncé ponctuel (`S ∈ dense X ↔ ∀ {Y} (f : Y ⟶ X), ∃ …`).
On fournit ici sa traduction à la forme flèche `dense.Covers S f`, la
stabilité par précomposition et le lien avec l'appartenance ponctuelle.

Le fil conducteur : tout énoncé ponctuel `S ∈ J X` admet un jumeau en forme
flèche `J.Covers S f` (par `covers_iff`, `S.pullback f ∈ J Y`). Les parties
39-43 ont montré le motif pour `⊓`, `⊔`, `sInf`, `sSup`, la couverture du
pullback et l'ordre ; ici on l'applique à la topologie dense.
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck.CoversTopologies

open CategoryTheory

/-!
## Section 1 : la forme flèche de la topologie dense

La topologie dense de Mathlib est définie ponctuellement :
`dense_covering : S ∈ dense X ↔ ∀ {Y} (f : Y ⟶ X), ∃ (Z) (g : Z ⟶ Y), S (g ≫ f)`.
Sa traduction à la forme flèche dit qu'un crible `S` couvre une flèche
`f : Y ⟶ X` pour `dense` si et seulement si toute factorisation de `f`
se raffine en une flèche de `S` : c'est exactement la condition de
définition, réécrite sur `S.pullback f ∈ dense Y`.
-/

/-- Forme flèche de `dense_covering` : `S` est dense au-dessus de `f`
    si et seulement si toute flèche `g` vers le domaine de `f` admet une
    factorisation dont le composite est dans `S`.
    Preuve : `covers_iff` réduit le membre gauche à `S.pullback f ∈ dense Y`,
    puis `dense_covering` déplie la définition ponctuelle ; la
    réécriture `(S.pullback f) (h ≫ g) = S (h ≫ g ≫ f)` (définition du
    pullback d'un crible plus associativité) fait coïncider les deux membres. -/
theorem dense_covers_iff {C : Type*} [Category C] {X Y : C} (S : Sieve X) (f : Y ⟶ X) :
    GrothendieckTopology.dense.Covers S f ↔
      ∀ {Z : C} (g : Z ⟶ Y), ∃ (W : C) (h : W ⟶ Z), S (h ≫ g ≫ f) := by
  rw [GrothendieckTopology.covers_iff, GrothendieckTopology.dense_covering]
  simp

/-!
## Section 2 : stabilité par précomposition

La propriété de topologie `pullback_stable` de `dense` dit qu'une flèche
dans `S.pullback f ∈ dense Y` se transporte à `(S.pullback f).pullback g`.
Par l'identité `S.pullback (g ≫ f) = (S.pullback f).pullback g`
(`Sieve.pullback_comp`), c'est exactement la stabilité de la forme flèche :
si `S` est dense au-dessus de `f`, il l'est au-dessus de tout `g ≫ f`.
-/

/-- La forme flèche de `dense` est stable par précomposition : si `S` couvre
    `f : Y ⟶ X` pour `dense`, alors `S` couvre aussi `g ≫ f` pour toute
    `g : Z ⟶ Y`.
    Preuve : `covers_iff` des deux côtés, puis `Sieve.pullback_comp`
    identifie `S.pullback (g ≫ f)` à `(S.pullback f).pullback g`, et
    `pullback_stable g h` de la topologie dense conclut. -/
theorem dense_covers_precomp {C : Type*} [Category C] {X Y Z : C} (S : Sieve X)
    (f : Y ⟶ X) (g : Z ⟶ Y) :
    GrothendieckTopology.dense.Covers S f → GrothendieckTopology.dense.Covers S (g ≫ f) := by
  intro h
  rw [GrothendieckTopology.covers_iff] at h ⊢
  rw [Sieve.pullback_comp]
  exact GrothendieckTopology.dense.pullback_stable g h

/-!
## Section 3 : identité et appartenance ponctuelle

`Sieve.pullback_id` rend le pullback le long de l'identité trivial :
`S.pullback (𝟙 X) = S`. La forme flèche de `dense` au-dessus de `𝟙 X`
retombe donc exactement sur l'appartenance ponctuelle `S ∈ dense X`.
-/

/-- La forme flèche de `dense` au-dessus de l'identité coïncide avec
    l'appartenance ponctuelle : `dense.Covers S (𝟙 X) ↔ S ∈ dense X`.
    Preuve : `covers_iff` puis `Sieve.pullback_id`. -/
theorem dense_covers_id {C : Type*} [Category C] {X : C} (S : Sieve X) :
    GrothendieckTopology.dense.Covers S (𝟙 X) ↔ S ∈ GrothendieckTopology.dense X := by
  rw [GrothendieckTopology.covers_iff, Sieve.pullback_id]

/-- Toute flèche de `S` est couverte par `dense` : `S f → dense.Covers S f`.
    Preuve : `S f` force `S.pullback f = ⊤` (`Sieve.pullback_eq_top_of_mem`),
    et `⊤` appartient à tout crible d'une topologie (`top_mem`). -/
theorem dense_covers_of_mem {C : Type*} [Category C] {X Y : C} (S : Sieve X)
    {f : Y ⟶ X} (h : S f) :
    GrothendieckTopology.dense.Covers S f := by
  rw [GrothendieckTopology.covers_iff]
  rw [Sieve.pullback_eq_top_of_mem S h]
  exact GrothendieckTopology.top_mem GrothendieckTopology.dense Y

end Grothendieck.CoversTopologies
