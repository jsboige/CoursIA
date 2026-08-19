/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 57 : forme flèche de la topologie atomique

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-56 ont établi les fondamentaux : catégories, cribles,
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
au sens de `Coverage`, de la topologie engendrée par une pré-couverture,
et de la topologie de Zariski sur les schémas.

Cette partie applique le fil conducteur « forme flèche » à la **topologie
atomique** — deuxième topologie *nommée* abstraite de la série après la
topologie dense (Partie 44). Mathlib définit
`GrothendieckTopology.atomic (hro : RightOreCondition C) : GrothendieckTopology C`
(un crible est couvrant s'il est non vide ; la condition d'Ore à droite est
requise pour la stabilité par pullback), mais **ne fournit ni le pont
ponctuel** (l'analogue de `dense_covering` pour `atomic`) **ni aucune loi
en forme flèche**. On comble le trou par six théorèmes propres :

  - `atomic_covering` (pont ponctuel, `Iff.rfl`) : `S ∈ atomic hro X ↔
    ∃ Y f, S f` — l'analogue manquant de `dense_covering` ;
  - `covers_iff_atomic` (central) : `(atomic hro).Covers S f ↔ ∃ Z g,
    S (g ≫ f)` — la topologie atomique couvre `f` par `S` si et seulement
    si `S` contient au moins une flèche au-dessus de `f` ;
  - `covers_atomic_of_mem` : toute flèche de `S` couvre toute flèche ;
  - `covers_atomic_precomp` : stabilité par précomposition ;
  - `covers_atomic_id` : retombée ponctuelle à l'identité ;
  - `covers_atomic_top` : le crible maximal couvre toute flèche.

Le fil conducteur : tout énoncé ponctuel `S ∈ J X` admet un jumeau en forme
flèche `J.Covers S f` (par `covers_iff`, `S.pullback f ∈ J Y`). Après la
topologie dense (P44) et la topologie de Zariski (P56), la topologie
atomique est le troisième jalon nommé : sa forme flèche dit exactement que
« couvrir = être non vide au-dessus de la cible ».
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck.CoversAtomicArrow

open CategoryTheory

/-!
## Section 1 : le pont ponctuel et la forme flèche

La topologie atomique de Mathlib est construite ponctuellement
(`sieves X := {S | ∃ (Y) (f : Y ⟶ X), S f}`), mais sans le lemme
d'appartenance que Mathlib fournit pour `dense` (`dense_covering`). On
l'établit d'abord (`Iff.rfl` : c'est la définition même), puis on le
traduit en forme flèche : `S` couvre `f` pour `atomic` si et seulement si
le pullback `S.pullback f` est non vide — c'est-à-dire si `S` contient une
flèche composant au-dessus de `f`.
-/

/-- Pont ponctuel pour la topologie atomique — l'analogue du
    `dense_covering` de Mathlib, absent de la bibliothèque : un crible est
    couvrant pour `atomic hro X` si et seulement s'il contient au moins une
    flèche.
    Preuve : `Iff.rfl` — l'appartenance est *définie* par ce prédicat dans
    la construction de la topologie. -/
theorem atomic_covering {C : Type*} [Category C] (hro : GrothendieckTopology.RightOreCondition C)
    {X : C} (S : Sieve X) :
    S ∈ GrothendieckTopology.atomic hro X ↔ ∃ (Y : C) (f : Y ⟶ X), S f :=
  Iff.rfl

/-- Forme flèche de la topologie atomique : `(atomic hro).Covers S f` si et
    seulement si `S` contient une flèche au-dessus de `f` — la non-vacuité
    du crible se teste après pullback le long de `f`.
    Preuve : `covers_iff` réduit le membre gauche à `S.pullback f ∈
    atomic hro Y`, `atomic_covering` déplie l'appartenance en « le pullback
    est non vide », et la définition du pullback d'un crible
    (`S.pullback f g = S (g ≫ f)`, plus associativité) fait coïncider les
    deux membres. -/
theorem covers_iff_atomic {C : Type*} [Category C]
    (hro : GrothendieckTopology.RightOreCondition C) {X Y : C} (S : Sieve X) (f : Y ⟶ X) :
    (GrothendieckTopology.atomic hro).Covers S f ↔ ∃ (Z : C) (g : Z ⟶ Y), S (g ≫ f) := by
  rw [GrothendieckTopology.covers_iff, atomic_covering]
  simp

/-!
## Section 2 : flèches témoins et stabilité

Deux conséquences immédiates de la section 1 : une flèche *témoin*
appartenant à `S` suffit à couvrir toute flèche vers `X`, et la couverture
flèche est stable par précomposition (propriété `pullback_stable` de la
topologie, réécrite via `Sieve.pullback_comp`).
-/

/-- Toute flèche de `S` couvre toute flèche vers `X` pour la topologie
    atomique : `S f → (atomic hro).Covers S f`.
    Preuve : `S f` force `S.pullback f = ⊤` (`Sieve.pullback_eq_top_of_mem`),
    et le crible maximal appartient à toute topologie (`top_mem`). -/
theorem covers_atomic_of_mem {C : Type*} [Category C]
    (hro : GrothendieckTopology.RightOreCondition C) {X Y : C} (S : Sieve X)
    {f : Y ⟶ X} (h : S f) :
    (GrothendieckTopology.atomic hro).Covers S f := by
  rw [GrothendieckTopology.covers_iff, Sieve.pullback_eq_top_of_mem S h]
  exact GrothendieckTopology.top_mem (GrothendieckTopology.atomic hro) Y

/-- La forme flèche de `atomic` est stable par précomposition : si `S`
    couvre `f : Y ⟶ X`, alors `S` couvre aussi `g ≫ f` pour toute
    `g : Z ⟶ Y`.
    Preuve : `covers_iff` des deux côtés, puis `Sieve.pullback_comp`
    identifie `S.pullback (g ≫ f)` à `(S.pullback f).pullback g`, et
    `pullback_stable g h` de la topologie atomique conclut. -/
theorem covers_atomic_precomp {C : Type*} [Category C]
    (hro : GrothendieckTopology.RightOreCondition C) {X Y Z : C} (S : Sieve X)
    (f : Y ⟶ X) (g : Z ⟶ Y) :
    (GrothendieckTopology.atomic hro).Covers S f →
      (GrothendieckTopology.atomic hro).Covers S (g ≫ f) := by
  intro h
  rw [GrothendieckTopology.covers_iff] at h ⊢
  rw [Sieve.pullback_comp]
  exact (GrothendieckTopology.atomic hro).pullback_stable g h

/-!
## Section 3 : identité, crible maximal

`Sieve.pullback_id` rend le pullback le long de l'identité trivial :
la forme flèche au-dessus de `𝟙 X` retombe exactement sur l'appartenance
ponctuelle `S ∈ atomic hro X`. Le crible maximal, lui, couvre toute flèche
pour toute topologie — on l'établit pour `atomic` via `Sieve.pullback_top`.
-/

/-- La forme flèche de `atomic` au-dessus de l'identité coïncide avec
    l'appartenance ponctuelle : `(atomic hro).Covers S (𝟙 X) ↔ S ∈ atomic hro X`.
    Preuve : `covers_iff` puis `Sieve.pullback_id`. -/
theorem covers_atomic_id {C : Type*} [Category C]
    (hro : GrothendieckTopology.RightOreCondition C) {X : C} (S : Sieve X) :
    (GrothendieckTopology.atomic hro).Covers S (𝟙 X) ↔
      S ∈ GrothendieckTopology.atomic hro X := by
  rw [GrothendieckTopology.covers_iff, Sieve.pullback_id]

/-- Le crible maximal couvre toute flèche pour la topologie atomique :
    `(atomic hro).Covers ⊤ f`.
    Preuve : `covers_iff` puis `Sieve.pullback_top` (`⊤.pullback f = ⊤`),
    et `top_mem` conclut. -/
theorem covers_atomic_top {C : Type*} [Category C]
    (hro : GrothendieckTopology.RightOreCondition C) {X Y : C} (f : Y ⟶ X) :
    (GrothendieckTopology.atomic hro).Covers ⊤ f := by
  rw [GrothendieckTopology.covers_iff, Sieve.pullback_top]
  exact GrothendieckTopology.top_mem (GrothendieckTopology.atomic hro) Y

end Grothendieck.CoversAtomicArrow
