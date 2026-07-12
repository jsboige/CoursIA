/-

# Hommage Grothendieck — Partie 12 : La topologie dense

Copyright (c) 2026 CoursIA. All rights reserved.
Libéré sous licence Apache 2.0, voir fichier LICENSE à la racine du dépôt.

## La topologie dense (FR canonical)

Une topologie de Grothendieck J sur une catégorie C est dite **dense** (ou
« ¬∀-topologie », ou topologie de la double négation) lorsqu'un crible S sur X
est couvrant dès qu'à toute flèche f : Y ⟶ X admet un raffinement dans S : il
existe Z et g : Z ⟶ Y tels que S (g ≫ f). C'est la traduction catégorielle de la
double négation : « à terme éventuellement couvrante » le long de toute flèche
entrante.

Cette topologie fournit un exemple standard de topologie de Grothendieck ni
triviale ni discrète. Nous y enregistrons les identités fondamentales :

  - Le crible maximal est dense-couvrant en tout objet.
  - La topologie dense est comprise entre les topologies triviale et discrète.
  - La caractérisation d'appartenance explicite (`dense_covering`).
  - La stabilité par pullback : dense-couvrant est stable par changement de base.

Une subtilité de nommage à signaler : dans Mathlib, `C` est un paramètre
*explicite* de `GrothendieckTopology.trivial` et `.discrete` mais *implicite*
de `.dense` (les déclarations `variable` diffèrent dans la source Mathlib). On
écrit donc `trivial C` et `discrete C` mais `dense` nu (Lean infère `C`) ;
écrire `dense C` appliquerait plutôt la topologie à `C` comme objet via la
coercion `DFunLike`.

### Note d'accessibilité (Epics #1452/#1453)

Ce module expose **7 theorem** sur la **topologie dense** (treillis complet des
topologies de Grothendieck), accessibilité progressive par 4 sections
thématiques : (1) crible maximal dense-couvrant, (2) ordre trivial/dense/discret,
(3) caractérisation d'appartenance explicite, (4) stabilité par pullback.

### Convention i18n (EPIC #4980 ratifiée par user 2026-07-04)

Ce module substantiel est apparié avec son jumeau anglais dans le fichier sibling
`DenseTopology_en.lean` (modèle sibling pair, voir PR #6154 pour le pilote sur
`Utility.lean`).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck.DenseTopology

open CategoryTheory

/-!
## 1. Le crible maximal est dense-couvrant

Toute flèche f : Y ⟶ X est raffinée par elle-même via l'identité :
g := 𝟙 Y donne ⊤ (𝟙 Y ≫ f). Donc le crible maximal couvre pour la
topologie dense en tout objet — c'est l'axiome d'identité d'une topologie
de Grothendieck, spécialisé à la topologie dense.
-/


/-- Le crible maximal est dense-couvrant en tout objet.
    Déplie `dense_covering` et témoigne du raffinement via 𝟙. -/

theorem dense_top_mem {C : Type*} [Category C] (X : C) :
    (⊤ : Sieve X) ∈ GrothendieckTopology.dense X := by
  rw [GrothendieckTopology.dense_covering]
  intro Y _f
  exact ⟨Y, 𝟙 Y, trivial⟩

/-!
## 2. La topologie dense est comprise entre triviale et discrète

La topologie triviale (la plus grossière) est en-dessous de la topologie dense,
et la topologie dense est en-dessous de la topologie discrète (la plus fine).
Cela découle directement de la structure de treillis complet sur
`GrothendieckTopology C`.

Notez que `dense` porte `C` implicitement (contrairement à `trivial`/`discrete`),
d'où on l'écrit sans argument explicite ici — Lean l'infère du type attendu.
-/


/-- La topologie triviale est en-dessous de la topologie dense. -/

theorem trivial_le_dense {C : Type*} [Category C] :
    (GrothendieckTopology.trivial C : GrothendieckTopology C) ≤
      GrothendieckTopology.dense := by
  rw [GrothendieckTopology.trivial_eq_bot]
  exact bot_le

/-- La topologie dense est en-dessous de la topologie discrète. -/

theorem dense_le_discrete {C : Type*} [Category C] :
    (GrothendieckTopology.dense : GrothendieckTopology C) ≤
      GrothendieckTopology.discrete C := by
  rw [GrothendieckTopology.discrete_eq_top]
  exact le_top

/-- Toute topologie dense est comprise entre triviale et discrète :
    ⊥ ≤ dense ≤ ⊤. -/

theorem trivial_le_dense_le_discrete {C : Type*} [Category C] :
    (GrothendieckTopology.trivial C : GrothendieckTopology C) ≤
      GrothendieckTopology.dense ∧
    (GrothendieckTopology.dense : GrothendieckTopology C) ≤
      GrothendieckTopology.discrete C :=
  ⟨trivial_le_dense, dense_le_discrete⟩

/-!
## 3. Caractérisation d'appartenance explicite

Un crible S est dense-couvrant si et seulement si toute flèche entrante admet
un raffinement dans S. C'est l'équivalence définitionnelle `dense_covering`,
reconditionnée en directions aller et retour pour la lisibilité.
-/


/-- Si toute flèche entrante f : Y ⟶ X admet un raffinement dans S, alors S
    est dense-couvrant. La direction aller est définitionnelle (`Iff.rfl`). -/

theorem mem_dense_of_refines {C : Type*} [Category C] {X : C} {S : Sieve X}
    (h : ∀ {Y : C} (f : Y ⟶ X), ∃ (Z : _) (g : Z ⟶ Y), S.arrows (g ≫ f)) :
    S ∈ GrothendieckTopology.dense X := by
  rw [GrothendieckTopology.dense_covering]
  exact h

/-- Un crible dense-couvrant raffine toute flèche entrante f : Y ⟶ X.
    Direction retour de `dense_covering`, mise en lemme exploitable. -/

theorem dense_refines_of_mem {C : Type*} [Category C] {X : C} {S : Sieve X}
    (hS : S ∈ GrothendieckTopology.dense X) {Y : C} (f : Y ⟶ X) :
    ∃ (Z : _) (g : Z ⟶ Y), S.arrows (g ≫ f) :=
  GrothendieckTopology.dense_covering.mp hS f

/-!
## 4. Stabilité par pullback

La propriété dense-couvrant est stable par pullback : si S est dense-couvrant
sur X et f : Y ⟶ X, alors `Sieve.pullback f S` est dense-couvrant sur Y.
C'est l'axiome de stabilité d'une topologie de Grothendieck, spécialisé à
`dense`.
-/


/-- Le pullback d'un crible dense-couvrant est dense-couvrant.
    C'est `GrothendieckTopology.pullback_stable` appliqué à la topologie dense.
    Notez que `dense` s'écrit sans argument explicite `C`. -/

theorem dense_pullback_stable {C : Type*} [Category C] {X Y : C}
    {S : Sieve X} (hS : S ∈ GrothendieckTopology.dense X) (f : Y ⟶ X) :
    Sieve.pullback f S ∈ GrothendieckTopology.dense Y :=
  GrothendieckTopology.dense.pullback_stable f hS

end Grothendieck.DenseTopology
