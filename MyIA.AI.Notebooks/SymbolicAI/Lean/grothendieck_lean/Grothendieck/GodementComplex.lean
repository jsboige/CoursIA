/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grothendieck.GodementExactness
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Le complexe de Godement : l'itération du pas canonique à tous les degrés

Partie 92 — la frontière nommée par les Parties 90 et 91. La Partie 89 a posé
le **pas canonique** `godementStep f = cokernel.π f ≫ toGodement (coker f)` et
sa null-composition `f ≫ godementStep f = 0` ; les Parties 89-90 en ont tiré
les différentielles `d⁰` et `d¹` avec `d⁰ ≫ d¹ = 0` ; la Partie 91 a établi
l'exactitude du début (`exact_toGodement_godementCanonicalDZero`). Ce module
itére le pas **à tous les degrés** et assemble le résultat en un objet
`CochainComplex` [God58, Chap. II §4.1].

## La chaîne des différentielles

1. `godementDChain F` : la chaîne des différentielles comme suite de flèches
   (`Arrow`), par récursion sur le degré — le degré `n + 1` est le pas
   canonique de la flèche de degré `n` : `d^{n+1} := godementStep dⁿ`. C'est
   l'itération exacte de la construction de [God58], chaque flèche passant par
   le conoyau de la précédente — le contraste avec la Partie 87 : la suite des
   unités itérées n'est **pas** un complexe, celle des pas canoniques l'est.
2. `godementCanonicalObj F n` et `godementCanonicalD F n` : le terme de degré
   `n` et la différentielle `X n ⟶ X (n+1)` extraits de la chaîne, avec les
   lemmes `rfl` de recalage sur les notations des Parties 89-90
   (`godementCanonicalD_zero`, `godementCanonicalD_one`, `godementCanonicalD_succ`).
3. `godementCanonicalD_comp_zero` : **la null-composition à tout degré** —
   `dⁿ ≫ d^{n+1} = 0` pour tout `n`, instance immédiate de
   `comp_godementStep_zero` (Partie 89) appliquée au degré `n`.
4. `godementCanonicalComplex F` : l'assemblage en `CochainComplex` indexé par
   `ℕ`, via le constructeur canonique `CochainComplex.of` de Mathlib, avec les
   lemmes d'interface `godementCanonicalComplex_X_zero`,
   `godementCanonicalComplex_d_zero`, `godementCanonicalComplex_d_one`.
5. `toGodement_comp_godementCanonicalD` : le début du complexe augmenté —
   `μ ≫ d⁰ = 0`, réénoncé de la Partie 89 dans les notations itérées.

## Ce que cette Partie pose vs. ce qu'elle laisse ouvert

**Posé** : la récursion `d^{n+1} = godementStep dⁿ` à tous les degrés, la
null-composition `dⁿ ≫ d^{n+1} = 0` pour tout `n`, et l'objet
`godementCanonicalComplex : CochainComplex … ℕ` — la résolution canonique de
Godement existe maintenant **comme objet complexe**, pas seulement comme suite
de flèches épinglées degré par degré.

**Non posé** — frontière nommée de la Partie 93 : l'**acyclicité**
`Hⁿ(C⁰) = 0` pour `n ≥ 1` ([God58] II Th. 5.2.1). Elle exigera l'exactitude en
chaque degré — c'est-à-dire l'itération de `exact_toGodement_godementCanonicalDZero`
(P91, non encore mergée) le long de la chaîne — puis le passage à l'homologie.
Le complexe augmenté `F ⟶ C⁰F ⟶ C⁰(coker μ) ⟶ ⋯` comme **résolution** de `F`
(la quasi-isomorphisme) suit l'acyclicité et n'est pas abordé ici.

## Références

* [God58] R. Godement, *Topologie algébrique et théorie des faisceaux*,
  Hermann, 1958, chap. II §4.1.
-/

universe u

open CategoryTheory Category Limits TopCat TopologicalSpace Opposite

namespace Grothendieck

variable {X : TopCat.{u}}

/-- La chaîne des différentielles de la résolution canonique, comme suite de
flèches : le degré 0 est la différentielle `d⁰` de la Partie 89, et chaque
degré suivant est le **pas canonique** (Partie 89) de la flèche précédente —
`d^{n+1} = godementStep dⁿ`, chaque flèche passant par le conoyau de la
précédente. -/
noncomputable def godementDChain (F : X.Presheaf AddCommGrpCat.{u}) :
    ℕ → Arrow (X.Presheaf AddCommGrpCat.{u})
  | 0 => Arrow.mk (godementCanonicalDZero F)
  | n + 1 => Arrow.mk (godementStep (godementDChain F n).hom)

/-- Le terme de degré `n` de la résolution canonique : le but de la flèche de
degré `n - 1`, c'est-à-dire `C⁰` du conoyau de la différentielle précédente. -/
noncomputable def godementCanonicalObj (F : X.Presheaf AddCommGrpCat.{u}) (n : ℕ) :
    X.Presheaf AddCommGrpCat.{u} :=
  (godementDChain F n).left

/-- La différentielle de degré `n` de la résolution canonique, du terme `n` au
terme `n + 1` — par construction le pas canonique de la différentielle de
degré `n - 1`. -/
noncomputable def godementCanonicalD (F : X.Presheaf AddCommGrpCat.{u}) (n : ℕ) :
    godementCanonicalObj F n ⟶ godementCanonicalObj F (n + 1) :=
  (godementDChain F n).hom

@[simp]
theorem godementCanonicalObj_zero (F : X.Presheaf AddCommGrpCat.{u}) :
    godementCanonicalObj F 0 = godementPresheaf F :=
  rfl

theorem godementCanonicalObj_succ (F : X.Presheaf AddCommGrpCat.{u}) (n : ℕ) :
    godementCanonicalObj F (n + 2) =
      godementPresheaf (cokernel (godementCanonicalD F n)) :=
  rfl

@[simp]
theorem godementCanonicalD_zero (F : X.Presheaf AddCommGrpCat.{u}) :
    godementCanonicalD F 0 = godementCanonicalDZero F :=
  rfl

@[simp]
theorem godementCanonicalD_one (F : X.Presheaf AddCommGrpCat.{u}) :
    godementCanonicalD F 1 = godementCanonicalDOne F :=
  rfl

@[simp]
theorem godementCanonicalD_succ (F : X.Presheaf AddCommGrpCat.{u}) (n : ℕ) :
    godementCanonicalD F (n + 1) = godementStep (godementCanonicalD F n) :=
  rfl

/-- **La null-composition à tout degré** : chaque différentielle composée avec
la suivante est nulle, par la null-composition du pas canonique (Partie 89)
appliquée à la différentielle de degré `n`. C'est ce qui fait de la suite des
pas canoniques un complexe — là où la suite des unités itérées de la Partie 87
échouait (témoin injectif). -/
theorem godementCanonicalD_comp_zero (F : X.Presheaf AddCommGrpCat.{u}) (n : ℕ) :
    godementCanonicalD F n ≫ godementCanonicalD F (n + 1) = 0 :=
  comp_godementStep_zero _

/-- Le début du complexe augmenté est un complexe : l'unité de Godement
composée avec la différentielle de degré 0 est nulle (réénoncé itératif de la
Partie 89). -/
theorem toGodement_comp_godementCanonicalD (F : X.Presheaf AddCommGrpCat.{u}) :
    toGodement F ≫ godementCanonicalD F 0 = 0 :=
  toGodement_comp_godementCanonicalDZero F

/-- **Le complexe de Godement canonique** : la résolution canonique assemblée
en objet `CochainComplex` indexé par `ℕ` — termes `C⁰` des conoyaux
successifs, différentielles données par la récursion
`d^{n+1} = godementStep dⁿ`, null-composition à tout degré. -/
noncomputable def godementCanonicalComplex (F : X.Presheaf AddCommGrpCat.{u}) :
    CochainComplex (X.Presheaf AddCommGrpCat.{u}) ℕ :=
  CochainComplex.of (godementCanonicalObj F) (godementCanonicalD F)
    (godementCanonicalD_comp_zero F)

theorem godementCanonicalComplex_X (F : X.Presheaf AddCommGrpCat.{u}) :
    (godementCanonicalComplex F).X = godementCanonicalObj F :=
  rfl

theorem godementCanonicalComplex_X_zero (F : X.Presheaf AddCommGrpCat.{u}) :
    (godementCanonicalComplex F).X 0 = godementPresheaf F :=
  rfl

@[simp]
theorem godementCanonicalComplex_d (F : X.Presheaf AddCommGrpCat.{u}) (n : ℕ) :
    (godementCanonicalComplex F).d n (n + 1) = godementCanonicalD F n :=
  CochainComplex.of_d _ _ _

theorem godementCanonicalComplex_d_zero (F : X.Presheaf AddCommGrpCat.{u}) :
    (godementCanonicalComplex F).d 0 1 = godementCanonicalDZero F := by
  rw [godementCanonicalComplex_d, godementCanonicalD_zero]

theorem godementCanonicalComplex_d_one (F : X.Presheaf AddCommGrpCat.{u}) :
    (godementCanonicalComplex F).d 1 2 = godementCanonicalDOne F := by
  rw [godementCanonicalComplex_d, godementCanonicalD_one]

end Grothendieck
