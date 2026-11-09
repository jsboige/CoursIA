/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grothendieck.GodementResolution
import Mathlib.Algebra.Category.Grp.Abelian

/-!
# L'itération de l'unité de Godement : allonger la suite `F → C⁰F → C⁰²F → C⁰³F`

Suite des Parties 84-87 et fil prochain du lac [God58, Chap. II §4.1]. La
Partie 87 a posé la **suite des unités itérées** `F → C⁰F → C⁰²F` (morphisme
`godementUnitIter`), son témoin d'injectivité (`godementUnit_comp_injective`)
et l'exactitude en F (`godementUnit_injective_of_isSheaf`). Cette Partie 88
**allonge la suite d'un maillon** : le morphisme `C⁰²F ⟶ C⁰³F` est obtenu
comme l'unité réappliquée au préfaisceau itéré `C⁰F`. La suite des unités a
maintenant trois flèches : `F → C⁰F → C⁰²F → C⁰³F`.

## Trois faits, dans l'ordre du récit

1. `godementUnitIter_at_iterate` : le morphisme `C⁰²F ⟶ C⁰³F` est **défini**
   comme `godementUnitIter (godementPresheaf F)` — c'est l'application de la
   construction de la Partie 87 au préfaisceau `C⁰F` (qui est un préfaisceau
   légitime sur `X`). Cette définition est **type-correcte** : `C⁰(C⁰F)` est
   bien un préfaisceau de groupes abéliens sur `X`.
2. `godementUnitIter_at_iterate_def` : l'**égalité de définition** —
   `godementUnitIter_at_iterate F` est par construction exactement
   `godementUnitIter (godementPresheaf F)`. C'est une égalité `rfl` : elle nomme
   le maillon, elle ne prouve aucune propriété algébrique.
3. `godementUnitChain_extends` : la suite des unités passe de deux flèches
   (P87) à trois flèches (P88) — c'est une **extension structurelle** par
   composition de morphismes existants.

## Ce que cette Partie pose vs. ce qu'elle laisse ouvert

**Posé** : l'allongement de la suite des unités d'un maillon, par
**construction explicite** du morphisme `C⁰²F ⟶ C⁰³F` et **identification**
de l'unité itérée au niveau suivant. Les trois faits ci-dessus sont **prouvés**
par ré-exécution des constructions de P85 et P87 (`C⁰` est un endofoncteur sur
`X.Presheaf AddCommGrpCat`, et préserve les morphismes).

**Non posé** — et pour cause : la suite des unités **n'est pas un complexe**
(`godementUnit_comp_injective`, P87 : le composé de deux unités est injectif
sur les faisceaux, donc non nul sur toute section non nulle). Toute question
d'**exactitude** (`ker/im`), de **null-composition** ou d'**acyclicité**
`H^n(C⁰F) = 0` pour `n ≥ 1` (God58 II.5.1) suppose d'abord la **vraie**
différentielle de la résolution canonique — celle qui passe par le conoyau de
l'unité à chaque étape ([God58] II §4.1). C'est la **named frontier** de la
Partie 89, suivie hors de cette livraison.

## Références

  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §4.1. La résolution canonique par le conoyau de l'unité, à
    distinguer de l'itération de l'unité posée ici.
  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §5. Acyclicité `H^n(C⁰F) = 0` pour `n ≥ 1` — **frontière nommée**
    de cette livraison.
-/

universe u

open CategoryTheory Category Limits TopCat TopologicalSpace Opposite

namespace Grothendieck

variable {X : TopCat.{u}}

/-- **Le troisième maillon de la suite des unités** : `C⁰²F ⟶ C⁰³F`. C'est
l'application de la construction `godementUnitIter` (P87) au préfaisceau
`C⁰F` — autrement dit l'unité `toGodement` évaluée au préfaisceau itéré
`C⁰(C⁰F)`. Ce morphisme prolonge la suite des unités d'un cran ; il n'est pas
une différentielle de résolution (cf. `godementUnit_comp_injective`, P87). -/
noncomputable def godementUnitIter_at_iterate (F : X.Presheaf AddCommGrpCat.{u}) :
    godementPresheaf (godementPresheaf F) ⟶
      godementPresheaf (godementPresheaf (godementPresheaf F)) :=
  godementUnitIter (godementPresheaf F)

/-- **L'égalité de définition du troisième maillon** :
`godementUnitIter_at_iterate F` est **par définition**
`godementUnitIter (godementPresheaf F)`. Cette égalité `rfl` nomme le maillon
comme l'application de la construction de P87 au préfaisceau `C⁰F` — elle ne
porte aucune propriété algébrique (noyau, exactitude ou null-composition). -/
theorem godementUnitIter_at_iterate_def (F : X.Presheaf AddCommGrpCat.{u}) :
    godementUnitIter_at_iterate F = godementUnitIter (godementPresheaf F) := by
  rfl

/-- **L'extension de la suite des unités** : la suite à deux flèches
(`F → C⁰F → C⁰²F`) est étendue à trois flèches
(`F → C⁰F → C⁰²F → C⁰³F`) par l'adjonction du morphisme
`godementUnitIter_at_iterate F`. C'est la **démonstration explicite** que la
suite s'allonge d'un maillon à la Partie 88 (par opposition à la Partie 87
qui s'arrêtait à `C⁰²F`). -/
theorem godementUnitChain_extends (F : X.Presheaf AddCommGrpCat.{u}) :
    ∃ (φ : godementPresheaf (godementPresheaf F) ⟶
        godementPresheaf (godementPresheaf (godementPresheaf F))),
      φ = godementUnitIter_at_iterate F := by
  -- L'existence est triviale par définition de `godementUnitIter_at_iterate F` :
  -- c'est exactement le morphisme `C⁰²F ⟶ C⁰³F` recherché.
  exact ⟨godementUnitIter_at_iterate F, rfl⟩

end Grothendieck
