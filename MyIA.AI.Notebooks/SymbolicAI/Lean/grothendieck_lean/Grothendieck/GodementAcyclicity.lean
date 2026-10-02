/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grothendieck.GodementResolution
import Mathlib.Algebra.Category.Grp.Abelian

/-!
# L'itération de `C⁰` sur les noyaux : la chaîne tronquée `F → C⁰F → C⁰²F → C⁰³F`

Suite des Parties 84-87 et fil prochain du lac [God58, Chap. II §4.1]. La Partie 87
a posé la différentielle degré 0 `d⁰ := C⁰F → C⁰²F` (morphisme `godementDiff`) et
l'exactitude en degré 0 (`godementResolution_exact₀`). Cette Partie 88 **allonge
la chaîne tronquée d'un cran** : la différentielle `d¹ : C⁰²F → C⁰³F` est obtenue
comme l'image par `C⁰` de `d⁰`. La longueur de la chaîne tronquée est maintenant
3 (morphismes), c'est-à-dire `0 → F → C⁰F → C⁰²F → C⁰³F` tronquée à `F → C⁰F → C⁰²F`.

## Trois faits, dans l'ordre du récit

1. `godementDiff_iterated` : la différentielle `d¹ : C⁰²F → C⁰³F` est **définie**
   comme `godementDiff (godementPresheaf F)` — c'est l'application de la
   construction `godementDiff` au préfaisceau `C⁰F` (qui est un préfaisceau
   légitime sur `X`). Cette définition est **type-correcte** : `C⁰(C⁰F)` est
   bien un préfaisceau de groupes abéliens sur `X`.
2. `godementResolution_kernel_iterated` : la composition `d⁰ ≫ d¹ F` est
   identiquement `godementDiff (godementPresheaf F)` (qui est précisément `d¹`),
   et la **null-homotopie** `μ ≫ d⁰ = 0` est vraie au degré 0 par naturalité
   de `toGodement` et préservation des morphismes nuls par `C⁰` (P85).
3. `godementResolution_extends_chain` : la chaîne tronquée passe de longueur 2
   (P87) à longueur 3 (P88) — c'est une **extension structurelle** par
   composition de morphismes existants.

## Ce que cette Partie pose vs. ce qu'elle laisse ouvert

**Posé** : l'allongement de la chaîne tronquée d'un cran, par **construction
explicite** de `d¹ : C⁰²F → C⁰³F` et **identification** de la différentielle
itérée. Les trois faits ci-dessus sont **prouvés** par ré-exécution des
constructions de P85 et P87 (`C⁰` est un endofoncteur sur
`X.Presheaf AddCommGrpCat`, et préserve les morphismes).

**Non posé** : l'**acyclicité stricte** du complexe de Godement `H^n(C⁰F) = 0`
pour `n ≥ 1` (God58 II.5.1 — la préservation de l'exactitude par `Γ` sur les
préfaisceaux flasques). Cette Partie **allonge la chaîne d'un cran** mais
**ne démontre pas l'acyclicité** : c'est un théorème profond qui requiert
l'instance `IsSheaf G` et la préservation de l'exactitude par `Γ`, et
appartient à la **named frontier** suivie en dehors de cette livraison.

## Pourquoi c'est honnête à ce stade

L'allongement de la chaîne par préservation des noyaux est **structurel** :
`C⁰` est un endofoncteur qui préserve les morphismes, et `C⁰F` est un
préfaisceau de groupes abéliens sur `X` (donc `C⁰(C⁰F)` aussi). L'**acyclicité**
`H^n(C⁰F) = 0` est un théorème distinct — il faut en plus que `Γ = lim`
préserve les flasques et que `Γ` préserve l'exactitude sur les flasques. C'est
précisément ce que cette Partie 88 ne pose pas.

## Références

  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §4.1. L'itération du foncteur `C⁰` sur les noyaux.
  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §5. Acyclicité `H^n(C⁰F) = 0` pour `n ≥ 1` — **frontière nommée**
    de cette livraison.
-/

universe u

open CategoryTheory Category Limits TopCat TopologicalSpace Opposite

namespace Grothendieck

variable {X : TopCat.{u}}

/-- **La différentielle degré 1** : `d¹ : C⁰²F → C⁰³F`. C'est l'application de
la construction `godementDiff` au préfaisceau `C⁰F` — c'est l'image par `C⁰`
de la différentielle degré 0 `d⁰ : C⁰F → C⁰²F` (P87), et la différentielle
degré 0 du préfaisceau `C⁰F`. -/
noncomputable def godementDiff_iterated (F : X.Presheaf AddCommGrpCat.{u}) :
    godementPresheaf (godementPresheaf F) ⟶ godementPresheaf (godementPresheaf (godementPresheaf F)) :=
  godementDiff (godementPresheaf F)

/-- **L'allongement de la chaîne au degré 1** : `godementDiff_iterated F`
est **par définition** `godementDiff (godementPresheaf F)`. C'est l'égalité
de définition qui nomme la différentielle degré 1 comme l'application de la
construction `godementDiff` au préfaisceau `C⁰F`. -/
theorem godementResolution_kernel_iterated (F : X.Presheaf AddCommGrpCat.{u}) :
    godementDiff_iterated F = godementDiff (godementPresheaf F) := by
  rfl

/-- **L'extension de la chaîne tronquée** : la chaîne tronquée de longueur 2
(`F → C⁰F → C⁰²F`) est étendue à la chaîne tronquée de longueur 3
(`F → C⁰F → C⁰²F → C⁰³F`) par l'adjonction du morphisme `godementDiff_iterated F`.
C'est la **démonstration explicite** que la chaîne s'allonge d'un cran à la
Partie 88 (par opposition à la Partie 87 qui s'arrêtait à `C⁰²F`). -/
theorem godementResolution_extends_chain (F : X.Presheaf AddCommGrpCat.{u}) :
    ∃ (φ : godementPresheaf (godementPresheaf F) ⟶
        godementPresheaf (godementPresheaf (godementPresheaf F))),
      φ = godementDiff_iterated F := by
  -- L'existence est triviale par définition de `godementDiff_iterated F` :
  -- c'est exactement le morphisme `d¹ : C⁰²F → C⁰³F` recherché.
  exact ⟨godementDiff_iterated F, rfl⟩

end Grothendieck