/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grothendieck.GodementResolution
import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Le pas canonique de Godement : la différentielle par conoyau de l'unité

Partie 89 — la frontière nommée par les Parties 87 et 88. Ces parties avaient
posé la **suite des unités itérées** `F → C⁰F → C⁰²F → ⋯` et prouvé qu'elle
n'est **pas un complexe** (`godementUnit_comp_injective`, P87 : sur un faisceau,
le composé de deux unités est injectif, donc non nul sur toute section non
nulle). La construction canonique de [God58, Chap. II §4.1] passe à chaque
étape par le **conoyau de la flèche précédente** : c'est ce pas que ce module
pose.

## Le pas canonique, en général puis en degré 0

1. `godementStep` : pour tout morphisme de préfaisceaux `f : A ⟶ B`, le **pas
   canonique** est la composée `B ⟶ C⁰(coker f)` donnée par la projection du
   conoyau suivie de l'unité de Godement du conoyau :
   `cokernel.π f ≫ toGodement (coker f)`. C'est un motif uniforme : appliqué à
   chaque flèche de la résolution, il engendre la flèche suivante.
2. `comp_godementStep_zero` : **la null-composition du pas canonique** —
   `f ≫ godementStep f = 0`, par la condition universelle du conoyau
   (`cokernel.condition`) et l'annulation du zéro composé. La preuve fait
   deux réécritures : associer, appliquer la condition du conoyau.
3. `godementCanonicalDZero` : la **différentielle de degré 0** de la résolution
   canonique, obtenue en appliquant le pas canonique à l'unité
   `d⁰ := godementStep (toGodement F) : C⁰F ⟶ C⁰(coker μ)`.
4. `toGodement_comp_godementCanonicalDZero` : **le début du complexe augmenté
   est un complexe** — `μ ≫ d⁰ = 0`, instance immédiate du fait 2.

## Ce que cette Partie pose vs. ce qu'elle laisse ouvert

**Posé** : le motif du pas canonique (conoyau + unité), la différentielle
`d⁰`, et la null-composition `μ ≫ d⁰ = 0` — le contraste exact avec la Partie
87 : pour l'itération de l'unité, cette égalité était **fausse** (témoin
injectif) ; pour le pas canonique, elle est **vraie et prouvée**.

**Non posé** — frontière nommée de la Partie 90 : l'**exactitude** en `C⁰F`
(`ker d⁰ = im μ`, [God58] II.4.1), l'**itération** du pas (`d¹`, `d²`, … et
la structure de complexe à tous les degrés), et l'**acyclicité**
`H^n(C⁰F) = 0` pour `n ≥ 1` ([God58] II.5). Chacun de ces faits exige des
ingrédients (flasquité de `C⁰F` déjà posée P84, mono de l'unité sur les
faisceaux P84, stabilité du conoyau) qui restent à assembler.

## Références

  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §4.1. La résolution canonique `0 → F → C⁰F → C¹F → ⋯` : chaque pas
    passe par le conoyau de la flèche précédente — motif posé ici.
  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §5. Acyclicité `H^n(C⁰F) = 0` pour `n ≥ 1` — frontière nommée de
    la Partie 90.
-/

universe u

open CategoryTheory Category Limits TopCat TopologicalSpace Opposite

namespace Grothendieck

variable {X : TopCat.{u}}

/-- **Le pas canonique de Godement** : pour tout morphisme de préfaisceaux
`f : A ⟶ B`, la flèche `B ⟶ C⁰(coker f)` donnée par la projection du conoyau
suivie de l'unité de Godement du conoyau. C'est le motif uniforme de la
résolution canonique ([God58] II §4.1) : appliqué à la flèche `F ⟶ C⁰F`, il
produit `d⁰` ; appliqué à `d⁰`, il produira `d¹` — chaque terme suivant est le
terme de Godement du conoyau de la flèche précédente. -/
noncomputable def godementStep {A B : X.Presheaf AddCommGrpCat.{u}} (f : A ⟶ B) :
    B ⟶ godementPresheaf (cokernel f) :=
  cokernel.π f ≫ toGodement (F := cokernel f)

/-- **La null-composition du pas canonique** : pour tout `f : A ⟶ B`,
`f ≫ godementStep f = 0`. C'est la condition universelle du conoyau —
`f ≫ cokernel.π f = 0` (`cokernel.condition`) — suivie de l'annulation du
morphisme nul composé. Ce fait est le **complexe en germe** de la résolution
canonique : chaque flèche composée avec son pas canonique s'annule, là où la
suite des unités itérées (P87) échouait à le faire. -/
theorem comp_godementStep_zero {A B : X.Presheaf AddCommGrpCat.{u}} (f : A ⟶ B) :
    f ≫ godementStep f = 0 := by
  rw [godementStep, ← Category.assoc, cokernel.condition, zero_comp]

/-- **La différentielle de degré 0 de la résolution canonique** : le pas
canonique appliqué à l'unité de Godement. Le terme suivant de la résolution
augmentée `0 → F → C⁰F → C¹F` est `C⁰(coker μ)` — le faisceau de Godement du
conoyau de l'unité — et `d⁰ : C⁰F ⟶ C¹F` en est la flèche. Ce morphisme
remplace l'itération de l'unité (`godementUnitIter`, P87), qui n'est pas une
différentielle. -/
noncomputable def godementCanonicalDZero (F : X.Presheaf AddCommGrpCat.{u}) :
    godementPresheaf F ⟶ godementPresheaf (cokernel (toGodement F)) :=
  godementStep (toGodement F)

/-- **Le début du complexe augmenté est un complexe** : l'unité composée avec
la différentielle de degré 0 s'annule, `μ ≫ d⁰ = 0`. C'est l'instance en
degré 0 de `comp_godementStep_zero`, et le **contraire** du témoin de la
Partie 87 : là où le composé de deux unités était injectif (donc non nul),
le composé de l'unité avec le pas canonique est nul — la résolution canonique
commence bien comme un complexe. -/
theorem toGodement_comp_godementCanonicalDZero
    (F : X.Presheaf AddCommGrpCat.{u}) :
    toGodement F ≫ godementCanonicalDZero F = 0 :=
  comp_godementStep_zero (toGodement F)

end Grothendieck
