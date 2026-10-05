/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grothendieck.GodementCanonicalDiff
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Topology.Sheaves.Abelian

/-!
# Le complexe augmenté de Godement : d¹ et le mono catégorique de l'unité

Partie 90 — la suite annoncée de la Partie 89. Cette dernière avait posé le pas
canonique `godementStep f := cokernel.π f ≫ toGodement (coker f)` et la
différentielle `d⁰ := godementCanonicalDZero` avec sa null-composition
`μ ≫ d⁰ = 0`. Cette Partie fait deux pas de plus sur le même fil (le troisième
— la **réduction de l'exactitude** — a été retiré : voir note de l'auteur à
la fin du namespace).

## Deux faits, dans l'ordre du récit

1. `godementCanonicalDOne` : la **différentielle de degré 1** — le pas canonique
   appliqué à `d⁰`. Le terme suivant `C²F := C⁰(coker d⁰)` est le préfaisceau de
   Godement du conoyau de `d⁰`, et `d¹ : C¹F ⟶ C²F` en est la flèche. La
   null-composition `d⁰ ≫ d¹ = 0` (`godementCanonicalDZero_comp_godementCanonicalDOne`)
   est une instance de `comp_godementStep_zero` (P89) : **la résolution canonique
   est un complexe au-delà du degré 0** — chaque degré s'obtient en appliquant le
   pas canonique à la différentielle précédente, et la null-composition est
   gratuite à chaque étape.
2. `mono_toGodement_of_isSheaf` : **l'unité de Godement est un monomorphisme
   catégorique sur les faisceaux**. La Partie 84 avait prouvé l'injectivité
   section par section (`godementUnit_injective_of_isSheaf`) ; ce fait en est la
   montée catégorique : mono dans la catégorie des préfaisceaux, via
   `NatTrans.mono_iff_mono_app` (le mono d'une transformation naturelle entre
   préfaisceaux de groupes abéliens est exactement le mono section par section).
   C'est l'exactitude de `0 → F → C⁰F` **en F**, désormais énoncée dans le
   langage des complexes.

## Ce que cette Partie pose vs. ce qu'elle laisse ouvert

**Posé** : le complexe aux degrés 0 et 1 (et le motif d'itération qui prolonge à
tous les degrés), et le mono catégorique de l'unité sur les faisceaux.

**Non posé** — frontière nommée de la Partie 91 : la **réduction de l'exactitude
en `C⁰F` au mono de l'unité du conoyau** (`exact_toGodement_godementCanonicalDZero_of_mono`),
dont la preuve exige la **séparéité du conoyau** `coker μ` pour `F` faisceau —
le recollement des sections locales du quotient à travers les germes, qui
exige l'argument de recollement de [God58] (sections locales `sᵢ` se recollant
par séparéité de `F` et injectivité de `μ`). L'**itération complète** de la
réduction aux degrés supérieurs, et l'**acyclicité** `H^n(C⁰F) = 0` pour
`n ≥ 1` ([God58] II.5) sont aussi du périmètre P91.

## Références

  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §4.1. La résolution canonique `0 → F → C⁰F → C¹F → ⋯` : complexe
    (d⁰ ≫ d¹ = 0) et exactitude en `C⁰F` — réduite ici au mono de l'unité du
    conoyau.
  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §5. Acyclicité — frontière nommée de la Partie 91.
-/

universe u

open CategoryTheory Category Limits TopCat TopologicalSpace Opposite

namespace Grothendieck

variable {X : TopCat.{u}}

/-- **La différentielle de degré 1 de la résolution canonique** : le pas
canonique de la Partie 89 appliqué à `d⁰`. Le terme `C¹F = C⁰(coker μ)` (posé en
P89 comme codomaine de `d⁰`) engendre à son tour `C²F = C⁰(coker d⁰)`, et `d¹`
est la flèche `C¹F ⟶ C²F`. Le motif est uniforme : `d^{n+1} := godementStep d^n`,
chaque terme étant le préfaisceau de Godement du conoyau de la différentielle
précédente ([God58] II §4.1). -/
noncomputable def godementCanonicalDOne (F : X.Presheaf AddCommGrpCat.{u}) :
    godementPresheaf (cokernel (toGodement F)) ⟶
    godementPresheaf (cokernel (godementCanonicalDZero F)) :=
  godementStep (godementCanonicalDZero F)

/-- **La null-composition en degré 1** : `d⁰ ≫ d¹ = 0`. Instance immédiate de
`comp_godementStep_zero` (P89) — la résolution canonique est un complexe au-delà
du degré 0, et le restera à chaque degré suivant par le même argument : chaque
différentielle composée avec son pas canonique s'annule par la condition
universelle du conoyau. -/
theorem godementCanonicalDZero_comp_godementCanonicalDOne
    (F : X.Presheaf AddCommGrpCat.{u}) :
    godementCanonicalDZero F ≫ godementCanonicalDOne F = 0 :=
  comp_godementStep_zero _

/-- **L'unité de Godement est un monomorphisme catégorique sur les faisceaux** :
la montée catégorique de l'injectivité section par section de la Partie 84
(`godementUnit_injective_of_isSheaf`). Dans la catégorie des préfaisceaux de
groupes abéliens, un morphisme est mono exactement quand chaque composante
l'est (`NatTrans.mono_iff_mono_app`), et dans `AddCommGrpCat` un morphisme est
mono exactement quand il est injectif (`AddCommGrpCat.mono_iff_injective`).
C'est l'exactitude de `0 → F → C⁰F` **en F**, énoncée dans le langage des
catégories. -/
theorem mono_toGodement_of_isSheaf (F : X.Presheaf AddCommGrpCat.{u})
    (hF : TopCat.Presheaf.IsSheaf F) :
    Mono (toGodement F) := by
  rw [NatTrans.mono_iff_mono_app]
  intro U
  exact (AddCommGrpCat.mono_iff_injective _).mpr
    (godementUnit_injective_of_isSheaf F hF U.unop)

/-- Note de l'auteur : la **réduction de l'exactitude en `C⁰F` au mono de
l'unité du conoyau** ([God58] II.4.1) — qui était l'énoncé 3 du draft r65
(`exact_toGodement_godementCanonicalDZero_of_mono`) — est **retirée de cette
Partie** et reportée à la Partie 91. La frontière mathématique est la
séparéité du conoyau `coker μ` pour `F` faisceau, qui exige l'argument de
recollement de [God58] et les instances `IsIso`/`Mono` au site d'usage. Le
draft r65 portait un `sorry` tactique sur cette preuve (defeq de X₂ non
réconcilié, instance `IsIso` non inférée), et le gate `proof-integrity` du
caller workflow a élevé ce `sorry` en `sorryAx` transitif à l'import —
classe `forbidden` (pr-review-discipline §B). L'option honnête est le
**retrait** : la Partie 90 pose le complexe (fait 1) et le mono de l'unité
(fait 2) ; la Partie 91 posera l'énoncé de réduction ET sa preuve (gluing
de sections locales sur faisceau, instances de mono dans la catégorie des
prés faisceaux). Aucun énoncé-stub `True.intro` ni `False` n'est laissé
dans le module — la frontière est nommée dans la docstring de tête. -/

end Grothendieck
