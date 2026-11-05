/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grothendieck.GodementFunctor
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Préservation des monomorphismes par `C⁰`

Suite de la Partie 85 [God58, Chap. II §4.1]. La Partie 85 a construit le foncteur
`C⁰` et son unité naturelle, et y a laissé **nommé** le prérequis manquant pour
itérer la construction sur les noyaux : « la préservation des monomorphismes par
`C⁰` n'est **pas** établie ici ». C'est l'objet de cette Partie, et rien d'autre.

Trois faits, dans l'ordre du récit :

1. `injective_app_of_mono` : un monomorphisme `φ : F ⟶ G` de préfaisceaux de
   groupes abéliens est **injectif sur chaque ouvert**. Dans `AddCommGrpCat`,
   monomorphisme et injection coïncident, et le mono d'une transformation
   naturelle se lit composante par composante : chaque `φ.app (op U)` est une
   application injective.
2. `godementHomApp_injective` : cette injectivité **descend aux tiges** et donne
   l'injectivité section par section de `C⁰φ`. Une section de Godement est une
   fonction sur `U` à valeurs dans les tiges ; deux sections qui coïncident après
   application de `C⁰φ` coïncident en chaque point, parce que l'application
   induite sur les tiges est injective
   (`Presheaf.stalkFunctor_map_injective_of_app_injective`).
3. `godementMapHom_mono` : `C⁰φ` est un monomorphisme — l'injectivité section par
   section est exactement le mono des morphismes de `AddCommGrpCat`, lu composante
   par composante.

Ce qui est acquis est ce qui est prouvé : `C⁰` est un endofoncteur qui **préserve
les monomorphismes**, et la forme consommable de ce fait est l'instance
`godementFunctor_preservesMonomorphisms` — `Functor.map_mono` s'applique désormais
à `C⁰`. C'est le prérequis qui manquait pour la résolution canonique de Godement
`0 → F → C⁰F → C⁰(K) → ⋯` (itérer `C⁰` sur les noyaux), fil prochain du lac.

## Références

  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §4.1. La résolution canonique de Godement.
-/

universe u

open CategoryTheory Category Limits TopCat TopologicalSpace Opposite

namespace Grothendieck

variable {X : TopCat.{u}}

/-- **Un mono est injectif sur chaque ouvert** : pour un morphisme `φ : F ⟶ G` de
préfaisceaux de groupes abéliens, `φ.app (op U)` est injectif dès que `φ` est un
monomorphisme. Les deux moitiés : `NatTrans.mono_iff_mono_app` lit le mono d'une
transformation naturelle composante par composante (les produits fibrés existent
dans `AddCommGrpCat`), et dans `AddCommGrpCat` monomorphisme et injection
coïncident. -/
theorem injective_app_of_mono {F G : X.Presheaf AddCommGrpCat.{u}} (φ : F ⟶ G)
    [Mono φ] (U : Opens X) : Function.Injective (φ.app (op U)) :=
  (AddCommGrpCat.mono_iff_injective _).mp inferInstance

/-- **L'injectivité descend aux tiges, donc à `C⁰`** : si `φ` est injectif sur
chaque ouvert, `C⁰φ` est injectif section par section. Une section de Godement est
une fonction, l'injectivité est donc ponctuelle : en chaque point, l'application
induite sur les tiges est injective — deux germes égaux proviennent de sections
égales (`Presheaf.stalkFunctor_map_injective_of_app_injective`, valable pour tout
préfaisceau de groupes abéliens) — et l'égalité des images point par point force
l'égalité des sections. -/
theorem godementHomApp_injective {F G : X.Presheaf AddCommGrpCat.{u}} (φ : F ⟶ G)
    (hφ : ∀ U : Opens X, Function.Injective (φ.app (op U))) (U : Opens X) :
    Function.Injective (godementHomApp φ U) := by
  intro s t hst
  funext x
  exact TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective hφ (x : X)
    (congrFun hst x)

/-- **`C⁰` préserve les monomorphismes** : si `φ` est un mono, `C⁰φ` en est un.
L'injectivité section par section établie ci-dessus est exactement le mono dans
`AddCommGrpCat` (`AddCommGrpCat.mono_iff_injective`), et le mono d'une
transformation naturelle se lit composante par composante
(`NatTrans.mono_iff_mono_app`). -/
theorem godementMapHom_mono {F G : X.Presheaf AddCommGrpCat.{u}} (φ : F ⟶ G) [Mono φ] :
    Mono (godementMapHom φ) := by
  rw [NatTrans.mono_iff_mono_app]
  intro U
  rw [AddCommGrpCat.mono_iff_injective]
  exact godementHomApp_injective φ (fun V => injective_app_of_mono φ V) U.unop

/-- **`C⁰` est un foncteur qui préserve les monomorphismes** — la forme utilisable
pour la suite : `Functor.map_mono` s'applique désormais à `C⁰`. C'est le prérequis
qui manquait à la Partie 85 pour itérer la construction sur les noyaux et former le
complexe de Godement. [God58] Chap. II §4.1. -/
instance godementFunctor_preservesMonomorphisms :
    (godementFunctor (X := X)).PreservesMonomorphisms where
  preserves f _ := godementMapHom_mono f

end Grothendieck