/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grothendieck.GodementComplex
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Partie 95, brique 1 : la cohomologie de Godement — définition et recalages

La voie P95 arrêtée par la Partie 94 (cf README, rang 94) : le corollaire
faisceau direct reste derrière la faisceification abélienne (absente de
Mathlib au pin du lake) ; la **résolution flasque** est la route retenue —
et elle commence par *nommer* ce que la résolution calcule. Ce module pose
la **cohomologie de Godement** de `F` sur `U` : l'homologie du complexe des
sections sur `U` du complexe canonique ([God58, Chap. II §5.1] — c'est la
définition historique, antérieure à toute présentation par Ext).

## Contenu

1. `sectionsFunctorAdditive` : le foncteur « sections sur `U` »
   `F ↦ F.obj (op U)`, muni de son instance `Additive` (champ unique
   `map_add`, par `rfl` — l'addition des transformations naturelles est
   composante par composante ; `PreservesZeroMorphisms` en découle par le
   pont Mathlib `preservesZeroMorphisms_of_additive`). Écrit à la main
   plutôt que via un évaluateur générique — aucune dépendance à un nom
   d'instance Mathlib incertain au pin.
2. `godementSectionsComplex` : le complexe des sections — l'image du
   complexe canonique (Partie 92) par le foncteur sections, via
   `Functor.mapHomologicalComplex`. Chaque étage est le groupe des sections
   `CⁿF(U)`, chaque différentielle l'action champ par champ de `dⁿ`.
3. `godementCohomologyObj` : **la cohomologie de Godement** `Hⁿ_God(U, F)` —
   l'homologie de ce complexe en degré `n`.
4. `godementSectionsComplex_X` : le recalage définitionnel de l'étage —
   `(Γ(U, C^●F)).X n = godementCanonicalObj F n (op U)` par `rfl`, pont
   vers les notations des Parties 89-92.

## Ce que cette brique pose vs. ce qu'elle laisse ouvert

**Posé** : la définition complète `Hⁿ_God(U, F) = Hⁿ(Γ(U, C^●F))`, les
recalages d'étages, et le foncteur sections additif (brique réutilisable —
le capstone « flasque ⇒ Γ-acyclique » (Partie 94 fusionnée #21072)
s'y raccordera après retarget de la pile sur main).

**Non posé** — frontières nommées :
- la **fonctorialité en `F`** : elle exige d'abord la fonctorialité du
  *complexe canonique* lui-même (`F ↦ C^●F` sur les morphismes), que la
  Partie 92 n'a pas posée — grain distinct `godementCanonicalComplex_map` ;
- `H⁰_God(U, F) ≅ F(U)` pour `F` faisceau (brique 2 du plan P95 — mur de
  faisheification identifié, à instruire à froid) ;
- la suite exacte longue (brique 3 : cone ou dimension-shift).

## Références

* [God58] R. Godement, *Topologie algébrique et théorie des faisceaux*,
  Hermann 1958, Chap. II §5.1 (définition), Th. 5.2.1 (acyclicité).
-/
universe u

namespace Grothendieck.SheafCohomology

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

variable {X : TopCat.{u}}

/-- Le foncteur « sections sur `U` » : `F ↦ F(U)`, action champ par champ.
Écrit à la main (aucune dépendance à un évaluateur générique du pin). -/
@[simps]
def sectionsFunctorAdditive (U : Opens X) :
    X.Presheaf AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} where
  obj F := F.obj (Opposite.op U)
  map f := f.app (Opposite.op U)

instance (U : Opens X) : (sectionsFunctorAdditive (X := X) U).Additive where
  map_add := rfl

/-- **Le complexe des sections du complexe canonique** : l'image de
`godementCanonicalComplex F` (Partie 92) par le foncteur sections. -/
noncomputable def godementSectionsComplex (U : Opens X)
    (F : X.Presheaf AddCommGrpCat.{u}) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  ((sectionsFunctorAdditive (X := X) U).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (godementCanonicalComplex F)

/-- **Partie 95 — la cohomologie de Godement** : `Hⁿ_God(U, F)` est
l'homologie en degré `n` du complexe des sections du complexe canonique
([God58] II §5.1). C'est la définition historique — la voie P95 la
consomme ; le théorème de comparaison avec le `Hⁿ` par Ext du module
`SheafCohomology.Basic` est une frontière au-delà. -/
noncomputable def godementCohomologyObj (U : Opens X)
    (F : X.Presheaf AddCommGrpCat.{u}) (n : ℕ) :
    AddCommGrpCat.{u} :=
  (godementSectionsComplex (X := X) U F).homology n

/-- Recalage définitionnel de l'étage de degré `n` du complexe des
sections : c'est le groupe `CⁿF(U)` — pont vers les notations des
Parties 89-92. -/
theorem godementSectionsComplex_X (U : Opens X)
    (F : X.Presheaf AddCommGrpCat.{u}) (n : ℕ) :
    (godementSectionsComplex (X := X) U F).X n =
      (godementCanonicalObj F n).obj (Opposite.op U) := rfl

end Grothendieck.SheafCohomology
