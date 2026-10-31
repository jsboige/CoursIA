/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grothendieck.GodementComplex
import Grothendieck.GodementExactness
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
5. `godementSectionsComplex_d_zero` : le recalage de la différentielle de
   degré 0 — `(Γ(U, C^●F)).d 0 1 = d⁰(U)`, composante en `U` du pas canonique.
6. `exact_app_toGodement_godementCanonicalDZero` : **l'exactitude du pas B
   (Partie 91) évaluée en `U`** — la suite de sections `F(U) → C⁰F(U) → C¹F(U)`
   est exacte. L'évaluation en un ouvert est un foncteur exact (limites et
   colimites des préfaisceaux sont ponctuelles : `evaluationPreservesLimits`,
   `evaluation_preservesColimits`), donc transporte l'exactitude par
   `Functor.exact_tfae` — aucun recours aux tiges ni à AB5.
7. `godementZerothCohomologyIso` : **la brique 2 — `H⁰_God(U, F) ≅ F(U)`
   pour `F` faisceau** ([God58] II §5.1). Assemblage sans faisheification :
   `H⁰ = ker d⁰` (rien en degré −1), puis `ker d⁰(U) ≅ F(U)` parce que le
   relèvement au noyau `F(U) ⟶ ker d⁰(U)` est epi (exactitude évaluée,
   `Exact.epi_kernelLift`) et mono (l'unité de Godement est mono, Partie 90,
   évaluée en `U`) — donc un iso (`isIso_iff_epi_and_mono`, `AddCommGrpCat`
   est balancée).

## Ce que cette brique pose vs. ce qu'elle laisse ouvert

**Posé** : la définition complète `Hⁿ_God(U, F) = Hⁿ(Γ(U, C^●F))`, les
recalages d'étages et de `d⁰`, le foncteur sections additif (brique
réutilisable — le capstone « flasque ⇒ Γ-acyclique » (Partie 94 fusionnée
#21072) s'y raccordera après retarget de la pile sur main), et **la brique
2** : `H⁰_God(U, F) ≅ F(U)` pour `F` faisceau — le mur de faisheification
identifié au plan P95 n'est pas requis ici : le mono de l'unité (Partie 90)
et l'exactitude du pas B (Partie 91), évalués en `U`, suffisent. La
faisheification reste requise par la brique 3 seule.

**Non posé** — frontières nommées :
- la **fonctorialité en `F`** : elle exige d'abord la fonctorialité du
  *complexe canonique* lui-même (`F ↦ C^●F` sur les morphismes), que la
  Partie 92 n'a pas posée — grain distinct `godementCanonicalComplex_map` ;
- la suite exacte longue (brique 3 : cone ou dimension-shift — c'est elle
  qui exigera la faisheification abélienne).

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

/-! ## La brique 2 : `H⁰_God(U, F) ≅ F(U)` pour `F` faisceau

Trois gestes, aucun mur : (1) l'exactitude du pas B (Partie 91) est une
exactitude de **préfaisceaux**, et l'évaluation en un ouvert est un
foncteur exact — limites et colimites des catégories de foncteurs sont
ponctuelles — donc la suite de sections `F(U) → C⁰F(U) → C¹F(U)` est
exacte sans aucun recours aux tiges ni à AB5 ; (2) l'unité de Godement
est mono pour `F` faisceau (Partie 90), donc sa composante en `U` aussi ;
(3) le relèvement au noyau `F(U) ⟶ ker d⁰(U)` est alors epi (exactitude
évaluée) et mono (composition du mono évalué avec `kernel.ι`), donc un
iso en `AddCommGrpCat` balancée. La faisheification identifiée au plan P95
n'est requise que par la brique 3 (suite exacte longue). -/

/-- **La différentielle de degré 0 du complexe des sections est la
composante en `U` de `d⁰`** : le champ `d` de `mapHomologicalComplex` est
l'image fonctorielle (définitionnel), le foncteur sections agit champ par
champ (`map_app`), et la Partie 92 a recalé `d 0 1 = godementCanonicalDZero`.
Pont entre le complexe des sections et les notations des Parties 89-92. -/
theorem godementSectionsComplex_d_zero (U : Opens X)
    (F : X.Presheaf AddCommGrpCat.{u}) :
    (godementSectionsComplex (X := X) U F).d 0 1 =
      (godementCanonicalDZero F).app (Opposite.op U) := by
  show (sectionsFunctorAdditive (X := X) U).map
      ((godementCanonicalComplex F).d 0 1) = _
  rw [godementCanonicalComplex_d_zero]
  rfl

/-- **Le pas B de la Partie 91, évalué en un ouvert** : pour `F` faisceau,
la suite de sections `F(U) → C⁰F(U) → C¹F(U)` est exacte en `C⁰F(U)`.
L'évaluation en un ouvert est un foncteur exact (limites et colimites des
préfaisceaux sont ponctuelles), donc transporte l'exactitude du pas B par
`Functor.exact_tfae` — là où la lecture par tiges de la Partie 93(a)
exigeait AB5, la lecture par sections d'un ouvert fixé est gratuite. -/
theorem exact_app_toGodement_godementCanonicalDZero
    (F : X.Presheaf AddCommGrpCat.{u}) (hF : TopCat.Presheaf.IsSheaf F)
    (U : Opens X) :
    (ShortComplex.mk ((toGodement F).app (Opposite.op U))
      ((godementCanonicalDZero F).app (Opposite.op U))
      (by rw [← NatTrans.comp_app, toGodement_comp_godementCanonicalDZero,
        zero_app])).Exact := by
  -- `ShortComplex.map` réclame `PreservesZeroMorphisms` du foncteur d'évaluation :
  -- la synthèse ne le trouve pas quand le foncteur est donné sous la forme
  -- `(evaluation …).obj (op U)` (vérifié par sonde : l'instance passe seule, pas
  -- dans cette position), donc on la fournit localement — champ unique
  -- `map_zero`, vrai point par point car le zéro d'une catégorie de foncteurs
  -- l'est (instance Mathlib équivalente, non trouvée par la synthèse ici).
  haveI hz : ((evaluation (Opposite (Opens X)) AddCommGrpCat.{u}).obj
      (Opposite.op U)).PreservesZeroMorphisms :=
    ⟨fun _ _ => by simp⟩
  have key : ∀ (S : ShortComplex (X.Presheaf AddCommGrpCat.{u})),
      S.Exact → (S.map ((evaluation (Opposite (Opens X)) AddCommGrpCat.{u}).obj
        (Opposite.op U))).Exact :=
    (((evaluation (Opposite (Opens X)) AddCommGrpCat.{u}).obj
      (Opposite.op U)).exact_tfae.out 3 1 rfl rfl).mp ⟨inferInstance, inferInstance⟩
  exact key (ShortComplex.mk (toGodement F) (godementCanonicalDZero F)
    (toGodement_comp_godementCanonicalDZero F))
    (exact_toGodement_godementCanonicalDZero F hF)

/-- **Partie 95, brique 2 — `H⁰_God(U, F) ≅ F(U)` pour `F` faisceau** :
l'homologie de degré 0 du complexe des sections de Godement est le groupe
des sections de `F` ([God58] II §5.1, Th. 5.1.1).

La chaîne : `H⁰ = ker d⁰` car il n'y a rien en degré −1 (recalage
`isoSc'` avec `prev 0 = 0`, puis `homologyIsoCokernelLift` et
`cokernelZeroIsoTarget` — l'image de la flèche nulle est nulle) ; puis
`ker d⁰(U) ≅ F(U)` parce que le relèvement au noyau `F(U) ⟶ ker d⁰(U)`
est epi (`exact_app_toGodement_godementCanonicalDZero`,
`Exact.epi_kernelLift`) et mono (l'unité de Godement est mono, Partie 90,
et composer à droite avec `kernel.ι` préserve le mono) — un iso en
`AddCommGrpCat` balancée. Aucune faisheification : le mur identifié au
plan P95 n'appartient qu'à la brique 3 (suite exacte longue). -/
noncomputable def godementZerothCohomologyIso (U : Opens X)
    (F : X.Presheaf AddCommGrpCat.{u}) (hF : TopCat.Presheaf.IsSheaf F) :
    godementCohomologyObj U F 0 ≅ F.obj (Opposite.op U) := by
  -- Les indices au bord : `prev 0 = 0` (aucun prédécesseur dans `up ℕ`),
  -- `next 0 = 1` — mêmes équations manuelles que la Partie 93(b).
  have hprev : (ComplexShape.up ℕ).prev 0 = 0 := by
    unfold ComplexShape.prev
    split
    case isTrue h =>
      have h2 : h.choose + 1 = 0 := h.choose_spec
      omega
    case isFalse h => rfl
  have hnext : (ComplexShape.up ℕ).next 0 = 1 := by
    unfold ComplexShape.next
    split
    case isTrue h =>
      have h2 : 0 + 1 = h.choose := h.choose_spec
      exact h2.symm
    case isFalse h =>
      exact (h (Exists.intro 1 rfl : ∃ j, (ComplexShape.up ℕ).Rel 0 j)).elim
  set K := godementSectionsComplex (X := X) U F with hK
  have hd00 : K.d 0 0 = 0 := K.shape 0 0 (by simp)
  have hd01 : K.d 0 1 = (godementCanonicalDZero F).app (Opposite.op U) :=
    godementSectionsComplex_d_zero U F
  -- La suite de sections, exacte (pas B évalué), et le mono évalué (P90).
  have hex : (ShortComplex.mk ((toGodement F).app (Opposite.op U))
      ((godementCanonicalDZero F).app (Opposite.op U))
      (by rw [← NatTrans.comp_app, toGodement_comp_godementCanonicalDZero,
        zero_app])).Exact :=
    exact_app_toGodement_godementCanonicalDZero F hF U
  have hmono : Mono ((toGodement F).app (Opposite.op U)) :=
    (NatTrans.mono_iff_mono_app _).mp (mono_toGodement_of_isSheaf F hF)
      (Opposite.op U)
  -- Le relèvement au noyau : epi par l'exactitude, mono par composition
  -- avec `kernel.ι` au-dessus du mono évalué — donc un iso (`AddCommGrpCat`
  -- est balancée).
  set φ : F.obj (Opposite.op U) ⟶
      kernel ((godementCanonicalDZero F).app (Opposite.op U)) :=
    kernel.lift ((godementCanonicalDZero F).app (Opposite.op U))
      ((toGodement F).app (Opposite.op U))
      (by rw [← NatTrans.comp_app, toGodement_comp_godementCanonicalDZero,
        zero_app]) with hφ
  have hφepi : Epi φ := hex.epi_kernelLift
  have hφmono : Mono φ := by
    have hcomp : φ ≫ kernel.ι _ = (toGodement F).app (Opposite.op U) :=
      kernel.lift_ι _ _ _
    constructor
    intro W u v huv
    refine hmono.right_cancellation u v ?_
    rw [← hcomp, ← Category.assoc, huv]
    exact Category.assoc _ _ _
  have hφiso : IsIso φ := (isIso_iff_epi_and_mono φ).mpr ⟨hφepi, hφmono⟩
  letI := hφiso
  -- L'iso final par assemblage.
  have e1 := K.isoSc' (i := 0) (j := 0) (k := 1) hprev hnext
  have hzc : (0 : K.X 0 ⟶ K.X 0) ≫ K.d 0 1 = 0 := by rw [zero_comp]
  have e2 : ShortComplex.mk (K.d 0 0) (K.d 0 1) (K.d_comp_d 0 0 1) ≅
      ShortComplex.mk (0 : K.X 0 ⟶ K.X 0) (K.d 0 1) hzc :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [hd00])
      (by simp)
  have e3 : (ShortComplex.mk (0 : K.X 0 ⟶ K.X 0) (K.d 0 1) hzc).homology ≅
      kernel (K.d 0 1) := by
    have h1 := ShortComplex.homologyIsoCokernelLift
      (S := ShortComplex.mk (0 : K.X 0 ⟶ K.X 0) (K.d 0 1) hzc)
    have h0 : kernel.lift (K.d 0 1) (0 : K.X 0 ⟶ K.X 0) hzc = 0 := by
      rw [← cancel_mono (kernel.ι (K.d 0 1)), kernel.lift_ι, zero_comp]
    rw [h0] at h1
    exact h1 ≪≫ cokernelZeroIsoTarget
  have e4 : kernel (K.d 0 1) ≅
      kernel ((godementCanonicalDZero F).app (Opposite.op U)) := by
    rw [hd01]
    exact Iso.refl _
  exact (ShortComplex.homologyMapIso e1 ≪≫ ShortComplex.homologyMapIso e2 ≪≫
    e3 ≪≫ e4 ≪≫ (asIso φ).symm)

end Grothendieck.SheafCohomology
