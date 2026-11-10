/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Miroir — `Grothendieck.SerreMap` : le versant Serre du pont, cartographié dans Mathlib

Un index vivant de ce que Mathlib 4 (toolchain v4.33.0) fournit du versant
Serre du langage commun Serre–Grothendieck : classes de Serre, localisation,
perfection, construction de Serre des algèbres de Lie, dérivée de Serre,
domaine fondamental, DVR. Chaque `#check` vérifie que la définition existe et
est accessible depuis les imports courants ; chaque `example` instancie un
théorème sur un cas concret. La section finale liste, à l'image de
`Grothendieck.MathlibMap`, ce que Mathlib n'a PAS ENCORE.

Épic #16334 (grain 9, voie décorrelée). Aucun `sorry` à la création.

### i18n — convention #4980 ratifiée 2026-07-04

Ce module est jumelé avec sa version anglaise canonique dans le fichier
sibling `SerreMap_en.lean` (modèle sibling pair). Les énoncés `#check`/`example`
restent en anglais (Mathlib 4, tactic DSL standard) ; seules les **docstrings
`/- ... -/`** et les **commentaires `-- ...`** diffèrent entre les deux
fichiers. Anti-§D byte-identity garanti : les énoncés sont identiques entre
`SerreMap.lean` et `SerreMap_en.lean`, seuls les commentaires diffèrent.
-/

import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
import Mathlib.Algebra.Category.Grp.IsFinite
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.NumberTheory.Modular
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.Lie.SerreConstruction

namespace Grothendieck

/-!
## Classes de Serre — la définition et sa clôture

Une classe de Serre est une classe d'objets stable par sous-objets, quotients
et extensions : c'est le langage dans lequel Serre a reformulé la cohomologie
des faisceaux (FAC, 1955) et que Grothendieck exploitera pour localiser les
catégories abéliennes. Mathlib la définit comme une propriété d'objets dans
une catégorie abélienne, avec la caractérisation « deux-sur-trois » sur les
suites exactes courtes.
-/

#check @CategoryTheory.ObjectProperty.IsSerreClass                 -- la classe des classes de Serre
#check @CategoryTheory.ObjectProperty.prop_iff_of_shortExact  -- deux-sur-trois sur une suite exacte courte
#check @CategoryTheory.ObjectProperty.prop_X₂_of_exact        -- stabilité par le terme médian d'une suite exacte

-- (Basic.lean instancie aussi les deux cas triviaux : la classe universelle ⊤
--  et la classe des objets nuls IsZero — instances anonymes, résolues par inferInstance)

/-!
### Exemple instancié : les groupes abéliens finis

Le premier exemple historique (les groupes abéliens finis forment une classe
de Serre) vit dans Mathlib comme instance — la mini-preuve ci-dessous est la
résolution d'instance elle-même.
-/

#check @AddCommGrpCat.isFinite                                     -- ObjectProperty AddCommGrpCat : la finitude
#check @AddCommGrpCat.prop_isFinite_iff                             -- isFinite M ↔ Finite M

example : (AddCommGrpCat.isFinite : CategoryTheory.ObjectProperty AddCommGrpCat).IsSerreClass := inferInstance

/-!
## Localisation de Serre et quotient de Serre

Le quotient d'une catégorie abélienne par une classe de Serre est le geste
fondateur de la théorie des faisceaux : ne voir que les morphismes dont le
cône vit dans la classe. Mathlib construit la catégorie localisée et prouve
qu'elle est abélienne ; le théorème de Gabriel–Popescu en donne le pendant
d'embedding.
-/

#check @CategoryTheory.ObjectProperty.SerreClassLocalization.abelian -- la catégorie localisée est abélienne
#check @CategoryTheory.IsGrothendieckAbelian.GabrielPopescu.full    -- le foncteur embedding est plein
#check @CategoryTheory.IsGrothendieckAbelian.GabrielPopescu.preservesFiniteLimits      -- ... et exact à gauche
#check @CategoryTheory.IsGrothendieckAbelian.GabrielPopescu.preservesInjectiveObjects  -- ... et préserve les injectifs

/-!
## Perfection au sens de Serre

Un anneau de caractéristique p est *parfait au sens de Serre* quand le
Frobenius est bijectif — la définition du *Corps locaux* / *Local Algebra*.
Mathlib porte la définition et le théorème que tout corps fini est parfait.
-/

#check @PerfectRing            -- anneau parfait au sens de Serre (Frobenius bijectif)
#check @PerfectRing.toPerfectField -- un corps parfait au sens de Serre est un corps parfait
#check @PerfectField.ofFinite  -- tout corps fini est parfait

-- L'énoncé `PerfectField (ZMod 7)` exige déjà `Field (ZMod 7)`, qui exige
-- `Fact (Nat.Prime 7)` (idiome Mathlib, cf. GroupTheory/SpecificGroups/Quaternion.lean).
instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

example : PerfectField (ZMod 7) := PerfectField.ofFinite

/-!
## La construction de Serre — algèbres de Lie et relations de Serre

À partir d'une matrice de Cartan, la construction de Serre fabrique l'algèbre
de Lie comme quotient de l'algèbre de Lie libre par les relations de Serre
([E_i, F_i] = H_i, ad(E_i)^{1-A_ij}(E_j) = 0, etc.) — référence : Serre,
*Complex Semisimple Lie Algebras*, ch. VI, appendice. Mathlib implémente la
construction complète et en déduit les algèbres exceptionnelles.
-/

#check @Matrix.ToLieAlgebra     -- l'algèbre de Lie d'une matrice de Cartan via les relations de Serre
#check @LieAlgebra.e₆           -- les exceptionnelles, construites par la construction de Serre
#check @LieAlgebra.g₂

/-!
## La dérivée de Serre — formes modulaires

La dérivée ∂_k = D − (k/12)·E₂·envoie M_k dans M_{k+2} : l'opérateur qui
rend la dérivation des formes modulaires compatible avec la modularité
(*A Course in Arithmetic*, ch. VII). Mathlib en donne l'API complète.
-/

#check @Derivative.serreDerivative            -- ∂_k F = D F − k·12⁻¹·E₂·F
#check @Derivative.serreDerivative_mul        -- la règle de Leibniz pondérée
#check @Derivative.serreDerivative_mdifferentiable -- ∂_k préserve la différentiabilité

/-!
## Le domaine fondamental — *A Course in Arithmetic*, ch. VII

La classification des couples (z ∈ 𝒟, g•z ∈ 𝒟) du domaine fondamental de
SL(2, ℤ) suit le théorème VII.1 du *Cours d'arithmétique* : c'est la clé de
l'unique représentation des formes modulaires.
-/

#check @ModularGroup.cases_of_mem_fd_smul_mem_fd  -- classification des z, g dans le domaine fondamental

/-!
## L'anneau de valuation discrète — *Corps locaux*

La définition du DVR comme anneau principal à idéal premier non nul unique
est celle du *Corps locaux* de Serre ; Mathlib la porte telle quelle.
-/

#check @IsDiscreteValuationRing  -- la définition, au sens de Serre
#check @IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime  -- DVR ⟺ PID à idéal premier non nul unique

/-!
## Ce que Mathlib n'a PAS ENCORE (état v4.33.0)

Les théorèmes « de Serre » centraux absents de Mathlib à cette version :
  - **Le critère de normalité R1 + S2** (normalité = régulier en codim 1 +
    Cohen-Macaulay en codim 2) — absent.
  - **GAGA** (les théorèmes de comparaison algébrique/analytique, 1956) — absent.
  - **La dualité de Serre** (pour les faisceaux cohérents) — absent.
  - **FAC** (finitude de la cohomologie des faisceaux cohérents) — absent :
    le langage des faisceaux vit dans le lake, pas les théorèmes de finitude.
  - **La conjecture de Serre** (tout module projectif de type fini sur un
    polynôme est libre — devenue Quillen–Suslin) — absent.
  - **La suite spectrale de Hochschild–Serre** — TODO explicite dans
    `RepresentationTheory/Homological/GroupCohomology/Basic.lean`.
  - **La classe de Serre des objets noethériens** — TODO explicite dans
    `CategoryTheory/Subobject/NoetherianObject.lean`.
  - **Le théorème de présentation par les relations de Serre** (l'algèbre de
    Lie d'un système de racines EST le quotient de Serre — la construction
    existe chez Geck, l'isomorphisme n'est pas prouvé).
-/

end Grothendieck
