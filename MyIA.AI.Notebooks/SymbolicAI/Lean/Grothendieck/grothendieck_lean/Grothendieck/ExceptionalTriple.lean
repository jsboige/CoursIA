/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Partie 35 — `Grothendieck.ExceptionalTriple` : le triple adjoint `f_! ⊣ f^* ⊣ f_*`
## et l'effondrement de l'image inverse exceptionnelle au niveau préfaisceau

Alexandre Grothendieck (1928-2014).

Extension Phase 2+ (#2159, Epic #1646). La Partie 34 (`ExceptionalDirect.lean`)
a livré `f_!` au niveau préfaisceau (extension de Kan à gauche le long de
`f.op`) et son adjonction `f_! ⊣ f^*`. Cette partie complète la vue en
assemblant le **triple adjoint** `f_! ⊣ f^* ⊣ f_*` : la troisième patte
`f^* ⊣ f_*` est l'image directe ordinaire (extension de Kan à droite le long
de `f.op`), et c'est leur enchâssement en un **triple** qui est ici la substance.

### Ce que le niveau préfaisceau offre de non dégénéré

Aucune des deux adjonctions prise isolément n'est neuve : `f_! ⊣ f^*` est la
Partie 34, et `f^* ⊣ f_*` n'est qu'une réinstanciation de `Functor.ranAdjunction`
(Mathlib). Ce qui n'est **pas** du Mathlib recopié, c'est le **triple** et les
propriétés qui n'existent que parce qu'il y en a un :

  - **`presheafSixOpsTriple`** : l'enchâssement `f_! ⊣ f^* ⊣ f_*` comme
    `CategoryTheory.Adjunction.Triple`.
  - **La cohérence** : `f_!` est pleinement fidèle **si et seulement si**
    `f_*` l'est (`Adjunction.Triple.fullyFaithfulEquiv`). C'est un énoncé sur
    `f_!` prouvé *via* `f_*` — hors de portée de la Partie 34 seule.
  - **`exceptionalInverse_collapses_to_pullback`** : pour tout `G` tel que
    `f_! ⊣ G`, on a `G ≅ f^*` (`rightAdjointUniq`). C'est le plafond honnête :
    au niveau préfaisceau, il n'y a **pas** d'image inverse exceptionnelle
    `f^!` distincte de `f^*`.

### Le plafond (honnête, conformément au point d'acceptance 5)

Ce triple vit au niveau **préfaisceau**. Le `f_!` faisceautique à support propre
des six opérations exige une faisceautification et une hypothèse de propreté sur
`f` ; son adjoint à droite `f^!` demande la **dualité de Verdier**.
L'effondrement `G ≅ f^*` ci-dessus rend cette impossibilité **prouvable** en
Lean, pas seulement déclarée en prose — c'est exactement la borne que la Partie
34 annonçait.

Epic #1646, See #2159. Tous les `sorry` éliminés à la création.

### i18n — convention #4980 ratifiée 2026-07-04

Ce module est jumelé avec sa version anglaise canonique dans le fichier sibling
`ExceptionalTriple_en.lean` (modèle **jumeau consommateur** : le `_en` importe
le module FR `Grothendieck.ExceptionalDirect` et ne re-déclare pas ses
définitions — cf `CoversLattice_en.lean`). Les énoncés de théorèmes/lemmes, les
noms de lemmes, les tactiques Lean et les références Mathlib restent en anglais
(Mathlib 4, tactic DSL standard) ; le namespace porte le suffixe `_en`. Seules
les **docstrings `/-- ... -/`** et les **commentaires `-- ...`** diffèrent entre
les deux fichiers. Anti-§D byte-identity garanti sur les signatures, preuves et
tactiques (vérifiable par diff).
-/

import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Whiskering
import Grothendieck.ExceptionalDirect

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Grothendieck.ExceptionalTriple

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {H : Type u₃} [Category.{v₃} H]

/-!
## 1. `f_*` au niveau préfaisceau : extension de Kan à droite le long de `f.op`

La troisième patte du triple. L'image directe ordinaire `f_*` étend un
préfaisceau `F : Cᵒᵖ ⥤ H` en `f_* F : Dᵒᵖ ⥤ H` comme le meilleur relèvement de
`F` par la droite — l'extension de Kan à droite `(f.op).ran`. Elle est adjointe
à **droite** de l'image réciproque `f^*` : c'est l'analogue préfaisceau de
l'adjonction fondamentale `f^* ⊣ f_*` des faisceaux de modules, instanciée ici
par `Functor.ranAdjunction`.
-/

/-- **`f_*` au niveau préfaisceau.** L'image directe d'un préfaisceau
    `F : Cᵒᵖ ⥤ H` le long de `f : C ⥤ D`, définie comme l'extension de Kan à
    droite le long de `f.op : Cᵒᵖ ⥤ Dᵒᵖ`. C'est un foncteur covariant
    `(Cᵒᵖ ⥤ H) ⥤ (Dᵒᵖ ⥤ H)`. L'hypothèse `[∀ G, f.op.HasRightKanExtension G]`
    garantit l'existence pointwise des extensions. -/
noncomputable def directImagePresheaf (f : C ⥤ D)
    [∀ (G : Cᵒᵖ ⥤ H), f.op.HasRightKanExtension G] : (Cᵒᵖ ⥤ H) ⥤ (Dᵒᵖ ⥤ H) :=
  f.op.ran

/-- **L'adjonction `f^* ⊣ f_*` au niveau préfaisceau.** Prouvée en instanciant
    `Functor.ranAdjunction` de Mathlib (`f.op.ranAdjunction H`), qui établit
    formellement `(whiskeringLeft Cᵒᵖ Dᵒᵖ H).obj f.op ⊣ (f.op).ran` — c'est-à-dire
    exactement `f^* ⊣ f_*`. -/
noncomputable def directImagePresheafAdjunction (f : C ⥤ D)
    [∀ (G : Cᵒᵖ ⥤ H), f.op.HasRightKanExtension G] :
    ExceptionalDirect.pullbackPresheaf (H := H) f ⊣ directImagePresheaf (H := H) f :=
  f.op.ranAdjunction H

/-!
## 2. Le triple `f_! ⊣ f^* ⊣ f_*`

L'enchâssement des deux adjonctions en un **triple adjoint**. La Partie 34
fournit `adj₁ : f_! ⊣ f^*` ; cette partie fournit `adj₂ : f^* ⊣ f_*`. Leur
réunion est le triple `f_! ⊣ f^* ⊣ f_*`, la brique des six opérations (au niveau
préfaisceau).
-/

/-- **Le triple adjoint `f_! ⊣ f^* ⊣ f_*` au niveau préfaisceau.** Assemble
    l'adjonction de la Partie 34 (`exceptionalDirectImageAdjunction`, `adj₁`)
    avec l'adjonction `f^* ⊣ f_*` de la section 1
    (`directImagePresheafAdjunction`, `adj₂`) en un
    `CategoryTheory.Adjunction.Triple`. -/
noncomputable def presheafSixOpsTriple (f : C ⥤ D)
    [∀ (F : Cᵒᵖ ⥤ H), f.op.HasLeftKanExtension F]
    [∀ (G : Cᵒᵖ ⥤ H), f.op.HasRightKanExtension G] :
    CategoryTheory.Adjunction.Triple
      (ExceptionalDirect.exceptionalDirectImage (H := H) f)
      (ExceptionalDirect.pullbackPresheaf (H := H) f) (directImagePresheaf (H := H) f) where
  adj₁ := ExceptionalDirect.exceptionalDirectImageAdjunction (H := H) f
  adj₂ := directImagePresheafAdjunction (H := H) f

/-!
## 3. Cohérence : `f_!` et `f_*` sont simultanément pleinement fidèles

Un énoncé que **ni l'une ni l'autre des deux moitiés ne donne** : `f_!` est
pleinement fidèle **si et seulement si** `f_*` l'est. Il se prouve *via*
`Adjunction.Triple.fullyFaithfulEquiv`, qui relie les deux extrémités du triple.
-/

/-- **`f_!` pleinement fidèle ssi `f_*` pleinement fidèle.** Énoncé de cohérence
    du triple, prouvé par `presheafSixOpsTriple.fullyFaithfulEquiv`
    (`Adjunction.Triple.fullyFaithfulEquiv`). C'est la seule propriété du triple
    qui ne soit pas recopiée d'une moitié : un énoncé sur `f_!` prouvé *via*
    `f_*`. -/
noncomputable def exceptionalDirectImage_fullyFaithful_iff_directImage (f : C ⥤ D)
    [∀ (F : Cᵒᵖ ⥤ H), f.op.HasLeftKanExtension F]
    [∀ (G : Cᵒᵖ ⥤ H), f.op.HasRightKanExtension G] :
    (ExceptionalDirect.exceptionalDirectImage (H := H) f).FullyFaithful ≃
      (directImagePresheaf (H := H) f).FullyFaithful :=
  (presheafSixOpsTriple (H := H) f).fullyFaithfulEquiv

/-!
## 4. Le plafond : l'image inverse exceptionnelle s'effondre sur `f^*`

C'est le résultat de méthode. Au niveau préfaisceau, il n'y a **pas** de `f^!`
distinct de `f^*` : si un foncteur `G` est adjoint à droite de `f_!`, alors
`G ≅ f^*`. La preuve utilise `rightAdjointUniq` (unicité de l'adjoint à droite)
appliqué à l'adjonction de la Partie 34 (et à l'adjonction donnée `adj`). Ce
fait documente durablement pourquoi le lake n'aura de `f^!` qu'avec la dualité
de Verdier.
-/

/-- **L'image inverse exceptionnelle s'effondre sur `f^*`.** Pour tout
    `G : (Dᵒᵖ ⥤ H) ⥤ (Cᵒᵖ ⥤ H)` tel que `f_! ⊣ G`, on a `G ≅ f^*`. C'est
    l'unicité de l'adjoint à droite (`rightAdjointUniq`) appliquée à
    `exceptionalDirectImageAdjunction` (Partie 34) et à l'adjonction donnée
    `adj`. Plafond honnête : au niveau préfaisceau, `f^! = f^*`. -/
noncomputable def exceptionalInverse_collapses_to_pullback (f : C ⥤ D)
    [∀ (F : Cᵒᵖ ⥤ H), f.op.HasLeftKanExtension F]
    (G : (Dᵒᵖ ⥤ H) ⥤ (Cᵒᵖ ⥤ H))
    (adj : ExceptionalDirect.exceptionalDirectImage (H := H) f ⊣ G) :
    G ≅ ExceptionalDirect.pullbackPresheaf (H := H) f :=
  (CategoryTheory.Adjunction.rightAdjointUniq
    (ExceptionalDirect.exceptionalDirectImageAdjunction (H := H) f) adj).symm

end Grothendieck.ExceptionalTriple
