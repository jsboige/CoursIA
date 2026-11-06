/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Partie 34 — `Grothendieck.ExceptionalDirect` : image directe exceptionnelle `f_!`
## et l'adjonction `f_! ⊣ f^*` au niveau préfaisceau

Alexandre Grothendieck (1928-2014).

Extension Phase 2+ (#2159, Epic #1646). Cette partie répond à la frontière
déclarée par `MathlibMap.lean` : `f_!` / `f^!` et le formalisme complet des six
opérations restent absents de Mathlib 4. Nous livrons ici le chaînon le plus
accessible — `f_!` **au niveau préfaisceau** et son adjonction `f_! ⊣ f^*`.

### Contexte : ce que l'on a déjà, ce qui manque

Pour un morphisme de schémas `f : X ⟶ Y`, Mathlib fournit l'adjonction
fondamentale `f^* ⊣ f_*` sur les faisceaux de modules
(`DirectImage.lean`, `AlgebraicGeometry.Modules.Sheaf`). C'est la base du
transport des faisceaux. Mais le formalisme des **six opérations** de
Grothendieck demande davantage : il faut aussi `f_!` (image directe *à support
propre*) et son adjoint à droite `f^!`, pour énoncer la dualité de Poincaré,
la formule de Künneth, la suite exacte longue en cohomologie à support propre.

`f_!` faisceautique est subtil : il exige la faisceautification d'un foncteur
défini sur les préfaisceaux, plus une condition de support propre. En
revanche, **au niveau préfaisceau**, `f_!` admet une définition purement
catégorique et universelle : c'est l'**extension de Kan à gauche** de `f^*` le
long de `f`. C'est ce chaînon — honnêtement borné au niveau préfaisceau — que
ce module formalise.

### La construction (niveau préfaisceau)

Soit `f : C ⥤ D` un foncteur (lu comme un « morphisme de sites » au sens le
plus large). Les préfaisceaux sur `C` à valeurs dans `H` sont les foncteurs
contravariants `Cᵒᵖ ⥤ H`. Deux foncteurs canoniques apparaissent :

  - **`f^*` (image réciproque préfaisceau)** : précomposition par `f.op`. Pour
    `G : Dᵒᵖ ⥤ H`, on tire `G` en arrière en `f^* G : Cᵒᵖ ⥤ H` en composant avec
    `f.op : Cᵒᵖ ⥤ Dᵒᵖ`. C'est `(whiskeringLeft Cᵒᵖ Dᵒᵖ H).obj f.op`.
  - **`f_!` (image directe exceptionnelle préfaisceau)** : extension de Kan à
    gauche le long de `f.op`. Pour `F : Cᵒᵖ ⥤ H`, `f_! F : Dᵒᵖ ⥤ H` est le
    « meilleur relèvement » de `F` au-delà de l'image de `f.op`. C'est
    `(f.op).lan`.

### Le point de variance (non-trivial)

Les préfaisceaux sont **contravariants** : la flèche source de l'adjonction
n'est pas `f` mais **`f.op`**. La précomposition par `f.op` est bien
covariante en tant que foncteur `(Dᵒᵖ ⥤ H) ⥤ (Cᵒᵖ ⥤ H)`, et l'extension de Kan
gauche le long de `f.op` est covariante en sens inverse. L'adjonction
`(f.op).lan ⊣ (whiskeringLeft Cᵒᵖ Dᵒᵖ H).obj f.op` est donc exactement
`f_! ⊣ f^*`. Mathlib fournit ce fait comme `Functor.lanAdjunction`
(`Mathlib.CategoryTheory.Functor.KanExtension.Adjunction`) : nous l'instantions.

### Plafond atteignable (honnête, point d'acceptance 5)

Ce module établit `f_!` et `f_! ⊣ f^*` **au niveau préfaisceau** pour un
foncteur arbitraire `f : C ⥤ D`, sous l'hypothèse d'existence des extensions
de Kan `[∀ F, f.op.HasLeftKanExtension F]`. Ce n'est **pas** le `f_!`
faisceautique à support propre des six opérations : celui-ci s'obtient en
faisceautifiant le `f_!` préfaisceau puis en restreignant aux sections à support
propre, et exige une hypothèse de propreté sur `f`. Symétriquement, `f^!`
(l'adjoint à droite du `f_!` faisceautique) demande la **dualité de Verdier**
et n'est pas atteint ici. Documenter cette borne fait partie du livrable, ce
n'est pas une excuse : c'est la différence entre un plafond honnête et un
workaround consacré (cf `sota-not-workaround.md`).

Epic #1646, See #2159. Tous les `sorry` éliminés à la création.

### i18n — convention #4980 ratifiée 2026-07-04

Ce module est jumelé avec sa version anglaise canonique dans le fichier
sibling `ExceptionalDirect_en.lean`. Les énoncés de théorèmes/lemmes, les noms
de lemmes, les tactiques Lean et les références Mathlib restent en anglais
(Mathlib 4, tactic DSL standard) ; le namespace porte le suffixe `_en`. Seules
les **docstrings `/-- ... -/`** et les **commentaires `-- ...`** diffèrent entre
les deux fichiers. Anti-§D byte-identity garanti sur les signatures, preuves et
tactiques (vérifiable par diff).
-/

import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Whiskering

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Grothendieck.ExceptionalDirect

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {H : Type u₃} [Category.{v₃} H]

/-!
## 1. `f^*` au niveau préfaisceau : précomposition par `f.op`

Pour `f : C ⥤ D`, l'image réciproque préfaisceau tire un préfaisceau sur `D`
en un préfaisceau sur `C` par précomposition avec le foncteur opposé
`f.op : Cᵒᵖ ⥤ Dᵒᵖ`. C'est l'instance site-level du `(whiskeringLeft …).obj …`
de Mathlib, avec la variance opposée exigée par la contravariance des
préfaisceaux.
-/

/-- **`f^*` au niveau préfaisceau.** L'image réciproque d'un préfaisceau
    `G : Dᵒᵖ ⥤ H` le long de `f : C ⥤ D`, obtenue par précomposition avec
    `f.op : Cᵒᵖ ⥤ Dᵒᵖ`. C'est un foncteur covariant
    `(Dᵒᵖ ⥤ H) ⥤ (Cᵒᵖ ⥤ H)`. Le `.op` est la variance contravariante des
    préfaisceaux — l'erreur classique serait de précomposer par `f` au lieu de
    `f.op`. -/
noncomputable def pullbackPresheaf (f : C ⥤ D) : (Dᵒᵖ ⥤ H) ⥤ (Cᵒᵖ ⥤ H) :=
  (Functor.whiskeringLeft (C := Cᵒᵖ) (D := Dᵒᵖ) (E := H)).obj f.op

/-!
## 2. `f_!` au niveau préfaisceau : extension de Kan à gauche le long de `f.op`

L'image directe exceptionnelle préfaisceau étend un préfaisceau `F : Cᵒᵖ ⥤ H`
en `f_! F : Dᵒᵖ ⥤ H` comme le meilleur relèvement de `F` au-delà de l'image de
`f.op`. C'est l'extension de Kan à gauche `(f.op).lan`, qui existe dès que
chaque `F` admet une telle extension (typeclass `HasLeftKanExtension`).
-/

/-- **`f_!` au niveau préfaisceau.** L'image directe exceptionnelle d'un
    préfaisceau `F : Cᵒᵖ ⥤ H` le long de `f : C ⥤ D`, définie comme l'extension
    de Kan à gauche le long de `f.op : Cᵒᵖ ⥤ Dᵒᵖ`. C'est un foncteur covariant
    `(Cᵒᵖ ⥤ H) ⥤ (Dᵒᵖ ⥤ H)`. L'hypothèse
    `[∀ F, f.op.HasLeftKanExtension F]` garantit l'existence pointwise des
    extensions (elle tient typiquement pour `H = Type*` car la catégorie des
    préfaisceaux est cocomplète). -/
noncomputable def exceptionalDirectImage (f : C ⥤ D)
    [∀ (F : Cᵒᵖ ⥤ H), f.op.HasLeftKanExtension F] : (Cᵒᵖ ⥤ H) ⥤ (Dᵒᵖ ⥤ H) :=
  f.op.lan

/-!
## 3. L'adjonction `f_! ⊣ f^*`

Théorème central : l'image directe exceptionnelle préfaisceau est **adjointe à
gauche** de l'image réciproque préfaisceau. Les morphismes de préfaisceaux
`f_! F ⟶ G` (sur `D`) sont en correspondance naturelle avec les morphismes
`F ⟶ f^* G` (sur `C`). C'est l'analogue, transposé au niveau préfaisceau et
avec un adjoint à gauche au lieu de l'image directe, de l'adjonction
fondamentale `f^* ⊣ f_*` de `DirectImage.lean`. La preuve n'est pas un
`#check` de pont : elle instancie `Functor.lanAdjunction` de Mathlib, qui
établit `lan L ⊣ (whiskeringLeft _ _ _).obj L` comme adjonction à part
entière (avec unité, coïnité et hom-équivalence naturelles), pour
`L := f.op`.
-/

/-- **L'adjonction `f_! ⊣ f^*` au niveau préfaisceau.** Prouvée (pas un pont
    `#check`) en instanciant `Functor.lanAdjunction` de Mathlib
    (`f.op.lanAdjunction H`), qui établit formellement
    `(f.op).lan ⊣ (whiskeringLeft Cᵒᵖ Dᵒᵖ H).obj f.op` comme adjonction —
    c'est-à-dire exactement `f_! ⊣ f^*`. -/
noncomputable def exceptionalDirectImageAdjunction (f : C ⥤ D)
    [∀ (F : Cᵒᵖ ⥤ H), f.op.HasLeftKanExtension F] :
    exceptionalDirectImage (H := H) f ⊣ pullbackPresheaf (H := H) f :=
  f.op.lanAdjunction H

-- **Rappel : cette adjonction vit au niveau préfaisceau.** L'adjoint à gauche
-- est l'extension de Kan le long de `f.op`, l'adjoint à droite la
-- précomposition par `f.op`.
--
-- Le lemme `adjunction_left_eq_lan` (projection `.left` sur l'adjonction)
-- n'est pas énoncé : la structure `Adjunction` de Mathlib ne porte pas de
-- projection `.left`/`.right` (cf `Mathlib/CategoryTheory/Adjunction/Basic.lean`,
-- `structure Adjunction (F : C ⥤ D) (G : D ⥤ C) where unit counit ...` —
-- les foncteurs sont des **arguments** du type, pas des champs). L'identité
-- « adjoint à gauche = `lan` » est en revanche portée **dans le type** de
-- `exceptionalDirectImageAdjunction f` (sa composante gauche est précisément
-- `f.op.lan`), ce qui est strictement plus fort qu'un `@[simp]`.

-- **Symétrique, même conclusion.** `adjunction_right_eq_pullback` n'est pas
-- énoncé non plus, et pour la raison exacte qui tue `.left` : `.right` n'est pas
-- davantage un champ de `Adjunction`. L'identité « adjoint à droite =
-- `pullbackPresheaf` » est portée **dans le type** de
-- `exceptionalDirectImageAdjunction` ci-dessus (`... ⊣ pullbackPresheaf (H := H) f`),
-- donc vérifiée à l'élaboration de la définition elle-même. Rien n'est perdu :
-- ce que le lemme aurait affirmé, la signature l'exige déjà.

/-!
## 4. Le plafond : niveau préfaisceau, pas faisceautique

Nous énonçons noir sur blanc la borne, conformément au point d'acceptance 5 :
ce `f_!` est préfaisceau, pas le `f_!` faisceautique à support propre des six
opérations. Cette section est une **partie du livrable** (documenter le plafond
atteignable), pas une excuse.
-/

/-- **Plafond honnête.** Ce `f_!` est l'image directe exceptionnelle au niveau
    **préfaisceau**. Le `f_!` faisceautique à support propre des six opérations
    de Grothendieck s'en déduit par faisceautification puis restriction aux
    sections à support propre (sous une hypothèse de properté de `f`), et son
    adjoint à droite `f^!` demande la dualité de Verdier. Ce lemme-témoin
    rappelle la définition pour ancrer le plafond : il n'y a ici aucune
    `sorry`, aucune preuve fabriquée — seulement l'adjonction Kan au niveau
    préfaisceau, qui est ce que Mathlib permet de prouver proprement. -/
theorem exceptionalDirectImage_is_presheaf_level (f : C ⥤ D)
    [∀ (F : Cᵒᵖ ⥤ H), f.op.HasLeftKanExtension F] :
    exceptionalDirectImage (H := H) f = f.op.lan (H := H) :=
  rfl

end Grothendieck.ExceptionalDirect
