/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 33 : Image directe et image reciproque des faisceaux

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-29 ont etabli les fondamentaux : categories, cribles, topologies,
lois de treillis, identites de pullback, bases de faisceaux, cloture couvrante,
calibration, sous-canonicalite, topologies denses, faisceaux, hom interne,
cohomologie de Cech, limite de Mayer-Vietoris.

Ce module introduit le couple **image directe / image reciproque** des faisceaux
de modules sur les schemas : pour un morphisme de schemas `f : X ⟶ Y`, le foncteur
**image directe** `f_* : X.Modules ⥤ Y.Modules` (pushforward) et le foncteur
**image reciproque** `f^* : Y.Modules ⥤ X.Modules` (pullback), relies par
l'**adjonction fondamentale `f^* ⊣ f_*`**.

Cette adjonction est la pierre angulaire du transport des faisceaux le long des
morphismes en geometrie algebrique : c'est l'instance la plus simple du
formalisme des « six operations » de Grothendieck (SGA 4, SGA 5). Elle dit que
les morphismes de faisceaux de modules `f^* G ⟶ M` (sur X) sont en bijection
naturelle avec les morphismes `G ⟶ f_* M` (sur Y).

Constructions clefs pontees depuis Mathlib (`AlgebraicGeometry.Modules.Sheaf`) :

  - `Scheme.Modules X`        : la categorie abelienne des `𝒪ₓ`-modules sur un schema X
  - `pushforward f`           : le foncteur image directe `f_* : X.Modules ⥤ Y.Modules`
  - `pullback f`              : le foncteur image reciproque `f^* : Y.Modules ⥤ X.Modules`
  - `pullbackPushforwardAdjunction f` : l'adjonction `f^* ⊣ f_*`
  - `pushforwardId X`         : `f_*` le long de l'identite s'identifie au foncteur identite
  - `pushforwardComp f g`     : `f_*` puis `g_*` s'identifie a `(g ∘ f)_*`
  - `pullbackId X`, `pullbackComp f g` : analogues pour `f^*`

EPIC #1646, Phase 5 (#2159). Tous les `sorry`s elimines a la creation.

### Note d'accessibilite (Epics #1452/#1453)

Ce module expose **8 verifications `#check`** sur le couple image directe /
image reciproque, organisees par 6 sections thematiques : (1) la categorie des
`𝒪ₓ`-modules sur un schema, (2) l'image directe `f_*`, (3) l'image reciproque
`f^*`, (4) l'adjonction fondamentale `f^* ⊣ f_*`, (5) les identites de
fonctorialite de l'image directe `f_*` (identite, composition), (6) les
identites de fonctorialite de l'image reciproque `f^*` (analogue dual).

### Convention i18n (EPIC #4980 ratifiee par user 2026-07-04)

Ce module substantiel est apparie avec son jumeau anglais dans le fichier sibling
`DirectImage_en.lean` (modele sibling pair, voir PR #6154 pour le pilote sur
`Utility.lean` et #6275/#6277/#6280/#6284 pour la continuite du rollout).
Namespace suffix `_en` applique au fichier EN (anti-collision, conforme
code-style.md #4980). Les verifications `#check`, les signatures, les variables
et les univers sont **byte-identical** entre les deux fichiers ; seules les
docstrings `/-- ... -/` et les commentaires `-- ...` different.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf

universe u

namespace Grothendieck.DirectImage

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme (Modules)
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules (pullbackId pullbackComp)

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-!
## Section 1 : La categorie des faisceaux de modules sur un schema

Pour un schema `X`, le type `X.Modules` est la categorie abelienne des faisceaux
de modules sur le faisceau structural `𝒪ₓ`. C'est le cadre naturel ou vivent
l'image directe et l'image reciproque : ce sont des foncteurs entre de telles
categories, parametres par un morphisme de schemas `f : X ⟶ Y`.
-/

-- La categorie des 𝒪ₓ-modules sur un schema X (categorie abelienne).
#check (Scheme.Modules X : Type _)

/-!
## Section 2 : L'image directe (pushforward, `f_*`)

Pour un morphisme de schemas `f : X ⟶ Y`, l'**image directe** `f_*` envoie un
`𝒪ₓ`-module `M` sur le `𝒪_Y`-module `f_* M` dont les sections sur un ouvert
`U` de `Y` sont les sections de `M` sur l'image reciproque `f ⁻¹ᵁ U`.

C'est la facon naturelle de *pousser en avant* un faisceau le long de `f`.
-/

-- Le foncteur image directe f_* : des 𝒪ₓ-modules vers les 𝒪_Y-modules.
#check (pushforward f : X.Modules ⥤ Y.Modules)

/-!
## Section 3 : L'image reciproque (pullback, `f^*`)

L'**image reciproque** `f^*` est le foncteur adjoint a gauche de `f_*` : il
*tire en arriere* un `𝒪_Y`-module sur `X`. Geometriquement, `f^* G` represente
le faisceau `G` vu sur l'espace source `X` via le morphisme `f`.
-/

-- Le foncteur image reciproque f^* : des 𝒪_Y-modules vers les 𝒪ₓ-modules.
#check (pullback f : Y.Modules ⥤ X.Modules)

/-!
## Section 4 : L'adjonction fondamentale `f^* ⊣ f_*`

Le resultat central : l'image reciproque est adjointe a gauche de l'image
directe. Les morphismes de `𝒪ₓ`-modules `f^* G ⟶ M` sont en correspondance
naturelle avec les morphismes de `𝒪_Y`-modules `G ⟶ f_* M`. Cette adjonction
est le coeur du transport des faisceaux en geometrie algebrique et l'ancetre
le plus simple du formalisme des six operations de Grothendieck.
-/

-- L'adjonction fondamentale : f^* est adjoint a gauche de f_*.
#check (pullbackPushforwardAdjunction f : pullback f ⊣ pushforward f)

/-!
## Section 5 : Identites de fonctorialite de l'image directe `f_*`

L'image directe `f_*` se comporte bien vis-a-vis de l'identite et de la
composition des morphismes de schemas : pousser en avant le long de l'identite
est l'identite, et pousser en avant le long de `f` puis `g` s'identifie au
pushforward le long de la composee `f ≫ g`.
-/

-- f_* le long de l'identite s'identifie au foncteur identite.
#check (pushforwardId X : pushforward (𝟙 X) ≅ 𝟭 _)

-- f_* puis g_* s'identifie au pushforward de la composee (f ≫ g)_*.
#check (pushforwardComp f g : pushforward f ⋙ pushforward g ≅ pushforward (f ≫ g))

/-!
## Section 6 : Identites de fonctorialite de l'image reciproque `f^*`

L'image reciproque `f^*` satisfait les identites duales : tirer en arriere le
long de l'identite est l'identite, et tirer en arriere le long de `f ≫ g`
s'identifie a tirer en arriere selon `g` puis `f` (notez l'ordre renverse :
`pullback g ⋙ pullback f`, car `f^*` est contravariante en `f`).
-/

-- f^* le long de l'identite s'identifie au foncteur identite.
#check pullbackId X

-- f^* de la composee : pullback g puis pullback f = pullback (f ≫ g) (ordre renverse, contravariance).
#check pullbackComp f g

/-!
## Section 7 : Theoremes ponts : loi fonctorielle sur pushforward et pullback

Les foncteurs `pushforward f` et `pullback f` sont des `Functor` a part
entiere : ils preservent les identites et la composition (les fields
`Functor.map_id` et `Functor.map_comp` de la structure). Les 4 bridges
ci-dessous font la jointure entre les definitions du module et les
faits Mathlib 4 sous-jacents :

  - `pushforward_map_id` / `pushforward_map_comp` : champs de structure
    du foncteur `pushforward f` (acces direct
    `(pushforward f).map_id X` / `(pushforward f).map_comp f g`).
  - `pullback_map_id` / `pullback_map_comp` : champs de structure
    symetriques du foncteur `pullback f`.

Pour les champs de structure de `Functor` (L902 ★★ Tier 5), l'application
directe `(F).map_id X` / `(F).map_comp f g` est l'idiotisme canonique
(pas `by rw [Functor.map_id]`, qui defait la LHS mais ne ferme pas le
but sur Type equality, ni `rfl`, qui n'est PROUVABLE que pour les
egalites definitionnelles).
-/

/-- Bridge : le foncteur `pushforward f` preserve les identites. C'est le champ
    `Functor.map_id` de la structure, accessible directement. -/
theorem pushforward_map_id {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules) :
    (pushforward f).map (𝟙 M) = 𝟙 ((pushforward f).obj M) :=
  (pushforward f).map_id M

/-- Bridge : le foncteur `pushforward f` preserve la composition des morphismes.
    Champ `Functor.map_comp` de la structure. -/
theorem pushforward_map_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N P : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ P) :
    (pushforward f).map (φ ≫ ψ) =
      (pushforward f).map φ ≫ (pushforward f).map ψ :=
  (pushforward f).map_comp φ ψ

/-- Bridge : le foncteur `pullback f` preserve les identites. Champ `Functor.map_id`
    de la structure. Dual de `pushforward_map_id`. -/
theorem pullback_map_id {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Y.Modules) :
    (pullback f : Y.Modules ⥤ X.Modules).map (𝟙 G) =
      𝟙 ((pullback f : Y.Modules ⥤ X.Modules).obj G) :=
  (pullback f : Y.Modules ⥤ X.Modules).map_id G

/-- Bridge : le foncteur `pullback f` preserve la composition des morphismes.
    Champ `Functor.map_comp` de la structure. Dual de `pushforward_map_comp`. -/
theorem pullback_map_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    {G H K : Y.Modules} (φ : G ⟶ H) (ψ : H ⟶ K) :
    (pullback f : Y.Modules ⥤ X.Modules).map (φ ≫ ψ) =
      (pullback f : Y.Modules ⥤ X.Modules).map φ ≫
        (pullback f : Y.Modules ⥤ X.Modules).map ψ :=
  (pullback f : Y.Modules ⥤ X.Modules).map_comp φ ψ


/-- Bridge : l'identité de la catégorie `X.Modules` appliquée aux sections
    vaut l'identité de l'anneau de sections. C'est le lemme
    `AlgebraicGeometry.Scheme.Modules.Hom.id_app` de Mathlib 4 :
    `((𝟙 M : M ⟶ N).app U = 𝟙 _)`. -/

theorem id_app_field (X : Scheme.{u}) (M : X.Modules) (U : X.Opens) :
    (𝟙 M : M ⟶ M).app U = 𝟙 (Γ(M, U)) :=
  @AlgebraicGeometry.Scheme.Modules.Hom.id_app X U M

/-- Bridge : la composition des morphismes de `X.Modules` est calculée
    pointwise comme la composition des morphismes de sections. C'est le lemme
    `Hom.comp_app` de Mathlib 4 : `(φ ≫ ψ).app U = φ.app U ≫ ψ.app U`. -/

theorem comp_app_field (X : Scheme.{u}) {M N K : X.Modules} (φ : M ⟶ N)
    (ψ : N ⟶ K) (U : X.Opens) :
    (φ ≫ ψ).app U = φ.app U ≫ ψ.app U :=
  @AlgebraicGeometry.Scheme.Modules.Hom.comp_app X M N K U φ ψ

/-- Bridge : l'addition des morphismes de `X.Modules` est calculée
    pointwise comme l'addition des morphismes de sections. C'est le lemme
    `Hom.add_app` de Mathlib 4 : `(φ + ψ).app U = φ.app U + ψ.app U`. -/

theorem add_app_field (X : Scheme.{u}) {M N : X.Modules} (φ ψ : M ⟶ N)
    (U : X.Opens) :
    (φ + ψ).app U = φ.app U + ψ.app U :=
  @AlgebraicGeometry.Scheme.Modules.Hom.add_app X M N U φ ψ

/-- Bridge : l'action scalaire d'une section de l'anneau structural sur un
    morphisme de `X.Modules` est calculée pointwise. C'est le lemme
    `Hom.app_smul` de Mathlib 4 : `φ.app U (r • x) = r • φ.app U x`. -/

theorem app_smul_field (X : Scheme.{u}) {M N : X.Modules} (φ : M ⟶ N)
    (U : X.Opens) (r : Γ(X, U)) (x : Γ(M, U)) :
    φ.app U (r • x) = r • φ.app U x :=
  @AlgebraicGeometry.Scheme.Modules.Hom.app_smul X M N U φ r x

/-- Bridge : le morphisme nul `0 : M ⟶ N` applique à l'identité nulle sur
    les sections. C'est le lemme `Hom.zero_app` de Mathlib 4 :
    `(0 : M ⟶ N).app U = 0`. -/

theorem zero_app_field (X : Scheme.{u}) {M N : X.Modules} (U : X.Opens) :
    (0 : M ⟶ N).app U = 0 :=
  @AlgebraicGeometry.Scheme.Modules.Hom.zero_app X M N U

/-- Bridge : un morphisme de `X.Modules` est un isomorphisme ssi ses
    composantes sur chaque ouvert sont des isomorphismes d'anneaux de
    sections. C'est le lemme `Hom.isIso_iff_isIso_app` de Mathlib 4 :
    `IsIso φ ↔ ∀ U, IsIso (φ.app U)`. -/

theorem isIso_iff_isIso_app_field (X : Scheme.{u}) {M N : X.Modules}
    (φ : M ⟶ N) :
    IsIso φ ↔ ∀ (U : X.Opens), IsIso (φ.app U) :=
  @AlgebraicGeometry.Scheme.Modules.Hom.isIso_iff_isIso_app X M N φ

end Grothendieck.DirectImage
