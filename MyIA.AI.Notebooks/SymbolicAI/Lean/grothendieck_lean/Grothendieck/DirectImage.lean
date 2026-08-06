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

end Grothendieck.DirectImage
