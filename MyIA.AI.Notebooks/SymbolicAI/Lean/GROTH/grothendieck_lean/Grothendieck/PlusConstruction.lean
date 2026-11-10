/-
Grothendieck hommage — Partie 62 : la construction Plus.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #1646).

La sheafification de Godement–Grothendieck s'obtient en deux passes de la
**construction Plus** : `P⁺ = P.plus J`, puis `P⁺⁺`, et le théorème
d'associativité fait de `P⁺⁺` le faisceau associé à `P`. La Partie 20
(`Sheafification.lean`) a posé l'adjonction ; celle-ci en enregistre
l'ingrédient constructif, tel que Mathlib l'expose dans
`CategoryTheory.Sites.Plus` (namespace `GrothendieckTopology`) :

  - `J.plusObj P` : le préfaisceau des sections localement compatibles —
    en chaque `X`, le colimit du diagramme de multiequalizers indexé par
    les cribles couvrants `J.Cover X`. Les hypothèses de colimites sont
    portées par les instances `HasMultiequalizer` / `HasColimitsOfShape`.
  - `J.plusMap η` : la fonctorialité en `P` — un morphisme de préfaisceaux
    induit `P⁺ ⟶ Q⁺`.
  - `J.toPlus P` : la flèche canonique `P ⟶ P⁺` (« mettre une section dans
    sa classe locale »).

Ce module enregistre les identités fondamentales :

  - `plusFunctor_obj_field`, `plusMap_id_field`, `plusMap_comp_field` :
    `plusFunctor` est un foncteur (objet, identité, composition)
  - `toPlusNatTrans_app_field`, `toPlus_naturality_field` : `toPlus` est
    une transformation naturelle `𝟭 ⟶ plusFunctor`
  - `plusMap_toPlus_field` : **l'identité algébrique clé**
    `(P ⟶ P⁺)⁺ = P⁺ ⟶ P⁺⁺` — c'est elle qui rend la double construction
    associative
  - `isoToPlus_hom_field`, `isoToPlus_inv_field` : un **faisceau est un
    point fixe de Plus** — `P ≅ P⁺` dès que `P` est un faisceau
  - `plusLift_toPlus_field`, `plusLift_unique_field`, `plus_hom_ext_field`,
    `plusMap_plusLift_field` : la **propriété universelle** — toute flèche
    `P ⟶ Q` vers un faisceau `Q` factorise de manière unique par
    `P ⟶ P⁺ ⟶ Q`, et `toPlus` est épimorphisme vis-à-vis des faisceaux
    (`plus_hom_ext` : deux flèches de `P⁺` vers un faisceau égales après
    composition par `toPlus` sont égales)

Le lien avec SGA : la construction Plus est l'exposé II.3 de SGA 4
(faisceaux associés par la procédure en deux temps de Godement 1958,
reprise par Grothendieck). La propriété universelle ci-dessous en est le
cœur opérationnel : `P⁺` est la « sheafification partielle » universelle
vis-à-vis des faisceaux.

Epic #1646, Phase 2 (#2159). Tous les `sorry`s éliminés à la création.

### i18n — convention #4980 ratifiée 2026-07-04

Ce module est jumelé avec sa version anglaise canonique dans le fichier
sibling `PlusConstruction_en.lean` (modèle sibling pair, voir PR #6154 pour
le pilote sur `Utility.lean`). Les énoncés de théorèmes, les noms de lemmes,
les tactiques Lean (`:= by`, `rfl`, `exact`, etc.) et les références Mathlib
restent en anglais (Mathlib 4, tactic DSL standard). Seules les **docstrings
`/-- ... -/`** et **commentaires `-- ...`** diffèrent entre les deux fichiers.
Anti-§D byte-identity garanti : le namespace body est préservé bit-à-bit
(énoncés et preuves byte-identiques entre `PlusConstruction.lean` et
`PlusConstruction_en.lean`).
-/

import Mathlib.CategoryTheory.Sites.Plus

namespace Grothendieck

open CategoryTheory CategoryTheory.Limits

section Bridges

variable {C : Type*} [Category C] {D : Type*} [Category D]
  (J : GrothendieckTopology C)
  [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]

/-!
## Fonctorialité de Plus

`J.plusFunctor D` envoie `P` sur `J.plusObj P` et `η` sur `J.plusMap η`.
Les trois identités ci-dessous certifient que c'est un foncteur : l'action
sur les objets est `plusObj`, l'action sur `𝟙` est `𝟙`, l'action préserve
la composition.
-/

/-- PLUS (rfl) : l'action sur les objets du foncteur Plus est `plusObj`. -/
theorem plusFunctor_obj_field (P : Cᵒᵖ ⥤ D) :
    (J.plusFunctor D).obj P = J.plusObj P := rfl

/-- PLUS (plusMap_id) : le foncteur Plus préserve l'identité. -/
theorem plusMap_id_field (P : Cᵒᵖ ⥤ D) :
    (J.plusFunctor D).map (𝟙 P) = 𝟙 (J.plusObj P) :=
  J.plusMap_id P

/-- PLUS (plusMap_comp) : le foncteur Plus préserve la composition. -/
theorem plusMap_comp_field {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) :
    (J.plusFunctor D).map (η ≫ γ) = J.plusMap η ≫ J.plusMap γ :=
  J.plusMap_comp η γ

/-!
## La flèche canonique `toPlus` est naturelle

`J.toPlus P : P ⟶ P⁺` est la composante en `P` d'une transformation
naturelle `𝟭 ⟶ plusFunctor` (`J.toPlusNatTrans D`) : commuter avec tout
morphisme de préfaisceaux.
-/

/-- PLUS (rfl) : la composante de `toPlusNatTrans` en `P` est `toPlus P`. -/
theorem toPlusNatTrans_app_field (P : Cᵒᵖ ⥤ D) :
    (J.toPlusNatTrans D).app P = J.toPlus P := rfl

/-- PLUS (toPlus_naturality) : `toPlus` est naturel — toute flèche `η`
    commute avec l'insertion dans la construction Plus. -/
theorem toPlus_naturality_field {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    η ≫ J.toPlus Q = J.toPlus P ≫ J.plusMap η :=
  J.toPlus_naturality η

/-!
## L'identité algébrique clé : `(P ⟶ P⁺)⁺ = P⁺ ⟶ P⁺⁺`

Appliquer Plus à la flèche canonique de `P` donne la flèche canonique de
`P⁺`. C'est cette identité qui rend la double construction `P⁺⁺`
compatible avec l'itération et prépare l'associativité de la
sheafification en deux passes.
-/

/-- PLUS (plusMap_toPlus) : l'identité algébrique clé — appliquer Plus à
    la flèche canonique donne la flèche canonique du Plus. -/
theorem plusMap_toPlus_field (P : Cᵒᵖ ⥤ D) :
    J.plusMap (J.toPlus P) = J.toPlus (J.plusObj P) :=
  J.plusMap_toPlus P

/-!
## Un faisceau est un point fixe de Plus

Si `P` est un faisceau pour `J`, la flèche canonique `P ⟶ P⁺` est un
isomorphisme (`J.isoToPlus`) : la construction Plus ne modifie pas les
faisceaux. C'est la cohérence du point fixe qui garantit que la double
construction s'arrête sur un objet stable.
-/

/-- PLUS (isoToPlus_hom) : pour un faisceau `P`, l'homomorphisme de
    l'iso `P ≅ P⁺` est la flèche canonique `toPlus`. -/
theorem isoToPlus_hom_field (P : Cᵒᵖ ⥤ D) (hP : Presheaf.IsSheaf J P) :
    (J.isoToPlus P hP).hom = J.toPlus P :=
  J.isoToPlus_hom P hP

/-- PLUS (isoToPlus_inv) : pour un faisceau `P`, l'inverse de l'iso
    `P ≅ P⁺` est le relevé de l'identité. -/
theorem isoToPlus_inv_field (P : Cᵒᵖ ⥤ D) (hP : Presheaf.IsSheaf J P) :
    (J.isoToPlus P hP).inv = J.plusLift (𝟙 P) hP :=
  J.isoToPlus_inv P hP

/-!
## La propriété universelle : factorisation unique par `P⁺`

Toute flèche `η : P ⟶ Q` vers un **faisceau** `Q` se factorise de manière
unique par `toPlus` : `η = toPlus P ≫ plusLift η`. Réciproquement, une
flèche de `P⁺` vers un faisceau est déterminée par sa composée avec
`toPlus` (`plus_hom_ext`) — `toPlus` est épimorphisme vis-à-vis des
faisceaux. C'est le cœur opérationnel de SGA 4 II.3 : `P⁺` est la
« sheafification partielle » universelle.
-/

/-- PLUS (toPlus_plusLift) : la factorisation — composer `toPlus` avec le
    relevé redonne la flèche de départ. -/
theorem plusLift_toPlus_field {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q)
    (hQ : Presheaf.IsSheaf J Q) :
    J.toPlus P ≫ J.plusLift η hQ = η :=
  J.toPlus_plusLift η hQ

/-- PLUS (plusLift_unique) : l'unicité du relevé — toute factorisation
    par `toPlus` coïncide avec `plusLift`. -/
theorem plusLift_unique_field {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q)
    (hQ : Presheaf.IsSheaf J Q) (γ : J.plusObj P ⟶ Q)
    (hγ : J.toPlus P ≫ γ = η) :
    γ = J.plusLift η hQ :=
  J.plusLift_unique η hQ γ hγ

/-- PLUS (plus_hom_ext) : l'extensionnalité — deux flèches de `P⁺` vers un
    faisceau, égales après composition par `toPlus`, sont égales. -/
theorem plus_hom_ext_field {P Q : Cᵒᵖ ⥤ D} (η γ : J.plusObj P ⟶ Q)
    (hQ : Presheaf.IsSheaf J Q)
    (h : J.toPlus P ≫ η = J.toPlus P ≫ γ) :
    η = γ :=
  J.plus_hom_ext η γ hQ h

/-- PLUS (plusMap_plusLift) : le relevé est compatible à la composition —
    composer puis relever égale relever la composée. -/
theorem plusMap_plusLift_field {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R)
    (hR : Presheaf.IsSheaf J R) :
    J.plusMap η ≫ J.plusLift γ hR = J.plusLift (η ≫ γ) hR :=
  J.plusMap_plusLift η γ hR

end Bridges

end Grothendieck
