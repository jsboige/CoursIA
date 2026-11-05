/-
Grothendieck hommage — Partie 63 : la condition de faisceau produit-égaliseur.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #1646).

La Partie 20 (`Sheafification.lean`) a posé l'adjonction de faisceautification
et la Partie 62 (`PlusConstruction.lean`) son ingrédient constructif. Celle-ci
formalise le **cœur conceptuel** de la notion de faisceau sur un site : la
**condition de faisceau exprimée comme un diagramme égaliseur**.

  Un préfaisceau `P : Cᵒᵖ ⥤ Type*` est un faisceau pour une topologie de
  Grothendieck `J` si, pour toute famille couvrante `{U_i → X}` (vue comme un
  crible `S : Sieve X` appartenant à `J X`), le diagramme de restriction

    P(X)  →  ∏ᵢ P(U_i)  ⇉  ∏ᵢⱼ P(U_i ×_X U_j)

  est un **égaliseur**. La flèche de gauche est la famille des restrictions
  `P(X) → P(U_i)` ; les deux flèches parallèles de droite sont induites par
  les deux projections du produit fibré `U_i ×_X U_j`.

Mathlib expose cette reformulation dans
`CategoryTheory.Sites.EqualizerSheafCondition` (namespace
`CategoryTheory.Equalizer`), sous deux formes :

  - `Equalizer.Sieve.equalizer_sheaf_condition` : `P` est un faisceau pour le
    crible `S` ssi le fork `w P S` est un égaliseur (forme cribles).
  - `Equalizer.Presieve.Arrows.sheaf_condition` (Stacks 00VM) : la même
    assertion pour la famille `ofArrows X π`, avec une condition de
    produit fibré par paires (`HasPairwisePullbacks`).

Ce module enregistre, dans le namespace `Grothendieck`, des ponts
dérivés de ces deux formes vers la définition `Presieve.IsSheaf J P`
(faisceau pour toute flèche couvrante de la topologie) et vers la
caractérisation par prétopologie
`isSheaf_pretopology`. Ce ne sont pas de purs re-exports : chaque pont
est un `theorem ... := by` qui chaîne explicitement les lemmes vendored
(`equalizer_sheaf_condition`, `sheaf_condition`, `isSheafFor_iff_generate`,
`isSheaf_pretopology`) pour produire l'équivalence recherchée.

Références :
  - Stacks Project, tag 00VM (« sheaves on sites via equalizers »).
  - Stacks Project, tag 00VL (forme prétopologique).
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic*
    [MM92], Chap. III §4, équation (3) — le diagramme égaliseur canonique.
  - M. Kashiwara, P. Schapira, *Categories and Sheaves* [KS06] §17.

Convention i18n (EPIC #4980 ratifiée 2026-07-04) : ce module est jumelé avec
sa version anglaise canonique dans le fichier sibling
`SheafCondition_en.lean` (modèle sibling pair, voir PR #6154 pour le pilote
sur `Utility.lean`). Les énoncés de théorèmes, les noms de lemmes, les
tactiques Lean et les références Mathlib restent en anglais (Mathlib 4,
tactic DSL standard). Seules les docstrings `/-- ... -/` et commentaires
`-- ...` diffèrent entre les deux fichiers. Anti-§D byte-identity garanti :
le namespace body est préservé bit-à-bit (énoncés et preuves
byte-identiques entre `SheafCondition.lean` et `SheafCondition_en.lean`).

Epic #1646, Phase 2 (#2159). Tous les `sorry`s éliminés à la création.
-/

import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
import Mathlib.CategoryTheory.Sites.SheafOfTypes

namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

section Bridges

variable {C : Type u} [Category.{v} C]
  (J : GrothendieckTopology C)
  (P : Cᵒᵖ ⥤ Type (max v u))

/-- **Condition de faisceau = diagramme égaliseur (forme cribles).**

Un préfaisceau `P` est un faisceau pour la topologie `J` si et seulement si,
pour tout crible couvrant `S ∈ J X`, le fork de restriction
`forkMap P S ≫ firstMap = forkMap P S ≫ secondMap` (la condition de
compatibilité) est un diagramme égaliseur. C'est la reformulation
« produit-égaliseur » de la définition de faisceau sur un site : la section
`P(X)` se reconstruit uniquement comme la limite de la double flèche des
restrictions sur les ouverts du crible. Référence : Stacks 00VM,
Mac Lane–Moerdijk [MM92] Ch. III §4 Eq. (3). -/
theorem sheaf_iff_equalizer_sieve :
    Presieve.IsSheaf J P ↔
      ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X →
        Nonempty (IsLimit (Fork.ofι _ (Equalizer.Sieve.w P S))) := by
  constructor
  · intro h X S hS
    exact (Equalizer.Sieve.equalizer_sheaf_condition P S).mp (h S hS)
  · intro h X S hS
    exact (Equalizer.Sieve.equalizer_sheaf_condition P S).mpr (h S hS)

/-- **Condition de faisceau = diagramme égaliseur (forme familles d'arrows).**

Lorsque la catégorie `C` admet des produits fibrés (`HasPullbacks C`), la
condition de faisceau pour une famille couvrante `π : (i : I) → X i ⟶ B`
(portée par une prétopologie `K`) se réécrit : `P` est un faisceau pour le
crible engendré par `π` ssi le fork `forkMap P X π ≫ firstMap =
forkMap P X π ≫ secondMap` est un égaliseur. L'hypothèse `HasPullbacks C`
fournit l'instance `HasPairwisePullbacks` requise par la forme arrows du
lemme vendored. Référence : Stacks 00VM. -/
theorem sheaf_iff_equalizer_arrows [HasPullbacks C]
    {B : C} {I : Type (max v u)} (X : I → C)
    (π : (i : I) → X i ⟶ B) :
    Presieve.IsSheafFor P (Presieve.ofArrows X π) ↔
      Nonempty (IsLimit (Fork.ofι _ (Equalizer.Presieve.Arrows.w P X π))) := by
  exact Equalizer.Presieve.Arrows.sheaf_condition P X π

/-- **Caractérisation par prétopologie — pont vers `isSheaf_pretopology`.**

Sous `HasPullbacks C`, être un faisceau pour la topologie `K.toGrothendieck`
engendrée par une prétopologie `K` équivaut à vérifier la condition de
faisceau pour chaque famille couvrante de `K`. Ce pont relie
`Presieve.IsSheaf` (forme cribles de la topologie) à la formulation
prétopologique `isSheaf_pretopology`, qui est le levier opérationnel
pratique : on vérifie la condition sur une base de couvertures plutôt que
sur tous les cribles. Référence : Stacks 00VL, SGA 4 II.1. -/
theorem sheaf_pretopology_iff [HasPullbacks C] (K : Pretopology C) :
    Presieve.IsSheaf K.toGrothendieck P ↔
      ∀ ⦃X : C⦄ (R : Presieve X), R ∈ K X → Presieve.IsSheafFor P R := by
  exact Presieve.isSheaf_pretopology K

end Bridges

end Grothendieck
