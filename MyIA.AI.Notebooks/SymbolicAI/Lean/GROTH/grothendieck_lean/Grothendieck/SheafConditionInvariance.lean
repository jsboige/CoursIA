/-
Grothendieck hommage — Partie 64 : invariance de la condition de faisceau
égaliseur.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #1646).

La Partie 63 (`SheafCondition.lean`) a formalisé la **condition de faisceau
produit-égaliseur** sous trois formes (cribles, familles d'arrows, prétopologie)
et l'a reliée à la définition `Presieve.IsSheaf J P`. La Partie 7
(`SheafBasics.lean`) a montré que les conditions `IsSheaf`/`IsSeparated` sont
invariantes sous isomorphisme et équivalence naturelle de préfaisceaux.

Ce module pousse cette invariance **jusqu'à la forme égaliseur elle-même** :

  - `equalizer_sheaf_condition_iff_of_nat_equiv` : la condition de faisceau
    égaliseur (forme cribles) est préservée dans les deux sens par une
    équivalence naturelle composant par composant. C'est la version « forme
    égaliseur » de `isSheaf_iff_of_nat_equiv` de la Partie 7 — ni Mathlib ni
    la Partie 63 ne l'énoncent sous cette forme.
  - `equalizer_arrows_iff_sieve_generate` : pour une famille couvrante
    `π : (i : I) → X i ⟶ B`, la condition égaliseur (forme arrows,
    `Arrows.w`) est équivalente à la condition égaliseur (forme cribles,
    `Sieve.w`) sur le crible `Sieve.generate (ofArrows X π)` qu'elle engendre.
    C'est le pont opérationnel entre les deux formes : vérifier l'égaliseur
    sur une famille couvrante revient à le vérifier sur son crible engendré.

Références :
  - Stacks Project, tag 00VM (« sheaves on sites via equalizers »).
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Chap. III §4 — la condition de faisceau est une propriété de la classe
    d'isomorphie du préfaisceau.
  - M. Kashiwara, P. Schapira, *Categories and Sheaves* [KS06] §17.

Convention i18n (EPIC #4980 ratifiée 2026-07-04) : ce module est jumelé avec
sa version anglaise canonique dans le fichier sibling
`SheafConditionInvariance_en.lean` (modèle sibling pair, voir PR #6154 pour le
pilote sur `Utility.lean`). Les énoncés de théorèmes, les noms de lemmes, les
tactiques Lean et les références Mathlib restent en anglais (Mathlib 4,
tactic DSL standard). Seules les docstrings `/-- ... -/` et commentaires
`-- ...` diffèrent entre les deux fichiers. Anti-§D byte-identity garanti :
le namespace body est préservé bit-à-bit (énoncés et preuves
byte-identiques entre `SheafConditionInvariance.lean` et
`SheafConditionInvariance_en.lean`).

Epic #1646, Phase 2 (#2159). Tous les `sorry`s éliminés à la création.
-/

import Grothendieck.SheafBasics
import Grothendieck.SheafCondition
import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
import Mathlib.CategoryTheory.Sites.SheafOfTypes

namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

section Contenu

variable {C : Type u} [Category.{v} C]
  (J : GrothendieckTopology C)
  (P : Cᵒᵖ ⥤ Type (max v u))

/-- **Invariance de la condition égaliseur sous équivalence naturelle (forme cribles).**

Si deux préfaisceaux `P₁` et `P₂` sont reliés composant par composant par une
famille d'équivalences naturelles `e : ∀ {X}, P₁(X) ≃ P₂(X)`, alors la
condition de faisceau produit-égaliseur de `P₁` (tout crible couvrant donne un
égaliseur) équivaut à celle de `P₂`. La propriété « être un faisceau au sens de
l'égaliseur » dépend donc uniquement de la classe d'équivalence naturelle du
préfaisceau. Ceci renforce `isSheaf_iff_of_nat_equiv` de la Partie 7 : on ne se
contente pas d'une invariance de `Presieve.IsSheaf`, on la transporte dans la
forme égaliseur explicite. Référence : MM92 Chap. III §4. -/
theorem equalizer_sheaf_condition_iff_of_nat_equiv
    {P₁ : Cᵒᵖ ⥤ Type (max v u)} {P₂ : Cᵒᵖ ⥤ Type (max v u)}
    (e : ∀ ⦃X : C⦄, P₁.obj (Opposite.op X) ≃ P₂.obj (Opposite.op X))
    (he : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : P₁.obj (Opposite.op Y)),
      e (P₁.map f.op x) = P₂.map f.op (e x)) :
    (∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X →
      Nonempty (IsLimit (Fork.ofι _ (Equalizer.Sieve.w P₁ S))))
      ↔ (∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X →
        Nonempty (IsLimit (Fork.ofι _ (Equalizer.Sieve.w P₂ S)))) := by
  rw [← Grothendieck.sheaf_iff_equalizer_sieve J P₁]
  rw [← Grothendieck.sheaf_iff_equalizer_sieve J P₂]
  exact Grothendieck.isSheaf_iff_of_nat_equiv J e he

/-- **La condition égaliseur (arrows) équivaut à la condition égaliseur (crible engendré).**

Pour une famille couvrante `π : (i : I) → X i ⟶ B` d'une prétopologie, la
condition de faisceau exprimée sur la famille `ofArrows X π` (forme arrows,
`Equalizer.Presieve.Arrows.w`) est équivalente à la condition de faisceau
exprimée sur le crible `Sieve.generate (ofArrows X π)` qu'elle engendre (forme
cribles, `Equalizer.Sieve.w`). C'est le pont opérationnel entre les deux formes :
vérifier l'égaliseur sur une famille couvrante équivaut à le vérifier sur son
crible engendré — ce qui légitime de tester la condition de faisceau sur une
base de couvertures plutôt que sur tous les cribles. Référence : Stacks 00VM. -/
theorem equalizer_arrows_iff_sieve_generate [HasPullbacks C]
    {B : C} {I : Type (max v u)} (X : I → C)
    (π : (i : I) → X i ⟶ B) :
    Nonempty (IsLimit (Fork.ofι _ (Equalizer.Presieve.Arrows.w P X π))) ↔
      Nonempty (IsLimit (Fork.ofι _ (Equalizer.Sieve.w P (Sieve.generate (Presieve.ofArrows X π))))) := by
  rw [← Equalizer.Presieve.Arrows.sheaf_condition P X π]
  rw [← Equalizer.Sieve.equalizer_sheaf_condition P (Sieve.generate (Presieve.ofArrows X π))]
  exact Presieve.isSheafFor_iff_generate (Presieve.ofArrows X π)

end Contenu

end Grothendieck
