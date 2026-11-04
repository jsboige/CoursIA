/-
Grothendieck hommage — Partie 65 : caractérisation de la condition de faisceau
égaliseur.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #1646).

La Partie 63 (`SheafCondition.lean`) a relié la **condition de faisceau
produit-égaliseur** à la définition `Presieve.IsSheaf J P`. La Partie 7
(`SheafBasics.lean`) a montré que `IsSheaf`/`IsSeparated` descendent le long de
`J₁ ≤ J₂`. Ce module pousse ces deux fils **dans la forme égaliseur explicite** :

  - `equalizer_sheaf_condition_mono` : la condition égaliseur descend
    monotoniquement — si `J₁ ≤ J₂`, alors tout préfaisceau satisfaisant la
    condition égaliseur pour la topologie la plus fine `J₂` la satisfait aussi
    pour `J₁`. C'est la version « forme égaliseur » de `isSheaf_of_le` (Partie 7).
  - `equalizer_sheaf_condition_iff_separated_compatible` : la condition
    égaliseur équivaut exactement à la conjonction de la **séparation** et de
    l'**existence d'un recollement** pour toute famille compatible. C'est la
    version « forme égaliseur » de
    `isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor` (Mathlib) : un
    préfaisceau est un faisceau au sens de l'égaliseur ssi il est séparé et
    toute famille compatible s'amalgame — la séparation seule garantit
    l'unicité, l'existence est précisément ce qu'ajoute la condition de faisceau.

Références :
  - Stacks Project, tag 00VM (« sheaves on sites via equalizers »).
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Chap. III §4 — la condition de faisceau comme recollement + séparation.
  - M. Kashiwara, P. Schapira, *Categories and Sheaves* [KS06] §17.

Convention i18n (EPIC #4980 ratifiée 2026-07-04) : ce module est jumelé avec
sa version anglaise canonique dans le fichier sibling
`SheafConditionCharacterization_en.lean` (modèle sibling pair, voir PR #6154
pour le pilote sur `Utility.lean`). Les énoncés de théorèmes, les noms de
lemmes, les tactiques Lean et les références Mathlib restent en anglais
(Mathlib 4, tactic DSL standard). Seules les docstrings `/-- ... -/` et
commentaires `-- ...` diffèrent entre les deux fichiers. Anti-§D byte-identity
garanti : le namespace body est préservé bit-à-bit (énoncés et preuves
byte-identiques entre `SheafConditionCharacterization.lean` et
`SheafConditionCharacterization_en.lean`).

Epic #1646, Phase 2 (#2159). Tous les `sorry`s éliminés à la création.
-/

import Grothendieck.SheafBasics
import Grothendieck.SheafCondition
import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.CategoryTheory.Sites.SheafOfTypes

namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

section Contenu

variable {C : Type u} [Category.{v} C]
  (J : GrothendieckTopology C)
  (P : Cᵒᵖ ⥤ Type (max v u))

/-- **La condition égaliseur descend le long de `J₁ ≤ J₂`.**

Si `J₁ ≤ J₂` (toute crible couvrant pour `J₁` est couvrant pour `J₂`), alors un
préfaisceau qui satisfait la condition de faisceau produit-égaliseur pour la
topologie la plus fine `J₂` la satisfait aussi pour `J₁`. C'est la version
« forme égaliseur » de `isSheaf_of_le` de la Partie 7 : la propriété d'être un
faisceau au sens de l'égaliseur est monotone décroissante en la topologie.
Référence : MM92 Chap. III §4 ; Stacks 00VM. -/
theorem equalizer_sheaf_condition_mono {J₁ : GrothendieckTopology C} {J₂ : GrothendieckTopology C}
    (h : J₁ ≤ J₂) :
    (∀ ⦃X : C⦄ (S : Sieve X), S ∈ J₂ X → Nonempty (IsLimit (Fork.ofι _ (Equalizer.Sieve.w P S))))
      → (∀ ⦃X : C⦄ (S : Sieve X), S ∈ J₁ X → Nonempty (IsLimit (Fork.ofι _ (Equalizer.Sieve.w P S)))) := by
  intro h₂
  rw [← Grothendieck.sheaf_iff_equalizer_sieve J₁ P]
  rw [← Grothendieck.sheaf_iff_equalizer_sieve J₂ P] at h₂
  exact Grothendieck.isSheaf_of_le h h₂

/-- **La condition égaliseur équivaut à : séparé et toute famille compatible s'amalgame.**

Un préfaisceau est un faisceau au sens produit-égaliseur ssi il est **séparé**
(pour tout crible couvrant, toute famille compatible a au plus un recollement)
**et** toute famille compatible s'amalgame (au moins un recollement). La
séparation porte l'unicité ; l'existence du recollement est précisément la
condition supplémentaire qu'apporte la condition de faisceau. C'est la version
« forme égaliseur » de `isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor`
(Mathlib). Référence : MM92 Chap. III §4 ; Stacks 00VM. -/
theorem equalizer_sheaf_condition_iff_separated_compatible :
    (∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → Nonempty (IsLimit (Fork.ofι _ (Equalizer.Sieve.w P S))))
      ↔ Presieve.IsSeparated J P ∧
        (∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → ∀ x : Presieve.FamilyOfElements P (S : Presieve X),
          x.Compatible → ∃ t, x.IsAmalgamation t) := by
  rw [← Grothendieck.sheaf_iff_equalizer_sieve J P]
  constructor
  · intro h
    constructor
    · intro X S hS
      exact (Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor.2 (h S hS)).1
    · intro X S hS x hx
      exact (Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor.2 (h S hS)).2 x hx
  · intro h X S hS
    exact Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor.1 ⟨h.1 S hS, h.2 S hS⟩

end Contenu

end Grothendieck
