/-
Grothendieck hommage — Partie 67 : le spectre de surjectivité locale.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #1646).

La Partie 66 a étudié les topologies pour lesquelles un préfaisceau est un
faisceau. Ce module passe des objets aux morphismes : pour quelles topologies
un morphisme de préfaisceaux est-il localement surjectif ?

Pour `f : F ⟶ G`, Mathlib associe à chaque section `s` de `G` le crible
`imageSieve f s` des restrictions qui admettent un antécédent local. Le
morphisme est localement surjectif pour `J` lorsque chacun de ces cribles est
`J`-couvrant. Cette définition fait apparaître un spectre **croissant** dans
le treillis des topologies, dual du spectre décroissant de faisceaux de la
Partie 66 :

  - `isLocallySurjective_top` : tout morphisme est localement surjectif pour
    la topologie maximale, qui déclare tout crible couvrant ;
  - `isLocallySurjective_sup` : la propriété pour le premier terme suffit
    pour leur suprémum ;
  - `isLocallySurjective_iSup` : de même, un témoin dans une famille suffit
    pour son suprémum ;
  - `isLocallySurjective_bot_iff` : à l'autre extrémité, la surjectivité locale
    pour la topologie minimale équivaut à la surjectivité objet par objet.

Le dernier résultat donne le contenu géométrique du spectre : sous la
topologie minimale, le seul recouvrement est le crible maximal, donc un
antécédent « local » au-dessus de l'identité est déjà un antécédent global.

Références :
  - Stacks Project, tag 00WL (« Injective and surjective maps of sheaves »).
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Chap. III §4.
  - Mathlib, `CategoryTheory.Sites.LocallySurjective`.

Convention i18n (EPIC #4980 ratifiée 2026-07-04) : ce module est jumelé avec
`LocalSurjectivitySpectrum_en.lean`. Les énoncés, preuves et noms Lean restent
identiques ; seules les docstrings et les commentaires diffèrent.

Epic #1646, Phase 2 (#2159). Aucun `sorry` introduit.
-/

import Grothendieck.TopologyLattice
import Mathlib.CategoryTheory.Sites.LocallySurjective

namespace Grothendieck

open CategoryTheory CategoryTheory.GrothendieckTopology Opposite

universe u v w

section Contenu

variable {C : Type u} [Category.{v} C]
variable {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G)

/-- Tout morphisme de préfaisceaux est localement surjectif pour la topologie
maximale : chaque crible image y est couvrant par définition. -/
theorem isLocallySurjective_top :
    Presheaf.IsLocallySurjective (⊤ : GrothendieckTopology C) f := by
  constructor
  intro U s
  exact GrothendieckTopology.top_covering

/-- Le spectre de surjectivité locale est croissant vers tout suprémum binaire.

La couverture du crible image pour `J₁` se transporte vers `J₁ ⊔ J₂` par
l'inclusion canonique `J₁ ≤ J₁ ⊔ J₂`. -/
theorem isLocallySurjective_sup {J₁ J₂ : GrothendieckTopology C}
    (h : Presheaf.IsLocallySurjective J₁ f) :
    Presheaf.IsLocallySurjective (J₁ ⊔ J₂) f := by
  exact Presheaf.isLocallySurjective_of_le le_sup_left f h

/-- Le spectre de surjectivité locale est croissant vers un suprémum indexé.

Un témoin dans la famille fournit la couverture du crible image, puis
`le_iSup` la transporte vers la topologie engendrée par tous les membres. -/
theorem isLocallySurjective_iSup {ι : Type*} {J : ι → GrothendieckTopology C}
    (h : ∃ i, Presheaf.IsLocallySurjective (J i) f) :
    Presheaf.IsLocallySurjective (⨆ i, J i) f := by
  obtain ⟨i, hi⟩ := h
  exact Presheaf.isLocallySurjective_of_le (le_iSup J i) f hi

/-- Pour la topologie minimale, la surjectivité locale équivaut à la
surjectivité objet par objet.

Dans le sens direct, `bot_covering` force chaque crible image à être maximal ;
l'identité appartient donc au crible, ce qui fournit un antécédent global. Le
sens réciproque est la construction de Mathlib à partir des applications
surjectives. -/
theorem isLocallySurjective_bot_iff :
    Presheaf.IsLocallySurjective (⊥ : GrothendieckTopology C) f ↔
      ∀ U, Function.Surjective (f.app U) := by
  constructor
  · intro h U s
    have hs : Presheaf.imageSieve f s = ⊤ :=
      GrothendieckTopology.bot_covering.mp (h.imageSieve_mem s)
    have hid : Presheaf.imageSieve f s (𝟙 U.unop) := by
      rw [hs]
      trivial
    obtain ⟨t, ht⟩ := hid
    exact ⟨t, by simpa using ht⟩
  · intro h
    exact Presheaf.isLocallySurjective_of_surjective (⊥ : GrothendieckTopology C) f h

end Contenu

end Grothendieck
