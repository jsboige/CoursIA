/-
Grothendieck hommage — Partie 66 : le spectre de topologies d'un préfaisceau.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #1646).

La question directrice : **pour quelles topologies un préfaisceau donné
est-il un faisceau ?** La Partie 65 (`SheafConditionCharacterization.lean`)
a caractérisé la condition égaliseur pour une topologie FIXÉE ; la Partie 7
(`SheafBasics.lean`) a montré que `IsSheaf` descend le long de `J₁ ≤ J₂`
(`isSheaf_of_le`). Ce module fait porter la question sur la COORDONNÉE
topologie — le « spectre » `Spec(P) = {J | P est un faisceau pour J}` :

  - `isSheaf_const_unit` : le préfaisceau constant singleton est un faisceau
    pour TOUTE topologie — son spectre est le treillis tout entier. C'est
    l'objet terminal approché du monde des faisceaux : aucune donnée à
    recoller, donc aucun recollement ne peut échouer.
  - `isSheaf_inf` : le spectre est stable par infimum binaire — si `P` est
    un faisceau pour `J₁` et pour `J₂`, il l'est pour `J₁ ⊓ J₂`.
  - `isSheaf_iInf` : la version indexée — le spectre est stable par
    infimum arbitraire (famille non vide). L'hypothèse `Nonempty ι` est
    nécessaire : sur une famille vide, `⨅ i, J i` est la topologie
    maximale (tout crible couvre), pour laquelle tous les préfaisceaux ne
    sont pas des faisceaux.

Les trois preuves sont des compositions directes : `Subsingleton` pour le
premier, `Grothendieck.TopologyLattice.inf_covering` / `iInf_covering`
(Partie du lake, décomposition de l'appartenance à l'infimum) pour les deux
autres.

Références :
  - Stacks Project, tag 00Z8 (« sheaves and sieves »).
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Chap. III §4 — la dépendance en la topologie de la condition de faisceau.
  - M. Kashiwara, P. Schapira, *Categories and Sheaves* [KS06] §17.

Convention i18n (EPIC #4980 ratifiée 2026-07-04) : ce module est jumelé avec
sa version anglaise canonique dans le fichier sibling
`SheafTopologySpectrum_en.lean` (modèle sibling pair, voir PR #6154
pour le pilote sur `Utility.lean`). Les énoncés de théorèmes, les noms de
lemmes, les tactiques Lean et les références Mathlib restent en anglais
(Mathlib 4, tactic DSL standard). Seules les docstrings `/-- ... -/` et
commentaires `-- ...` diffèrent entre les deux fichiers. Anti-§D byte-identity
garanti : le namespace body est préservé bit-à-bit (énoncés et preuves
byte-identiques entre `SheafTopologySpectrum.lean` et
`SheafTopologySpectrum_en.lean`).

Epic #1646, Phase 2 (#2159). Tous les `sorry`s éliminés à la création.
-/

import Grothendieck.SheafBasics
import Grothendieck.TopologyLattice
import Mathlib.CategoryTheory.Sites.SheafOfTypes

namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

section Contenu

variable {C : Type u} [Category.{v} C]

/-- **Le préfaisceau constant singleton est un faisceau pour toute topologie.**

Pour le foncteur constant sur `PUnit` (le préfaisceau « sans donnée »), la
condition de faisceau est vide : toute famille compatible s'amalgame en
l'unique élément, et l'amalgame est unique car les valeurs sont des
singletons. Le spectre de topologies de ce préfaisceau est donc le treillis
tout entier — c'est la forme primitive du fait que l'objet terminal du
topos de préfaisceaux est un faisceau. Référence : MM92 Chap. III §4. -/
theorem isSheaf_const_unit (J : GrothendieckTopology C) :
    Presieve.IsSheaf J ((Functor.const Cᵒᵖ).obj PUnit.{max v u + 1}) := by
  haveI : ∀ Z : Cᵒᵖ, Subsingleton (((Functor.const Cᵒᵖ).obj PUnit.{max v u + 1}).obj Z) :=
    fun _ => inferInstanceAs (Subsingleton PUnit)
  intro X S hS x hx
  refine ⟨PUnit.unit, ?_, ?_⟩
  · intro Y f hf
    exact Subsingleton.elim _ _
  · intro t ht
    exact Subsingleton.elim _ _

/-- **Le spectre de topologies d'un préfaisceau est stable par infimum binaire.**

Si `P` est un faisceau pour `J₁` et pour `J₂`, il est un faisceau pour
`J₁ ⊓ J₂` : couvrir par l'infimum, c'est couvrir par les deux (Partie
`TopologyLattice` du lake, `inf_covering`), et l'hypothèse la plus fine
suffit. Version « spectre » du `isSheaf_of_le` de la Partie 7 : l'ensemble
des topologies pour lesquelles `P` est un faisceau est un sous-treillis
pour les infima. Référence : MM92 Chap. III §4. -/
theorem isSheaf_inf {J₁ J₂ : GrothendieckTopology C} {P : Cᵒᵖ ⥤ Type (max v u)}
    (h₁ : Presieve.IsSheaf J₁ P) (_h₂ : Presieve.IsSheaf J₂ P) :
    Presieve.IsSheaf (J₁ ⊓ J₂) P := by
  intro X S hS
  exact h₁ S (TopologyLattice.inf_covering S |>.1 hS).1

/-- **Le spectre de topologies est stable par infimum arbitraire (famille non vide).**

Si `P` est un faisceau pour chaque `J i`, il est un faisceau pour `⨅ i, J i`.
L'hypothèse `Nonempty ι` est nécessaire : sur une famille vide l'infimum est
la topologie maximale (tout crible couvre), qui n'admet pas tous les
préfaisceaux comme faisceaux. Référence : MM92 Chap. III §4. -/
theorem isSheaf_iInf {ι : Type*} [Nonempty ι] {J : ι → GrothendieckTopology C}
    {P : Cᵒᵖ ⥤ Type (max v u)}
    (h : ∀ i, Presieve.IsSheaf (J i) P) :
    Presieve.IsSheaf (⨅ i, J i) P := by
  intro X S hS
  exact h (Classical.arbitrary ι) S ((TopologyLattice.iInf_covering J S).1 hS (Classical.arbitrary ι))

end Contenu

end Grothendieck
