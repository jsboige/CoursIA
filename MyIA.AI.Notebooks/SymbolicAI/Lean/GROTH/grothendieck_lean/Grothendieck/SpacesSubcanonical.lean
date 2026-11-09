/-
Grothendieck hommage — Partie 71 : la sous-canonicité de la topologie des
recouvrements ouverts.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #1646).

Une topologie de Grothendieck est *sous-canonique* lorsque tout préfaisceau
représentable est un faisceau (Mathlib : `Subcanonical`). Pour le site des
ouverts d'un espace topologique, c'est le fait fondateur qui permet de voir
chaque ouvert `U` comme le faisceau qu'il représente : le plongement de
Yoneda factorise par la catégorie des faisceaux (Mathlib :
`GrothendieckTopology.yoneda`).

La preuve est ponctuelle : le recollement d'une famille compatible de
sections du représentable `yoneda.obj U` le long d'un crible couvrant `S` se
construit point par point — chaque point de `X` vit dans le domaine d'une
flèche de `S`, la famille fournit une section au-dessus de ce domaine (donc
une flèche vers `U` contenant le point) — et l'unicité est celle des flèches
entre ouverts (la catégorie `Opens T` est fine).

Références :
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Chap. II §1 (sites sous-canoniques).
  - Mathlib, `CategoryTheory.Sites.Canonical` (classe `Subcanonical`,
    constructeur `Subcanonical.of_isSheaf_yoneda_obj`).
  - Partie 68 (`Grothendieck.Spaces`) : la construction `opensTopology`.

Convention i18n (EPIC #4980 ratifiée 2026-07-04) : ce module est jumelé avec
`SpacesSubcanonical_en.lean`. Les énoncés, preuves et noms Lean restent
identiques ; seules les docstrings et les commentaires diffèrent.

Epic #1646, Phase 2 (#2159). Aucun `sorry` introduit.
-/

import Grothendieck.Spaces
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.SheafOfTypes

namespace Grothendieck

open CategoryTheory TopologicalSpace

universe u

section Contenu

variable (T : Type u) [TopologicalSpace T]

/-- Lemme central : pour tout ouvert `U`, le préfaisceau représentable
`yoneda.obj U` est un faisceau pour la topologie `opensTopology`. Le
recollement s'obtient point par point — chaque point de `X` est couvert par
une flèche du crible, dont la section de la famille compatible donne
l'appartenance à `U` — et l'unicité est l'unicité des flèches entre ouverts
(catégorie fine). -/
theorem isSheaf_yoneda_opensTopology (U : Opens T) :
    Presieve.IsSheaf (opensTopology T) (yoneda.obj U) := by
  intro X S hS xf _hcomp
  have hXU : X ≤ U := by
    intro p hp
    obtain ⟨W, f, hf, hpW⟩ := hS p hp
    have hsec : W ⟶ U := show W ⟶ U from xf f hf
    exact hsec.le hpW
  refine ⟨homOfLE hXU, ?amal, ?uniq⟩
  · intro Y f hf
    apply Subsingleton.elim (α := Y ⟶ U)
  · intro t' _ht'
    apply Subsingleton.elim (α := X ⟶ U)

/-- **Résultat central** : la topologie `opensTopology` est sous-canonique.
Tout préfaisceau représentable sur le site des ouverts d'un espace
topologique est un faisceau — chaque ouvert se voit donc comme un faisceau,
et le plongement de Yoneda factorise par la catégorie des faisceaux (voir
`GrothendieckTopology.yoneda` dans Mathlib, disponible dès cette instance). -/
theorem opensTopology_subcanonical : GrothendieckTopology.Subcanonical (opensTopology T) :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ fun U => isSheaf_yoneda_opensTopology T U

end Contenu

end Grothendieck
