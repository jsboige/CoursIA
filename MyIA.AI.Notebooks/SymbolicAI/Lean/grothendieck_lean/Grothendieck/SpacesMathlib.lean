/-
Grothendieck hommage — Partie 70 : le pont vers Mathlib.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #1646).

La Partie 68 (`Spaces.lean`) a construit à la main, dans la langue du lake,
la topologie de Grothendieck des recouvrements ouverts d'un espace
topologique. Mathlib pose la même construction dans
`Mathlib.CategoryTheory.Sites.Spaces` (`Opens.grothendieckTopology`). Ce
module ferme la boucle : les deux définitions sont ÉGALES — pas isomorphes,
pas équivalentes : égales, car la Partie 68 a transcrit fidèlement la même
spécification de cribles.

L'égalité n'est pas une curiosité : `TopCat.Presheaf.IsSheaf`, la condition
de faisceau de Mathlib pour un espace topologique, est DÉFINIE comme la
condition de faisceau pour `Opens.grothendieckTopology ↑X`
(`Mathlib.Topology.Sheaves.Sheaf`). Le corollaire
`isSheaf_opensTopology_iff` dit donc exactement : un préfaisceau est un
faisceau sur le site own `(Opens T, opensTopology T)` si et seulement si
c'est un faisceau au sens usuel de la topologie — le cas fondateur de
Mac Lane – Moerdijk, et l'accès de tout le corpus Mathlib
(`Topology.Sheaves` : faisceification, germes, espaces étalés, foncteur
points) au site du lake, sans traduction.

  - `opensTopology_eq` : `opensTopology T = Opens.grothendieckTopology T` ;
  - `opensPretopology_eq` : la même coïncidence côté prétopologies ;
  - `isSheaf_opensTopology_iff_types` : transport de la condition de
    faisceau (faisceaux de types) ;
  - `isSheaf_opensTopology_iff` : le résultat central, à valeurs dans une
    catégorie arbitraire ;
  - `coversTop_opensTopology_iff` : transport de la notion de famille
    couvrante.

Références :
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Chap. II.
  - Mathlib, `CategoryTheory.Sites.Spaces`, `Topology.Sheaves.Sheaf`.

Convention i18n (EPIC #4980 ratifiée 2026-07-04) : ce module est jumelé avec
`SpacesMathlib_en.lean`. Les énoncés, preuves et noms Lean restent identiques ;
seules les docstrings et les commentaires diffèrent.

Epic #1646, Phase 2 (#2159). Aucun `sorry` introduit.
-/

import Grothendieck.Spaces
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.Topology.Sheaves.Sheaf

namespace Grothendieck

open CategoryTheory TopologicalSpace CategoryTheory.Limits

universe u w w'

section Contenu

variable (T : Type u) [TopologicalSpace T]

/-- **Égalité des topologies** : la topologie définie à la main en Partie 68
est exactement la topologie `Opens.grothendieckTopology` de Mathlib. La
Partie 68 a transcrit la même spécification de cribles (« tout point de
l'ouvert cible appartient au domaine d'une flèche du crible ») ; le champ de
données `sieves` coïncide définitionnellement et les champs de preuve tombent
par irrélevance des preuves. -/
theorem opensTopology_eq :
    opensTopology T = Opens.grothendieckTopology T :=
  rfl

/-- **Égalité des prétopologies** : la prétopologie own des recouvrements
ouverts (`opensPretopology`, Partie 68) est exactement la prétopologie
`Opens.pretopology` de Mathlib — le champ de données `coverings` porte la
même spécification. -/
theorem opensPretopology_eq :
    opensPretopology T = Opens.pretopology T :=
  rfl

variable {T}

/-- Transport de la condition de faisceau pour les faisceaux de types :
être un faisceau pour la topologie own ou pour celle de Mathlib est la même
chose. -/
theorem isSheaf_opensTopology_iff_types (P : (Opens T)ᵒᵖ ⥤ Type*) :
    Presheaf.IsSheaf (opensTopology T) P ↔
      Presheaf.IsSheaf (Opens.grothendieckTopology T) P := by
  rw [opensTopology_eq]

/-- **Résultat central** : la condition de faisceau sur le site
`(Opens T, opensTopology T)` est exactement la condition de faisceau usuelle
de Mathlib pour un espace topologique. `TopCat.Presheaf.IsSheaf` est
définie comme `Presheaf.IsSheaf (Opens.grothendieckTopology ↑X)`
(`Mathlib.Topology.Sheaves.Sheaf`), et le pont `opensTopology_eq` transporte
l'une dans l'autre : tout le corpus `Topology.Sheaves` (faisceification,
germes, espaces étalés, foncteur points) s'applique au site own sans
traduction. -/
theorem isSheaf_opensTopology_iff {C : Type w} [Category.{w'} C]
    (F : TopCat.Presheaf C (TopCat.of T)) :
    Presheaf.IsSheaf (opensTopology T) F ↔ TopCat.Presheaf.IsSheaf F := by
  rw [opensTopology_eq]
  rfl

/-- Transport de la notion de famille couvrante : `CoversTop` pour la
topologie own est `CoversTop` pour celle de Mathlib. Combiné aux deux
caractérisations par `IsOpenCover` (celle de la Partie 68
`coversTop_isOpenCover_iff`, celle de Mathlib `Opens.coversTop_iff`), les
deux mondes énoncent la même notion de recouvrement. -/
theorem coversTop_opensTopology_iff {ι : Type*} (U : ι → Opens T) :
    (opensTopology T).CoversTop U ↔ (Opens.grothendieckTopology T).CoversTop U := by
  rw [opensTopology_eq]

end Contenu

end Grothendieck
