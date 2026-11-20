/-
Grothendieck hommage — Partie 72 : germes et tiges (stalks) sur le site des
ouverts.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #1646).

La tige d'un préfaisceau `F` en un point `x` est la colimite des sections
au-dessus des voisinages ouverts de `x` : deux sections ont même germe
lorsqu'elles coïncident sur un voisinage assez petit. La Partie 70 a établi
que la topologie `opensTopology` est exactement celle de Mathlib — les
préfaisceaux sous-jacents sont définitionnellement les mêmes, et toute
l'API `TopCat.Presheaf` (tiges, germes, `germ_res`, `stalk_hom_ext`)
s'applique telle quelle aux préfaisceaux du site own.

Le résultat nouveau de cette partie est le calcul complet de la tige du
représentable. Pour un ouvert `U`, le préfaisceau `yoneda.obj U` (un
faisceau, par la sous-canonicité de la Partie 71) a une tige en `x` qui
est un singleton exactement lorsque `x ∈ U`, et vide sinon : la tige du
représentable détecte l'appartenance du point. C'est le premier maillon du
dictionnaire faisceaux ↔ espaces étalés — la fibre en `x` de l'espace étalé
du faisceau représenté par `U` est `U` lui-même.

La preuve va chercher chaque élément de la tige comme germe d'une section
(`exists_germ_eq` : les flèches `germ` atteignent conjointement la
colimite), puis identifie ce germe au germe de l'identité de `U` par
restriction (`germ_res`) : une section du représentable au-dessus d'un
voisinage `W` est une flèche `W ⟶ U`, l'inclusion d'un voisinage contenu
dans `U`.

Références :
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Chap. II §3 (germes et faisceaux sur un espace).
  - Mathlib, `Mathlib.Topology.Sheaves.Stalks` (tiges et germes :
    `exists_germ_eq`, `germ_res`).
  - Partie 70 (`Grothendieck.SpacesMathlib`) : le pont d'égalité des
    topologies, qui rend l'API de Mathlib applicable au site own.
  - Partie 71 (`Grothendieck.SpacesSubcanonical`) : la sous-canonicité —
    `yoneda.obj U` est un faisceau.

Convention i18n (EPIC #4980 ratifiée 2026-07-04) : ce module est jumelé avec
`Stalks_en.lean`. Les énoncés, preuves et noms Lean restent identiques ;
seules les docstrings et les commentaires diffèrent.

Epic #1646, Phase 2 (#2159). Aucun `sorry` introduit.
-/

import Grothendieck.Spaces
import Mathlib.Topology.Sheaves.Stalks

namespace Grothendieck

open CategoryTheory TopologicalSpace

universe u

section Contenu

variable (T : Type u) [TopologicalSpace T]

/-- **Tige du représentable, cas intérieur** : en un point `x ∈ U`, la tige
du préfaisceau `yoneda.obj U` — vu comme préfaisceau sur l'espace `T` via le
pont de la Partie 70 — est un singleton, dont l'unique élément est le germe
de l'identité de `U`. Tout élément de la tige est le germe d'une section
(`exists_germ_eq`) ; une telle section au-dessus d'un voisinage `W ∋ x` est
une flèche `W ⟶ U`, et son germe s'identifie au germe de `𝟙 U` par
restriction (`germ_res`). -/
@[reducible]
noncomputable def unique_stalk_yoneda (U : Opens T) {x : T} (hx : x ∈ U) :
    Unique (TopCat.Presheaf.stalk (X := TopCat.of T) (yoneda.obj U) x) := by
  have key : ∀ z : TopCat.Presheaf.stalk (X := TopCat.of T) (yoneda.obj U) x,
      z = TopCat.Presheaf.germ (X := TopCat.of T) (yoneda.obj U) U x hx (𝟙 U) := by
    intro z
    obtain ⟨W, hW, w, rfl⟩ :=
      TopCat.Presheaf.exists_germ_eq (X := TopCat.of T) (yoneda.obj U) z
    have w' : W ⟶ U := w
    have h := TopCat.Presheaf.germ_res_apply (X := TopCat.of T) (yoneda.obj U) w' x hW (𝟙 U)
    simp only [CategoryTheory.yoneda_obj_map] at h
    exact h
  exact ⟨⟨TopCat.Presheaf.germ (X := TopCat.of T) (yoneda.obj U) U x hx (𝟙 U)⟩, key⟩

/-- **Tige du représentable, cas extérieur** : si `x ∉ U`, la tige de
`yoneda.obj U` est vide — tout germe provient d'une section `W ⟶ U`
au-dessus d'un voisinage `W ∋ x`, qui forcerait `x ∈ U`. -/
theorem isEmpty_stalk_yoneda (U : Opens T) {x : T} (hx : x ∉ U) :
    IsEmpty (TopCat.Presheaf.stalk (X := TopCat.of T) (yoneda.obj U) x) := by
  refine ⟨fun z => ?_⟩
  obtain ⟨W, hW, w, -⟩ :=
    TopCat.Presheaf.exists_germ_eq (X := TopCat.of T) (yoneda.obj U) z
  have w' : W ⟶ U := w
  exact hx (w'.le hW)

/-- **La tige du représentable détecte l'appartenance** — jonction avec la
Partie 71 : `yoneda.obj U` est un faisceau (sous-canonicité de
`opensTopology`), et sa tige en `x` est habitée exactement aux points de
`U`. C'est l'ombre ponctuelle du fait que le faisceau représenté par `U`
« vit sur `U` » : la fibre en `x` de l'espace étalé associé est habitée
dans `U`, vide au-dehors. -/
theorem nonempty_stalk_yoneda_iff (U : Opens T) (x : T) :
    Nonempty (TopCat.Presheaf.stalk (X := TopCat.of T) (yoneda.obj U) x) ↔ x ∈ U := by
  constructor
  · rintro ⟨z⟩
    by_contra hx
    exact (isEmpty_stalk_yoneda T U hx).elim z
  · exact fun hx => ⟨(unique_stalk_yoneda T U hx).default⟩

end Contenu

end Grothendieck
