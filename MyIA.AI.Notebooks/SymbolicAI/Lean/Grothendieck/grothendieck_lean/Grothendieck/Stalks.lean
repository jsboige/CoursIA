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
  - `AxiomMath/Stacks`, `StacksFrontier/Topology/Sheaves/Skyscraper/Stalk.lean`
    (tag 009B) : la tige du **gratte-ciel**, seul énoncé de Stacks portant
    la même architecture « détecteur d'appartenance ». Voir la section
    « Correspondance Stacks » en fin de module.
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Chap. II §3 (germes et faisceaux sur un espace).
  - Mathlib, `Mathlib.Topology.Sheaves.Stalks` (tiges et germes :
    `exists_germ_eq`, `germ_res`).
  - Partie 70 (`Grothendieck.SpacesMathlib`) : le pont d'égalité des
    topologies, qui rend l'API de Mathlib applicable au site own.
  - Partie 71 (`Grothendieck.SpacesSubcanonical`) : la sous-canonicité —
    `yoneda.obj U` est un faisceau.

Correspondance Stacks (groupe #14 de #28537 — « les tiges », mesure du 26/11)
--------------------------------------------------------------------------
Lecture de `AxiomMath/Stacks` sur l'**arborescence locale**
`StacksFrontier/Topology/Sheaves/` (clone sparse du dossier entier) : la
couverture est ici bien plus large que celle des relevés du 22/11 et du
25/11, qui ne pouvaient lire que quelques fichiers par l'API `contents`
(l'arbre récursif de GitHub est tronqué et `Topology/Sheaves` n'y apparaît
pas). Un verdict « absent » signifie donc : **aucun énoncé de ce nom dans
l'ensemble de `Topology/Sheaves/`**.

| Énoncé | Classe | Référent Stacks | Ce que notre version ajoute |
|---|---|---|---|
| `unique_stalk_yoneda` | absent | plus proche : `Skyscraper/Stalk.lean:36` `skyscraperPresheafStalkOfSpecializes` (009B) | l'unicité **et** la description de l'élément (le germe de l'identité de `U`) |
| `isEmpty_stalk_yoneda` | absent | plus proche : `Skyscraper/Stalk.lean:41` `skyscraperPresheafStalkOfNotSpecializes` (009B) | le **raisonnement** du vide, là où Stacks énonce une égalité de groupes |
| `nonempty_stalk_yoneda_iff` | absent | aucun | la chaîne complète « appartenance ⇔ non-vide » |

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
restriction (`germ_res`).

Correspondance Stacks — **ABSENT** : Stacks ne calcule pas la tige du
représentable. Le seul énoncé de la même forme — « la tige vaut un objet
trivialement calculable qui détecte l'appartenance » — est celui du
**gratte-ciel** : `StacksFrontier/Topology/Sheaves/Skyscraper/Stalk.lean:36`
(`skyscraperPresheafStalkOfSpecializes`, tag 009B) dit que la tige du
préfaisceau du gratte-ciel en `x` est le groupe sous-jacent lorsque `x`
spécialise le point, et `:41` (`skyscraperPresheafStalkOfNotSpecializes`)
qu'elle est vide sinon. Même architecture, objet différent : le grate-ciel et
non le représentable. Ce que notre version ajoute : l'**unicité** et la
**description** de l'élément — le germe de l'identité de `U` — là où Stacks
ne donne que l'égalité de la tige avec un groupe. -/
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
au-dessus d'un voisinage `W ∋ x`, qui forcerait `x ∈ U`.

Correspondance Stacks — **ABSENT** : même absence que ci-dessus, le pendant
étant `Skyscraper/Stalk.lean:41` (`skyscraperPresheafStalkOfNotSpecializes`),
qui vide la tige du grate-ciel hors des points spécialisants. Ce que notre
version ajoute : le **raisonnement** du vide — une flèche `W ⟶ U` au-dessus
d'un voisinage de `x` forcerait `x ∈ U` — là où Stacks énonce une égalité
de groupes. -/
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
dans `U`, vide au-dehors.

Correspondance Stacks — **ABSENT** : le « détecteur d'appartenance » du
gratte-ciel (`Skyscraper/Stalk.lean:36` et `:41`) est le seul énoncé voisin ;
aucun Stacks n'énonce l'équivalence « la tige du représentable est non vide
si et seulement si le point est dans l'ouvert ». Ce que notre version
ajoute : la **chaîne complète** — appartenance ⇔ non-vide — là où Stacks
donne deux faits disjoints (vide / non vide) sur un autre objet. -/
theorem nonempty_stalk_yoneda_iff (U : Opens T) (x : T) :
    Nonempty (TopCat.Presheaf.stalk (X := TopCat.of T) (yoneda.obj U) x) ↔ x ∈ U := by
  constructor
  · rintro ⟨z⟩
    by_contra hx
    exact (isEmpty_stalk_yoneda T U hx).elim z
  · exact fun hx => ⟨(unique_stalk_yoneda T U hx).default⟩

end Contenu

end Grothendieck
