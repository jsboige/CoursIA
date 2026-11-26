/-
Grothendieck hommage — Partie 73 : points du site des ouverts et tiges.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #1646).

Un point d'un site au sens de SGA 4 (IV 6.3) est un foncteur fibre : un
foncteur vers `Type` dont la catégorie des éléments est cofiltrée et qui
rencontre tous les cribles couvrants. La Partie 15 (`SitePoints`) avait
établi la théorie abstraite ; la Partie 72 (`Stalks`) le calcul concret des
tiges sur le site des ouverts. Cette partie soude les deux : à tout point
`x : T` on associe un point du site `(Opens T, opensTopology T)` — la fibre
en `U` est l'ensemble (au plus unimodal) des éléments de `U` égaux à `x` —
et l'on montre que **le foncteur fibre de ce point est exactement la tige
en `x`** :

  `stalkFiberIso : (opensPoint T x).presheafFiber.obj F ≅ F.stalk x`

C'est le TODO explicite de Mathlib (`Topology/Sheaves/Points.lean` :
« Redefine the stalks functors in Stalks.lean using
`GrothendieckTopology.Point.presheafFiber` ») — l'iso est ici établi côté
lake. La preuve est un double passage à la colimite : les germes forment un
cône sur le diagramme des éléments de la fibre (via `germ_res`), les
`toPresheafFiber` forment un cône sur le diagramme des voisinages (via
`toPresheafFiber_w`), et les deux universalités se répondent via les deux
lemmes d'extension (`stalk_hom_ext`, `presheafFiber_hom_ext`). L'iso est
naturel en le préfaisceau.

Références :
  - SGA 4, IV 6.3 (points d'un site, foncteurs fibres).
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Chap. II §3, exercice (les points de l'espace redonnent les tiges).
  - Mathlib, `Mathlib.Topology.Sheaves.Points` (le point canonique
    `Opens.pointGrothendieckTopology`, dont la construction de
    `opensPoint` est la transcription sur le site own).
  - Partie 15 (`Grothendieck.SitePoints`) : foncteurs fibres abstraits.
  - Partie 70 (`Grothendieck.SpacesMathlib`) : l'égalité des topologies.
  - Partie 72 (`Grothendieck.Stalks`) : germes et tiges concrets.

Correspondance Stacks (groupe #15 de #28537 — « les points et les germes », mesure du 26/11)
--------------------------------------------------------------------------
Lecture de `AxiomMath/Stacks` sur l'**arborescence locale**
`StacksFrontier/Topology/Sheaves/` (clone sparse du dossier entier, 1756
fichiers couverts sur 1756) : un verdict « absent » signifie **aucun énoncé
de ce nom dans l'ensemble de `Topology/Sheaves/`**.

La machinerie du point de site n'est **pas** absente de Stacks : elle est
utilisée dans un seul fichier de l'arborescence lue,
`Cohomology/PerfectComplexes/FiniteFreeLocus/UniverseLift.lean`, pour un
besoin technique de relèvement d'univers. C'est là que se trouve le pendant
le plus proche de `stalkFiberIso` — d'où la classe « partiel » partout où
nous avons un énoncé là où Stacks a une construction.

| Énoncé | Classe | Référent Stacks | Ce que notre version ajoute |
|---|---|---|---|
| `opensPoint` | partiel | `Cohomology/PerfectComplexes/FiniteFreeLocus/UniverseLift.lean:325` `openNhdsEquivPointElements` (attention à l'homonyme `opensPoint` de Stacks, même fichier `:76`) | la construction du point sur le site own, avec sa structure cofiltrée |
| `mem_of_fiber` | absent | aucun (l'inverse de l'équivalence de Stacks fait le travail sans le nommer) | l'énoncé nommé de la réciproque tautologique |
| `fiberElem` | absent | aucun | la construction de l'élément canonique |
| `fiberToStalkCocone` | partiel | `UniverseLift.lean:338` `neighbourhoodColimitFunctor` ; `:344` | le cône explicite, avec sa naturalité prouvée |
| `fiberToStalk` | partiel | `UniverseLift.lean:344` (l'inverse de l'iso) | la descente universelle explicite |
| `stalkToFiberCocone` | partiel | `UniverseLift.lean:338` | le cône des `toPresheafFiber` sur le diagramme des voisinages |
| `stalkToFiber` | partiel | `UniverseLift.lean:344` `neighbourhoodColimitIsoPointFiber` | le morphisme public, en `Type u` quelconque |
| `toPresheafFiber_fiberToStalk` | partiel | `UniverseLift.lean:344` (via `Functor.Final.colimitIso`) | la formule composante par composante |
| `germ_stalkToFiber` | partiel | `UniverseLift.lean:344` | idem, dans l'autre sens |
| `stalkToFiber_comp_fiberToStalk` | partiel | `UniverseLift.lean:344` (champs `left_inv`/`right_inv` de l'iso) | l'identité de tour complet, nommée et prouvée |
| `fiberToStalk_comp_stalkToFiber` | partiel | `UniverseLift.lean:344` | idem |
| `stalkFiberIso` | partiel | `UniverseLift.lean:344` `neighbourhoodColimitIsoPointFiber` | l'iso public, en préfaisceaux de `Type u`, non `private` |
| `stalkFiberIso_naturality` | partiel | `UniverseLift.lean:344` (un `NatIso`) | l'égalité de morphismes, isolée et nommée |

Convention i18n (EPIC #4980 ratifiée 2026-07-04) : ce module est jumelé avec
`StalkPoints_en.lean`. Les énoncés, preuves et noms Lean restent identiques ;
seules les docstrings et les commentaires diffèrent.

Epic #1646, Phase 2 (#2159). Aucun `sorry` introduit.
-/

import Grothendieck.Spaces
import Grothendieck.SpacesMathlib
import Mathlib.Topology.Sheaves.Points
import Mathlib.Topology.Sheaves.Stalks

universe u

namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

section Contenu

variable (T : Type u) [TopologicalSpace T] (x : T)

/-- **Le point du site des ouverts associé à `x`** : la fibre d'un ouvert
`U` est l'ensemble des éléments de `U` égaux à `x` (un type au plus
singleton, habité exactement lorsque `x ∈ U`). La catégorie des éléments —
les voisinages ouverts de `x` et leurs inclusions — est cofiltrée ; tout
crible couvrant d'un ouvert contenant `x` contient un voisinage de `x`
(`mem_opensTopology_iff`). C'est la transcription sur le site own du point
canonique `Opens.pointGrothendieckTopology` de Mathlib, l'égalité des
topologies (Partie 70) garantissant qu'il s'agit du même point.

Correspondance Stacks — **PARTIEL** : le point du site des ouverts n'est
pas absent de Stacks, mais Stacks **utilise** celui de Mathlib
(`Opens.pointGrothendieckTopology`) au lieu de le reconstruire, et en prouve
l'équivalence avec les éléments de la fibre : le fichier
`Cohomology/PerfectComplexes/FiniteFreeLocus/UniverseLift.lean:325`
(`openNhdsEquivPointElements`,
`OpenNhds x ≌ (Opens.pointGrothendieckTopology x).fiber.Elements`), « les
voisinages ouverts d'un point sont les éléments de la fibre du point
grothendieckien en ce point ». Attention à l'homonyme : le seul `opensPoint`
de Stacks (même fichier, `:76`) est « un point d'un ouvert `U`, lu comme point
du sous-espace ouvert `U` », c'est-à-dire l'identité `x : U` — ce n'est pas un
point du site. Ce que notre version ajoute : la construction du point sur le
site **own** (avec la structure cofiltrée et la
conjointement-surjectivité construites ici), et non empruntée. -/
def opensPoint : GrothendieckTopology.Point (opensTopology T) where
  fiber.obj U := ULift.{u} (PLift (x ∈ U))
  fiber.map f := ↾fun h ↦ ⟨⟨leOfHom f h.down.down⟩⟩
  isCofiltered :=
    { nonempty := ⟨⊤, ⟨⟨by simp⟩⟩⟩
      cone_objs := by
        rintro ⟨U, ⟨⟨hU⟩⟩⟩ ⟨V, ⟨⟨hV⟩⟩⟩
        exact ⟨⟨U ⊓ V, ⟨⟨⟨hU, hV⟩⟩⟩⟩, ⟨homOfLE (by simp), rfl⟩,
          ⟨homOfLE (by simp), rfl⟩, ⟨⟩⟩
      cone_maps _ _ _ _ := ⟨_, 𝟙 _, rfl⟩ }
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective := by
    rintro U R hR ⟨⟨hU⟩⟩
    rw [mem_opensTopology_iff] at hR
    obtain ⟨V, f, hf, hV⟩ := hR x hU
    exact ⟨_, _, hf, ⟨⟨hV⟩⟩, rfl⟩

/-- Tout élément de la fibre de `U` provient d'une appartenance `x ∈ U`
(réciproque tautologique de la construction).

Correspondance Stacks — **ABSENT** : aucun énoncé de ce nom dans
`StacksFrontier/Topology/Sheaves/` (recherche `mem_of_fiber` : 0 résultat).
Le pendant le plus proche est l'`inverse` de `openNhdsEquivPointElements`
(`Cohomology/PerfectComplexes/FiniteFreeLocus/UniverseLift.lean:325`), qui
extrait d'un élément de la fibre son ouvert et son appartenance, sans nommer
l'énoncé. Ce que notre version ajoute : la réciproque tautologique
nommée. -/
theorem mem_of_fiber {U : Opens T} (p : (opensPoint T x).fiber.obj U) : x ∈ U :=
  p.down.down

/-- L'élément de la fibre codant une appartenance `x ∈ U`.

Correspondance Stacks — **ABSENT** : aucun énoncé de ce nom dans
`StacksFrontier/Topology/Sheaves/` (recherche `fiberElem` : 0 résultat) ; le
seul endroit de l'arborescence qui manipule la fibre d'un point de site est
`Cohomology/PerfectComplexes/FiniteFreeLocus/UniverseLift.lean`, où elle
n'est jamais construite élément par élément. Ce que notre version ajoute : la
construction de l'élément canonique. -/
def fiberElem {U : Opens T} (hx : x ∈ U) : (opensPoint T x).fiber.obj U :=
  ⟨⟨hx⟩⟩

variable (F : TopCat.Presheaf (Type u) (TopCat.of T))

/-- Le cône des germes sur le diagramme des éléments de la fibre : un
élément `(U, p)` vit au-dessus d'un ouvert `U` qui contient `x`, et le germe
s'y restreint (`germ_res`).

Correspondance Stacks — **PARTIEL** : Stacks dispose du même diagramme —
les éléments de la fibre du point — et de la colimite correspondante, mais
il l'obtient par une **équivalence de finitude** plutôt que par un cône
explicite : `Cohomology/PerfectComplexes/FiniteFreeLocus/UniverseLift.lean:338`
(`neighbourhoodColimitFunctor`, la colimite sur les voisinages ouverts, donc
la tige) et `:344` (`neighbourhoodColimitIsoPointFiber`), dont la preuve
passe par `Functor.Final.colimitIso E (P ⋙ M)`. Ce que notre version ajoute :
le cône des germes sur le diagramme des éléments de la fibre, avec sa
naturalité **prouvée**. -/
noncomputable def fiberToStalkCocone :
    Cocone ((CategoryOfElements.π (opensPoint T x).fiber).op ⋙ F) where
  pt := TopCat.Presheaf.stalk (X := TopCat.of T) F x
  ι.app e := TopCat.Presheaf.germ (X := TopCat.of T) F e.unop.1 x e.unop.2.down.down
  ι.naturality _ j' f := by
    obtain ⟨V, ⟨⟨hV⟩⟩⟩ := j'
    exact TopCat.Presheaf.germ_res (X := TopCat.of T) F f.unop.1 x hV

/-- **De la fibre vers la tige** : descente universelle du cône des germes,
morphisme de la fibre colimite vers la tige.

Correspondance Stacks — **PARTIEL** : le morphisme existe chez Stacks
comme l'inverse de l'iso `neighbourhoodColimitIsoPointFiber`
(`Cohomology/PerfectComplexes/FiniteFreeLocus/UniverseLift.lean:344`), mais
comme composante d'un `NatIso`, sans être posé comme une descente
universelle. Ce que notre version ajoute : la descente universelle
explicite, au sens de `colimit.desc`. -/
noncomputable def fiberToStalk :
    (opensPoint T x).presheafFiber.obj F ⟶ TopCat.Presheaf.stalk (X := TopCat.of T) F x :=
  colimit.desc _ (fiberToStalkCocone T x F)

/-- Le cône des `toPresheafFiber` sur le diagramme des voisinages : chaque
voisinage `U ∋ x` fournit une section au-dessus de `U`, donc un élément de
la fibre colimite (`toPresheafFiber_w`).

Correspondance Stacks — **PARTIEL** : le diagramme des voisinages est chez
Stacks (`Cohomology/PerfectComplexes/FiniteFreeLocus/UniverseLift.lean:338`,
`neighbourhoodColimitFunctor`, `(OpenNhds.inclusion x).op ⋙ colim`), mais
l'autre face — les `toPresheafFiber` — est la machinerie `presheafFiber` de
Mathlib, jamais rejouée par Stacks sous forme de cône. Ce que notre version
ajoute : le cône des `toPresheafFiber` sur le diagramme des voisinages, avec
sa naturalité prouvée. -/
noncomputable def stalkToFiberCocone :
    Cocone ((OpenNhds.inclusion (X := TopCat.of T) x).op ⋙ F) where
  pt := (opensPoint T x).presheafFiber.obj F
  ι.app j := (opensPoint T x).toPresheafFiber j.unop.1 ⟨⟨j.unop.2⟩⟩ F
  ι.naturality _ j' f := by
    obtain ⟨V, hV⟩ := j'
    exact (opensPoint T x).toPresheafFiber_w f.unop ⟨⟨hV⟩⟩ F

/-- **De la tige vers la fibre** : descente universelle du cône des
`toPresheafFiber`, morphisme de la tige vers la fibre.

Correspondance Stacks — **PARTIEL** : c'est l'iso
`neighbourhoodColimitIsoPointFiber`
(`Cohomology/PerfectComplexes/FiniteFreeLocus/UniverseLift.lean:344`), dont
la première composante va de la colimite des voisinages vers la fibre du
point. Ce que notre version ajoute : un morphisme public et nommé, en
préfaisceaux de `Type u` quelconque, et non en groupes abéliens. -/
noncomputable def stalkToFiber :
    TopCat.Presheaf.stalk (X := TopCat.of T) F x ⟶ (opensPoint T x).presheafFiber.obj F :=
  colimit.desc _ (stalkToFiberCocone T x F)

/-- Le morphisme `fiberToStalk` envoie le `toPresheafFiber` d'une section
au-dessus de `U` sur son germe : les deux côtés sont des composantes de
colimite (`colimit.ι_desc`).

Correspondance Stacks — **PARTIEL** : l'égalité des deux côtés est le
contenu de l'iso `neighbourhoodColimitIsoPointFiber`
(`Cohomology/PerfectComplexes/FiniteFreeLocus/UniverseLift.lean:344`), dont
les composantes sont obtenues par `Functor.Final.colimitIso` — mais Stacks
n'énonce nulle part la formule « le `toPresheafFiber` d'une section vaut son
germe ». Ce que notre version ajoute : la formule composante par
composante. -/
theorem toPresheafFiber_fiberToStalk (U : Opens T) (p : (opensPoint T x).fiber.obj U) :
    (opensPoint T x).toPresheafFiber U p F ≫ fiberToStalk T x F =
      TopCat.Presheaf.germ (X := TopCat.of T) F U x p.down.down :=
  colimit.ι_desc _ _

/-- Le morphisme `stalkToFiber` envoie chaque germe sur le `toPresheafFiber`
de la section : les deux côtés sont des composantes de colimite
(`colimit.ι_desc`).

Correspondance Stacks — **PARTIEL** : symétrique du précédent — le contenu
de l'iso `neighbourhoodColimitIsoPointFiber`
(`Cohomology/PerfectComplexes/FiniteFreeLocus/UniverseLift.lean:344`) est
l'identité des deux descriptions, mais elle n'est pas formulée « le germe
envoie sur le `toPresheafFiber` de la section ». Ce que notre version
ajoute : cette formule. -/
theorem germ_stalkToFiber (U : Opens T) (hx : x ∈ U) :
    TopCat.Presheaf.germ (X := TopCat.of T) F U x hx ≫ stalkToFiber T x F =
      (opensPoint T x).toPresheafFiber U ⟨⟨hx⟩⟩ F :=
  colimit.ι_desc _ _

section

set_option backward.isDefEq.respectTransparency false

/-- La section tige → fibre → tige est l'identité : deux morphismes sortant
de la tige coïncident dès qu'ils coïncident après tout germe
(`stalk_hom_ext`), et le triangle se ferme par les deux caractérisations
ci-dessus.

Correspondance Stacks — **PARTIEL** : l'identité de tour complet est
portée par les champs `left_inv`/`right_inv` de l'iso
`neighbourhoodColimitIsoPointFiber`
(`Cohomology/PerfectComplexes/FiniteFreeLocus/UniverseLift.lean:344`), sans
énoncé nommé ni démonstration. Ce que notre version ajoute : l'identité
nommée et prouvée, par les deux lemmes d'extension. -/
@[simp]
theorem stalkToFiber_comp_fiberToStalk :
    stalkToFiber T x F ≫ fiberToStalk T x F = 𝟙 _ := by
  apply TopCat.Presheaf.stalk_hom_ext (X := TopCat.of T)
  intro U hx
  rw [← Category.assoc, germ_stalkToFiber, toPresheafFiber_fiberToStalk,
    Category.comp_id]

/-- La section fibre → tige → fibre est l'identité : deux morphismes sortant
de la fibre colimite coïncident dès qu'ils coïncident après tout
`toPresheafFiber` (`presheafFiber_hom_ext`), et le triangle se ferme de
façon symétrique.

Correspondance Stacks — **PARTIEL** : idem pour l'autre tour, par les
champs `left_inv`/`right_inv` de l'iso
`neighbourhoodColimitIsoPointFiber`
(`Cohomology/PerfectComplexes/FiniteFreeLocus/UniverseLift.lean:344`). Ce
que notre version ajoute : l'identité nommée et prouvée par
`presheafFiber_hom_ext`. -/
@[simp]
theorem fiberToStalk_comp_stalkToFiber :
    fiberToStalk T x F ≫ stalkToFiber T x F = 𝟙 _ := by
  apply (opensPoint T x).presheafFiber_hom_ext
  intro U p
  obtain ⟨⟨h⟩⟩ := p
  rw [← Category.assoc, toPresheafFiber_fiberToStalk, germ_stalkToFiber,
    Category.comp_id]

end

/-- **La tige est le foncteur fibre du point associé** : iso canonique entre
la fibre de tout préfaisceau `F` au point du site `opensPoint T x` et la tige
topologique de `F` en `x`. Cet iso est le TODO explicite de
`Mathlib.Topology.Sheaves.Points` ; il soude la théorie abstraite de la
Partie 15 au calcul concret de la Partie 72.

Correspondance Stacks — **PARTIEL** : l'énoncé a bien son pendant exact
chez Stacks — « la colimite des voisinages d'un point est le foncteur fibre
du point grothendieckien en ce point » :
`Cohomology/PerfectComplexes/FiniteFreeLocus/UniverseLift.lean:344`
(`neighbourhoodColimitIsoPointFiber`), établi via `:325`
(`openNhdsEquivPointElements`) et `:338` (`neighbourhoodColimitFunctor`).
Trois écarts : chez Stacks l'iso est **`private`** (outil technique de
relèvement d'univers, non API) ; il porte sur des **groupes abéliens**
(`Ab.{max u v}`), non sur des préfaisceaux de `Type u` ; et il est établi sur
le site des ouverts de Mathlib, non sur notre site own. Ce que notre version
ajoute : l'iso public, en `Type u` quelconque, sur le site own. -/
noncomputable def stalkFiberIso :
    (opensPoint T x).presheafFiber.obj F ≅ TopCat.Presheaf.stalk (X := TopCat.of T) F x where
  hom := fiberToStalk T x F
  inv := stalkToFiber T x F
  hom_inv_id := fiberToStalk_comp_stalkToFiber T x F
  inv_hom_id := stalkToFiber_comp_fiberToStalk T x F

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- L'iso `stalkFiberIso` est naturel en le préfaisceau : il entrelace
`presheafFiber.map` et `stalkFunctor.map`.

Correspondance Stacks — **PARTIEL** : la naturalité en le préfaisceau est
**incluse dans le type** de l'iso de Stacks — un `NatIso`, dont la preuve de
naturalité est `NatIso.ofComponents … (by intros; rfl)`
(`Cohomology/PerfectComplexes/FiniteFreeLocus/UniverseLift.lean:344`) — mais
elle n'est ni isolée ni énoncée comme une égalité de morphismes. Ce que
notre version ajoute : l'égalité de morphismes, nommée et prouvée. -/
theorem stalkFiberIso_naturality {G : TopCat.Presheaf (Type u) (TopCat.of T)} (f : F ⟶ G) :
    (opensPoint T x).presheafFiber.map f ≫ fiberToStalk T x G =
      fiberToStalk T x F ≫
        (TopCat.Presheaf.stalkFunctor (Type u) (X := TopCat.of T) x).map f := by
  apply (opensPoint T x).presheafFiber_hom_ext
  intro U p
  rw [← Category.assoc, (opensPoint T x).toPresheafFiber_naturality f U p, Category.assoc]
  rw [toPresheafFiber_fiberToStalk T x G U p]
  rw [← Category.assoc, toPresheafFiber_fiberToStalk T x F U p]
  exact (@TopCat.Presheaf.stalkFunctor_map_germ (Type u) _ _ (X := TopCat.of T)
    F G U x p.down.down f).symm

end Contenu

end Grothendieck
