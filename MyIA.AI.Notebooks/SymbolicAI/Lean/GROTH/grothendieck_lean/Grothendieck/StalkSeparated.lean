/-
Grothendieck hommage — Partie 74 : les tiges détectent l'égalité des sections.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #1646).

La Partie 72 (`Stalks`) a calculé les tiges sur le site des ouverts, la
Partie 73 (`StalkPoints`) a identifié la tige au foncteur fibre du point du
site. Cette partie établit la propriété de **détection** : deux sections
d'un préfaisceau de types **séparé** qui ont mêmes germes en tout point
sont égales.

  `eq_of_germ_eq_of_isSeparated : (∀ x ∈ U, germe_x s = germe_x t) → s = t`

L'assemblage est à deux leviers, tous deux déjà disponibles :

  - `TopCat.Presheaf.germ_eq` (Mathlib, valable pour TOUT préfaisceau) :
    des germes égaux en `x` donnent un voisinage `W ∋ x` sur lequel les
    restrictions de `s` et `t` coïncident ;
  - `Presheaf.IsSeparated` (le prédicat de séparabilité bundlé de Mathlib,
    dont le cœur est `IsSeparatedFor.ext`) : pour un préfaisceau séparé,
    deux sections dont les restrictions coïncident sur chaque flèche d'un
    crible couvrant sont égales.

Le crible témoin est construit à la main : les voisinages `V p` choisis par
axiome de choix couvrent `U`, et le crible « être dominé par l'un des
`V p` » couvre `U` pour `opensTopology T` (Partie 70, l'appartenance s'y
lit par `mem_opensTopology_iff`).

Deux corollaires complètent la tranche :

  - `eq_of_germ_eq_of_isSheaf` : pour un FAISCEAU de types, la même
    conclusion sans les hypothèses de limites qu'exige le `section_ext` de
    Mathlib (`[HasLimits C]`, `[PreservesLimits (forget C)]`,
    `[(forget C).ReflectsIsomorphisms]`) — tout faisceau est séparé
    (`Presheaf.IsSheaf.isSeparated`), et le pont `isSheaf_opensTopology_iff`
    (Partie 70) transporte la condition de faisceau de Mathlib vers le
    site own ;
  - `injective_germ_family_of_isSeparated` : reformulation combinatoire —
    l'application « famille des germes » `s ↦ (germe_x s)ₓ` est injective.
    C'est la brique ponctuelle du dictionnaire faisceaux ↔ espaces étalés :
    une section est déterminée par ses valeurs germinales.

Références :
  - SGA 4, II.5 (condition de séparabilité sur un site).
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Chap. II §6 (sections égales ssi égales localement).
  - Mathlib, `Mathlib.Topology.Sheaves.Stalks` (`germ_eq`, et `section_ext`
    — la version faisceau, dont celle-ci est le relâchement séparé).
  - Partie 70 (`Grothendieck.SpacesMathlib`) : `opensTopology_eq`,
    `isSheaf_opensTopology_iff`.
  - Partie 72 (`Grothendieck.Stalks`) : germes et tiges concrets.
  - Partie 73 (`Grothendieck.StalkPoints`) : la tige comme foncteur fibre.

Convention i18n (EPIC #4980 ratifiée 2026-07-04) : ce module est jumelé avec
`StalkSeparated_en.lean`. Les énoncés, preuves et noms Lean restent identiques ;
seules les docstrings et les commentaires diffèrent.

Epic #1646, Phase 2 (#2159). Aucun `sorry` introduit.
-/

import Grothendieck.Spaces
import Grothendieck.SpacesMathlib
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.Topology.Sheaves.Stalks

universe u

namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

section Contenu

variable (T : Type u) [TopologicalSpace T]

/-- **Les tiges détectent l'égalité des sections (cas séparé)** : deux
sections d'un préfaisceau de types séparé pour la topologie des ouverts qui
ont mêmes germes en tout point de `U` sont égales. La preuve choisit, pour
chaque point, un voisinage où les restrictions coïncident (`germ_eq` —
valable pour tout préfaisceau), forme le crible des ouverts dominés par
l'un de ces voisinages — crible couvrant pour `opensTopology T` — puis
conclut en appliquant le prédicat de séparabilité bundlé
(`Presheaf.IsSeparated`, dont le cœur est `IsSeparatedFor.ext`). C'est le
relâchement séparé du `section_ext` de Mathlib, qui exige un faisceau
complet. Référence : [MM92] Chap. II §6. -/
theorem eq_of_germ_eq_of_isSeparated (F : TopCat.Presheaf (Type u) (TopCat.of T))
    (hF : Presheaf.IsSeparated (J := opensTopology T) F)
    {U : Opens T} {s t : F.obj (op U)}
    (h : ∀ (x : T) (hx : x ∈ U),
      TopCat.Presheaf.germ (X := TopCat.of T) F U x hx s =
        TopCat.Presheaf.germ (X := TopCat.of T) F U x hx t) :
    s = t := by
  classical
  -- Pour chaque point `p` de `U`, choix d'un voisinage `V p` où `s` et `t`
  -- coïncident (germ_eq, deux flèches `V p ⟶ U` car les deux sections vivent sur `U`).
  choose V m i₁ i₂ heq using fun (p : {x : T // x ∈ U}) =>
    TopCat.Presheaf.germ_eq (X := TopCat.of T) F p.1 p.2 p.2 s t (h p.1 p.2)
  -- Le crible des ouverts dominés par l'un des `V p` couvre `U`.
  refine hF U ⟨fun (Y : Opens T) _ => ∃ p : {x : T // x ∈ U}, Y ≤ V p, ?sieve⟩ ?mem s t ?ext
  · -- stabilité descendante : composer les inclusions d'ouverts.
    intro Y Z f hf g
    obtain ⟨p, hp⟩ := hf
    exact ⟨p, g.le.trans hp⟩
  · rw [mem_opensTopology_iff]
    intro x hx
    exact ⟨V ⟨x, hx⟩, i₁ ⟨x, hx⟩, ⟨⟨x, hx⟩, le_refl _⟩, m ⟨x, hx⟩⟩
  · -- sur chaque flèche du crible, les restrictions coïncident (via `V p`).
    rintro Y f ⟨p, hYV⟩
    have hf₁ : f = homOfLE hYV ≫ i₁ p := Subsingleton.elim _ _
    have hf₂ : f = homOfLE hYV ≫ i₂ p := Subsingleton.elim _ _
    calc F.map f.op s
        = F.map ((homOfLE hYV ≫ i₁ p).op) s := by rw [hf₁]
      _ = (F.map (i₁ p).op ≫ F.map (homOfLE hYV).op) s := by
          rw [op_comp, Functor.map_comp]
      _ = F.map (homOfLE hYV).op (F.map (i₁ p).op s) := rfl
      _ = F.map (homOfLE hYV).op (F.map (i₂ p).op t) := by rw [heq p]
      _ = (F.map (i₂ p).op ≫ F.map (homOfLE hYV).op) t := rfl
      _ = F.map ((homOfLE hYV ≫ i₂ p).op) t := by
          rw [op_comp, Functor.map_comp]
      _ = F.map f.op t := by rw [hf₂]

/-- **Corollaire faisceau** : pour un faisceau de types, la même conclusion
sans aucune hypothèse de limite — là où le `section_ext` de Mathlib exige
`[HasLimits C]` et compagnie, la séparabilité suffit ici : tout faisceau
est séparé (`Presheaf.IsSheaf.isSeparated`), et le pont de la Partie 70
(`isSheaf_opensTopology_iff`) transporte la condition de faisceau de
Mathlib vers le site own. -/
theorem eq_of_germ_eq_of_isSheaf (F : TopCat.Presheaf (Type u) (TopCat.of T))
    (hF : TopCat.Presheaf.IsSheaf F)
    {U : Opens T} {s t : F.obj (op U)}
    (h : ∀ (x : T) (hx : x ∈ U),
      TopCat.Presheaf.germ (X := TopCat.of T) F U x hx s =
        TopCat.Presheaf.germ (X := TopCat.of T) F U x hx t) :
    s = t :=
  eq_of_germ_eq_of_isSeparated T F ((isSheaf_opensTopology_iff F).mpr hF).isSeparated h

/-- **Une section est déterminée par sa famille de germes** : pour un
préfaisceau de types séparé, l'application qui envoie une section sur `U`
vers sa famille de germes aux points de `U` est injective. Reformulation
combinatoire du théorème principal — la brique ponctuelle du dictionnaire
faisceaux ↔ espaces étalés amorcé aux Parties 72-73. -/
theorem injective_germ_family_of_isSeparated (F : TopCat.Presheaf (Type u) (TopCat.of T))
    (hF : Presheaf.IsSeparated (J := opensTopology T) F) (U : Opens T) :
    Function.Injective (fun (s : F.obj (op U)) (p : {x : T // x ∈ U}) =>
      TopCat.Presheaf.germ (X := TopCat.of T) F U p.1 p.2 s) := by
  intro s t hst
  refine eq_of_germ_eq_of_isSeparated T F hF ?_
  intro x hx
  exact congrFun hst ⟨x, hx⟩

end Contenu

end Grothendieck