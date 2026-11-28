/-
Grothendieck hommage — Partie 75 : recollement des familles de germes.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #1646).

La Partie 74 a établi l'injectivité de l'application qui associe à une
section sa famille de germes. Cette partie formalise la réciproque correcte :
une famille de germes ne provient pas arbitrairement d'une section, mais elle
en provient dès qu'elle est **localement représentable** par des sections.

La preuve choisit les représentants locaux donnés par l'hypothèse. Sur chaque
intersection, leurs restrictions ont les mêmes germes ; la Partie 74 les rend
donc égales. La condition de faisceau sous sa forme de recollement unique
(`existsUnique_gluing'`) produit alors une section globale. Ses germes sont la
famille prescrite, et l'unicité découle à nouveau de la Partie 74.

Références :
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Chap. II §6 (faisceaux et espaces étalés).
  - Mathlib, `Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing`.
  - Partie 74 (`Grothendieck.StalkSeparated`) : détection par les germes.

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
| `GermFamily` | **couvert** | `Stalk/Separated.lean:65` `toStalkProduct` (EGA IV 21.9.1) | la dépendance au sous-type `{x // x ∈ U}` |
| `GermFamily.IsLocallyRepresentable` | absent | aucun (`LocallyRepresentable`, `germFamily` : 0 résultat) ; plus proche : `Glueing/Sheaf.lean:232` `gluedPresheaf` (00AL) | le recollement d'une famille de **germes**, Stacks recollant des sections |
| `germFamily_isLocallyRepresentable` | absent | aucun | la trivialité du cas « la famille vient d'une section » |
| `existsUnique_gluing'_of_isSheaf` | partiel | `Glueing/Sheaf.lean:240` `gluedPresheaf_isSheaf` ; `:278` `glued` (00AL) | la variante à cible explicite, sans hypothèse de préservation des limites |
| `existsUnique_section_of_isLocallyRepresentable` | absent | aucun | la **reconstruction** de la section à partir des germes (sens inverse du dictionnaire) |
| `surjective_germ_family_to_locallyRepresentable` | absent | aucun | la formulation « section ↦ famille de germes » |

Convention i18n (EPIC #4980 ratifiée 2026-07-04) : ce module est jumelé avec
`StalkGluing_en.lean`. Les énoncés, preuves et noms Lean restent identiques ;
seules les docstrings et les commentaires diffèrent.

Epic #1646, Phase 2 (#2159). Aucun `sorry` introduit.
-/

import Grothendieck.StalkSeparated
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

universe u

namespace Grothendieck

open CategoryTheory Opposite TopCat TopologicalSpace TopologicalSpace.Opens

section Contenu

variable (T : Type u) [TopologicalSpace T]

/-- La famille des germes d'un préfaisceau `F` aux points d'un ouvert `U`.

Correspondance Stacks — **COUVERT** :
`StacksFrontier/Topology/Sheaves/Stalk/Separated.lean:65` (`toStalkProduct
(U : Opens X) : F.obj (Opposite.op U) → ∀ x : U, F.stalk x.1`, EGA
IV 21.9.1) est la même famille de germes — le type `∀ x : U` est la version
non dépendante de notre `∀ p : {x // x ∈ U}`. Ce que notre version ajoute :
la **dépendance** au sous-type `{x : T // x ∈ U}`, qui garde l'appartenance
à `U` dans le type. -/
abbrev GermFamily (F : TopCat.Presheaf (Type u) (TopCat.of T)) (U : Opens T) :=
  ∀ p : {x : T // x ∈ U}, F.stalk p.1

/-- Une famille de germes sur `U` est **localement représentable** si chaque
point `p : U` possède un voisinage ouvert `V p ⟶ U` et une section sur `V p`
dont le germe en tout point de `V p` est la valeur prescrite par la famille.
Cette condition est entièrement locale : elle ne suppose aucune section sur
`U`.

Correspondance Stacks — **ABSENT** : aucun énoncé de ce nom dans
`StacksFrontier/Topology/Sheaves/` (recherches `LocallyRepresentable` et
`germFamily` : 0 résultat). Le pendant le plus proche est la donnée de
recollement `Glueing/Sheaf.lean:232` (`gluedPresheaf (D : GlueData X U)`,
Stacks 00AL), qui recolle des **isomorphismes de restriction** entre
faisceaux sur un recouvrement — pas une famille de germes. L'écart est
l'**objet** du recollement : chez nous des germes, chez Stacks des
sections. -/
def GermFamily.IsLocallyRepresentable
    (F : TopCat.Presheaf (Type u) (TopCat.of T)) (U : Opens T)
    (a : GermFamily T F U) : Prop :=
  ∃ (V : {x : T // x ∈ U} → Opens T)
    (iVU : ∀ p, V p ⟶ U)
    (_hmem : ∀ p, p.1 ∈ V p)
    (sf : ∀ p, F.obj (op (V p))),
      ∀ (p) (x : T) (hx : x ∈ V p),
        F.germ (V p) x hx (sf p) = a ⟨x, (iVU p).le hx⟩

/-- La famille des germes d'une section est localement représentable.

Correspondance Stacks — **ABSENT** : corollaire du précédent — la
représentabilité locale d'une famille de germes n'a pas d'énoncé nommé chez
Stacks (recherche `germFamily` sur toute l'arborescence
`StacksFrontier/Topology/Sheaves/` : 0 résultat). Ce que notre version
ajoute : la **trivialité** du cas « la famille vient d'une section » — le
représentant local est la section elle-même, restreinte à `U`. -/
theorem germFamily_isLocallyRepresentable
    (F : TopCat.Presheaf (Type u) (TopCat.of T)) (U : Opens T)
    (s : F.obj (op U)) :
    GermFamily.IsLocallyRepresentable T F U
      (fun p => F.germ U p.1 p.2 s) := by
  refine ⟨fun _ => U, fun _ => 𝟙 U, fun p => p.2, fun _ => s, ?_⟩
  intro p x hx
  congr 1

/-- Variante sur un ouvert cible explicite du recollement unique pour les
faisceaux de types. Contrairement à `TopCat.Sheaf.existsUnique_gluing'`, elle
part directement d'un préfaisceau muni de sa propriété de faisceau et n'exige
aucune hypothèse générale de préservation des limites.

Correspondance Stacks — **PARTIEL** : Stacks 00AL construit le faisceau
recollé d'une donnée de recollement (`Glueing/Sheaf.lean:232`
`gluedPresheaf`, `:240` `gluedPresheaf_isSheaf`, `:278` `glued`). Même
cœur — le recollement unique de données compatibles — mais deux cadres :
Stacks recolle des **faisceaux** sur un **recouvrement** au moyen
d'isomorphismes de restriction vérifiant la cocycle, nous recollons des
**sections compatibles** d'un **préfaisceau** au sens de `IsCompatible`,
sans hypothèse générale de préservation des limites. Ce que notre version
ajoute : la variante à cible explicite et l'absence de ces hypothèses. -/
theorem existsUnique_gluing'_of_isSheaf
    (F : TopCat.Presheaf (Type u) (TopCat.of T)) (hF : TopCat.Presheaf.IsSheaf F)
    {ι : Type*} (V : ι → Opens T) (U : Opens T) (iVU : ∀ i, V i ⟶ U)
    (hcover : U ≤ iSup V) (sf : ∀ i, F.obj (op (V i)))
    (hcompatible : TopCat.Presheaf.IsCompatible F V sf) :
    ∃! s : F.obj (op U), ∀ i, F.map (iVU i).op s = sf i := by
  have hU : U = iSup V := le_antisymm hcover (iSup_le fun i => (iVU i).le)
  obtain ⟨gl, hgl, huniq⟩ := hF.isSheafUniqueGluing_types sf hcompatible
  refine ⟨F.map (eqToHom hU).op gl, ?_, ?_⟩
  · intro i
    rw [← ConcreteCategory.comp_apply, ← F.map_comp]
    exact hgl i
  · intro t ht
    convert! congr_arg (F.map (eqToHom hU).op)
      (huniq (F.map (eqToHom hU.symm).op t) fun i => _) <;>
        rw [← ConcreteCategory.comp_apply, ← F.map_comp]
    · simp
    · exact ht i

/-- **Recollement des germes** : toute famille de germes localement
représentable d'un faisceau de types provient d'une unique section globale.
L'existence utilise le recollement des représentants locaux ; l'unicité est
exactement la détection des sections par leurs germes établie en Partie 74.

Correspondance Stacks — **ABSENT** : le recollement d'une **famille de
germes** localement représentable n'a pas d'énoncé nommé chez Stacks
(recherche `germFamily` : 0 résultat ; `Glueing/Sheaf.lean` recolle des
sections données sur un recouvrement, pas des germes reconstruisant une
section). C'est le **sens inverse** du dictionnaire : Stacks part de la
section locale vers le faisceau, nous partons des germes vers la section
globale. Ce que notre version ajoute : la reconstruction elle-même, et
l'unicité qui en découle par la détection de la Partie 74. -/
theorem existsUnique_section_of_isLocallyRepresentable
    (F : TopCat.Presheaf (Type u) (TopCat.of T)) (hF : TopCat.Presheaf.IsSheaf F)
    (U : Opens T) (a : GermFamily T F U)
    (ha : GermFamily.IsLocallyRepresentable T F U a) :
    ∃! s : F.obj (op U), ∀ p : {x : T // x ∈ U}, F.germ U p.1 p.2 s = a p := by
  classical
  rcases ha with ⟨V, iVU, hmem, sf, hsf⟩
  have hcover : U ≤ iSup V := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩
  have hcompatible : TopCat.Presheaf.IsCompatible F V sf := by
    intro p q
    apply eq_of_germ_eq_of_isSheaf T F hF
    intro x hx
    rw [F.germ_res_apply (infLELeft (V p) (V q)) x hx,
      F.germ_res_apply (infLERight (V p) (V q)) x hx]
    calc
      F.germ (V p) x ((inf_le_left : V p ⊓ V q ≤ V p) hx) (sf p) =
          a ⟨x, (iVU p).le ((inf_le_left : V p ⊓ V q ≤ V p) hx)⟩ :=
        hsf p x ((inf_le_left : V p ⊓ V q ≤ V p) hx)
      _ = a ⟨x, (iVU q).le ((inf_le_right : V p ⊓ V q ≤ V q) hx)⟩ := by
        congr 1
      _ = F.germ (V q) x ((inf_le_right : V p ⊓ V q ≤ V q) hx) (sf q) :=
        (hsf q x ((inf_le_right : V p ⊓ V q ≤ V q) hx)).symm
  obtain ⟨s, hs, _⟩ :=
    existsUnique_gluing'_of_isSheaf T F hF V U iVU hcover sf hcompatible
  have hsg : ∀ p : {x : T // x ∈ U}, F.germ U p.1 p.2 s = a p := by
    intro p
    calc
      F.germ U p.1 p.2 s = F.germ (V p) p.1 (hmem p) (F.map (iVU p).op s) :=
        (F.germ_res_apply (iVU p) p.1 (hmem p) s).symm
      _ = F.germ (V p) p.1 (hmem p) (sf p) := by rw [hs p]
      _ = a ⟨p.1, (iVU p).le (hmem p)⟩ := hsf p p.1 (hmem p)
      _ = a p := by congr 1
  refine ⟨s, hsg, ?_⟩
  intro t ht
  apply eq_of_germ_eq_of_isSheaf T F hF
  intro x hx
  exact (ht ⟨x, hx⟩).trans (hsg ⟨x, hx⟩).symm

/-- Reformulation en surjectivité : l'application « section ↦ famille de
germes » est surjective sur le sous-type des familles localement
représentables.

Correspondance Stacks — **ABSENT** : reformulation en surjectivité du
précédent ; aucun énoncé de ce nom chez Stacks (recherche `germFamily` sur
toute l'arborescence `StacksFrontier/Topology/Sheaves/` : 0 résultat). Ce
que notre version ajoute : la formulation « application section ↦ famille
de germes », qui rend le dictionnaire faisceaux ↔ espaces étalés
explicite. -/
theorem surjective_germ_family_to_locallyRepresentable
    (F : TopCat.Presheaf (Type u) (TopCat.of T)) (hF : TopCat.Presheaf.IsSheaf F)
    (U : Opens T) :
    Function.Surjective
      (fun (s : F.obj (op U)) =>
        (⟨fun p => F.germ U p.1 p.2 s,
          germFamily_isLocallyRepresentable T F U s⟩ :
          {a : GermFamily T F U // GermFamily.IsLocallyRepresentable T F U a})) := by
  intro a
  obtain ⟨s, hs, _⟩ :=
    existsUnique_section_of_isLocallyRepresentable T F hF U a.1 a.2
  refine ⟨s, Subtype.ext ?_⟩
  funext p
  exact hs p

end Contenu

end Grothendieck
