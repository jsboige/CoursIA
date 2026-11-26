/-
Grothendieck hommage — Partie 76 : le faisceau est exactement le préfaisceau
séparé qui recolle.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #1646).

Les Parties 74 et 75 ont établi les deux moitiés séparément. La Partie 74 a
montré que les germes détectent l'égalité des sections d'un faisceau, et la
Partie 75 que toute famille de germes localement représentable provient d'une
unique section. Cette partie les assemble en l'équivalence qui les fonde :

  `IsSheaf F  ↔  <séparation par les germes>  ∧  <recollement des familles
  localement représentables>`

C'est la caractérisation classique du faisceau comme préfaisceau séparé
vérifiant le recollement des sections localement définies (Mac Lane–Moerdijk
[MM92] II.6, Stacks 00AK).

Le sens direct ne fait que reprendre les deux Parties précédentes. Le sens
réciproque est le seul endroit du lake où la condition de faisceau est
**dérivée** plutôt que consommée : la Partie 75 avait besoin de `IsSheaf`
comme hypothèse, la présente partie le produit. On construit la famille de
germes lue sur les représentants locaux d'une famille couvrante compatible,
on l'injecte dans le recollement fourni par l'hypothèse, et la séparation fait
le reste — elle donne à la fois que la section obtenue restreint à chaque
représentant, et qu'elle est l'unique à le faire.

Aucune des deux hypothèses n'est superflue : la séparation est l'unicité, le
recollement fournit l'existence.

Références :
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92], Chap. II
    §6 (faisceaux et espaces étalés).
  - Stacks Project, tag 00AK (faisceaux et recollement).
  - Mathlib, `Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing`
    (`IsSheafUniqueGluing`, `isSheaf_of_isSheafUniqueGluing_types`, consommé
    dans `Mathlib/Topology/Sheaves/LocalPredicate.lean:246`).
  - Parties 74 (`Grothendieck.StalkSeparated`, la séparation) et 75
    (`Grothendieck.StalkGluing`, le recollement).

Correspondance Stacks (groupe #15 de #28537 — « les points et les germes », mesure du 26/11)
--------------------------------------------------------------------------
Lecture de `AxiomMath/Stacks` sur l'**arborescence locale**
`StacksFrontier/Topology/Sheaves/` (clone sparse du dossier entier, 1756
fichiers couverts sur 1756) : un verdict « absent » signifie **aucun énoncé
de ce nom dans l'ensemble de `Topology/Sheaves/`**.

| Énoncé | Classe | Référent Stacks | Ce que notre version ajoute |
|---|---|---|---|
| `GermSeparated` | **couvert** | `Stalk/Separated.lean:78` `TopCat.Presheaf.IsSeparated'` ; `:86` `isSeparated'_iff` (Stacks 007A) | la forme pointwise sur le sous-type `{x // x ∈ U}` |
| `GermGluing` | partiel | `Basis/Germs.lean:329` `germMap_range_eq_conditionStar` ; `:339` `germMap_bijection` (009M) | l'existence sur le site des ouverts, sans condition de base |
| `germ_eq_of_isCompatible` | partiel | `Basis/Germs.lean:224` `germ_res` ; `:212` `germ_eq_iff_rel` | l'énoncé autonome, avec un prédicat `IsCompatible` de préfaisceau |
| `isSheaf_iff_germSeparated_and_germGluing` | partiel | `Basis/Germs.lean:308` `germMap_injective` ; `:329` (009M) ; `Basis/Sheaf.lean:140` `main_theorem009J` (009J) | le sens inverse, où la condition de faisceau est **dérivée** des germes |

Convention i18n (EPIC #4980 ratifiée 2026-07-04) : ce module est jumelé avec
`StalkCharacterization_en.lean`. Les énoncés, preuves et noms Lean restent
identiques ; seules les docstrings et les commentaires diffèrent.

Epic #1646, Phase 2 (#2159). Aucun `sorry` introduit.
-/

import Grothendieck.StalkSeparated
import Grothendieck.StalkGluing
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

universe u

namespace Grothendieck

open CategoryTheory Opposite TopCat TopologicalSpace TopologicalSpace.Opens

section Contenu

variable (T : Type u) [TopologicalSpace T]

/-- **Séparation par les germes** : deux sections d'un préfaisceau qui ont le
même germe en tout point d'un ouvert sont égales. La Partie 74 établissait
cette conclusion pour un faisceau ; on la promeut ici en propriété du
préfaisceau lui-même, pour pouvoir la prendre comme hypothèse.

Correspondance Stacks — **COUVERT** :
`StacksFrontier/Topology/Sheaves/Stalk/Separated.lean:78`
(`TopCat.Presheaf.IsSeparated'`, Stacks 007A) pose la même propriété — la
carte « section ↦ famille de ses germes » est injective — et `:86`
(`isSeparated'_iff`) en donne la forme pointwise identique à la nôtre : deux
sections dont les germes coïncident en tout point de l'ouvert sont égales.
Stacks note au passage (`:43`) que Mathlib a les tiges et les cartes de
germe mais **pas** ce prédicat : c'est Stacks qui l'ajoute. Ce que notre
version ajoute : la forme pointwise est la nôtre pour un préfaisceau de
`Type u` quelconque, sans hypothèse de faisceau, mais avec la dépendance au
sous-type `{x : T // x ∈ U}`. -/
def GermSeparated (F : TopCat.Presheaf (Type u) (TopCat.of T)) : Prop :=
  ∀ (U : Opens T) (s t : F.obj (op U)),
    (∀ (x : T) (hx : x ∈ U), F.germ U x hx s = F.germ U x hx t) → s = t

/-- **Recollement des germes** : toute famille de germes localement
représentable (au sens de la Partie 75) provient d'une section. La Partie 75
démontrait cette existence pour un faisceau **et** en donnait l'unicité ; on
retient ici la seule existence, l'unicité étant exactement la séparation
ci-dessus.

Correspondance Stacks — **PARTIEL** : Stacks 009M
(`StacksFrontier/Topology/Sheaves/Basis/Germs.lean:329`,
`germMap_range_eq_conditionStar`, et `:339`, `germMap_bijection`) prouve que
l'image de la carte des germes est **exactement** l'ensemble des familles de
germes vérifiant la condition (*), donc que toute famille de germes
**localement représentable** provient d'une section. La condition (*) de
Stacks est la même que notre `IsLocallyRepresentable` : pour chaque point,
un représentant local dont le germe coïncide avec la famille. Deux écarts de
cadre : Stacks travaille sur un **préfaisceau sur une base**
(`PresheafOnBasisOpenSet`) et sa tige est le **quotient** par la relation
d'équivalence des germes (`:132` `Stalk`), la nôtre une colimit filtrée ; et
Stacks établit le sens direct sous l'hypothèse `hF : F.IsSheaf`, le nôtre le
pose en hypothèse. Ce que notre version ajoute : l'existence dans le cadre
du site des ouverts, sans condition de base. -/
def GermGluing (F : TopCat.Presheaf (Type u) (TopCat.of T)) : Prop :=
  ∀ (U : Opens T) (a : GermFamily T F U),
    GermFamily.IsLocallyRepresentable T F U a →
      ∃ s : F.obj (op U), ∀ p : {x : T // x ∈ U}, F.germ U p.1 p.2 s = a p

/-- La forme « germe » de la compatibilité : deux membres d'une famille
compatible ont le même germe en tout point de leur intersection. C'est
l'ingrédient qui rend bien définie la famille de germes construite sur une
famille couvrante — deux représentants locaux d'un même point coïncident
localement, et donc en germe.

Correspondance Stacks — **PARTIEL** : l'ingrédient est chez Stacks :
`Basis/Germs.lean:224` (`germ_res`) montre que le germe commute avec la
restriction, et `:212` (`germ_eq_iff_rel`) que l'égalité des germes équivaut
à la relation d'équivalence des germes. Stacks n'a cependant **pas**
d'énoncé nommé « les germes de deux représentants locaux compatibles
coïncident » : chez lui la compatibilité est exprimée par l'égalité des
restrictions sur les éléments de base
(`Basis/LocallyBijectiveBasisIso.lean:83`, `IsCompatibleOnBasisPresheaf`) et
la conclusion s'en déduit. Ce que notre version ajoute : l'énoncé autonome,
avec un prédicat `IsCompatible` de préfaisceau et le site des ouverts. -/
theorem germ_eq_of_isCompatible
    (F : TopCat.Presheaf (Type u) (TopCat.of T)) {ι : Type*}
    (U : ι → Opens T) (sf : ∀ i, F.obj (op (U i)))
    (hc : TopCat.Presheaf.IsCompatible F U sf)
    {i j : ι} {x : T} (hi : x ∈ U i) (hj : x ∈ U j) :
    F.germ (U i) x hi (sf i) = F.germ (U j) x hj (sf j) := by
  have hmem : x ∈ U i ⊓ U j := ⟨hi, hj⟩
  rw [← F.germ_res_apply (infLELeft (U i) (U j)) x hmem (sf i),
    ← F.germ_res_apply (infLERight (U i) (U j)) x hmem (sf j), hc i j]

/-- **Caractérisation du faisceau par les tiges** : un préfaisceau de types sur
un espace topologique est un faisceau si et seulement si les germes détectent
l'égalité des sections (séparation) et si toute famille de germes localement
représentable provient d'une section (recollement).

C'est le capstone de la veine ouverte par les Parties 72-75, et le seul
endroit du lake où la condition de faisceau est dérivée de propriétés
élémentaires plutôt que postulée.

Correspondance Stacks — **PARTIEL** : les deux moitiés existent chez Stacks,
mais **séparément** et dans un cadre différent. Sens direct (faisceau ⇒
propriétés des germes) : Stacks 009M (`Basis/Germs.lean:308`
`germMap_injective` et `:329` `germMap_range_eq_conditionStar`). Sens inverse
(les propriétés des germes ⇒ faisceau) : Stacks ne l'a pas — sa condition de
faisceau est **définie** par la séparation et le recollement de **sections**
(`Basis/Germs.lean:95` `PresheafOnBasisOpenSet.IsSheaf` ; `Basis/Sheaf.lean:88`
`IsSheafOnBasis`, EGA 0 3.2.2, et `:140` `main_theorem009J`, 009J, le critère
de la base). Ce que notre version ajoute : l'équivalence **dans le sens
direct** sur le site des ouverts, sans condition de base, et le sens inverse
où la condition de faisceau est **dérivée** des germes plutôt que
postulée. -/
theorem isSheaf_iff_germSeparated_and_germGluing
    (F : TopCat.Presheaf (Type u) (TopCat.of T)) :
    TopCat.Presheaf.IsSheaf F ↔ GermSeparated T F ∧ GermGluing T F := by
  constructor
  · intro hF
    refine ⟨?_, ?_⟩
    · intro U s t h
      exact eq_of_germ_eq_of_isSheaf T F hF fun x hx => h x hx
    · intro U a ha
      exact (existsUnique_section_of_isLocallyRepresentable T F hF U a ha).exists
  · rintro ⟨hsep, hglu⟩
    refine TopCat.Presheaf.isSheaf_of_isSheafUniqueGluing_types F ?_
    intro ι U sf hc
    classical
    -- index témoin choisi pour chaque point de l'ouvert total
    let k : {x : T // x ∈ iSup U} → ι := fun p =>
      Classical.choose (Opens.mem_iSup.mp p.2)
    have hk : ∀ p : {x : T // x ∈ iSup U}, p.1 ∈ U (k p) := fun p =>
      Classical.choose_spec (Opens.mem_iSup.mp p.2)
    -- la famille de germes lue sur les représentants locaux
    let a : GermFamily T F (iSup U) := fun p => F.germ (U (k p)) p.1 (hk p) (sf (k p))
    -- elle est localement représentable, les représentants étant ceux de `sf`
    have hlr : GermFamily.IsLocallyRepresentable T F (iSup U) a :=
      ⟨fun p => U (k p), fun p => Opens.leSupr U (k p), fun p => hk p,
        fun p => sf (k p), fun p x hx =>
          germ_eq_of_isCompatible T F U sf hc hx
            (hk ⟨x, (Opens.leSupr U (k p)).le hx⟩)⟩
    obtain ⟨s, hs⟩ := hglu (iSup U) a hlr
    refine ⟨s, ?_, ?_⟩
    · -- `s` restreint à chaque `U i` : les germes coïncident, la séparation conclut
      intro i
      apply hsep (U i)
      intro x hx
      rw [F.germ_res_apply (Opens.leSupr U i) x hx s,
        hs ⟨x, (Opens.leSupr U i).le hx⟩]
      exact germ_eq_of_isCompatible T F U sf hc
        (hk ⟨x, (Opens.leSupr U i).le hx⟩) hx
    · -- unicité : deux recollements ont les mêmes germes, la séparation conclut
      intro t ht
      apply hsep (iSup U)
      intro x hx
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
      rw [hs ⟨x, hx⟩, ← F.germ_res_apply (Opens.leSupr U i) x hi t, ht i]
      exact germ_eq_of_isCompatible T F U sf hc hi (hk ⟨x, hx⟩)

end Contenu

end Grothendieck
