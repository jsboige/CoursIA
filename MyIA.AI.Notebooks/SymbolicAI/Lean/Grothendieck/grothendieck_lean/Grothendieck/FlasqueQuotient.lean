/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Grothendieck hommage — Partie 83 : le pont se referme — cribles, Mathlib,
et le quotient de Godement II.3.1.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #1646).
-/
/-
Partie 83 — Le pont se referme : cribles, Mathlib, et le quotient de Godement II.3.1
=================================================================================

Contexte (Parties 79, 80, 81, 82) : la flasquité de cribles `IsFlasqueSieves`
(Partie 79) exige l'amalgamation de toute famille compatible sur **tout**
crible — couvrant ou non — là où la définition de Mathlib
`TopCat.Presheaf.IsFlasque` exige seulement l'épimorphie des restrictions.
La Partie 82 a documenté l'écart résiduel : le pont `IsFlasque →
IsFlasqueSieves` était établi pour les cribles **mono-générateurs**
(`exists_isAmalgamation_of_isFlasque_generate_singleton`), la frontière
multi-générateurs restant ouverte.

Cette Partie referme les deux bouts :

* **Aller** (`isFlasqueSieves_of_isFlasque_of_isSheaf`) : un préfaisceau de
  types **faisceau** et flasque au sens de Mathlib est flasque au sens des
  cribles. Sur `Opens X`, la frontière multi-générateurs de la Partie 82
  disparaît **sans Zorn** : le treillis des ouverts borne la famille — le
  supremum `V₀` des membres du crible est un ouvert, la famille s'y colle
  par la condition de faisceau (`presieveOfCovering.mem_grothendieckTopology`),
  et la flasquité étend la section de `V₀` à `U`. C'est l'argument
  « colle puis étends » élémentaire, là où le cas d'un site général
  exigerait un raisonnement transfini.

* **Retour** (`isFlasque_of_isFlasqueSieves`) : la flasquité de cribles
  entraîne celle de Mathlib pour **toute** flèche de `Opens X` — le site
  est mince, toute flèche y est mono, et le relèvement mono de la Partie 82
  (`exists_lift_of_isFlasqueSieves_of_mono`) s'applique à chaque restriction.
  Sur un site général, l'aller ne tient que pour les cribles mono-générateurs
  et le retour pour les flèches mono : sur `Opens X`, les deux notions
  coïncident pour les faisceaux.

* **Quotient** (`isFlasqueSieves_of_shortExact_of_isFlasque₁₂`) : Godement
  II.3.1, seconde moitié, lu côté cribles — dans une suite exacte courte de
  faisceaux de groupes abéliens dont les deux premiers termes sont flasques
  de cribles, le troisième l'est aussi. Miroir de
  `TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂` (Mathlib), dont la
  preuve consomme la flasquité de `X₁` (via `epi_of_shortExact`, Zorn) pour
  l'épimorphie de `S.g` sur chaque ouvert, et celle de `X₂` pour
  l'épimorphie des restrictions du composite. Ici les deux ingrédients
  proviennent des contreparties de cribles : l'épi de `S.g` de la Partie 82
  (`epi_of_shortExact_of_isFlasqueSieves`), les restrictions de `X₂` du
  pont retour ci-dessus.
-/
import Grothendieck.Flasque
import Grothendieck.FlasqueExact
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.Topology.Sheaves.SheafCondition.Sites

universe u v

namespace Grothendieck

open CategoryTheory TopCat TopCat.Presheaf TopologicalSpace Opposite

set_option maxHeartbeats 800000

section Pont

variable {X : TopCat.{u}}

/-- **Retour du pont** : flasque de cribles ⇒ flasque au sens de Mathlib.
Toute flèche de `Opens X` est mono (site mince), donc le relèvement mono de
la Partie 82 fournit un antécédent à chaque section le long de chaque
restriction — l'épimorphie au sens de Mathlib. Aucune hypothèse de
faisceau : le retour vaut pour tout préfaisceau de types sur `Opens X`. -/
theorem isFlasque_of_isFlasqueSieves {P : TopCat.Presheaf (Type (max u u)) X}
    [IsFlasqueSieves P] : P.IsFlasque where
  epi {U V} i := by
    refine (CategoryTheory.epi_iff_surjective (P.map i)).mpr (fun s => ?_)
    obtain ⟨t, ht⟩ := exists_lift_of_isFlasqueSieves_of_mono (P := P) i.unop s
    exact ⟨t, ht⟩

/-- **Aller du pont** : faisceau + flasque au sens de Mathlib ⇒ flasque de
cribles. La preuve referme la frontière multi-générateurs documentée en
tête de `Grothendieck.FlasqueExact` : étant donné un crible `R` sur `U`, le
supremum `V₀` de ses membres est un ouvert de `X`, le crible y devient
couvrant, la condition de faisceau colle la famille en une section de
`V₀`, et la flasquité étend cette section le long de l'inclusion
`V₀ ⟶ U`. Le treillis des ouverts joue le rôle que Zorn joue sur un site
général : il borne la famille avant le collage. -/
theorem isFlasqueSieves_of_isFlasque_of_isSheaf {P : TopCat.Presheaf (Type (max u u)) X}
    (hsheaf : Presieve.IsSheaf (Opens.grothendieckTopology X) P)
    (hfla : P.IsFlasque) : IsFlasqueSieves P where
  amalgamates {U} R x hx := by
    -- La famille couvrante des membres du crible, et son supremum.
    set fam := coveringOfPresieve _ R.arrows with hfam
    set V₀ : Opens X := iSup fam with hV₀
    -- La flasquité étendra la section de `V₀` à `U` le long de l'inclusion.
    have hle : V₀ ≤ U := iSup_le fun j => leOfHom j.2.1
    -- Chaque flèche `g : W ⟶ V₀` du précrible couvrant provient d'un
    -- membre du crible : le composite `g ≫ (V₀ ⟶ U)` est une flèche de
    -- `R` (les flèches de `Opens X` forment un sous-singulier : le
    -- composite coïncide avec la flèche membre d'origine).
    have kar : ∀ {W : Opens X} {g : W ⟶ V₀}, presieveOfCovering fam g →
        R.arrows (g ≫ homOfLE hle) := by
      intro W g ⟨i, hi⟩
      subst hi
      have heq : (g ≫ homOfLE hle : fam i ⟶ U) = i.2.1 := Subsingleton.elim _ _
      rw [heq]
      exact i.2.2
    -- La famille transportée sur le précrible couvrant de `V₀`.
    set z : Presieve.FamilyOfElements P (presieveOfCovering fam) :=
      fun W g hg => x (g ≫ homOfLE hle) (kar hg) with hzdef
    have hz : z.Compatible := by
      intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ _
      exact hx g₁ g₂ (kar h₁) (kar h₂) (Subsingleton.elim _ _)
    -- Le précrible couvrant engendre un crible de la topologie : la
    -- condition de faisceau colle la famille en une section de `V₀`.
    have hmem : Sieve.generate (presieveOfCovering fam) ∈ Opens.grothendieckTopology X V₀ :=
      presieveOfCovering.mem_grothendieckTopology fam
    obtain ⟨t₀, ht₀⟩ := hsheaf _ hmem z.sieveExtend hz.sieveExtend
    have hz₀ : z.IsAmalgamation t₀ := by
      rw [← Presieve.restrict_extend hz]
      exact Presieve.isAmalgamation_restrict _ _ _ ht₀.1
    obtain ⟨t, ht⟩ := (CategoryTheory.epi_iff_surjective (P.map (homOfLE hle).op)).mp
      (hfla.epi (homOfLE hle).op) t₀
    refine ⟨t, ?_⟩
    intro Y f hf
    -- `Y` est un membre de la famille couvrante : flèche vers `V₀`.
    have hYle : Y ≤ V₀ := le_iSup fam ⟨Y, f, hf⟩
    have hmemY : presieveOfCovering fam (homOfLE hYle) := ⟨⟨Y, f, hf⟩, rfl⟩
    have hstep : P.map f.op t = P.map (homOfLE hYle : Y ⟶ V₀).op t₀ := by
      have hfeq : f = (homOfLE hYle : Y ⟶ V₀) ≫ homOfLE hle := Subsingleton.elim _ _
      rw [hfeq, op_comp, Functor.map_comp, CategoryTheory.comp_apply, ht]
    have hzY : P.map (homOfLE hYle : Y ⟶ V₀).op t₀
        = x ((homOfLE hYle : Y ⟶ V₀) ≫ homOfLE hle) (kar hmemY) :=
      hz₀ _ hmemY
    have hxm : x ((homOfLE hYle : Y ⟶ V₀) ≫ homOfLE hle) (kar hmemY) = x f hf := by
      have heq : (homOfLE hYle : Y ⟶ V₀) ≫ homOfLE hle = f := Subsingleton.elim _ _
      rw [heq]
    rw [hstep, hzY]
    exact hxm

end Pont

section Exact

variable {X : TopCat.{u}}

/-- **Godement II.3.1, seconde moitié, saveur cribles** : dans une suite
exacte courte de faisceaux de groupes abéliens `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`
dont `X₁` et `X₂` sont flasques de cribles, `X₃` est flasque de cribles.
Miroir de `TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂` (Mathlib) :
l'épimorphie de `S.g` sur chaque ouvert vient de la Partie 82 (partant de
la flasquité de cribles de `X₁`), l'épimorphie des restrictions de `X₂`
vient du pont retour ci-dessus, et la conclusion du pont aller — `X₃` est
faisceau et ses restrictions sont épi, donc il amalgamate tout crible.
[God58] Chap. II §3.1. -/
theorem isFlasqueSieves_of_shortExact_of_isFlasque₁₂
    {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    [IsFlasqueSieves (S.X₁.obj ⋙ CategoryTheory.forget AddCommGrpCat)]
    [IsFlasqueSieves (S.X₂.obj ⋙ CategoryTheory.forget AddCommGrpCat)] :
    IsFlasqueSieves (S.X₃.obj ⋙ CategoryTheory.forget AddCommGrpCat) := by
  -- Épimorphie de `S.g` sur chaque ouvert, depuis la flasquité de cribles
  -- de `X₁` (Partie 82).
  have hg : ∀ U : Opens X, Epi (S.g.hom.app (op U)) := fun U =>
    epi_of_shortExact_of_isFlasqueSieves hS
  -- Restrictions de `X₂` épi en types : pont retour, puis transfert vers
  -- AddCommGrpCat par la surjectivité (le foncteur d'oubli ne change pas
  -- l'application sous-jacente).
  have hI₂ : TopCat.Presheaf.IsFlasque (S.X₂.obj ⋙ CategoryTheory.forget AddCommGrpCat) :=
    isFlasque_of_isFlasqueSieves
  have hX₂ : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), Epi (S.X₂.obj.map i) := by
    intro U V i
    refine (AddCommGrpCat.epi_iff_surjective _).mpr (fun s => ?_)
    obtain ⟨t, ht⟩ := (CategoryTheory.epi_iff_surjective
      ((S.X₂.obj ⋙ CategoryTheory.forget AddCommGrpCat).map i)).mp (hI₂.epi i) s
    exact ⟨t, ht⟩
  -- Restrictions de `X₃` épi : miroir de la preuve Mathlib — par
  -- naturalité le composite `X₂.map i ≫ S.g.app` est épi (deux facteurs
  -- épi), et l'épi du composite se transmet à `X₃.map i` après
  -- annulation de `S.g.app`.
  have hX₃ : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), Epi (S.X₃.obj.map i) := by
    intro U V i
    have hgV : Epi (S.g.hom.app V) := hg V.unop
    have hcomp : Epi (S.g.hom.app U ≫ S.X₃.obj.map i) := by
      rw [← S.g.hom.naturality i]
      exact CategoryTheory.epi_comp' (hX₂ i) hgV
    exact @CategoryTheory.epi_of_epi _ _ _ _ _ (S.g.hom.app U) (S.X₃.obj.map i) hcomp
  -- `X₃` est faisceau de types (transfert du foncteur d'oubli, qui crée
  -- les limites) et flasque de Mathlib en types : le pont aller conclut.
  have hX₃sheaf : Presieve.IsSheaf (Opens.grothendieckTopology X)
      (S.X₃.obj ⋙ CategoryTheory.forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp ((isSheaf_iff_isSheaf_comp _ _).mp S.X₃.2)
  exact isFlasqueSieves_of_isFlasque_of_isSheaf hX₃sheaf
    ⟨fun i => by
      refine (CategoryTheory.epi_iff_surjective _).mpr (fun s => ?_)
      obtain ⟨t, ht⟩ := (AddCommGrpCat.epi_iff_surjective (S.X₃.obj.map i)).mp (hX₃ i) s
      exact ⟨t, ht⟩⟩

end Exact

end Grothendieck
