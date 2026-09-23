/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Grothendieck hommage — Partie 82 : du crible à l'épi — prolongement des
sections et suite exacte courte.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #1646).

La Partie 79 a posé la flasquité par cribles — `IsFlasqueSieves P` :
toute famille compatible sur **tout** crible s'amalgame. Cette partie
demande ce que cette lecture **implique** et **reçoit** de la définition
topologique de Mathlib (`TopCat.Presheaf.IsFlasque`, revendiqué :
restriction épimorphe le long de **toute** flèche de `(Opens X)ᵒᵖ`),
puis fait franchir au théorème de Godement la frontière site/topologie.

Quatre résultats :

  - `exists_isAmalgamation_of_sieveTop` : le crible **maximal** amalgamate
    toujours, sans aucune hypothèse sur `P` — toute famille compatible
    y est déterminée par sa valeur en `𝟙`, la compatibilité avec le couple
    `(g, 𝟙)` forçant `x g = P.map g.op (x 𝟙)`. La flasquité de cribles
    est donc une condition sur les **cribles propres** uniquement.
  - `exists_lift_of_isFlasqueSieves_of_mono` : flasque de cribles ⇒ toute
    section se prolonge le long de tout **mono** `f` (site arbitraire,
    aucune topologie). La famille singleton d'une section `s` n'est
    compatible que si `s` est invariante par les paires `p₁ ≫ f = p₂ ≫ f` ;
    un mono simplifie exactement ces paires — c'est la lecture « sous-objet »
    du prolongement des sections.
  - `exists_isAmalgamation_of_isFlasque_generate_singleton` : réciproque
    partielle, topologique cette fois — `Presheaf.IsFlasque` (Mathlib, epi
    sur toutes les flèches) ⇒ amalgamation sur tout crible **engendré par
    une flèche unique**. L'écart résiduel entre `IsFlasque` et
    `IsFlasqueSieves` est exactement l'amalgamation sur les cribles
    multi-générateurs.
  - `epi_of_shortExact_of_isFlasqueSieves` : **Godement II.3 lu côté
    cribles**. La preuve Zorn de Mathlib (`epi_of_shortExact`) ne consomme
    la flasquité de `X₁` qu'**une seule fois**, sur l'inclusion
    `homOfLE inf_le_right` — la reprise locale de l'argument avec la seule
    substitution du prolongement mono ci-dessus montre que l'hypothèse
    « epi sur toutes les flèches » peut y être remplacée par
    « amalgamation sur tous les cribles ». Le théorème de la suite exacte
    courte vit donc déjà dans le monde des sites.

Frontière honnête, dans la lignée des Parties 80-81 : la réciproque
complète (`Presheaf.IsFlasque` ⇒ `IsFlasqueSieves`) exigerait l'argument
de Zorn sur les familles multi-flèches — le prolongement mono est sans
choix, l'amalgamation générale ne l'est pas. Elle reste ouverte et
documentée ici.

Références :
  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §3 (théorème de la suite exacte courte) et II §5 (Zorn).
  - Mathlib, `Mathlib.Topology.Sheaves.Flasque` (revendiqué) — la preuve
    `epi_of_shortExact` et son unique consommation de l'hypothèse.
  - SGA 4, Exposé II (sites et cribles).
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Chap. II §3, III §4 (familles compatibles).
  - Partie 79 (`Grothendieck.Flasque`) : `IsFlasqueSieves`.
  - Partie 80 (`Grothendieck.FlasqueStability`) : la ligne « sans choix ».
  - Partie 81 (`Grothendieck.FlasqueRetract`) : rétractes, même frontière.

Convention i18n (EPIC #4980 ratifiée 2026-07-04) : ce module est jumelé avec
sa version anglaise canonique dans le fichier sibling
`Grothendieck/FlasqueExact_en.lean` — suffixe `_en` sur le namespace
(`Grothendieck.FlasqueExact_en`), imports miroirs, docstrings et commentaires
traduits. Les énoncés de théorèmes, tactiques Lean, noms de lemmes et
références Mathlib restent en anglais (Mathlib 4, tactic DSL standard).
Seules les docstrings `/-- ... -/` et commentaires `-- ...` diffèrent entre
les deux fichiers. Anti-§D byte-identity garanti : le namespace body est
préservé bit-à-bit (énoncés et preuves byte-identiques entre
`FlasqueExact.lean` et `FlasqueExact_en.lean`).

Epic #1646, Phase 2 (#2159). Tous les `sorry`s éliminés à la création.
-/

import Grothendieck.Flasque

namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

section Site

variable {C : Type u} [Category.{v} C]

/-- Le crible **maximal** amalgamate toujours : toute famille compatible
sur `⊤` est entièrement déterminée par sa valeur en `𝟙` — la compatibilité
appliquée au couple `(g, 𝟙)` au-dessus de `(𝟙, g)` force
`x g = P.map g.op (x 𝟙)` pour toute flèche `g`. Aucune hypothèse sur `P` :
la flasquité de cribles (Partie 79) est une condition sur les cribles
**propres**, le crible maximal n'y contribue rien. -/
theorem exists_isAmalgamation_of_sieveTop {P : Cᵒᵖ ⥤ Type (max v u)} {A : C}
    (x : (⊤ : Sieve A).arrows.FamilyOfElements P) (hx : x.Compatible) :
    ∃ t, x.IsAmalgamation t := by
  refine ⟨x (𝟙 A) (Sieve.top_apply (𝟙 A)), ?_⟩
  intro Y g _
  have h := hx (Y₁ := A) (Y₂ := Y) (Z := Y) (g₁ := g) (g₂ := 𝟙 Y)
    (f₁ := 𝟙 A) (f₂ := g) (Sieve.top_apply (𝟙 A)) (Sieve.top_apply g) (by simp)
  simpa using h

/-- **Prolongement le long d'un mono** : un préfaisceau flasque de cribles
étend toute section le long de toute flèche mono `f : B ⟶ A`. La famille
singleton d'une section `s` de `B` n'est compatible que si `s` est
invariante par les paires `p₁ ≫ f = p₂ ≫ f` — condition qu'un mono rend
triviale (`cancel_mono`). C'est la lecture « sous-objet » du prolongement
des sections : le crible engendré par `f` est l'image du sous-objet `B`
dans `A`, et l'amalgamation y est exactement le prolongement de `s`. -/
theorem exists_lift_of_isFlasqueSieves_of_mono {P : Cᵒᵖ ⥤ Type (max v u)}
    [IsFlasqueSieves P] {A B : C} (f : B ⟶ A) [Mono f] (s : P.obj (op B)) :
    ∃ t : P.obj (op A), P.map f.op t = s := by
  have hx₀ : ((Presieve.FamilyOfElements.singletonEquiv P f).symm s : (Presieve.singleton f).FamilyOfElements P).Compatible := by
    rw [Presieve.FamilyOfElements.compatible_singleton_iff]
    intro Z p₁ p₂ h
    have hp : p₁ = p₂ := (CategoryTheory.cancel_mono f).mp h
    subst hp
    rfl
  obtain ⟨t, ht⟩ := IsFlasqueSieves.amalgamates (Sieve.generate (Presieve.singleton f))
    ((Presieve.FamilyOfElements.singletonEquiv P f).symm s).sieveExtend hx₀.sieveExtend
  have h1 : (((Presieve.FamilyOfElements.singletonEquiv P f).symm s).sieveExtend.restrict
    (Sieve.le_generate (Presieve.singleton f))).IsAmalgamation t :=
    Presieve.isAmalgamation_restrict (Sieve.le_generate (Presieve.singleton f)) _ _ ht
  rw [Presieve.restrict_extend hx₀] at h1
  rw [Presieve.FamilyOfElements.isAmalgamation_singleton_iff] at h1
  exact ⟨t, by simpa [Presieve.FamilyOfElements.singletonEquiv_symm_apply_self] using h1⟩

end Site

section Topologique

open TopCat TopCat.Presheaf TopologicalSpace

open scoped AlgebraicGeometry

variable {X : TopCat.{u}}

/-- **Réciproque topologique partielle** : un préfaisceau flasque au sens
de Mathlib (`Presheaf.IsFlasque` — restriction épimorphe le long de
**toute** flèche de `(Opens X)ᵒᵖ`) amalgamate toute famille compatible sur
un crible **engendré par une flèche unique**. La surjectivité le long du
générateur `f` fournit le candidat ; la compatibilité restreinte au
singleton est exactement l'équation d'amalgamation. L'écart résiduel
entre `Presheaf.IsFlasque` et `IsFlasqueSieves` (Partie 79) se situe
entièrement dans les cribles **multi-générateurs** — frontière Zorn,
documentée en tête de module. -/
theorem exists_isAmalgamation_of_isFlasque_generate_singleton
    {P : TopCat.Presheaf Type X} [P.IsFlasque] {A B : Opens X} (f : B ⟶ A)
    (x : (Sieve.generate (Presieve.singleton f)).arrows.FamilyOfElements P)
    (hx : x.Compatible) : ∃ t, x.IsAmalgamation t := by
  have hf : Epi (P.map f.op) := IsFlasque.epi f.op
  obtain ⟨t, ht⟩ := (CategoryTheory.epi_iff_surjective _).mp hf
    (x f (Sieve.le_generate (Presieve.singleton f) _ _ ⟨⟩))
  have h0 : (x.restrict (Sieve.le_generate (Presieve.singleton f))).IsAmalgamation t :=
    (Presieve.FamilyOfElements.isAmalgamation_singleton_iff f _ _).mpr
      (by simpa [Presieve.FamilyOfElements.restrict] using ht)
  exact ⟨t, by
    rw [← Presieve.extend_restrict hx]
    exact Presieve.isAmalgamation_sieveExtend _ _ h0⟩

open TopCat.Sheaf.IsFlasque in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **Godement II.3 lu côté cribles** : pour une suite exacte courte de
faisceaux de groupes abéliens, si `X₁` est flasque **au sens des cribles**
(Partie 79, via l'oubli vers les types), alors `S.g` est épimorphe sur
chaque ouvert. La preuve Zorn de Mathlib (`epi_of_shortExact`) consomme la
flasquité de `X₁` une seule fois, sur l'inclusion `homOfLE inf_le_right` ;
la reprise locale de l'argument — seul ce maillon est substitué par
`exists_lift_of_isFlasqueSieves_of_mono` — montre que l'hypothèse « epi le
long de toute flèche » peut être remplacée par « amalgamation sur tout
crible ». [God58] Chap. II §3. -/
theorem epi_of_shortExact_of_isFlasqueSieves {S : ShortComplex (Sheaf AddCommGrpCat X)}
    (hS : S.ShortExact) [IsFlasqueSieves (S.X₁.obj ⋙ CategoryTheory.forget AddCommGrpCat)]
    {U : Opens X} : Epi (S.g.1.app (op U)) := by
  refine (AddCommGrpCat.epi_iff_surjective _).mpr (fun s => ?_)
  obtain ⟨t, ht⟩ := exists_maximal_of_chains_bounded
    (structured_arrows_elements_sheaf_chains_bounded S.g s)
    (fun ⟨f⟩ ⟨g⟩ => ⟨g ≫ f⟩)
  have tle : t.right.1.unop ≤ U := leOfHom t.hom.1.unop
  have tcomp : s |_ t.right.1.unop = S.g.hom.app t.right.1 t.right.2 :=
    CategoryOfElements.map_snd t.hom
  have hU : U ≤ t.right.1.unop := by
    intro x hx
    have hls := (TopCat.Sheaf.isLocallySurjective_iff_epi S.g).mpr hS.epi_g
    obtain ⟨W, Wle, ⟨t₁, ht₁⟩, hW⟩ := (isLocallySurjective_iff S.g.hom).mp hls U s x hx
    let t₂ := t.right.2 |_ (t.right.1.unop ⊓ W) - t₁ |_ (t.right.1.unop ⊓ W)
    have h0 : (S.g.hom.app (op (t.right.1.unop ⊓ W))) t₂ = 0 := by
      simp [map_restrict, ← tcomp, restrict_restrict, ht₁, t₂]
    obtain ⟨t₃, ht₃⟩ := Sheaf.sections_exact_of_left_exact hS.1 hS.2 t₂ h0
    obtain ⟨t₄, (htr : t₄ |_ (t.right.1.unop ⊓ W) = t₃)⟩ :=
      exists_lift_of_isFlasqueSieves_of_mono
        (P := S.X₁.obj ⋙ CategoryTheory.forget AddCommGrpCat)
        (homOfLE inf_le_right) t₃
    let f : Fin 2 → Opens X := ![t.right.1.unop, W]
    let sf : (i : Fin 2) → S.X₂.obj.obj (op (f i))
    | 0 => t.right.2
    | 1 => t₁ + (S.f.hom.app (op W)) t₄
    have hagree : sf 0 |_ (t.right.1.unop ⊓ W) = sf 1 |_ (t.right.1.unop ⊓ W) := by
      dsimp [sf, f]
      simp only [restrict_sum, ← map_restrict, htr, ht₃, t₂, add_sub_cancel]
    obtain ⟨t₅, ht₅, _⟩ : ∃! t₅, IsGluing S.X₂.obj f sf t₅ := by
      apply Sheaf.existsUnique_gluing
      simp only [IsCompatible, Fin.forall_fin_two]
      refine ⟨⟨rfl, hagree⟩, Eq.symm ?_, rfl⟩
      apply_fun (fun s => restrictOpen s (W ⊓ t.right.1.unop)
        (le_of_eq (inf_comm _ _))) at hagree
      rw [restrict_restrict, restrict_restrict] at hagree
      exact hagree
    have le : iSup f ≤ U := iSup_le_iff.mpr (Fin.forall_fin_two.mpr ⟨tle, Wle⟩)
    let t₆ : Under S.g s :=
      StructuredArrow.mk (S := ⟨op U, s⟩)
        (T := (Functor.whiskerRight S.g.hom (CategoryTheory.forget AddCommGrpCat)).mapElements)
        (Y := ⟨op (iSup f), t₅⟩) <| CategoryOfElements.homMk _ _ (homOfLE le).op (by
        refine (TopCat.Sheaf.eq_app_of_locally_eq ht₅ (by rw [Fin.forall_fin_two]; exact ⟨tle, Wle⟩) ?_).symm
        rw [Fin.forall_fin_two]
        refine ⟨tcomp.symm, ?_⟩
        simp only [Fin.isValue, map_add, homOfLE_leOfHom, sf, f]
        have hfg : (S.f.hom.app (op W) ≫ S.g.hom.app (op W)) = 0 := by
          rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom, S.zero]
          rfl
        simp [← CategoryTheory.comp_apply, hfg, ht₁]
        rfl)
    have h₆ : Nonempty (t₆ ⟶ t) := Nonempty.intro (StructuredArrow.homMk
      (CategoryOfElements.homMk _ _ (homOfLE (le_iSup f 0)).op (ht₅ 0)) (by cat_disch))
    exact leOfHom ((ht t₆) h₆).some.right.1.unop ((le_iSup f 1) hW)
  exact ⟨t.right.2 |_ U, by simp [map_restrict, ← tcomp, restrict_restrict]⟩

end Topologique

end Grothendieck
