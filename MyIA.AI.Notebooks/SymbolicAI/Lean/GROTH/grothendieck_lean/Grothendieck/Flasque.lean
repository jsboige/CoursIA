/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Grothendieck hommage — Partie 82 : faisceaux flasques, du topologique au site.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #1646).

Un faisceau est **flasque** (flabby, SGA 4 II 3.2 ; MM92 II.3 ; Godement)
lorsque ses sections s'étendent : toute section sur un « sous-objet ouvert »
se prolonge au tout. Mathlib formalise cette notion pour les espaces
topologiques (`Mathlib.Topology.Sheaves.Flasque`, revendiqué) :

  - `TopCat.Presheaf.IsFlasque F` : toute flèche de restriction `F.map i`
    est épimorphisme ;
  - l'instance `pushforward_isFlasque` : stabilité par image directe ;
  - `isFlasque_skyscraperSheaf_of_epi_from` et
    `isFlasque_skyscraperSheaf_of_hasZeroObject` : le gratte-ciel est flasque.

Ce que Mathlib ne pose **nulle part**, c'est la version **site** de la
flasquité — la lecture qui remplace « ouvert inclus dans un ouvert » par
« crible sur un objet », c'est-à-dire sous-objet du représentable dans la
topologie de Grothendieck. C'est ce que cette partie introduit :

  `IsFlasqueSieves P` : toute famille compatible sur **n'importe quel**
  crible `S` de `X` — couvrant ou non — possède une amalgamation.

Les conséquences enregistrées :

  - `nonempty_obj_of_isFlasqueSieves` : même le crible **vide** doit
    amalgamer — donc `P.obj (op X)` est non vide pour tout `X`. C'est la
    subtilité que la définition topologique ne voit pas : la flèche vers
    l'ouvert vide y est trivialement épi, alors qu'ici le crible vide exige
    l'existence d'une section globale.
  - `isSheaf_of_isFlasqueSieves_of_isSeparated` : **flasque + séparé ⇒
    faisceau**. La flasquité fournit l'existence de l'amalgamation (sur tout
    crible, donc sur les couvrants), la séparation fournit l'unicité — le
    théorème classique, ici par chaînage explicite de `IsSeparated.isSheaf`.
  - `isFlasqueSieves_const_of_subsingleton` : le préfaisceau **constant**
    n'est flasque que si la valeur est un **sous-singulier non vide**. La
    condition `Subsingleton` n'est pas de la prudence : deux flèches
    incomparables d'un crible peuvent porter des valeurs distinctes, qu'aucune
    amalgamation ne peut réconcilier — la compatibilité ne contraint que les
    flèches liées par factorisation. C'est le pendant exact du gratte-ciel :
    en dehors du point, la valeur est terminale, donc sous-singulière — et
    c'est précisément là que le gratte-ciel est flasque (croisement Partie 77).
  - `pushforward_isFlasque_bridge` : le pont vers l'instance de Mathlib,
    lu dans le vocabulaire de l'image directe de la Partie 33 ;
  - `isFlasque_skyscraper_bridge` : le pont vers le théorème
    gratte-ciel-flasque de Mathlib, lu comme application de la Partie 77 —
    le gratte-ciel à valeurs dans une catégorie à objet nul est flasque, et
    son support (Partie 77 : `closure {p₀}`) est porté par des sections qui
    s'étendent partout.

La lecture conceptuelle : la flasquité est la moitié « existence » de la
condition de faisceau, payée sur **tous** les cribles plutôt que sur les
seuls couvrants — la séparation est l'autre moitié, et leur réunion est la
condition de faisceau tout entière. La Partie 63 a décomposé cette condition
en produit-égaliseur ; celle-ci la décompose en existence + unicité.

Références :
  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §3 (faisceaux flasques, « mous »).
  - SGA 4, Exposé II (sites et cribles).
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Chap. II §3, Exercice 9 (flabby sheaves).
  - Mathlib, `Mathlib.Topology.Sheaves.Flasque` (revendiqué).
  - Partie 33 (`Grothendieck.DirectImage`) : image directe `f_*`.
  - Partie 63 (`Grothendieck.SheafCondition`) : la condition produit-égaliseur.
  - Partie 77 (`Grothendieck.Skyscraper`) : le gratte-ciel et son support.

Convention i18n (EPIC #4980 ratifiée 2026-07-04) : ce module est jumelé avec
sa version anglaise canonique dans le fichier sibling
`Grothendieck/Flasque_en.lean` — suffixe `_en` sur le namespace
(`Grothendieck.Flasque_en`), imports miroirs, docstrings et commentaires
traduits. Les énoncés de théorèmes, tactiques Lean, noms de lemmes et
références Mathlib restent en anglais (Mathlib 4, tactic DSL standard).
Seules les docstrings `/-- ... -/` et commentaires `-- ...` diffèrent entre
les deux fichiers. Anti-§D byte-identity garanti : le namespace body est
préservé bit-à-bit (énoncés et preuves byte-identiques entre `Flasque.lean`
et `Flasque_en.lean`).

Epic #1646, Phase 2 (#2159). Tous les `sorry`s éliminés à la création.
-/

import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.Topology.Sheaves.Skyscraper

namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

section Site

variable {C : Type u} [Category.{v} C]

/-- **Flasque au niveau des cribles** : toute famille compatible sur
n'importe quel crible `S` de `X` — couvrant ou non — possède une
amalgamation. C'est la moitié « existence » de la condition de faisceau,
exigée sur tous les sous-objets du représentable plutôt que sur les seuls
cribles couvrants. -/
class IsFlasqueSieves (P : Cᵒᵖ ⥤ Type (max v u)) : Prop where
  /-- Toute famille compatible sur tout crible s'amalgame. -/
  amalgamates : ∀ {X : C} (S : Sieve X) (x : S.arrows.FamilyOfElements P),
    x.Compatible → ∃ t, x.IsAmalgamation t

theorem isFlasqueSieves_iff (P : Cᵒᵖ ⥤ Type (max v u)) :
    IsFlasqueSieves P ↔ ∀ {X : C} (S : Sieve X) (x : S.arrows.FamilyOfElements P),
      x.Compatible → ∃ t, x.IsAmalgamation t :=
  ⟨fun h => h.amalgamates, fun h => ⟨h⟩⟩

/-- Le crible **vide** doit amalgamer sa (vide) famille compatible : un
préfaisceau flasque a des sections sur **tout** objet. La définition
topologique de Mathlib ne voit pas ce point — la restriction vers l'ouvert
vide y est trivialement épi. -/
theorem nonempty_obj_of_isFlasqueSieves {P : Cᵒᵖ ⥤ Type (max v u)} [IsFlasqueSieves P]
    (X : C) : Nonempty (P.obj (op X)) := by
  obtain ⟨t, _⟩ := IsFlasqueSieves.amalgamates (P := P) (⊥ : Sieve X)
    (fun Y f hf => False.elim hf)
    (fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ _ _ => False.elim h₁)
  exact ⟨t⟩

/-- **Flasque + séparé ⇒ faisceau** : la flasquité fournit l'existence de
l'amalgamation sur tout crible — donc sur les couvrants —, la séparation
fournit l'unicité. Chaînage explicite de `Presieve.IsSeparated.isSheaf`
(`Mathlib.CategoryTheory.Sites.SheafOfTypes`), dont la prémisse
d'amalgamation est exactement la spécialisation du champ
`IsFlasqueSieves.amalgamates` aux cribles couvrants. -/
theorem isSheaf_of_isFlasqueSieves_of_isSeparated {J : GrothendieckTopology C}
    {P : Cᵒᵖ ⥤ Type (max v u)} [IsFlasqueSieves P] (hsep : Presieve.IsSeparated J P) :
    Presieve.IsSheaf J P :=
  hsep.isSheaf fun _ _ _ x hx => IsFlasqueSieves.amalgamates _ x hx

/-- Le préfaisceau **constant** de valeur `A` est flasque dès que `A` est un
sous-singulier non vide. La condition `Subsingleton` est nécessaire et non
de la prudence : deux flèches incomparables d'un même crible peuvent porter
des valeurs distinctes — la compatibilité ne contraint que les flèches liées
par factorisation, et aucune amalgamation ne peut alors exister. -/
theorem isFlasqueSieves_const_of_subsingleton (A : Type (max v u))
    [Subsingleton A] [Nonempty A] : IsFlasqueSieves ((Functor.const Cᵒᵖ).obj A) where
  amalgamates := by
    intro X S x _
    refine ⟨Classical.choice ‹Nonempty A›, ?_⟩
    intro Y f _
    exact @Subsingleton.elim A _ _ _

end Site

section Topologique

open TopCat TopCat.Presheaf TopologicalSpace

variable {C : Type u} [Category.{v} C]

/-- Pont vers l'instance de Mathlib : l'image directe d'un préfaisceau
flasque le long d'une application continue est flasque. Lu dans le
vocabulaire de la Partie 33 (`Grothendieck.DirectImage`), où le couple
`f_* ⊣ f^*` est la première brique du formalisme des six opérations. -/
theorem pushforward_isFlasque_bridge {X Y : TopCat} {F : TopCat.Presheaf C X}
    [TopCat.Presheaf.IsFlasque F] (f : X ⟶ Y) :
    TopCat.Presheaf.IsFlasque ((TopCat.Presheaf.pushforward C f).obj F) :=
  TopCat.Presheaf.IsFlasque.pushforward_isFlasque F f

/-- Pont vers le théorème gratte-ciel-flasque de Mathlib : un gratte-ciel à
valeurs dans une catégorie à objet nul est flasque. Croisement Partie 77
(`Grothendieck.Skyscraper`) : hors du point `p₀`, la valeur est terminale —
donc sous-singulière, la situation exacte de
`isFlasqueSieves_const_of_subsingleton` — et c'est ce qui rend le prolongement
possible ; le support (`closure {p₀}`, Partie 77) est porté par des sections
qui s'étendent partout. -/
theorem isFlasque_skyscraper_bridge {X : TopCat} (p₀ : ↑X)
    [(U : Opens ↑X) → Decidable (p₀ ∈ U)] (A : C) [HasZeroObject C] :
    (skyscraperSheaf p₀ A).IsFlasque :=
  isFlasque_skyscraperSheaf_of_hasZeroObject p₀ A

end Topologique

end Grothendieck
