/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Grothendieck hommage — Partie 80 : stabilite de la flasquie, isomorphismes
et produits, frontiere de l'acyclicite.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #1646).

La Partie 79 a defini la flasquie au niveau des sites
(`Grothendieck.Flasque`, `IsFlasqueSieves`) : toute famille compatible sur
n'importe quel crible possede une amalgamation. Cette partie etudie la
**stabilite** de cette notion — la question qu'on pose a toute propriete
de faisceau des qu'elle est definie : par quels foncteurs est-elle
preservee ?

Ce que Mathlib formalise, c'est la version topologique
(`Mathlib.Topology.Sheaves.Flasque`) : stabilite de la flasquie par **image
directe** (`pushforward_isFlasque`). Ce que cette partie ajoute, pour la
version site de la Partie 79 :

  - `isFlasqueSieves_of_iso` : la flasquie est une propriete **invariante
    par isomorphisme** de prefaisceau. Godement la compte comme evidente
    (II.3.1) ; l'enregistrer la rend consommable par les parties
    ultérieures sans re-demonstration. La preuve transporte famille et
    amalgamation le long de l'iso, la compatibilite suivant la naturalite.

  - `isFlasqueSieves_pi` : tout **produit** de prefaisceaux flasques est
    flasque (Godement II.3.2, premiere moitie : produits et sommes directes
    de faisceaux flasques sont flasques ; les sommes directes, elles, vivent
    cote faisceaux abeliens). Une famille compatible sur un produit se
    projette en familles compatibles composante par composante, chacune
    s'amalgame, et l'amalgamation globale est le vecteur des amalgamations.
    Le point technique est le transport a travers `piObjIso`
    (`Mathlib.CategoryTheory.Limits.FunctorCategory`) : evaluer un produit
    de foncteurs, c'est prendre le produit des evaluations.

  - `subsingleton_H_succ_of_flasque_of_injective` : le **croisement** avec
    la cohomologie de la Partie 20 (`Grothendieck.SheafCohomology.Basic`) :
    un faisceau abelien flasque **et** injectif est acyclique —
    `Subsingleton (H F (n+1))`. Ce theoreme delivre son contenu dans
    l'enonce, pas la preuve (`inferInstance`, l'annulation etant une
    instance Mathlib deja pontee en Partie 20) : il pose la pierre ou
    Godement met Zorn. Le theoreme complet de Godement (II.5.2-5.3) est
    *flasque => injectif => Γ-acyclique* ; ici, **le seul maillon manquant
    est `flasque => injectif`** (II.5.2, demonstration par prolongement
    inductif via le lemme de Zorn), explicitement documente comme frontiere
    du lake : la chaine demontrable sans Zorn est enregistree, le maillon
    Zorn est laisse ouvert.

La lecture conceptuelle : les stabilites enregistrees ici sont celles qui
ne coutent **aucun choix** — l'isomorphisme transporte une structure
canoniquement, le produit amalgame composante par composante parce que
compatibilite et amalgamation se lisent composante par composante. La
frontiere est exactement la ou un choix (le prolongement maximal de Zorn)
devient necessaire : *flasque => injectif* n'est pas canonique. Cette
ligne de partage — ce qui se fait sans choix, ce qui exige le choix — est
une ligne grothendieckienne par excellence.

References :
  - R. Godement, *Topologie algebrique et theorie des faisceaux* [God58],
    Chap. II §3 (prop. 2 : stabilite par produits) et §5 (acyclicite des
    flasques, theoreme 5.2 : flasque => injectif par Zorn).
  - SGA 4, Expose II (sites et cribles).
  - Mathlib, `Mathlib.CategoryTheory.Limits.FunctorCategory` (`piObjIso`).
  - Partie 20 (`Grothendieck.SheafCohomology.Basic`) : la cohomologie Ext.
  - Partie 79 (`Grothendieck.Flasque`) : `IsFlasqueSieves`.
  - Partie 63 (`Grothendieck.SheafCondition`) : la decomposition
    produit-egaliseur dont la flasquie est la moitie existence.

Convention i18n (EPIC #4980 ratifiee 2026-07-04) : ce module est jumele avec
sa version anglaise canonique dans le fichier sibling
`Grothendieck/FlasqueStability_en.lean` — suffixe `_en` sur le namespace
(`Grothendieck.FlasqueStability_en`), imports miroirs, docstrings et
commentaires traduits. Les enonces de theoremes, tactiques Lean, noms de
lemmes et references Mathlib restent en anglais (Mathlib 4, tactic DSL
standard). Seules les docstrings `/-- ... -/` et commentaires `-- ...`
different entre les deux fichiers. Anti-§D byte-identity garanti : le
namespace body est preserve bit-a-bit (enonces et preuves byte-identiques
entre `FlasqueStability.lean` et `FlasqueStability_en.lean`).

Epic #1646, Phase 2 (#2159). Tous les `sorry`s elimines a la creation.
-/

import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Grothendieck.Flasque
import Grothendieck.SheafCohomology.Basic

namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

section Site

variable {C : Type u} [Category.{v} C]

/-- **Invariance par isomorphisme** : si `P ≅ Q` et `P` est flasque, `Q`
l'est aussi. La famille `Q` se transporte en famille `P` via `e.inv`, la
compatibilite suit la naturalite, et l'amalgamation `t` revient par
`e.hom`. Godement compte cela comme evident (II.3.1) ; l'enregistrer
evite a chaque partie aval de re-demontrer le transport. -/
theorem isFlasqueSieves_of_iso {P Q : Cᵒᵖ ⥤ Type (max v u)} (e : P ≅ Q)
    [IsFlasqueSieves P] : IsFlasqueSieves Q where
  amalgamates := by
    intro X S x hx
    obtain ⟨t, ht⟩ := IsFlasqueSieves.amalgamates (P := P) S
      (fun Y f hf => e.inv.app (op Y) (x f hf))
      (fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ h => by
        show P.map g₁.op (e.inv.app (op Y₁) (x f₁ hf₁))
          = P.map g₂.op (e.inv.app (op Y₂) (x f₂ hf₂))
        rw [← NatTrans.naturality_apply (φ := e.inv) g₁.op (x f₁ hf₁),
          ← NatTrans.naturality_apply (φ := e.inv) g₂.op (x f₂ hf₂),
          hx g₁ g₂ hf₁ hf₂ h])
    refine ⟨e.hom.app (op X) t, ?_⟩
    intro Y f hf
    have nat : (Q.map f.op) (e.hom.app (op X) t)
        = e.hom.app (op Y) ((P.map f.op) t) :=
      (NatTrans.naturality_apply (φ := e.hom) f.op t).symm
    rw [nat, ht f hf]
    simp

end Site

section Produit

variable {C : Type u} [Category.{v} C]

/-- **Stabilite par produit** (Godement II.3.2, premiere moitie) : tout
produit indexe de prefaisceaux flasques est flasque. Une famille
compatible se projette composante par composante via `piObjIso`, chaque
composante s'amalgame par flasquie, et le vecteur des amalgamations
amalgame la famille originale. C'est une stabilite que la version
topologique de Mathlib n'enregistre pas : elle ne vit que cote sites. -/
theorem isFlasqueSieves_pi {ι : Type (max v u)} (P : ι → (Cᵒᵖ ⥤ Type (max v u)))
    [∀ i, IsFlasqueSieves (P i)] : IsFlasqueSieves (∏ᶜ P) where
  amalgamates := by
    intro X S x hx
    -- Projeter puis evaluer, c'est evaluer la composante naturelle (en tout z).
    have proj : ∀ (i : ι) (Y : C) (z : (∏ᶜ P).obj (op Y)),
        (Pi.π (fun s => (P s).obj (op Y)) i) ((piObjIso P (op Y)).hom z)
          = (Pi.π P i).app (op Y) z := by
      intro i Y z
      have h := piObjIso_hom_comp_π P (op Y) i
      exact ConcreteCategory.congr_hom h z
    -- La famille composante est compatible : naturalite des projections.
    have hcomp : ∀ i,
        Presieve.FamilyOfElements.Compatible
          (fun Y f hf => (Pi.π P i).app (op Y) (x f hf)) := by
      intro i Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ h
      show (P i).map g₁.op ((Pi.π P i).app (op Y₁) (x f₁ hf₁))
          = (P i).map g₂.op ((Pi.π P i).app (op Y₂) (x f₂ hf₂))
      rw [← NatTrans.naturality_apply (φ := Pi.π P i) g₁.op (x f₁ hf₁),
        ← NatTrans.naturality_apply (φ := Pi.π P i) g₂.op (x f₂ hf₂),
        hx g₁ g₂ hf₁ hf₂ h]
    choose t ht using fun i =>
      IsFlasqueSieves.amalgamates (P := P i) S
        (fun Y f hf => (Pi.π P i).app (op Y) (x f hf)) (hcomp i)
    -- L'amalgamation globale : la famille t relevee au produit des evaluations.
    let w : ∏ᶜ (fun s => (P s).obj (op X)) :=
      (Pi.lift (fun i => TypeCat.ofHom (fun _ : PUnit.{max v u + 1} => t i))) PUnit.unit
    refine ⟨(piObjIso P (op X)).inv w, ?_⟩
    intro Y f hf
    -- La i-eme composante du candidat est exactement t i.
    have hπ : ∀ i : ι, (Pi.π P i).app (op X) ((piObjIso P (op X)).inv w) = t i := by
      intro i
      have h := piObjIso_inv_comp_π P (op X) i
      have h2 : (Pi.π P i).app (op X) ((piObjIso P (op X)).inv w)
          = (Pi.π (fun s => (P s).obj (op X)) i) w :=
        ConcreteCategory.congr_hom h w
      rw [h2]
      simp [w, TypeCat.ofHom_apply]
    -- Egalite composante par composante apres transport piObjIso.
    have comp : ∀ i : ι,
        (Pi.π (fun s => (P s).obj (op Y)) i) ((piObjIso P (op Y)).hom
          ((∏ᶜ P).map f.op ((piObjIso P (op X)).inv w)))
          = (Pi.π (fun s => (P s).obj (op Y)) i) ((piObjIso P (op Y)).hom
            (x f hf)) := by
      intro i
      rw [proj i Y ((∏ᶜ P).map f.op ((piObjIso P (op X)).inv w)),
        proj i Y (x f hf),
        NatTrans.naturality_apply (φ := Pi.π P i) f.op ((piObjIso P (op X)).inv w),
        hπ i, ht i f hf]
    -- L'extensionnalite des elements d'un produit de types est le lemme
    -- Mathlib Types.limit_ext (meme pattern que Equalizer.FirstObj.ext).
    have heq : (piObjIso P (op Y)).hom
        ((∏ᶜ P).map f.op ((piObjIso P (op X)).inv w))
        = (piObjIso P (op Y)).hom (x f hf) := by
      apply Limits.Types.limit_ext
      rintro ⟨i⟩
      exact comp i
    -- Un iso est injectif : conclure par le transport inverse.
    have inj : ∀ a b : (∏ᶜ P).obj (op Y),
        (piObjIso P (op Y)).hom a = (piObjIso P (op Y)).hom b → a = b := by
      intro a b hab
      calc a = (piObjIso P (op Y)).inv ((piObjIso P (op Y)).hom a) := by simp
        _ = (piObjIso P (op Y)).inv ((piObjIso P (op Y)).hom b) := by rw [hab]
        _ = b := by simp
    exact inj _ _ heq

end Produit

section Acyclicite

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **Croisement Partie 20 x Partie 79 — flasque et injectif est
acyclique** : pour un faisceau abelien `F` flasque au niveau des cribles
(compose par `forget`) **et** injectif dans la categorie des faisceaux, la
cohomologie `H^{n+1}` est triviale. L'annulation est l'instance Mathlib
deja pontee par la Partie 20 ; ce theoreme la consomme dans le cadre
flasque. La pierre posee ici designe exactement le maillon manquant du
theoreme de Godement II.5 : *flasque => injectif* (II.5.2, par Zorn) —
frontiere documentee du lake, consciemment non franchie. -/
theorem subsingleton_H_succ_of_flasque_of_injective
    (F : Sheaf J AddCommGrpCat.{max v u}) [Injective F]
    [HasSheafify J AddCommGrpCat.{max v u}]
    [HasExt (Sheaf J AddCommGrpCat.{max v u})]
    [IsFlasqueSieves (F.obj ⋙ forget AddCommGrpCat.{max v u})] {n : ℕ} :
    Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) := by
  infer_instance

end Acyclicite

end Grothendieck
