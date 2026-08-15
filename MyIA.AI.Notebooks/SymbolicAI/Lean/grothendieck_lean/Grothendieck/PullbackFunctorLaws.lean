/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 38 : lois de foncteur du pullback

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-37 ont etabli les fondamentaux : categories, cribles,
topologies, lois de treillis, identites de pullback, bases de faisceaux,
cloture couvrante, calibration, sous-canonicalite, topologies denses,
faisceaux, hom interne, cohomologie de Cech, limite de Mayer-Vietoris,
extensions de Kan, adjonctions, monades, equivalences, categories monoidales,
limites et colimites, couples comma, images directes, theoremes propres sur la
forme fleche (`J.Covers S f`), sur la couverture bundlee (`J.Cover X`) et les
lois de coherence du pseudo-foncteur pullback (Partie 37).

La Partie 37 a prouve les **lois de coherence** des isomorphismes naturels
`J.pullbackId X` et `J.pullbackComp f g` fournis par Mathlib. Cette partie va
plus loin : elle enonce et prouve les **lois de foncteur elles-memes** — les
egalites de foncteurs que Mathlib ne fournit **pas** (il n'enregistre que les
definitions `pullbackId`/`pullbackComp` au niveau iso) :

  - `pullback_functor_id` : pullbacker le long de l'identite est le foncteur
    identite — `J.pullback (𝟙 X) = 𝟭 (J.Cover X)`.
  - `pullback_functor_comp` : la contravariance — pullbacker le long de la
    composee `f ≫ g` est la composee des pullbacks —
    `J.pullback (f ≫ g) = J.pullback g ⋙ J.pullback f`.
  - `pullback_functor_comp_assoc` : l'associativite de la contravariance
    (deux groupements du produit de foncteurs).
  - `covers_pullback_comp` : la traduction de la contravariance a la forme
    fleche — `J.Covers S (f ≫ g)` equivaut a `J.Covers (S.pullback g) f`.

Chaque preuve est une **preuve tactique reelle** (veine DEEP) : `Functor.ext`
ramene l'egalite de foncteurs aux objets et aux fleches ; sur les objets,
`GrothendieckTopology.Cover.ext` + les lois de pullback de Mathlib
(`Sieve.pullback_id`, `Sieve.pullback_comp`) ; sur les fleches,
`Subsingleton.elim` (le codomaine `J.Cover X` est un preordre).

EPIC #1646, Phase 5 (#2159). Tous les `sorry`s elimines a la creation.

### Convention i18n (EPIC #4980 ratifiee par user 2026-07-04)

Ce module est apparie avec son jumeau anglais dans le fichier sibling
`PullbackFunctorLaws_en.lean` (modele sibling pair, voir PR #6154 pour le
pilote sur `Utility.lean`). Namespace suffix `_en` applique au fichier EN
(anti-collision, conforme code-style.md #4980). Les enonces de theoremes, les
noms de lemmes, les tactiques Lean et les references Mathlib restent en
anglais ; seules les docstrings `/-- ... -/` et les commentaires `-- ...`
different entre les deux fichiers (preservation byte-identity).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Functor.Category

namespace Grothendieck.PullbackFunctorLaws

open CategoryTheory

/-!
## Section 1 : lois de foncteur

Mathlib definit le foncteur contravariant `J.pullback f : J.Cover Y ⥤ J.Cover X`
pour une fleche `f : X ⟶ Y` (`@[simps obj]` : `(J.pullback f).obj S = S.pullback f`),
et les isomorphismes naturels `J.pullbackId X` / `J.pullbackComp f g`. Il ne
fournit **pas** les lois de foncteur correspondantes. Ce module les enonce et
les prouve — ce sont des egalites de foncteurs, plus fortes que les
isomorphismes. Strategie commune : `Functor.ext` decompose en composante
objet (lois de pullback de Mathlib) et composante fleche (`Subsingleton.elim`,
le preordre `J.Cover X` a des ensembles de fleches subsingletons).
-/

/-- Pullbacker le long de l'identite est le foncteur identite :
    `J.pullback (𝟙 X) = 𝟭 (J.Cover X)`.
    Preuve : `Functor.ext` ; sur les objets, `Cover.ext` + `Sieve.pullback_id`
    (`(f ≫ 𝟙 X)` se reduit a `f`) ; sur les fleches, `Subsingleton.elim`. -/
theorem pullback_functor_id {C : Type*} [Category C] (X : C)
    (J : GrothendieckTopology C) :
    J.pullback (𝟙 X) = 𝟭 (J.Cover X) := by
  apply CategoryTheory.Functor.ext
  · intro S T g
    apply Subsingleton.elim
  · intro S
    change S.pullback (𝟙 X) = S
    apply GrothendieckTopology.Cover.ext
    intro Y f
    rw [GrothendieckTopology.Cover.coe_pullback]
    simp [Category.comp_id]

/-- Contravariance du pullback : `J.pullback (f ≫ g) = J.pullback g ⋙ J.pullback f`.
    Preuve : `Functor.ext` ; sur les objets, `Cover.ext` + trois
    `coe_pullback` ramenant la membership de gauche a celle de droite via
    l'associativite `simp` ; sur les fleches, `Subsingleton.elim`. -/
theorem pullback_functor_comp {C : Type*} [Category C] {X Y Z : C}
    (J : GrothendieckTopology C) (f : X ⟶ Y) (g : Y ⟶ Z) :
    J.pullback (f ≫ g) = J.pullback g ⋙ J.pullback f := by
  apply CategoryTheory.Functor.ext
  · intro S T g'
    apply Subsingleton.elim
  · intro S
    change S.pullback (f ≫ g) = (S.pullback g).pullback f
    apply GrothendieckTopology.Cover.ext
    intro Y f'
    rw [GrothendieckTopology.Cover.coe_pullback, GrothendieckTopology.Cover.coe_pullback,
      GrothendieckTopology.Cover.coe_pullback]
    simp [Category.assoc]

/-- Associativite de la contravariance : pullbacker le long de `f ≫ g ≫ h`
    est, quel que soit le groupement, pullbacker le long de `h`, puis `g`,
    puis `f`. Preuve : deux reecritures de `pullback_functor_comp` puis
    `rfl` (l'associativite du produit des foncteurs est definitionnelle). -/
theorem pullback_functor_comp_assoc {C : Type*} [Category C] {W X Y Z : C}
    (J : GrothendieckTopology C) (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    J.pullback (f ≫ g ≫ h) = J.pullback h ⋙ (J.pullback g ⋙ J.pullback f) := by
  rw [pullback_functor_comp J f (g ≫ h)]
  rw [pullback_functor_comp J g h]
  rfl

/-!
## Section 2 : forme fleche (J.Covers)

La forme fleche `J.Covers S f` est definie par `S.pullback f ∈ J Y` (Mathlib,
`GrothendieckTopology.Covers` ; `covers_iff` est `Iff.rfl`). Le theoreme
suivant traduit la contravariance de la section precedente dans cette forme.
-/

/-- Traduction de `pullback_functor_comp` a la forme fleche : couvrir `S` le
    long de `f ≫ g` equivaut a couvrir `S.pullback g` le long de `f`.
    Preuve : `rw [covers_iff]` des deux cotes puis `Sieve.pullback_comp` (les
    deux membres sont `∈ J X`). -/
theorem covers_pullback_comp {C : Type*} [Category C] {X Y Z : C}
    (J : GrothendieckTopology C) (f : X ⟶ Y) (g : Y ⟶ Z) (S : J.Cover Z) :
    J.Covers (S : Sieve Z) (f ≫ g) ↔ J.Covers (S.pullback g : Sieve Y) f := by
  rw [GrothendieckTopology.covers_iff, GrothendieckTopology.covers_iff]
  rw [Sieve.pullback_comp]
  simp

end Grothendieck.PullbackFunctorLaws
