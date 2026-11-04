/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A Tribute to Grothendieck — Part 58: The subobject classifier — Ω, the presheaf of sieves

Alexandre Grothendieck (1928-2014).

Extension of #2159 (EPIC #1646).

Parts 1-44 established the foundations: categories, sieves, topologies,
lattice laws (`SieveLattice`), pullback/pushforward identities, sheaves,
sheafification, cohomology. Parts 45-57 systematized the arrow form of the
covering for a growing collection of named topologies.

This part crosses a threshold: it exhibits the **subobject classifier** of
the topos of presheaves and of the topos of sheaves — the ingredient that,
together with cartesian closure and finite limits, defines an **elementary
topos** (Lawvere–Tierney). The Grothendieckian revelation is that this
classifier is not an abstract construction: Ω is literally **the presheaf of
sieves** `Functor.sieves`, the very object that all of Part 6
(`SieveLattice`) equipped with a complete lattice (`pullback_imap`,
`pullback_iinf`, `pushforward_imap`…). The lattice laws of Part 6 are the
internal structure of Ω; Part 58 closes the loop by showing that this very
object classifies subpresheaves.

Key constructions bridged from Mathlib (`CategoryTheory.Topos.Sheaf`):

  - `Functor.sieves C`        : the presheaf `X ↦ Sieve X` — this is Ω
  - `Presheaf.truth C`        : the truth morphism `1 ⟶ Ω`, picking `⊤`
  - `Presheaf.χ m`            : the characteristic map of a mono `m : F ⟶ G`
  - `Presheaf.classifier C`   : the `Subobject.Classifier` of presheaves
  - `Sheaf.Ω J`               : the sheaf of **J-closed** sieves
  - `Sheaf.classifier J`      : the classifier of the topos of sheaves
  - instances `HasSubobjectClassifier (Cᵒᵖ ⥤ Type w)` and `HasSubobjectClassifier (Sheaf J (Type w))`

The topology enters through the door of closed sieves: for a mono `m`
between sheaves, the values of `χ m` are **J-closed** sieves
(`GrothendieckTopology.isClosed_χ_app_apply_of_isSheaf_of_isSeparated`),
and it is this closedness that lets Ω descend from presheaves to sheaves.

All `sorry`s eliminated at creation.

### Accessibility note (Epics #1452/#1453)

This module exposes **12 `#check` verifications** and **4 own theorems**,
organized in 5 sections: (1) Ω is the presheaf of sieves; (2) the truth
morphism and the characteristic map χ; (3) the classifier of presheaves;
(4) the topology filters Ω — closed sieves; (5) the classifier of sheaves.

### i18n convention (EPIC #4980 ratified by user 2026-07-04)

This module is paired with its canonical French version in the sibling file
`Classifier.lean` (sibling pair model). Namespace suffixed `_en`
(anti-collision). The `#check`s, signatures, variables and universes are
byte-identical between the two files; only docstrings and comments differ.
-/

import Mathlib.CategoryTheory.Topos.Sheaf

universe u v w

namespace Grothendieck.Classifier_en

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-!
## Section 1: Ω is the presheaf of sieves

The subobject classifier of a presheaf category lives inside the category
itself: it is `Functor.sieves C`, the object `X ↦ Sieve X`. Each component
of Ω is the complete lattice of sieves on `X` — the object that Part 6
(`SieveLattice`) traversed far and wide. The functoriality (`sieves_map`)
pulls a sieve back along an arrow: this is the `Sieve.pullback` of Part 6,
which preserves ⊥, ⊤, ⊔, ⊓, `iSup` and `iInf`.
-/

-- CALIBRATION: the presheaf of sieves, component by component.
#check @CategoryTheory.Functor.sieves          -- Cᵒᵖ ⥤ Type (max u v), X ↦ Sieve X.unop
#check @CategoryTheory.Functor.sieves_map       -- the functoriality is the pullback of sieves

/-!
## Section 2: The truth morphism and the characteristic map χ

The morphism `truth : 1 ⟶ Ω` is the "true" arrow: at each component, it
picks the maximal sieve `⊤`. The characteristic map `χ m` of a mono
`m : F ⟶ G` sends an element `x : G(X)` to the sieve of arrows `f : Y ⟶ X`
along which `x` lifts into `F`: `f ∈ χ m x` iff `∃ a, G(f)(x) = m(a)`.
-/

-- CALIBRATION: the truth morphism picks the maximal sieve.
#check @CategoryTheory.Presheaf.truth           -- (const PUnit) ⟶ sieves C
#check @CategoryTheory.Presheaf.χ               -- (m : F ⟶ G) : G ⟶ sieves C

variable {F G : Cᵒᵖ ⥤ Type (max u v)} (m : F ⟶ G) (X : Cᵒᵖ) (x : G.obj X)

/-- TRUE (rfl): the truth morphism picks exactly the maximal sieve.
    The component at `X` is constant with value `⊤`. -/
theorem truth_picks_top (X : Cᵒᵖ)
    (b : ((Functor.const Cᵒᵖ).obj PUnit).obj X) :
    (Presheaf.truth C).app X b = (⊤ : Sieve X.unop) := rfl

/-- BRIDGE: membership in the characteristic map reads off the definition —
    `f` belongs to the sieve `χ m x` exactly when `x` lifts into `F` along
    `f`. This is the member-by-member reading of the classifier. -/
theorem chi_app_mem_iff {Y : C} (f : Y ⟶ X.unop) :
    Sieve.arrows ((Presheaf.χ m).app X x) f ↔
      ∃ a : F.obj (Opposite.op Y), G.map f.op x = m.app (Opposite.op Y) a := Iff.rfl

/-- OWN: the characteristic map is downward closed — if `x` lifts along
    `f`, it lifts along any precomposition `g ≫ f`. This is the stability
    under pullback that makes `χ m x` a sieve (and not a mere set of
    arrows): the same proof Mathlib bakes into the definition of `χ`,
    exposed here as a named law. -/
theorem chi_app_downward_closed {Y Z : C} (f : Y ⟶ X.unop) (g : Z ⟶ Y)
    (hf : Sieve.arrows ((Presheaf.χ m).app X x) f) :
    Sieve.arrows ((Presheaf.χ m).app X x) (g ≫ f) := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨F.map g.op a, ?_⟩
  simp [ha, NatTrans.naturality_apply]

/-- OWN: an element defined in `F` has a maximal characteristic —
    if `x = m(a)` lies in the direct image, then `χ m x = ⊤`: the sieve of
    arrows along which `x` lifts is the whole maximal sieve. -/
theorem chi_app_eq_top_of_app (a : F.obj X) (h : m.app X a = x) :
    (Presheaf.χ m).app X x = (⊤ : Sieve X.unop) := by
  refine Sieve.ext fun Y f => ?_
  constructor
  · intro _
    exact Sieve.top_apply f
  · intro _
    refine ⟨F.map f.op a, ?_⟩
    rw [← h]
    exact (NatTrans.naturality_apply m f.op a).symm

/-!
## Section 3: The classifier of presheaves

`Presheaf.classifier C` packages Ω, `truth` and χ into a
`Subobject.Classifier`: every mono `m` admits exactly one characteristic
arrow (the universality `χ_unique`), and the square of `m`, the terminal,
`truth` and `χ m` is a pullback. On an essentially small site, the
`HasSubobjectClassifier` instance is available for free.
-/

-- CALIBRATION: the classifier packaging for presheaves.
#check @CategoryTheory.Presheaf.classifier      -- Subobject.Classifier (Cᵒᵖ ⥤ Type (max u v))
#check @CategoryTheory.Presheaf.comp_χ_eq
#check @CategoryTheory.Presheaf.isPullback_χ_truth
#check @CategoryTheory.Presheaf.χ_unique

variable [EssentiallySmall.{w} C]

/-- CALIBRATION: the classifier instance for type-valued presheaves. -/
example : HasSubobjectClassifier (Cᵒᵖ ⥤ Type w) := inferInstance

variable (J : GrothendieckTopology C)

/-!
## Section 4: The topology filters Ω — closed sieves

A Grothendieck topology `J` carves out of Ω its subsheaf of **J-closed**
sieves (`Functor.closedSieves`). The key bridge: for a mono `m` between
sheaves, every value `(χ m) x` is a J-closed sieve — this is exactly what
allows `χ` to land in the closed sieves and thus descend to the sheaf level.
-/

-- CALIBRATION: the subfunctor of J-closed sieves.
#check @CategoryTheory.Functor.closedSieves     -- subfunctor of sieves, J-closed sieves
#check @CategoryTheory.GrothendieckTopology.IsClosed

-- CALIBRATION (the topology ↔ classifier bridge): the characteristic map
-- of a mono between sheaves takes J-closed values.
#check @CategoryTheory.GrothendieckTopology.isClosed_χ_app_apply_of_isSheaf_of_isSeparated

/-!
## Section 5: The classifier of sheaves

At the sheaf level, Ω becomes the sheaf of closed sieves `Sheaf.Ω J`,
`truth` still picks `⊤` (the maximal sieve is closed), and the
characteristic map of a mono of sheaves is the same as at the presheaf
level — restricted to closed sieves. On an essentially small site, the
topos of sheaves of sets therefore has a subobject classifier: together
with cartesian closure and finite limits, this makes it an **elementary
topos** (Lawvere–Tierney). Mathlib states this consequence in prose; the
`ElementaryTopos` instance itself is not yet available in this revision of
Mathlib — the frontier stays honest, as in the map of Part 4.
-/

-- CALIBRATION: the sheaf of closed sieves and the classifier of sheaves.
#check @CategoryTheory.Sheaf.Ω                  -- Sheaf J (Type (max u v)), J-closed sieves
#check @CategoryTheory.Sheaf.truth               -- terminal ⟶ Ω, picks ⊤ (closed)
#check @CategoryTheory.Sheaf.classifier          -- Subobject.Classifier (Sheaf J (Type (max u v)))

/-- CALIBRATION: the classifier instance for the topos of sheaves. -/
example : HasSubobjectClassifier (Sheaf J (Type w)) := inferInstance

end Grothendieck.Classifier_en
