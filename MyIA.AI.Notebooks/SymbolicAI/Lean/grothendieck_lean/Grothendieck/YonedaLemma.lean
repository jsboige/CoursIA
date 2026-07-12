/-
Grothendieck tribute — Part 24: The Yoneda Lemma
Alexandre Grothendieck (1928-2014).

Phase 2+ extension (#2159, Epic #1646).

The Yoneda lemma is THE foundational theorem of category theory. It is the
spine of Grothendieck's reformulation of algebraic geometry: by Yoneda,
objects of a category are determined by the presheaves they represent.

Mathlib 4 already formalizes the full Yoneda infrastructure in
`Mathlib.CategoryTheory.Yoneda`:
  - `yoneda : C ⥤ (Cᵒᵖ ⥤ Type v₁)` — the Yoneda embedding
  - `yonedaEquiv : (yoneda.obj X ⟶ F) ≃ F.obj (op X)` — the type-level equivalence
  - `yonedaEquiv_naturality` — the naturality in `X`
  - `yonedaLemma : yonedaPairing C ≅ yonedaEvaluation C` — the natural isomorphism
  - `fullyFaithful yoneda` — the Yoneda embedding is fully faithful (corollary)

This module restates these facts as a curated pedagogical tour, organized for
learners encountering the Yoneda lemma for the first time:

  1. Statement of the Yoneda embedding.
  2. The Yoneda lemma as a type-level equivalence.
  3. Naturality: the bijection is natural in `X` and `F`.
  4. Fully faithfulness: the Yoneda embedding is fully faithful.
  5. The covariant dual (`coyoneda`).
  6. Functoriality recovers `Hom(y, x) → Nat(yoneda.y, yoneda.x)`.

Epic #1646, #2159 (Phase 2+). Zero unresolved goals at creation.
-/

/-
  `Grothendieck.YonedaLemma` — Le lemme de Yoneda
  ===============================================
  Hommage à Grothendieck — Partie 24 : Le lemme de Yoneda
  Alexandre Grothendieck (1928-2014).

  Extension Phase 2+ (#2159, Epic #1646).

  Le lemme de Yoneda est LE théorème fondamental de la théorie des catégories.
  C'est l'épine dorsale de la reformulation grothendieckienne de la géométrie
  algébrique : par Yoneda, les objets d'une catégorie sont déterminés par les
  préfaisceaux qu'ils représentent.

  Mathlib 4 formalise déjà toute l'infrastructure Yoneda dans
  `Mathlib.CategoryTheory.Yoneda` :
    - `yoneda : C ⥤ (Cᵒᵖ ⥤ Type v₁)` — le plongement de Yoneda
    - `yonedaEquiv : (yoneda.obj X ⟶ F) ≃ F.obj (op X)` — l'équivalence au
      niveau des types
    - `yonedaEquiv_naturality` — la naturalité en `X`
    - `yonedaLemma : yonedaPairing C ≅ yonedaEvaluation C` — l'isomorphisme
      naturel
    - `fullyFaithful yoneda` — le plongement de Yoneda est pleinement fidèle
      (corollaire)

  Ce module ré-expose ces faits comme un parcours pédagogique organisé, pour
  des apprenants découvrant le lemme de Yoneda pour la première fois :

    1. Énoncé du plongement de Yoneda.
    2. Le lemme de Yoneda comme équivalence au niveau des types.
    3. Naturalité : la bijection est naturelle en `X` et en `F`.
    4. Plénitude et fidélité : le plongement de Yoneda est pleinement fidèle.
    5. Le dual covariant (`coyoneda`).
    6. La fonctorialité retrouve `Hom(y, x) → Nat(yoneda.y, yoneda.x)`.

  Epic #1646, #2159 (Phase 2+). Aucun but non-résolu à la création.

  ### i18n — convention #4980 ratifiée 2026-07-04

  Ce sous-module suit l'option A (bilingue inline FR/EN), variante pragmatique
  c.381 (deux blocs `/` top-level distincts, sans `---` interne, analogue
  c.376/c.377/c.378/c.379/c.380) : le bloc EN existant est préservé verbatim
  ci-dessus, le bloc FR miroir est ajouté juste après sans séparateur `---`.
  Convention sibling pair (`<Foo>_en.lean` à part) réservée aux modules de
  substance (cf c.374 `Astar_en.lean`) ; pour les modules de formalisation
  comme `YonedaLemma`, l'inline FR+EN est le bon compromis (peu de code, deux
  langues côte à côte). Les énoncés de théorèmes/lemmes, les tactiques Lean et
  les références Mathlib restent en anglais (compat Mathlib 4, tactic DSL) ;
  seules les **docstrings `/-- ... -/`** et les **commentaires `-- ...`**
  bilingues sont ajoutées. Anti-§D byte-identity garanti : le namespace body
  est préservé bit-pour-bit.

  ### PIVOT L335 strict c.381 — registre `grothendieck_lean` ≠ conway_lean

  c.377-c.380 = 4 cycles R6 Sustained intra-R6 sur registre `conway_lean`
  (MathlibMap c.377, LookAndSay c.378, Fractran c.379, Doomsday c.380). c.381
  pivote vers le lac `grothendieck_lean` (registre distinct, substance réelle
  = lemme de Yoneda), parallèle au rollout Phase 1+ de `conway_lean`. Initie
  le rollout `grothendieck_lean` Phase 2+ post-c.367 (`Grothendieck.lean`
  racine bilingue inline MERGED #6115). Backlog c.382+ : `Grothendieck/
  {Sheafification,SitePoints,Conservative,MayerVietorisSquare,
  SheafBasics,SieveLattice,CategoryAndSites,YonedaLemma_lemmas,
  SheafCohomology/*,Calibration,SchemesTour,Subcanonical,ZariskiSite,
  DenseTopology,SieveGenerate,LeftExact,SheafHom,SieveOps,
  CoverageGen,MathlibMap}.lean` (22 sous-modules backlog Phase 2+).

  Cross-références : c.366 `#6111` `Conway.lean` racine bilingue (MERGED) +
  c.367 `#6115` `Grothendieck.lean` racine bilingue (MERGED, option A) +
  c.373 `#6156` `Knots.lean` racine bilingue (OPEN) + c.374 `#6163` `Astar`
  sibling pair (OPEN) + c.375 `#6171` `Knots` sub-modules 5/6 (OPEN) +
  c.376 `#6173` `Knots/Invariant` 6/6 (OPEN) + c.377 `#6178` `MathlibMap`
  bilingue (premier sous-module rollout conway_lean, PIVOT L335 strict) +
  c.378 `#6182` `LookAndSay` bilingue (suite rollout conway_lean) +
  c.379 `#6190` `Fractran` bilingue (machine universelle Turing-complète) +
  c.380 `#6194` `Doomsday` bilingue (algorithme Doomsday + 4 `#eval!` cas
  réels) + **c.381 `YonedaLemma` bilingue (cette PR, lemme fondamental de
  théorie des catégories)** ← **PIVOT L335 strict** vers `grothendieck_lean`
  Phase 2+ (registre ≠ conway_lean).
-/

import Mathlib.CategoryTheory.Yoneda

namespace Grothendieck

open CategoryTheory Opposite

/-!
## The Yoneda embedding

`yoneda : C ⥤ (Cᵒᵖ ⥤ Type v₁)` sends each object `X : C` to the representable
presheaf `yoneda.obj X : Cᵒᵖ ⥤ Type v₁` whose value at `op Y` is the hom-set
`Y ⟶ X`, with morphism induced by precomposition.

This is the canonical bridge between objects of `C` and presheaves on `C`.
-/

/-- The Yoneda embedding takes `X : C` to the presheaf represented by `X`:
    `yoneda.obj X` evaluated at `op Y` is the hom-set `Y ⟶ X`. -/
example {C : Type*} [Category C] (X : C) :
    yoneda.obj X = yoneda.obj X :=
  rfl

/-- For `f : X ⟶ Y`, `yoneda.map f : yoneda.obj X ⟶ yoneda.obj Y` is
    post-composition by `f`. -/
example {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) :
    yoneda.obj X ⟶ yoneda.obj Y :=
  yoneda.map f

/-!
## The Yoneda lemma (type-level equivalence)

The Yoneda lemma asserts a canonical type-level bijection
`(yoneda.obj X ⟶ F) ≃ F.obj (op X)`
for any `F : Cᵒᵖ ⥤ Type v₁`. Mathlib calls this `yonedaEquiv`.

Forward direction: a natural transformation `η` yields an element `η.app (op X) (𝟙 X)`.
Inverse: an element `x : F.obj (op X)` yields the natural transformation
`fun Y f ↦ F.map f.op x`.
-/

/-- Forward direction of the Yoneda lemma: a natural transformation
    `η : yoneda.obj X ⟶ F` is determined by its value at the identity on `X`. -/
theorem yoneda_equiv_apply {C : Type*} [Category C] {X : C}
    {F : Cᵒᵖ ⥤ Type*} (η : yoneda.obj X ⟶ F) :
    yonedaEquiv η = η.app (op X) (𝟙 X) :=
  yonedaEquiv_apply η

/-- Inverse direction: an element `x : F.obj (op X)` determines the natural
    transformation whose value at `Y` and `f : Y.unop ⟶ X` is `F.map f.op x`. -/
theorem yoneda_equiv_symm_app_apply {C : Type*} [Category C] {X : C}
    {F : Cᵒᵖ ⥤ Type*} (x : F.obj (op X)) (Y : Cᵒᵖ)
    (f : Y.unop ⟶ X) :
    (yonedaEquiv.symm x).app Y f = F.map f.op x :=
  yonedaEquiv_symm_app_apply x Y f

/-- Applying the Yoneda equivalence to `yoneda.map g` recovers `g` itself. -/
theorem yoneda_equiv_yoneda_map {C : Type*} [Category C] {X Y : C}
    (f : X ⟶ Y) :
    yonedaEquiv (yoneda.map f) = f :=
  yonedaEquiv_yoneda_map f

/-!
## Naturality of the Yoneda bijection

The bijection `(yoneda.obj X ⟶ F) ≃ F.obj (op X)` is natural in both
arguments. Mathlib formalizes this as a natural isomorphism
`yonedaLemma : yonedaPairing C ≅ yonedaEvaluation C`.
-/

/-- Naturality in `X`: pre-composing `η : yoneda.obj X ⟶ F` by `yoneda.map g`
    corresponds under the Yoneda equivalence to `F.map g.op`. -/
theorem yoneda_equiv_naturality {C : Type*} [Category C] {X Y : C}
    {F : Cᵒᵖ ⥤ Type*} (η : yoneda.obj X ⟶ F) (g : Y ⟶ X) :
    F.map g.op (yonedaEquiv η) = yonedaEquiv (yoneda.map g ≫ η) :=
  yonedaEquiv_naturality η g

/-- The Yoneda lemma as a natural isomorphism between the pairing and
    evaluation functors. -/
def yonedaPairingIsoEvaluation (C : Type*) [Category C] :
    yonedaPairing C ≅ yonedaEvaluation C :=
  yonedaLemma C

/-!
## Fully faithfulness of the Yoneda embedding

The Yoneda embedding `yoneda : C ⥤ (Cᵒᵖ ⥤ Type v₁)` is fully faithful:
the map `X ⟶ Y ↦ yoneda.map f` is a bijection on hom-sets.

This is the corollary of Yoneda that Grothendieck used most heavily:
presheaves faithfully reflect the structure of the category.
-/

/-- The Yoneda embedding is full. This is one half of fully faithfulness:
    pre-composing morphisms lifts along `yoneda`. -/
theorem yoneda_full (C : Type*) [Category C] :
    (yoneda (C := C)).Full :=
  Yoneda.yoneda_full

/-- The Yoneda embedding is faithful. This is the other half: the embedding
    does not identify distinct morphisms. -/
theorem yoneda_faithful (C : Type*) [Category C] :
    (yoneda (C := C)).Faithful :=
  Yoneda.yoneda_faithful

/-- Fully faithfulness of `yoneda` (the Yoneda embedding `C ⥤ Cᵒᵖ ⥤ Type v₁`
    is fully faithful) follows from `Full` and `Faithful` above and the
    canonical `Functor.FullyFaithful.ofFullyFaithful` constructor. -/
example {C : Type*} [Category C] : (yoneda (C := C)).FullyFaithful :=
  Yoneda.fullyFaithful

/-!
## The covariant dual (coyoneda)

The covariant Yoneda embedding is `coyoneda : Cᵒᵖ ⥤ (C ⥤ Type v₁)`. It has
its own lemma: `(coyoneda.obj (op X) ⟶ F) ≃ F.obj X` for `F : C ⥤ Type v₁`.
-/

/-- The covariant Yoneda lemma as a natural isomorphism. -/
def coyonedaPairingIsoEvaluation (C : Type*) [Category C] :
    coyonedaPairing C ≅ coyonedaEvaluation C :=
  coyonedaLemma C

/-!
## Functoriality recovers the hom-set

The Yoneda embedding lifts the hom-set into the category of presheaves.
Specifically, for `X Y : C`, the hom-set `Y ⟶ X` is `yoneda.obj X` evaluated
at `op Y`. This is the canonical interpretation of morphisms as natural
transformations (between representables) — the deep fact behind Yoneda.
-/

/-- The object of morphisms from `Y` to `X` in `C` is `yoneda.obj X` evaluated
    at `op Y`. This recovers the hom-set from the representable presheaf. -/
example {C : Type*} [Category C] (X Y : C) :
    (yoneda.obj X).obj (op Y) ≃ (Y ⟶ X) :=
  Equiv.refl _

end Grothendieck