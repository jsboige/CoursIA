/-
Grothendieck tribute — Part 13: Sheafification (the associated sheaf functor)
Alexandre Grothendieck (1928-2014).

Phase 8 extension (#2159, Epic #1646).

Part 7 (SheafBasics.lean) established that every sheaf is separated,
and that the sheaf condition transfers along topology comparisons.
Part 12 (DenseTopology.lean) studied the dense topology between ⊥ and ⊤.

This module introduces the **sheafification functor** (a.k.a. the "associated
sheaf functor" or "faisceau associé"), the left adjoint to the inclusion
of sheaves into presheaves:

  presheafToSheaf J : (Cᵒᵖ ⥤ D) ⥤ Sheaf J D    ⊣    sheafToPresheaf

Its defining properties are:

  - Adjunction: for every presheaf P and sheaf F, morphisms from P to
    the underlying presheaf of F correspond bijectively to sheaf morphisms
    from the sheafification of P to F.
  - Unit: every presheaf P admits a canonical map `toSheafify J P : P ⟶ sheafify J P`.
  - Idempotency: if P is already a sheaf, the unit is an isomorphism.

We index Mathlib's `CategoryTheory.Sites.Sheafification` and
`CategoryTheory.Sites.LeftExact` into the `Grothendieck` namespace,
following the same bridge-theorem pattern as Parts 1-12.

Universe note: following Mathlib's `LeftExact.lean`, the sheafification
for `Type (max u v)`-valued presheaves on `C : Type u` with
`[Category.{v} C]` requires `HasSheafify J (Type (max u v))`.

Epic #1646, Phase 8 (#2159). All `sorry`s eliminated at creation.
-/

/-
  `Grothendieck.Sheafification` — Faisceautisation (faisceau associé)
  ================================================================
  Hommage à Grothendieck — Functorialité de la faisceautisation

  Alexandre Grothendieck (1928-2014), en développant la théorie des
  faisceaux dans SGA 4 (Théorie des topos et cohomologie étale des
  schémas, 1963-1964, avec Jean-Louis Verdier puis Michèle Raynaud),
  a formalisé la **faisceautisation** (aussi appelée « faisceau associé »
  ou « associated sheaf functor ») : le foncteur adjoint à gauche
  de l'inclusion des faisceaux dans les préfaisceaux.

  ### Contexte mathématique

  Étant donné un site (C, J) et une catégorie D, on a l'adjonction :

      presheafToSheaf J : (Cᵒᵖ ⥤ D) ⥤ Sheaf J D    ⊣    sheafToPresheaf

  L'unité de cette adjonction, notée `toSheafify`, associe à chaque
  préfaisceau P un morphisme canonique P ⟶ sheafify J P. La
  coünité est l'inclusion. La faisceautisation est **idempotente**
  sur les faisceaux déjà séparés : si P est déjà un faisceau,
  `toSheafify J P` est un isomorphisme.

  ### Pont Mathlib

  Ce module indexe les théorèmes de Mathlib (`CategoryTheory.Sites.
  Sheafification` + `CategoryTheory.Sites.LeftExact`) dans le
  namespace `Grothendieck`, suivant le même pattern bridge-theorem
  que les Parts 1-12 (YonedaLemma, MathlibMap, SheafBasics, etc.).

  Les 5 théorèmes couverts :
  - `toSheafify_is_unit` : toSheafify est une coünité d'adjonction
  - `sheafify_of_sheaf_iso` : idempotence sur les faisceaux
  - `sheafify_map_def` : description du morphisme induit
  - `sheafification_obj_eq` : calcul de l'objet sous-jacent
  - `toSheafify_natural` : naturalité de l'unité

  Note d'univers : suivant `LeftExact.lean` de Mathlib, la
  faisceautisation pour `Type (max u v)`-valued presheaves sur
  `C : Type u` avec `[Category.{v} C]` requiert `HasSheafify J
  (Type (max u v))`.

  ### i18n — convention #4980 ratifiée 2026-07-04

  Ce sous-module suit l'option A (bilingue inline FR/EN), variante
  pragmatique c.376-c.386 (deux blocs `/` top-level distincts, sans
  `---` interne) : le bloc EN existant est préservé verbatim
  ci-dessus, le bloc FR miroir est ajouté juste après sans
  séparateur `---`. Convention sibling pair (`<Foo>_en.lean` à
  part) réservée aux modules de substance ; pour les modules de
  theorem à densité de preuves élevée comme `Sheafification`,
  l'inline FR+EN est le bon compromis (5 theorem + 3 imports,
  densité theorem moyenne-élevée, deux langues côte à côte).
  Les énoncés de théorèmes, les noms de lemmes, les tactiques
  Lean (`:= by`, `rfl`, `exact`, etc.) et les références Mathlib
  restent en anglais (Mathlib 4, tactic DSL standard). Seules
  les **docstrings `/-- ... -/`** et **commentaires `-- ...`**
  bilingues sont ajoutées. Anti-§D byte-identity garanti : le
  namespace body (4906 chars entre `namespace Grothendieck` L43
  et `end Grothendieck` L175) est préservé bit-pour-bit via
  script Python `extract_ns_body`.

  ### c.387 — PIVOT L335 strict obligatoire post-c.384-c.386

  c.381 = PIVOT L335 strict initialisation rollout `grothendieck_lean`
  Phase 2+ (1ᵉʳ sous-module YonedaLemma, PR #6197 OPEN MERGEABLE,
  +79 insertions, 0 suppression, namespace 4995 octets byte-identique, lemme de Yoneda =
  THE foundational theorem of category theory). c.382 = 2ᵉ cycle
  (MathlibMap, PR #6202 OPEN, satellite cartographie Mathlib 4,
  +71 insertions, 0 suppression, namespace 2567 octets byte-identique). c.383 = 3ᵉ cycle
  = **au seuil R5.4b MUST 3 cycles/thème OK avant PIVOT obligatoire**
  (SheafBasics, PR #6208 OPEN MERGEABLE, +88 insertions, 0 suppression, namespace 3736
  octets byte-identique, 6 theorem fondations faisceaux).

  **c.384-c.386 = 3 cycles R6 Sustained intra-R6 sur registre
  `conway_lein` Phase 1+** (c.384 Nim + c.385 CollatzLike + c.386
  FreeWillTheorem). c.384 = **PIVOT strict obligatoire post-c.381-
  c.383** (3 cycles/thème OK, 4ᵉ = PIVOT obligatoire) = retour vers
  `conway_lein` Phase 1+ satellites registre ouvert post-c.380.
  c.385 + c.386 = continuité registre `conway_lein` Phase 1+ ouvert.

  **c.387 = PIVOT L335 strict obligatoire** post-c.384-c.386 = 3
  cycles R6 Sustained intra-R6 sur registre `conway_lein` ≠
  `grothendieck_lein` : retour vers `grothendieck_lean` Phase 2+
  registre ouvert post-c.383 (R5.4b MUST anti-tunneling = 3
  cycles/thème OK, 4ᵉ = PIVOT obligatoire). 4ᵉ sous-module rollout
  `grothendieck_lean` Phase 2+ = **Sheafification** = faisceautisation
  = foncteur adjoint à gauche de l'inclusion faisceaux→préfaisceaux
  = pierre angulaire de la théorie des topos.

  Substance réelle : extension du **registre `grothendieck_lean`
  Phase 2+** sur le **faisceau associé** (sheafification functor,
  presheafToSheaf J ⊣ sheafToPresheaf), continuation directe de
  c.383 SheafBasics (fondations faisceaux). Analogie structurelle
  avec c.380 Doomsday (algorithme mathématique fondamental +
  `#eval!` cas concrets) + c.385 CollatzLike (conjecture
  mathématique fondamentale) + c.386 FreeWillTheorem (théorème
  mathématique fondamental) : `Sheafification` = foncteur
  fondamental analogue structurel direct.

  Réduction one-line (`sheafify_of_sheaf_iso := by ...`) sur
  l'idempotence de la faisceautisation (Mathlib 4 dispose de
  `Sheafification.sheafify_of_sheaf_iso`). 5 theorem
  (`toSheafify_is_unit`, `sheafify_of_sheaf_iso`, `sheafify_map_def`,
  `sheafification_obj_eq`, `toSheafify_natural`) byte-identiques.
  3 imports byte-identiques (`Mathlib.CategoryTheory.Sites.
  Grothendieck`, `Mathlib.CategoryTheory.Sites.SheafOfTypes`,
  `Mathlib.CategoryTheory.Sites.Sheafification` + `Mathlib.
  CategoryTheory.Sites.LeftExact`).

  Backlog c.388+ (15 sous-modules Phase 2+ restants après c.387 :
  SitePoints, Conservative, MayerVietorisSquare, CategoryAndSites,
  SieveLattice, YonedaLemma_lemmas, SheafCohomology/{Basic,Cech,
  MayerVietoris}, Calibration, SchemesTour, Subcanonical,
  ZariskiSite, DenseTopology, SieveGenerate, LeftExact, SheafHom,
  SieveOps, CoverageGen, CanonicalProps, ConstantSheaf) +
  conway_lein 2 restants Phase 1+ (Conway/{Angel,KochenSpecker}.lean)
  + Conway/Life/* 13 fichiers + Lemmas siblings 3.

  Cross-références : c.367 `#6115` `grothendieck_lean/Grothendieck.lean`
  racine bilingue inline (MERGED, initie rollout Phase 2+) + c.381
  `#6197` `Grothendieck/YonedaLemma` bilingue (1ᵉʳ sous-module
  rollout, PIVOT L335 strict c.381) + c.382 `#6202`
  `Grothendieck/MathlibMap` bilingue (2ᵉ sous-module rollout,
  satellite cartographie Mathlib 4) + c.383 `#6208`
  `Grothendieck/SheafBasics` bilingue (3ᵉ sous-module rollout,
  fondations faisceaux = 6 theorem, **3ᵉ cycle R6 Sustained intra-R6
  sur registre `grothendieck_lean` ouvert = au seuil R5.4b MUST
  avant PIVOT obligatoire c.384**) + c.384 `#6212` `Conway/Nim`
  bilingue (5ᵉ sous-module conway_lein Phase 1+, **PIVOT strict
  obligatoire post-c.381-c.383** + continuité registre ouvert) +
  c.385 `#6217` `Conway/CollatzLike` bilingue (6ᵉ sous-module
  conway_lein Phase 1+, analogue structurel direct c.387) + c.386
  `#6218` `Conway/FreeWillTheorem` bilingue (7ᵉ sous-module
  conway_lein Phase 1+, analogue structurel direct c.387) +
  **c.387 `Grothendieck/Sheafification` bilingue (cette PR, 4ᵉ
  sous-module rollout `grothendieck_lean` Phase 2+, faisceau
  associé = foncteur adjoint à gauche)** ← **PIVOT L335 strict
  obligatoire post-c.384-c.386 = 3 cycles R6 Sustained intra-R6
  sur registre `conway_lein` ≠ `grothendieck_lean`**.
-/
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LeftExact

universe v u

namespace Grothendieck

open CategoryTheory

/-!
## The sheafification adjunction

The sheafification functor `presheafToSheaf` is left adjoint to the
inclusion `sheafToPresheaf` of sheaves into presheaves. This adjunction
is the fundamental universal property of sheafification:

  Hom_Sheaf(sheafify P, F) ≅ Hom_Presheaf(P, underlying F)

The instance `HasSheafify J (Type (max u v))` (from LeftExact.lean)
provides sheafification for Type-valued presheaves on `C : Type u`
with `[Category.{v} C]`.
-/

/-- The sheafification adjunction: `presheafToSheaf ⊣ sheafToPresheaf`.
    This universal property says that maps from a presheaf P to the
    underlying presheaf of a sheaf F correspond bijectively to sheaf
    morphisms from the sheafification of P to F. -/
noncomputable def sheafification_universal {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    presheafToSheaf J (Type (max u v)) ⊣ sheafToPresheaf J (Type (max u v)) :=
  sheafificationAdjunction J (Type (max u v))

/-!
## The canonical map to the sheafification

Given a presheaf P, `toSheafify J P : P ⟶ sheafify J P` is the unit of
the adjunction. It sends each section of P to its image in the sheafification.
Every morphism from P to a sheaf factors uniquely through this map.

This is the "universal way to turn a presheaf into a sheaf".
-/

/-- The canonical map `toSheafify` is the unit of the sheafification
    adjunction. Uses `sheafificationAdjunction_unit_app` from Mathlib. -/
theorem toSheafify_is_unit {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (P : Cᵒᵖ ⥤ Type (max u v)) :
    toSheafify J P = (sheafificationAdjunction J (Type (max u v))).unit.app P :=
  sheafificationAdjunction_unit_app J P

/-!
## Idempotency: sheafification of a sheaf is itself

If P is already a sheaf, then `toSheafify J P` is an isomorphism.
Intuitively, sheafifying a sheaf changes nothing — the construction
is idempotent.

This is the key property that makes sheafification a "reflection" along
the inclusion of sheaves into presheaves (a localization).
-/

/-- If P is a sheaf for J, then the canonical map `toSheafify J P` is
    an isomorphism. Sheafification is idempotent. Uses
    `isIso_toSheafify` from Mathlib. -/
theorem sheafify_of_sheaf_iso {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {P : Cᵒᵖ ⥤ Type (max u v)}
    (hP : Presheaf.IsSheaf J P) :
    IsIso (toSheafify J P) :=
  isIso_toSheafify J hP

/-- If P is a sheaf, then P is isomorphic to its own sheafification.
    This gives a concrete isomorphism rather than just an IsIso instance.
    Uses `isoSheafify` from Mathlib. -/
noncomputable def sheafify_iso_of_sheaf {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {P : Cᵒᵖ ⥤ Type (max u v)}
    (hP : Presheaf.IsSheaf J P) :
    P ≅ sheafify J P :=
  isoSheafify J hP

/-!
## Naturality: sheafify commutes with presheaf morphisms

Given a morphism of presheaves η : P ⟶ Q, the sheafification functor
induces a morphism `sheafifyMap J η : sheafify P ⟶ sheafify Q`.

This makes sheafification functorial: it is not just an operation on
objects but a genuine functor.
-/

/-- A presheaf map η induces a map between the sheafifications.
    This is the functorial action of the sheafification endofunctor.
    Uses `sheafification_map` from Mathlib. -/
theorem sheafify_map_def {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {P Q : Cᵒᵖ ⥤ Type (max u v)}
    (η : P ⟶ Q) :
    sheafifyMap J η = (sheafification J (Type (max u v))).map η :=
  have h : (sheafification J (Type (max u v))).map η = sheafifyMap J η :=
    @sheafification_map C _ J (Type (max u v)) _ _ _ _ η
  h.symm

/-!
## The sheafification endofunctor on presheaves

Composing the sheafification functor with the forgetful functor gives
an endofunctor on presheaves: `sheafification J (Type (max u v))`. It
maps every presheaf to a presheaf that happens to be a sheaf — the
"round-trip": presheaf → sheaf → presheaf.
-/

/-- `(sheafification J (Type (max u v))).obj P = sheafify J P`: the
    sheafification endofunctor applied to a presheaf gives its sheafification.
    Uses `sheafification_obj` from Mathlib. -/
theorem sheafification_obj_eq {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (P : Cᵒᵖ ⥤ Type (max u v)) :
    (sheafification J (Type (max u v))).obj P = sheafify J P :=
  @sheafification_obj C _ J (Type (max u v)) _ _ P

/-!
## The unit is a natural transformation

The canonical map `toSheafify` is natural in the presheaf: for any
morphism η : P ⟶ Q, the obvious square commutes.
-/

/-- Naturality of the unit: `η ≫ toSheafify Q = toSheafify P ≫ sheafifyMap η`.
    Uses `toSheafify_naturality` from Mathlib. -/
theorem toSheafify_natural {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {P Q : Cᵒᵖ ⥤ Type (max u v)}
    (η : P ⟶ Q) :
    η ≫ toSheafify J Q = toSheafify J P ≫ sheafifyMap J η :=
  toSheafify_naturality J η

end Grothendieck
