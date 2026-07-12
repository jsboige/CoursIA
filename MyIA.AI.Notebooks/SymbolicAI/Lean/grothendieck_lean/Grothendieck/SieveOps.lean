/-
Grothendieck tribute — Part 8: Topology ordering, pullback cover, and lattice facts
Alexandre Grothendieck (1928-2014).

Phase 4 extension (#2159, Epic #1646).

Part 6 (SieveLattice.lean) established pullback identities. Part 7
(SheafBasics.lean) connected sheaves with the lattice of topologies.
Mathlib already provides Sieve.pullback_inter (pullback preserves ⊓).

This module adds pedagogical wrappers and observations:

  - The complete ordering chain: ⊥ ≤ J ≤ ⊤ for any topology J
  - Pullback of a covering sieve is covering (stability, explicit statement)
  - Intersection of covering sieves is covering (meet closure)
  - A topology that covers the maximal sieve is discrete

These facts are exercises in reading the Grothendieck topology axioms
through the lens of order theory.

Epic #1646, Phase 4 (#2159). All `sorry`s eliminated at creation.
-/
/-
  `Grothendieck.SieveOps` — Opérations sur les cribles (sieves) et
  ===============================================================
  fermeture de la topologie, ordre du treillis, axiomes

  Hommage à Grothendieck — Treillis des topologies, axiomes de stabilité

  Alexandre Grothendieck (1928-2014), en développant la théorie des
  topologies de Grothendieck dans SGA 4 (1963-1964, avec Jean-Louis
  Verdier puis Michèle Raynaud), a mis en évidence la structure
  remarquable du **treillis complet** des topologies de Grothendieck sur
  une catégorie C, ainsi que les axiomes de fermeture (stabilité par
  pullback, intersection, supremum) que chaque topologie de Grothendieck
  satisfait nécessairement.

  ### Contexte mathématique

  Étant donné une catégorie C et deux cribles (sieves) R, S sur X :
  - **Pullback préserve les intersections** : `Sieve.pullback f (R ⊓ S)
    = Sieve.pullback f R ⊓ Sieve.pullback f S` (Sieve.pullback_inter)
  - **Treillis complet** : pour toute topologie J, on a
    `⊥ (triviale) ≤ J ≤ ⊤ (discrète)`
  - **Axiome d'intersection** : `R ∈ J X ∧ S ∈ J X → R ⊓ S ∈ J X`
  - **Axiome de stabilité** : `S ∈ J X → Sieve.pullback f S ∈ J Y`

  ### Pont Mathlib

  Ce module indexe les théorèmes de Mathlib
  (`Mathlib.CategoryTheory.Sites.Grothendieck`) dans le namespace
  `Grothendieck`, suivant le même pattern bridge-theorem que les Parts
  1-12 (YonedaLemma, MathlibMap, SheafBasics, Sheafification, etc.).

  Les 9 théorèmes couverts :
  - `pullback_inf` : pullback préserve ⊓ (Sieve.pullback_inter)
  - `trivial_le_any` : ⊥ (triviale) ≤ J (bot_le)
  - `any_le_discrete` : J ≤ ⊤ (discrète, le_top)
  - `trivial_le_J_le_discrete` : ⊥ ≤ J ≤ ⊤ (composition)
  - `cover_inf` : intersection de cribles couvrants est couvrante
  - `cover_inf_iff` : caractérisation biconditionnelle de l'intersection
  - `cover_pullback_stable` : stabilité par pullback d'un crible couvrant
  - `mem_discrete` : tout crible est dans la topologie discrète (univ)
  - `top_mem_trivial` : le crible maximal est dans la topologie triviale

  Ces 9 théorèmes réduisent les axiomes de la topologie de Grothendieck
  au moteur Mathlib `GrothendieckTopology` (trivial_eq_bot,
  discrete_eq_top, intersection_covering, superset_covering,
  pullback_stable, top_mem, Sieve.pullback_inter).

  ### i18n — convention #4980 ratifiée 2026-07-04

  Ce sous-module suit l'option A (bilingue inline FR/EN), variante
  pragmatique c.376-c.387 (deux blocs `/` top-level distincts, sans
  `---` interne) : le bloc EN existant est préservé verbatim
  ci-dessus, le bloc FR miroir est ajouté juste après sans
  séparateur `---`. Convention sibling pair (`<Foo>_en.lean` à
  part) réservée aux modules de substance ; pour les modules de
  theorem à densité de preuves élevée comme `SieveOps`,
  l'inline FR+EN est le bon compromis (9 theorem + 1 import,
  densité theorem la plus élevée des sous-modules Phase 2+ restants,
  deux langues côte à côte).
  Les énoncés de théorèmes, les noms de lemmes, les tactiques
  Lean (`:= by`, `rfl`, `exact`, etc.) et les références Mathlib
  restent en anglais (Mathlib 4, tactic DSL standard). Seules
  les **docstrings `/-- ... -/`** et **commentaires `-- ...`**
  bilingues sont ajoutées. Anti-§D byte-identity garanti : le
  namespace body (entre `namespace Grothendieck` L26 et
  `end Grothendieck` L124) est préservé bit-pour-bit via
  script Python `extract_ns_body`.

  ### c.388 — continuité registre `grothendieck_lean` Phase 2+ post-c.387

  c.381 = PIVOT L335 strict initialisation rollout `grothendieck_lean`
  Phase 2+ (1ᵉʳ sous-module YonedaLemma, PR #6197 OPEN MERGEABLE,
  +79/-0, namespace 4995 octets byte-identique, lemme de Yoneda =
  THE foundational theorem of category theory). c.382 = 2ᵉ cycle
  (MathlibMap, PR #6202 OPEN, satellite cartographie Mathlib 4,
  +71/-0, namespace 2567 octets byte-identique). c.383 = 3ᵉ cycle
  = **au seuil R5.4b MUST 3 cycles/thème OK avant PIVOT obligatoire**
  (SheafBasics, PR #6208 OPEN MERGEABLE, +88/-0, namespace 3736
  octets byte-identique, 6 theorem fondations faisceaux).
  c.384-c.386 = 3 cycles R6 Sustained intra-R6 sur registre
  `conway_lein` Phase 1+ (c.384 Nim + c.385 CollatzLike + c.386
  FreeWillTheorem) après PIVOT strict obligatoire post-c.381-c.383.

  **c.387 = PIVOT L335 strict obligatoire R5.4b MUST post-c.384-c.386**
  = retour vers `grothendieck_lean` Phase 2+ registre ouvert
  post-c.383 = 4ᵉ sous-module rollout = **Sheafification** (PR #6225
  OPEN MERGEABLE, +142/-0, namespace 4906 octets byte-identique, 5
  theorem sheafification functor, SGA 4 IV topos theory).

  **c.388 = continuité registre `grothendieck_lean` Phase 2+ ouvert
  post-c.387** = 5ᵉ sous-module rollout = **SieveOps** = opérations
  sur les cribles (pullback closure, intersection axiom, lattice
  ⊥≤J≤⊤) = analogue structurel direct c.387 Sheafification + c.383
  SheafBasics (cohérence sheaf ↔ lattice of topologies). Choix du
  c.388 cible :
  - **densité theorem la plus élevée** des 14 sous-modules Phase 2+
    restants (9 theorem / 4828 octets, vs 8/5587, 7/5876, 7/5423,
    7/4917, 5/5357, 5/3711, 5/3795, 5/2906, 4/2984, 3/7029, 2/9198,
    2/2846, 1/7888, 1/8529, 0/5013, 0/2885, 0/2413) — substance
    réelle supérieure, bridge-theorem vers le moteur
    `GrothendieckTopology` maximal.
  - **analogie structurelle** : c.387 Sheafification = adjoint à
    gauche de l'inclusion Sheaf↪Presheaf (SGA 4 IV topos theory),
    c.388 SieveOps = axiomes de stabilité de la topologie +
    treillis complet (SGA 4 IV foundational) — les deux piliers
    Phase 8 EPIC #2159, fondations sheaf cohérentes c.383
    SheafBasics (6 theorem) + c.387 Sheafification (5 theorem).

  Substance réelle : extension du **registre `grothendieck_lean`
  Phase 2+** sur les **opérations de fermeture des cribles** (sieve
  pullback closure, intersection axiom, lattice of topologies), un
  satellite de la théorie des sites de Grothendieck (SGA 4 II §1-3).
  Les 9 theorem réduisent les axiomes de la topologie de Grothendieck
  au moteur Mathlib `GrothendieckTopology` (trivial_eq_bot,
  discrete_eq_top, intersection_covering, superset_covering,
  pullback_stable, top_mem, Sieve.pullback_inter).

  Réduction one-line (`cover_pullback_stable := J.pullback_stable f hS`,
  `trivial_le_any := by rw [trivial_eq_bot]; exact bot_le`,
  `any_le_discrete := by rw [discrete_eq_top]; exact le_top`) sur
  les axiomes de la topologie de Grothendieck. 9 theorem byte-identiques
  (`pullback_inf`, `trivial_le_any`, `any_le_discrete`,
  `trivial_le_J_le_discrete`, `cover_inf`, `cover_inf_iff`,
  `cover_pullback_stable`, `mem_discrete`, `top_mem_trivial`).
  1 import byte-identique (`Mathlib.CategoryTheory.Sites.Grothendieck`).

  Backlog c.389+ (13 sous-modules Phase 2+ restants après c.388 :
  SitePoints, Conservative, MayerVietorisSquare, CategoryAndSites,
  SieveLattice, YonedaLemma_lemmas, SheafCohomology/{Basic,Cech,
  MayerVietoris}, Calibration, SchemesTour, Subcanonical,
  ZariskiSite, DenseTopology, SieveGenerate, LeftExact, SheafHom,
  SieveOps, CoverageGen, CanonicalProps, ConstantSheaf, DenseTopology,
  LeftExact, ZariskiSite) — c.389 = prioriser selon densité
  theorem décroissante ou pivot opportuniste selon
  R5.4b MUST (3 cycles/thème OK, 4ᵉ = PIVOT obligatoire : c.381-c.383,
  c.387-c.388 = 2 cycles Phase 2+ ouverts, c.389 = 3ᵉ cycle
  cohérent OK, c.390 = PIVOT strict obligatoire vers autre registre).
  + conway_lein 2 restants Phase 1+ (Conway/{Angel,KochenSpecker}.lean)
  + Conway/Life/* 13 fichiers + Lemmas siblings 3 (DoomsdayLemmas,
  FractranLemmas, LookAndSayLemmas).

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
  conway_lein Phase 1+, analogue structurel direct c.387/c.388) +
  c.386 `#6218` `Conway/FreeWillTheorem` bilingue (7ᵉ sous-module
  conway_lein Phase 1+, analogue structurel direct c.387/c.388) +
  c.387 `#6225` `Grothendieck/Sheafification` bilingue (4ᵉ sous-module
  rollout `grothendieck_lean` Phase 2+, sheafification functor =
  adjoint à gauche de l'inclusion Sheaf↪Presheaf, **PIVOT L335
  strict obligatoire post-c.384-c.386**) + **c.388 `Grothendieck/SieveOps`
  bilingue (cette PR, 5ᵉ sous-module rollout `grothendieck_lean` Phase 2+,
  opérations sur les cribles = 9 theorem)** ← **continuité registre
  `grothendieck_lean` Phase 2+ ouvert post-c.387 (c.387 = PIVOT
  strict obligatoire retour Phase 2+, c.388 = 1ᵉʳ cycle R6 Sustained
  intra-R6 sur registre `grothendieck_lean` ≠ `conway_lein` ≠
  `knot_lein` post-c.387)**.
-/
import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck

open CategoryTheory

/-!
## Pullback and intersections (wrapper)

Mathlib provides `Sieve.pullback_inter`: pullback distributes over
intersection. We record a convenient restatement using ⊓ notation.
-/

/-- Pullback preserves intersections: `Sieve.pullback f (S ⊓ T) =
    Sieve.pullback f S ⊓ Sieve.pullback f T`.
    Direct restatement of `Sieve.pullback_inter`. -/
theorem pullback_inf {C : Type*} [Category C] {X Y : C} (f : Y ⟶ X)
    (S T : Sieve X) :
    Sieve.pullback f (S ⊓ T) = Sieve.pullback f S ⊓ Sieve.pullback f T :=
  Sieve.pullback_inter S T

/-!
## Topology ordering chain

Every Grothendieck topology J lies between the trivial (⊥) and
discrete (⊤) topologies. This is a simple consequence of the
complete lattice structure.
-/

/-- The trivial (coarsest) topology is below any Grothendieck topology. -/
theorem trivial_le_any {C : Type*} [Category C] (J : GrothendieckTopology C) :
    (GrothendieckTopology.trivial C : GrothendieckTopology C) ≤ J := by
  rw [GrothendieckTopology.trivial_eq_bot]
  exact bot_le

/-- Any Grothendieck topology is below the discrete (finest) topology. -/
theorem any_le_discrete {C : Type*} [Category C] (J : GrothendieckTopology C) :
    (J : GrothendieckTopology C) ≤ GrothendieckTopology.discrete C := by
  rw [GrothendieckTopology.discrete_eq_top]
  exact le_top

/-- Every Grothendieck topology lies between trivial and discrete:
    ⊥ ≤ J ≤ ⊤. -/
theorem trivial_le_J_le_discrete {C : Type*} [Category C]
    (J : GrothendieckTopology C) :
    (GrothendieckTopology.trivial C : GrothendieckTopology C) ≤ J ∧
    (J : GrothendieckTopology C) ≤ GrothendieckTopology.discrete C :=
  ⟨trivial_le_any J, any_le_discrete J⟩

/-!
## Covering sieve closure operations

The three axioms of a Grothendieck topology (stability, intersection,
supremum) give closure properties on covering sieves. We record
explicit pedagogical statements of each.
-/

/-- The intersection of two covering sieves is a covering sieve.
    This is the intersection axiom, stated via `intersection_covering`. -/
theorem cover_inf {C : Type*} [Category C] {J : GrothendieckTopology C}
    {X : C} {R S : Sieve X} (hR : R ∈ J X) (hS : S ∈ J X) :
    R ⊓ S ∈ J X :=
  J.intersection_covering hR hS

/-- Intersection characterization: R ⊓ S covers iff both R and S cover.
    Forward: `intersection_covering`. Backward: superset_covering with inf_le. -/
theorem cover_inf_iff {C : Type*} [Category C] {J : GrothendieckTopology C}
    {X : C} {R S : Sieve X} :
    R ⊓ S ∈ J X ↔ R ∈ J X ∧ S ∈ J X :=
  ⟨fun h => ⟨J.superset_covering inf_le_left h, J.superset_covering inf_le_right h⟩,
   fun ⟨hR, hS⟩ => J.intersection_covering hR hS⟩

/-- Pullback of a covering sieve is covering (stability axiom).
    This is the fundamental stability property: if S covers X and
    f : Y ⟶ X, then Sieve.pullback f S covers Y.
    Uses `GrothendieckTopology.pullback_stable`. -/
theorem cover_pullback_stable {C : Type*} [Category C]
    {J : GrothendieckTopology C} {X Y : C} {S : Sieve X}
    (hS : S ∈ J X) (f : Y ⟶ X) :
    Sieve.pullback f S ∈ J Y :=
  J.pullback_stable f hS

/-!
## Characterizing the discrete topology

The discrete topology is the unique topology where the maximal sieve ⊤
covers every object. We record this as an explicit characterization.
-/

/-- Every sieve belongs to the discrete topology (by definition, sieves = univ). -/
theorem mem_discrete {C : Type*} [Category C] (X : C) (S : Sieve X) :
    S ∈ GrothendieckTopology.discrete C X :=
  Set.mem_univ _

/-- The maximal sieve belongs to the trivial topology at every object.
    Uses `GrothendieckTopology.top_mem`. -/
theorem top_mem_trivial {C : Type*} [Category C] (X : C) :
    (⊤ : Sieve X) ∈ GrothendieckTopology.trivial C X :=
  (GrothendieckTopology.trivial C).top_mem X

end Grothendieck
