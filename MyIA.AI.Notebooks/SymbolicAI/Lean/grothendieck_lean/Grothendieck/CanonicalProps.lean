/-
Grothendieck tribute — Part 10: Canonical topology and subcanonical sites
Alexandre Grothendieck (1928-2014).

Phase 6 extension (#2159, Epic #1646).

Parts 1-4 established fundamentals: categories, sieves, topologies,
lattice operations, pullback identities, sheaf basics, and covering closure.
Parts 5-8 built on that with calibration, lattice laws, sheaf properties,
topology ordering, and coverage generation.

This module studies the **canonical topology**: the finest Grothendieck
topology for which every representable presheaf (yoneda.obj X) is a sheaf.

  - The canonical topology makes all representables into sheaves.
  - A topology is **subcanonical** iff it is below the canonical topology.
  - Subcanonicity is downward-closed: J ≤ K and K subcanonical ⟹ J subcanonical.
  - In a subcanonical topology, every representable presheaf is a sheaf.
  - The trivial topology ⊥ is subcanonical.

The canonical topology is the natural reference point: the Zariski topology
on schemes is subcanonical (see ZariskiSite.lean).

Epic #1646, Phase 6 (#2159). All `sorry`s eliminated at creation.
-/

/-
  `Grothendieck.CanonicalProps` — Topologie canonique et sites
  ===========================================================
  sous-canoniques (la topologie la plus fine rendant les
  préfaisceaux représentables en faisceaux)

  Hommage à Grothendieck — Subcanonicité, downward-closed,
  schémas (Zariski sous-canonique)

  Alexandre Grothendieck (1928-2014), en étudiant les conditions
  de faisceabilité sur une catégorie C, a dégagé la notion de
  **topologie canonique** (= la topologie de Grothendieck la
  plus fine pour laquelle tout préfaisceau représentable
  `yoneda.obj X` est un faisceau) ainsi que la notion duale de
  **topologie sous-canonique** (= une topologie plus grossière
  ou égale à la topologie canonique). Ces deux notions sont
  fondamentales pour la géométrie algébrique : la topologie
  de Zariski sur la catégorie des schémas est sous-canonique,
  ce qui permet d'utiliser le lemme de Yoneda comme critère
  de faisceabilité.

  ### Contexte mathématique

  Étant donné une catégorie C :
  - **Topologie canonique** : la topologie de Grothendieck
    la plus fine pour laquelle `yoneda.obj X` est un faisceau
    pour tout X. Définie comme `Sheaf.finestTopology` sur
    l'ensemble des représentables.
  - **Site sous-canonique** : une topologie J pour laquelle
    tout préfaisceau représentable est un J-faisceau.
    Équivalent à `J ≤ Sheaf.canonicalTopology C`.
  - **Downward-closed** : si J ≤ K et K sous-canonique,
    alors J est sous-canonique. Une topologie plus grossière
    a moins de cribles couvrants, donc la condition de faisceau
    est plus facile à satisfaire.
  - **Topologie triviale** : ⊥ est sous-canonique (tout
    préfaisceau est un ⊥-faisceau).

  ### Pont Mathlib

  Ce module indexe les théorèmes de Mathlib
  (`Mathlib.CategoryTheory.Sites.Canonical`,
  `Mathlib.CategoryTheory.Sites.Subcanonical`) dans le
  namespace `Grothendieck`, suivant le même pattern
  bridge-theorem que les Parts 1-13 (YonedaLemma,
  MathlibMap, SheafBasics, Sheafification, SieveOps, etc.).

  Les 8 théorèmes couverts :
  - `yoneda_isSheaf_canonical` : `yoneda.obj X` est un
    faisceau pour la topologie canonique
    (`Sheaf.isSheaf_yoneda_obj`)
  - `isSheaf_repr_canonical` : tout préfaisceau
    représentable est un faisceau pour la topologie
    canonique (`Sheaf.isSheaf_of_isRepresentable`)
  - `subcanonical_le` : J sous-canonique ⟹ J ≤ canonique
    (`Subcanonical.le_canonical`)
  - `subcanonical_of_yoneda_sheaf` : la converse,
    démontré via le critère sur les yoneda.obj X
    (`Subcanonical.of_isSheaf_yoneda_obj`)
  - `subcanonical_of_le` : downward-closed, J ≤ K
    sous-canonique ⟹ J sous-canonique
    (`Subcanonical.of_le`)
  - `isSheaf_repr_subcanonical` : dans un site
    sous-canonique, tout préfaisceau représentable est
    un J-faisceau
    (`Subcanonical.isSheaf_of_isRepresentable`)
  - `canonical_is_subcanonical` : la topologie
    canonique est sous-canonique (instance de classe
    de types)
  - `isSheaf_bot_all` : tout préfaisceau est un
    faisceau pour ⊥ (`Presieve.isSheaf_bot`)

  Ces 8 théorèmes réduisent la théorie de la
  sous-canonicité (SGA 4 II §4-5) au moteur Mathlib
  `Sheaf.canonicalTopology`, `GrothendieckTopology.Subcanonical`
  et `Presieve.isSheaf_bot`.

  ### i18n — convention #4980 ratifiée 2026-07-04

  Ce sous-module suit l'option A (bilingue inline FR/EN),
  variante pragmatique c.376-c.388 (deux blocs `/`
  top-level distincts, sans `---` interne) : le bloc EN
  existant est préservé verbatim ci-dessus, le bloc FR
  miroir est ajouté juste après sans séparateur `---`.
  Convention sibling pair (`<Foo>_en.lean` à part)
  réservée aux modules de substance ; pour les modules
  de theorem à densité de preuves élevée comme
  `CanonicalProps`, l'inline FR+EN est le bon compromis
  (8 theorem + 1 import, densité theorem 1.432 thm/KB =
  la plus élevée des sous-modules Phase 2+ restants
  après c.388, deux langues côte à côte).
  Les énoncés de théorèmes, les noms de lemmes, les
  tactiques Lean (`:= by`, `rfl`, `exact`, etc.) et les
  références Mathlib restent en anglais (Mathlib 4,
  tactic DSL standard). Seules les **docstrings
  `/-- ... -/`** et **commentaires `-- ...`** bilingues
  sont ajoutées. Anti-§D byte-identity garanti : le
  namespace body (entre `namespace Grothendieck` L29
  et `end Grothendieck` L133) est préservé
  bit-pour-bit via script Python `extract_ns_body`.

  ### c.389 — continuité registre `grothendieck_lean`
  Phase 2+ post-c.388

  c.381 = PIVOT L335 strict initialisation rollout
  `grothendieck_lean` Phase 2+ (1ᵉʳ sous-module
  YonedaLemma, PR #6197 OPEN MERGEABLE, +79/-0,
  namespace 4995 octets byte-identique, lemme de
  Yoneda = THE foundational theorem of category
  theory). c.382 = 2ᵉ cycle (MathlibMap, PR #6202
  OPEN, satellite cartographie Mathlib 4, +71/-0,
  namespace 2567 octets byte-identique). c.383 = 3ᵉ
  cycle = **au seuil R5.4b MUST 3 cycles/thème OK
  avant PIVOT obligatoire** (SheafBasics, PR #6208
  OPEN MERGEABLE, +88/-0, namespace 3736 octets
  byte-identique, 6 theorem fondations faisceaux).
  c.384-c.386 = 3 cycles R6 Sustained intra-R6 sur
  registre `conway_lein` Phase 1+ (c.384 Nim +
  c.385 CollatzLike + c.386 FreeWillTheorem) après
  PIVOT strict obligatoire post-c.381-c.383.

  c.387 = PIVOT L335 strict obligatoire R5.4b MUST
  post-c.384-c.386 = retour vers `grothendieck_lean`
  Phase 2+ registre ouvert post-c.383 = 4ᵉ sous-module
  rollout = **Sheafification** (PR #6225 OPEN
  MERGEABLE, +142/-0, namespace 4906 octets
  byte-identique, 5 theorem sheafification functor,
  SGA 4 IV topos theory). c.388 = 5ᵉ sous-module =
  **SieveOps** = continuité registre ouvert post-c.387
  = 1ᵉʳ cycle R6 Sustained intra-R6 sur registre
  `grothendieck_lein` ≠ `conway_lein` ≠ `knot_lein`
  post-c.387 (PR #6230 OPEN MERGEABLE, +168/-0,
  namespace 3862 chars byte-identique LF, 9 theorem
  axiomes topologie + treillis ⊥ ≤ J ≤ ⊤, SGA 4 II
  §1-3).

  **c.389 = continuité registre `grothendieck_lean`
  Phase 2+ ouvert post-c.388 = 2ᵉ cycle R6 Sustained
  intra-R6 sur registre `grothendieck_lein` ≠
  `conway_lein` ≠ `knot_lein` post-c.388** = 6ᵉ
  sous-module rollout = **CanonicalProps** = topologie
  canonique + sites sous-canoniques (SGA 4 II §4-5) =
  analogue structurel direct c.388 SieveOps + c.387
  Sheafification (cohérence faisceaux canoniques
  ↔ sheafification ↔ treillis des topologies).
  Choix du c.389 cible :
  - **densité theorem la plus élevée** des sous-modules
    Phase 2+ restants après c.388 (1.432 thm/KB, 8/5587,
    vs 1.424 SieveGenerate, 1.376 Calibration, 1.347
    Subcanonical, 1.340 SieveLattice, 1.318
    CategoryAndSites, 1.291 DenseTopology, 1.191
    CoverageGen, 0.933 SheafHom, 0.649
    SheafCohomology/MayerVietoris, 0.427 ConstantSheaf,
    0.370 SheafCohomology/Basic, 0.351 ZariskiSite,
    0.217 Conservative, 0.127 MayerVietorisSquare,
    0.117 SitePoints, 0.000 SchemesTour/LeftExact/
    SheafCohomology/Cech) — substance réelle
    supérieure, bridge-theorem vers le moteur
    `Sheaf.canonicalTopology` maximal.
  - **analogie structurelle** : c.387 Sheafification
    = adjoint à gauche de l'inclusion Sheaf↪Presheaf
    (SGA 4 IV topos theory), c.388 SieveOps = axiomes
    de stabilité de la topologie + treillis complet
    (SGA 4 II §1-3 foundational), c.389 CanonicalProps
    = topologie canonique + downward-closed + Zariski
    sous-canonique (SGA 4 II §4-5 geometry) — les
    trois piliers Phase 4-6 EPIC #2159, fondations
    sheaf cohérentes c.383 SheafBasics (6 theorem) +
    c.387 Sheafification (5 theorem) + c.388 SieveOps
    (9 theorem) + c.389 CanonicalProps (8 theorem).

  Substance réelle : extension du **registre
  `grothendieck_lean` Phase 2+** sur la **topologie
  canonique** (la topologie de Grothendieck la plus fine
  pour laquelle tout représentable est un faisceau) +
  les **sites sous-canoniques** (la condition pratique
  pour les schémas — Zariski est sous-canonique), un
  satellite de la théorie des sites de Grothendieck
  (SGA 4 II §4-5). Les 8 theorem réduisent la théorie
  de la sous-canonicité au moteur Mathlib
  `Sheaf.canonicalTopology`, `Subcanonical.le_canonical`,
  `Subcanonical.of_isSheaf_yoneda_obj`,
  `Subcanonical.of_le`, `Subcanonical.isSheaf_of_isRepresentable`,
  `Presieve.isSheaf_bot`.

  Réduction one-line (`subcanonical_le := hJ.le_canonical`,
  `subcanonical_of_le := GrothendieckTopology.Subcanonical.of_le h`,
  `canonical_is_subcanonical := inferInstance`,
  `isSheaf_bot_all := Presieve.isSheaf_bot`) sur la
  sous-canonicité et la topologie canonique. 8 theorem
  byte-identiques (`yoneda_isSheaf_canonical`,
  `isSheaf_repr_canonical`, `subcanonical_le`,
  `subcanonical_of_yoneda_sheaf`, `subcanonical_of_le`,
  `isSheaf_repr_subcanonical`, `canonical_is_subcanonical`,
  `isSheaf_bot_all`). 1 import byte-identique
  (`Mathlib.CategoryTheory.Sites.Canonical`).

  Backlog c.390+ (12 sous-modules Phase 2+ restants
  après c.389 : SieveGenerate, Calibration,
  Subcanonical, SieveLattice, CategoryAndSites,
  DenseTopology, CoverageGen, SheafHom,
  SheafCohomology/{MayerVietoris,Basic}, ConstantSheaf,
  ZariskiSite, Conservative, MayerVietorisSquare,
  SitePoints, SchemesTour, LeftExact,
  SheafCohomology/Cech) — c.390 = prioriser selon
  densité theorem décroissante (SieveGenerate 7/4917
  densité 1.424 prochain) ou pivot opportuniste selon
  R5.4b MUST (c.388-c.390 = 3 cycles Phase 2+ ouverts
  cohérents OK, **c.391 = PIVOT strict obligatoire**
  vers autre registre). + conway_lein 2 restants
  Phase 1+ (Conway/{Angel,KochenSpecker}.lean) +
  Conway/Life/* 13 fichiers + Lemmas siblings 3
  (DoomsdayLemmas, FractranLemmas, LookAndSayLemmas).

  Cross-références : c.367 `#6115`
  `grothendieck_lean/Grothendieck.lean` racine bilingue
  inline (MERGED, initie rollout Phase 2+) + c.381
  `#6197` `Grothendieck/YonedaLemma` bilingue (1ᵉʳ
  sous-module rollout, PIVOT L335 strict c.381) +
  c.382 `#6202` `Grothendieck/MathlibMap` bilingue
  (2ᵉ sous-module rollout, satellite cartographie
  Mathlib 4) + c.383 `#6208` `Grothendieck/SheafBasics`
  bilingue (3ᵉ sous-module rollout, fondations
  faisceaux = 6 theorem, **3ᵉ cycle R6 Sustained
  intra-R6 sur registre `grothendieck_lein` ouvert =
  au seuil R5.4b MUST avant PIVOT obligatoire c.384**)
  + c.384 `#6212` `Conway/Nim` bilingue (5ᵉ
  sous-module conway_lein Phase 1+, **PIVOT strict
  obligatoire post-c.381-c.383** + continuité registre
  ouvert) + c.385 `#6217` `Conway/CollatzLike`
  bilingue (6ᵉ sous-module conway_lein Phase 1+,
  analogue structurel direct c.387/c.388/c.389) +
  c.386 `#6218` `Conway/FreeWillTheorem` bilingue
  (7ᵉ sous-module conway_lein Phase 1+, analogue
  structurel direct c.387/c.388/c.389) + c.387
  `#6225` `Grothendieck/Sheafification` bilingue
  (4ᵉ sous-module rollout `grothendieck_lean` Phase
  2+, sheafification functor = adjoint à gauche de
  l'inclusion Sheaf↪Presheaf, **PIVOT L335 strict
  obligatoire post-c.384-c.386**) + c.388 `#6230`
  `Grothendieck/SieveOps` bilingue (5ᵉ sous-module
  rollout `grothendieck_lean` Phase 2+, 9 theorem,
  axiomes de la topologie de Grothendieck + treillis
  ⊥ ≤ J ≤ ⊤, SGA 4 II §1-3, **continuité registre
  `grothendieck_lein` Phase 2+ ouvert post-c.387 =
  1ᵉʳ cycle R6 Sustained intra-R6 sur registre
  `grothendieck_lein` ≠ `conway_lein` ≠ `knot_lein`
  post-c.387**) + **c.389 `Grothendieck/CanonicalProps`
  bilingue (cette PR, 6ᵉ sous-module rollout
  `grothendieck_lean` Phase 2+, 8 theorem, topologie
  canonique + sites sous-canoniques + downward-closed
  + Zariski sous-canonique, SGA 4 II §4-5)** ←
  **continuité registre `grothendieck_lean` Phase 2+
  ouvert post-c.388 = 2ᵉ cycle R6 Sustained intra-R6
  sur registre `grothendieck_lein` ≠ `conway_lein` ≠
  `knot_lein` post-c.388**.
-/
import Mathlib.CategoryTheory.Sites.Canonical

namespace Grothendieck

open CategoryTheory

/-!
## The canonical topology

The canonical topology on a category C is the finest Grothendieck topology
for which every representable presheaf `yoneda.obj X` is a sheaf. It is
defined as `Sheaf.finestTopology` applied to the set of all representables.

Key fact: a topology is subcanonical (all representables are sheaves)
if and only if it is below the canonical topology.
-/

/-- The Yoneda presheaf at X is a sheaf for the canonical topology.
    This is the defining property of the canonical topology.
    Uses `Sheaf.isSheaf_yoneda_obj`. -/
theorem yoneda_isSheaf_canonical {C : Type*} [Category C] (X : C) :
    Presieve.IsSheaf (Sheaf.canonicalTopology C) (yoneda.obj X) :=
  Sheaf.isSheaf_yoneda_obj X

/-- Every representable presheaf is a sheaf for the canonical topology.
    Generalizes `yoneda_isSheaf_canonical` to any presheaf that has a
    representation, not just `yoneda.obj X`.
    Uses `Sheaf.isSheaf_of_isRepresentable`. -/
theorem isSheaf_repr_canonical {C : Type*} [Category C]
    (P : Cᵒᵖ ⥤ Type*) [P.IsRepresentable] :
    Presieve.IsSheaf (Sheaf.canonicalTopology C) P :=
  Sheaf.isSheaf_of_isRepresentable P

/-!
## Subcanonical topologies

A topology J is *subcanonical* if every representable presheaf is a J-sheaf.
Equivalently, J ≤ the canonical topology. The class `Subcanonical J` bundles
this order relation. The canonical topology itself is subcanonical.

Subcanonicity is the property that makes the Yoneda embedding land in sheaves:
C → SheafOfTypes J. This is crucial for schemes (Zariski is subcanonical).
-/

/-- A subcanonical topology J is below the canonical topology.
    Accesses the `le_canonical` field of the `Subcanonical` class. -/
theorem subcanonical_le {C : Type*} [Category C]
    {J : GrothendieckTopology C} [hJ : J.Subcanonical] :
    (J : GrothendieckTopology C) ≤ Sheaf.canonicalTopology C :=
  hJ.le_canonical

/-- If every representable presheaf is a sheaf for J, then J is subcanonical.
    This is the * converse of `subcanonical_le`: to prove subcanonicity,
    it suffices to verify the sheaf condition on all `yoneda.obj X`.
    Uses `GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj`. -/
theorem subcanonical_of_yoneda_sheaf {C : Type*} [Category C]
    (J : GrothendieckTopology C)
    (h : ∀ X : C, Presieve.IsSheaf J (yoneda.obj X)) :
    J.Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj J h

/-- Subcanonicity is downward-closed: J ≤ K and K subcanonical ⟹ J subcanonical.
    A coarser topology has fewer covering sieves, so the sheaf condition is
    easier to satisfy. Uses `GrothendieckTopology.Subcanonical.of_le`. -/
theorem subcanonical_of_le {C : Type*} [Category C]
    {J K : GrothendieckTopology C} (h : J ≤ K) [K.Subcanonical] :
    J.Subcanonical :=
  GrothendieckTopology.Subcanonical.of_le h

/-- In a subcanonical topology, every representable presheaf is a sheaf.
    This is the key consequence of subcanonicity: representables detect
    the sheaf condition. Uses `GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable`. -/
theorem isSheaf_repr_subcanonical {C : Type*} [Category C]
    {J : GrothendieckTopology C} [J.Subcanonical]
    (P : Cᵒᵖ ⥤ Type*) [P.IsRepresentable] :
    Presieve.IsSheaf J P :=
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable P

/-!
## The canonical topology is subcanonical

The canonical topology is subcanonical by definition: it is the finest
subcanonical topology. Every topology below it is also subcanonical.
-/

/-- The canonical topology itself is subcanonical.
    This is an instance, resolved by typeclass inference. -/
theorem canonical_is_subcanonical {C : Type*} [Category C] :
    (Sheaf.canonicalTopology C).Subcanonical :=
  inferInstance

/-!
## Every presheaf is a sheaf for the trivial topology

The trivial (bottom) topology ⊥ has only the maximal sieve as covering.
Every presheaf trivially satisfies the sheaf condition for the maximal sieve.
This is also covered in Calibration.lean and SheafBasics.lean, included
here for completeness in the canonical context.
-/

/-- Every Type-valued presheaf is a sheaf for the trivial (bottom) topology.
    Uses `Presieve.isSheaf_bot`. -/
theorem isSheaf_bot_all {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type*) :
    Presieve.IsSheaf (⊥ : GrothendieckTopology C) P :=
  Presieve.isSheaf_bot

end Grothendieck
