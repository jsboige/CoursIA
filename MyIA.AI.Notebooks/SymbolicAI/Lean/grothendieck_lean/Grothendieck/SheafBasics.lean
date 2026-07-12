/-
Grothendieck tribute — Part 7: Sheaf basics
Alexandre Grothendieck (1928-2014).

Phase 3 extension (#2159, Epic #1646).

Part 1 (CategoryAndSites.lean) introduced Grothendieck topologies and sieves.
Part 5 (Calibration.lean) showed that every presheaf is a sheaf for the trivial
topology. Part 6 (SieveLattice.lean) established pullback identities on sieves.

This module records fundamental properties of sheaves and separated presheaves:

  - Every sheaf is separated (the fundamental inclusion).
  - Every presheaf is separated for the trivial (coarsest) topology.
  - For a subcanonical topology, every representable presheaf is a sheaf.
  - Sheaf condition transfers along topology comparisons (J₁ ≤ J₂).

These are the basic algebraic facts about sheaves on a site, connecting
the lattice-theoretic properties of sieves (Part 1/6) with the sheaf
condition (Part 5).

Epic #1646, Phase 3 (#2159). All `sorry`s eliminated at creation.
-/

/-
  `Grothendieck.SheafBasics` — Fondements des faisceaux
  =====================================================
  Hommage à Grothendieck — Partie 7 : Fondements des faisceaux
  Alexandre Grothendieck (1928-2014).

  Extension Phase 3 (#2159, Epic #1646).

  La Partie 1 (`CategoryAndSites.lean`) a introduit les topologies de
  Grothendieck et les cribles. La Partie 5 (`Calibration.lean`) a montré
  que tout préfaisceau est un faisceau pour la topologie triviale. La
  Partie 6 (`SieveLattice.lean`) a établi les identités de pullback sur
  les cribles.

  Ce module enregistre les propriétés fondamentales des faisceaux et des
  préfaisceaux séparés :

    - Tout faisceau est séparé (l'inclusion fondamentale).
    - Tout préfaisceau est séparé pour la topologie triviale (la plus grossière).
    - Pour une topologie sous-canonique, tout préfaisceau représentable
      est un faisceau.
    - La condition de faisceau se transfère le long des comparaisons
      de topologies (J₁ ≤ J₂).

  Ce sont les faits algébriques de base sur les faisceaux sur un site,
  connectant les propriétés théoriques de treillis des cribles
  (Parties 1/6) avec la condition de faisceau (Partie 5).

  Epic #1646, Phase 3 (#2159). Tous les `sorry`s éliminés à la création.

  ### i18n — convention #4980 ratifiée 2026-07-04

  Ce sous-module suit l'option A (bilingue inline FR/EN), variante pragmatique
  c.376-c.382 (deux blocs `/` top-level distincts, sans `---` interne) : le
  bloc EN existant est préservé verbatim ci-dessus, le bloc FR miroir est
  ajouté juste après sans séparateur `---`. Convention sibling pair
  (`<Foo>_en.lean` à part) réservée aux modules de substance (cf c.374
  `Astar_en.lean`) ; pour les modules de fondation comme `SheafBasics`,
  l'inline FR+EN est le bon compromis (peu de preuve pure, deux langues
  côte à côte). Les énoncés de théorèmes, les noms de lemmes, les tactiques
  Lean et les références Mathlib restent en anglais (Mathlib 4, tactic DSL
  standard). Seules les **docstrings `/-- ... -/`** et les **commentaires
  `-- ...`** bilingues sont ajoutées. Anti-§D byte-identity garanti : le
  namespace body est préservé bit-pour-bit (3736 octets extractibles
  byte-identique via script Python `extract_ns_body`).

  ### c.383 — 3ᵉ cycle R6 Sustained intra-R6 sur registre `grothendieck_lean` Phase 2+ ouvert post-c.381

  c.381 = 1ᵉʳ sous-module rollout `grothendieck_lean` Phase 2+ (YonedaLemma,
  PR #6197 OPEN MERGEABLE, lemme de Yoneda = THE foundational theorem of
  category theory). c.382 = 2ᵉ sous-module rollout (MathlibMap, PR #6202
  OPEN, satellite cartographie Mathlib 4 = analogue structurel c.377).
  c.383 = **3ᵉ sous-module rollout Phase 2+** = **au seuil R5.4b MUST
  3 cycles/thème OK** (c.381-c.383 = cohérent, registre `grothendieck_lean`
  ouvert, backlog 22 sous-modules Phase 2+, c.384 = **PIVOT obligatoire** par
  R5.4b MUST anti-tunneling). SheafBasics = analogue structurel c.381
  YonedaLemma (6 théorèmes fondamentaux sur les faisceaux et préfaisceaux
  séparés vs 1 lemme fondamental sur l'embedding de Yoneda) : **registre
  grothendieck_lean Phase 2+ ouvert post-PIVOT strict c.381** autorise
  continuer sur même registre tant que backlog substantiel. Théorème 3
  (`yoneda_isSheaf_subcanonical`) fait le pont avec c.381 Yoneda : pour
  une topologie sous-canonique, l'objet Yoneda est un faisceau. Backlog
  c.384+ (19 sous-modules backlog Phase 2+ après c.383) :
  `Grothendieck/{Sheafification,SitePoints,Conservative,MayerVietorisSquare,
  CategoryAndSites,SieveLattice,YonedaLemma_lemmas,SheafCohomology/*,
  Calibration,SchemesTour,Subcanonical,ZariskiSite,DenseTopology,
  SieveGenerate,LeftExact,SheafHom,SieveOps,CoverageGen,CanonicalProps,
  ConstantSheaf}.lean`.

  Cross-références : c.366 `#6111` `Conway.lean` racine bilingue (MERGED) +
  c.367 `#6115` `Grothendieck.lean` racine bilingue (MERGED, initie rollout
  Phase 2+) + c.373 `#6156` `Knots.lean` racine bilingue (OPEN) + c.374
  `#6163` `Astar` sibling pair (OPEN) + c.375 `#6171` `Knots` sub-modules
  5/6 (OPEN) + c.376 `#6173` `Knots/Invariant` 6/6 (OPEN) + c.377 `#6178`
  `Conway/MathlibMap` bilingue (premier sous-module rollout conway_lean,
  PIVOT L335 strict, analogue structurel c.382) + c.378 `#6182`
  `Conway/LookAndSay` bilingue + c.379 `#6190` `Conway/Fractran` bilingue
  + c.380 `#6194` `Conway/Doomsday` bilingue + c.381 `#6197`
  `Grothendieck/YonedaLemma` bilingue (1ᵉʳ sous-module rollout
  grothendieck_lean Phase 2+, PIVOT L335 strict) + c.382 `#6202`
  `Grothendieck/MathlibMap` bilingue (2ᵉ sous-module rollout, satellite
  cartographie Mathlib 4) + **c.383 `Grothendieck/SheafBasics` bilingue
  (cette PR, 3ᵉ sous-module rollout Phase 2+, fondations faisceaux = 6
  théorèmes, analogue structurel c.381 Yoneda)** ← **continuité registre
  `grothendieck_lean` Phase 2+ ouvert post-c.381 PIVOT strict** + **au seuil
  R5.4b MUST 3 cycles/thème OK avant PIVOT obligatoire c.384**.
-/

import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Sites.Canonical

namespace Grothendieck

open CategoryTheory

/-!
## Sheaf ⇒ Separated

The fundamental inclusion: every sheaf is automatically a separated
presheaf. Intuitively, if a presheaf admits unique gluings, then
compatible families have at most one gluing (uniqueness).
-/

/-- Every sheaf is separated. Uses `Presieve.IsSheaf.isSeparated` from Mathlib. -/
theorem sheaf_is_separated {C : Type*} [Category C]
    {J : GrothendieckTopology C} {P : Cᵒᵖ ⥤ Type*}
    (h : Presieve.IsSheaf J P) :
    Presieve.IsSeparated J P :=
  h.isSeparated

/-!
## Separated presheaves for the trivial topology

The trivial topology ⊥ (coarsest) has only the maximal sieve ⊤ as
covering. Since every presheaf is a sheaf for ⊥, every presheaf is
also separated.
-/

/-- Every Type-valued presheaf is separated for the trivial (coarsest)
    topology. This follows from `isSheaf_bot` combined with
    `sheaf_is_separated`. -/
theorem isSeparated_trivial {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type*) :
    Presieve.IsSeparated (⊥ : GrothendieckTopology C) P :=
  Presieve.isSheaf_bot.isSeparated

/-!
## Subcanonical topologies and representable sheaves

A Grothendieck topology J is *subcanonical* if every representable presheaf
(i.e., `yoneda.obj X` for any X) is a sheaf. This is equivalent to saying
that J ≤ the canonical topology (the finest subcanonical topology).

The Zariski topology on schemes is subcanonical (see ZariskiSite.lean).
-/

/-- For a subcanonical topology J, the Yoneda presheaf at X is a sheaf.
    This is the key bridge: the Yoneda embedding lands in sheaves.
    Uses `GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable`. -/
theorem yoneda_isSheaf_subcanonical {C : Type*} [Category C]
    (J : GrothendieckTopology C) [J.Subcanonical] (X : C) :
    Presieve.IsSheaf J (yoneda.obj X) :=
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj X)

/-!
## Sheaf condition along topology comparisons

If J₁ ≤ J₂ (J₁ has fewer covering sieves) and P is a sheaf for J₂,
then P is a sheaf for J₁. The coarser the topology, the more presheaves
are sheaves.
-/

/-- A presheaf that is a sheaf for a finer topology is also a sheaf for
    a coarser topology. Uses `Presieve.isSheaf_of_le` from Mathlib. -/
theorem isSheaf_of_le {C : Type*} [Category C]
    {J₁ J₂ : GrothendieckTopology C} (h : J₁ ≤ J₂)
    {P : Cᵒᵖ ⥤ Type*} (hP : Presieve.IsSheaf J₂ P) :
    Presieve.IsSheaf J₁ P :=
  Presieve.isSheaf_of_le P h hP

/-!
## Subcanonical is downward-closed

If K is subcanonical and J ≤ K, then J is also subcanonical.
This follows because having fewer covering sieves makes the
sheaf condition easier to satisfy.
-/

/-- Subcanonicity is downward-closed: if K is subcanonical and J ≤ K,
    then J is subcanonical. Uses `GrothendieckTopology.Subcanonical.of_le`. -/
theorem subcanonical_of_le {C : Type*} [Category C]
    {J K : GrothendieckTopology C} (h : J ≤ K) [K.Subcanonical] :
    J.Subcanonical :=
  GrothendieckTopology.Subcanonical.of_le h

/-!
## The trivial topology is subcanonical

Since the trivial (coarsest) topology ⊥ is below every topology,
and every topology is below the canonical topology (which is subcanonical),
the trivial topology is subcanonical.
-/

/-- The trivial (coarsest) topology is subcanonical.
    Every presheaf is a sheaf for ⊥, so in particular every representable
    presheaf is a sheaf. Uses `GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj`. -/
theorem trivial_subcanonical {C : Type*} [Category C] :
    @GrothendieckTopology.Subcanonical C _ (⊥ : GrothendieckTopology C) :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj ⊥
    (fun _ => Presieve.isSheaf_bot)

end Grothendieck
