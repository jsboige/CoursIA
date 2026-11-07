/-
## Catégories, cribles et topologies de Grothendieck (Partie 1 — hommage Grothendieck)

Hommage Grothendieck — Partie 1 : catégories sous-jacentes, cribles et
axiomes des topologies de Grothendieck.

Alexandre Grothendieck (1928-2014).

Phase 2 extension (#2159, Epic #2162).

Ce module introductif présente la formalisation Mathlib 4 des concepts
fondamentaux de la théorie des sites de Grothendieck (SGA 4 II §1-3) :

  - `Sieve X` : crible sur un objet X (sous-foncteur de l'embedding de
    Yoneda en X), forme un **treillis complet** via `inferInstance`
  - `GrothendieckTopology C` : fonction assignant à chaque X un ensemble
    de cribles couvrants satisfaisant **trois axiomes** (top_mem,
    pullback_stable, transitive)
  - `GrothendieckTopology.trivial` : la topologie triviale (la plus
    grossière, **bottom** ⊥ du treillis des topologies)
  - `GrothendieckTopology.discrete` : la topologie discrète (la plus
    fine, **top** ⊤ du treillis des topologies)
  - `GrothendieckTopology.dense` : la topologie dense (S couvre X ssi
    tout morphisme Y → X admet un facteur dans S)
  - `top_covers` : axiome 1 — le crible maximal est toujours couvrant
    (stabilité par identité)
  - `pullback_cover` : axiome 2 — les cribles couvrants sont stables
    par pullback (localité, voir c.393 SieveLattice pour les axiomes
    functoriels du pullback)
  - `transitivity` : axiome 3 — caractère local (transitivité)
  - `trivial_eq_bot` / `discrete_eq_top` : la topologie triviale est le
    **bottom** ⊥ et la topologie discrète est le **top** ⊤ du treillis
    complet des topologies de Grothendieck sur C

L'intuition clé (le « basculement catégoriel » de Grothendieck) :
remplacer les **espaces topologiques** (au sens de Bourbaki) par des
**catégories équipées d'une topologie** définie par des cribles
couvrants. Cette généralisation a révolutionné la géométrie algébrique
en permettant de définir les **faisceaux** sur des schémas, des
champs, des topos — bien au-delà des espaces topologiques classiques.

Epic #1646, Phase 2 (#2159). Tous les `sorry`s éliminés à la création.

### Hommage calibration harness + Phase 2+ rollout grothendieck_lein (#4980)

9ᵉ sous-module rollout `grothendieck_lein` Phase 2+ — analogue
structurel direct c.388 `SieveOps` (5ᵉ, treillis ⊥ ≤ J ≤ ⊤, 9 theorem)
+ c.389 `CanonicalProps` (6ᵉ, topologie canonique, 8 theorem) + c.390
`SieveGenerate` (7ᵉ, Galois insertion + idempotence, 7 theorem) + c.393
`SieveLattice` (8ᵉ, axiomes functoriels pullback, 4 theorem) =
continuité registre `grothendieck_lein` Phase 2+ ouvert post-c.390 =
**4ᵉ cycle R6 Sustained intra-R6 sur registre `grothendieck_lein`
post-c.391** = retour Phase 2+ post-c.392 ACHEVÉ 9/9 `conway_lein`
Phase 1+.

### Substance réelle — catégories sous-jacentes + axiomes topologie de Grothendieck (SGA 4 II §1-3)

Le bloc introduit les **5 theorem** (axiomes canoniques + bornes
treillis) et **5 example** (instances + topologies canoniques)
formels sur la théorie des sites de Grothendieck :

- **`top_covers`** : `(⊤ : Sieve X) ∈ J.sieves X` (le crible maximal
  est couvrant — axiome 1) — réduit à `J.top_mem X`
- **`pullback_cover`** : si `S ∈ J.sieves X` alors `S.pullback f ∈
  J.sieves Y` (stabilité par pullback — axiome 2, localité) — réduit
  à `J.pullback_stable f hS`
- **`transitivity`** : axiome 3 — si `S` couvre `X` et tout morphisme
  dans `S` admet un pullback couvrant `R`, alors `R` couvre `X` —
  réduit à `J.transitive hS R hR`
- **`trivial_eq_bot`** : `GrothendieckTopology.trivial C = ⊥` (borne
  inférieure du treillis des topologies)
- **`discrete_eq_top`** : `GrothendieckTopology.discrete C = ⊤` (borne
  supérieure du treillis des topologies)

Ce module formalise :
- `top_covers` : axiome 1 — crible maximal couvrant
- `pullback_cover` : axiome 2 — stabilité par pullback
- `transitivity` : axiome 3 — caractère local
- `trivial_eq_bot` : topologie triviale = ⊥ du treillis
- `discrete_eq_top` : topologie discrète = ⊤ du treillis
- + 4 `example` : instances `CompleteLattice (Sieve X)`,
  `CompleteLattice (GrothendieckTopology C)`, topologies canoniques
  `trivial`/`discrete`/`dense`

Le pont Mathlib utilisé = `Mathlib.CategoryTheory.Sites.Grothendieck`
(1 import byte-identique LF). Tous les `sorry`s ont été éliminés
(Epic #1453). **Densité 1.317 thm/KB** (5/3795) — analogue structurel
direct c.388 SieveOps (1.864 thm/KB, 9 theorem) + c.390 SieveGenerate
(1.424 thm/KB, 7 theorem) + c.393 SieveLattice (1.339 thm/KB, 4 theorem)
; densité modeste car substance = axiomes canoniques fondamentaux
(1 axiome = 1 ligne de la définition mathématique, comme `J.top_mem X`)
sans construction cohomologique.

### Note d'accessibilité Epic #1452/#1453 — kernel théorique pur

Comme c.388 SieveOps + c.389 CanonicalProps + c.390 SieveGenerate +
c.393 SieveLattice, ce module est entièrement **tractable** par
prouveur Lean 4 + Mathlib 4 = SOTA-OK : les 5 theorem utilisent
les tactiques canoniques (`J.top_mem X` + `J.pullback_stable f hS` +
`J.transitive hS R hR` + `GrothendieckTopology.trivial_eq_bot` +
`GrothendieckTopology.discrete_eq_top`) qui sont les **moteurs de
preuve standards Mathlib** pour ces énoncés canoniques. Le **coefficient
de décidabilité** est de 100 % : chaque axiome est directement un
champ de structure de `GrothendieckTopology` (Mathlib 4).

Les 4 `example` sont des **instanciations directes** via
`inferInstance` (CompleteLattice) ou `GrothendieckTopology.trivial` /
`discrete` / `dense` (constantes canoniques Mathlib 4) — purement
déclaratif, zéro tactique de preuve.

### Hommage MathOverflow + Mathlib i18n convention #4980

Hommage à une contribution MathOverflow sur l'**introduction aux sites
de Grothendieck** (la formalisation catégorielle des espaces
topologiques via les cribles couvrants de SGA 4 II §1-3) + convention
Mathlib i18n #4980 ratifiée par user 2026-07-04 (Option A pragmatique
: deux blocs `/` top-level distincts, sans `---` interne, comme
c.366-c.393).

### Cycle L335 anti-monoculture Sustained — c.394 = 4ᵉ cycle R6 Sustained intra-R6 `grothendieck_lein` ≠ `conway_lein` ≠ `knot_lein` post-c.391

- c.388 = 1ᵉʳ cycle R6 Sustained intra-R6 sur registre
  `grothendieck_lein` ≠ `conway_lein` ≠ `knot_lein` post-c.387
- c.389 = 2ᵉ cycle R6 Sustained intra-R6 sur registre
  `grothendieck_lein` ≠ `conway_lein` ≠ `knot_lein` post-c.388
- c.390 = 3ᵉ cycle R6 Sustained intra-R6 sur registre
  `grothendieck_lein` ≠ `conway_lein` ≠ `knot_lein` post-c.389 =
  c.391 = PIVOT strict obligatoire R5.4b MUST anti-tunneling
- c.391 = PIVOT strict obligatoire R5.4b MUST anti-tunneling
  post-c.388-c.390 = retour `conway_lein` Phase 1+ satellites =
  1ᵉʳ cycle R6 Sustained intra-R6 `conway_lein` ≠ `grothendieck_lein`
  ≠ `knot_lein` post-c.386
- c.392 = 2ᵉ cycle R6 Sustained intra-R6 sur registre `conway_lein`
  ≠ `grothendieck_lein` ≠ `knot_lein` post-c.391 = rollout Phase 1+
  `conway_lein` ACHEVÉ 9/9
- c.393 = 3ᵉ cycle R6 Sustained intra-R6 sur registre
  `grothendieck_lein` ≠ `conway_lein` ≠ `knot_lein` post-c.391 =
  retour Phase 2+ registre ouvert post-c.390 = 8ᵉ sous-module
  rollout `grothendieck_lein` Phase 2+
- **c.394 = 4ᵉ cycle R6 Sustained intra-R6 sur registre
  `grothendieck_lein`** = continuation registre Phase 2+ ouvert
  post-c.393 = cohérence post-c.392 ACHEVÉ 9/9 `conway_lein` Phase
  1+ = **9ᵉ sous-module rollout `grothendieck_lein` Phase 2+ =
  `CategoryAndSites`** = SGA 4 II §1-3 catégories sous-jacentes +
  axiomes canoniques topologie + treillis des topologies.
- Post-c.394 backlog c.395+ : autres `grothendieck_lein` Phase 2+
  restants (13 après c.394 : Calibration, Subcanonical, DenseTopology,
  CoverageGen, SheafHom, SheafCohomology/{MayerVietoris,Basic},
  ConstantSheaf, ZariskiSite, Conservative, MayerVietorisSquare,
  SitePoints, SchemesTour, LeftExact, SheafCohomology/Cech) OU
  Conway/Life/* 13 fichiers OU Lemmas 3 restants OU hors-Lean #5985/#6051
  OU GPU #5105 po-2024.

Tous les `sorry`s ont été éliminés (Epic #1453, #1646).
-/
import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck

open CategoryTheory

/-!
## Cribles

Un crible sur X est une collection de morphismes de codomaine X qui est close par
le bas : si f ∈ S et g se compose avec f, alors g ≫ f ∈ S. Dans Mathlib, un `Sieve X` est un
sous-foncteur de l'embedding de Yoneda en X.
-/

/-- Les cribles forment un treillis complet : intersections, unions, etc.
    Note : `Sieve X` (pas `Sieve C X`) — la catégorie est inférée. -/
example {C : Type*} [Category C] (X : C) : CompleteLattice (Sieve X) :=
  inferInstance

/-!
## Topologies de Grothendieck

Une `GrothendieckTopology` sur C est une fonction assignant à chaque X un ensemble de cribles couvrants, satisfaisant les trois axiomes : top_mem,
pullback_stable, transitive.
-/

/-- La topologie triviale : seul le crible maximal est couvrant.
    C'est la topologie la plus grossière (bottom). -/
example {C : Type*} [Category C] : GrothendieckTopology C :=
  GrothendieckTopology.trivial C

/-- La topologie discrète : tout crible est couvrant.
    C'est la topologie la plus fine (top). -/
example {C : Type*} [Category C] : GrothendieckTopology C :=
  GrothendieckTopology.discrete C

/-- La topologie dense : un crible S couvre X ssi pour tout f : Y → X,
    il existe une flèche dans S qui se factorise à travers f. -/
example {C : Type*} [Category C] : GrothendieckTopology C :=
  GrothendieckTopology.dense

/-!
## Les trois axiomes

Toute `J : GrothendieckTopology C` satisfait les trois axiomes explicitement.
-/

/-- Axiome 1 : le crible maximal est toujours couvrant. -/
theorem top_covers {C : Type*} [Category C] (J : GrothendieckTopology C) (X : C) :
    (⊤ : Sieve X) ∈ J.sieves X :=
  J.top_mem X

/-- Axiome 2 : les cribles couvrants sont stables par pullback. -/
theorem pullback_cover {C : Type*} [Category C] (J : GrothendieckTopology C)
    {X Y : C} {S : Sieve X} (f : Y ⟶ X) (hS : S ∈ J.sieves X) :
    S.pullback f ∈ J.sieves Y :=
  J.pullback_stable f hS

/-- Axiome 3 : axiome de transitivité (caractère local).
    Si S couvre X et que toute flèche dans S admet un pullback couvrant de R, alors R couvre X. -/
theorem transitivity {C : Type*} [Category C] (J : GrothendieckTopology C)
    {X : C} {S R : Sieve X} (hS : S ∈ J.sieves X)
    (hR : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S.arrows f → R.pullback f ∈ J.sieves Y) :
    R ∈ J.sieves X :=
  J.transitive hS R hR

/-!
## Les topologies de Grothendieck forment un treillis

L'ensemble des topologies de Grothendieck sur une catégorie est un treillis complet,
ordonné par inclusion des cribles couvrants.
-/

/-- Les topologies de Grothendieck sur C forment un treillis complet. -/
example {C : Type*} [Category C] : CompleteLattice (GrothendieckTopology C) :=
  inferInstance

/-- La topologie triviale est l'élément bottom. -/
theorem trivial_eq_bot {C : Type*} [Category C] :
    GrothendieckTopology.trivial C = ⊥ :=
  GrothendieckTopology.trivial_eq_bot

/-- La topologie discrète est l'élément top. -/
theorem discrete_eq_top {C : Type*} [Category C] :
    GrothendieckTopology.discrete C = ⊤ :=
  GrothendieckTopology.discrete_eq_top

end Grothendieck
