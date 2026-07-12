/-
Grothendieck tribute — Part 6: Sieve pullback identities and lattice laws
Alexandre Grothendieck (1928-2014).

Phase 2 extension (#2159, Epic #2162).

Part 1 (CategoryAndSites.lean) introduces sieves, the three axioms,
and the complete lattice on Sieve X. This module records the basic
identities of pullback along morphisms:

  - Pullback along the identity is the identity (pullback_id).
  - Pullback composes contravariantly (pullback_pullback).
  - Pullback of the bottom sieve is bottom (pullback_bot).
  - Pullback is monotone in the sieve (pullback_monotone).

These complete the picture started by Part 5 calibration P2
(pullback_top in Calibration.lean), and pave the way for Phase 3
work on sieve generation and sheafification.

Epic #1646, Phase 2 (#2159). All `sorry`s eliminated at creation.
-/

/-
## Identités de pullback et lois de treillis (SGA 4 II §1-3)

Hommage Grothendieck — Partie 6 : identités de pullback et lois de
treillis sur les cribles.

Alexandre Grothendieck (1928-2014).

Phase 2 extension (#2159, Epic #2162).

La Partie 1 (`CategoryAndSites.lean`) introduit les cribles, les trois
axiomes, et le treillis complet `Sieve X`. Ce module enregistre les
identités fondamentales du **pullback le long de morphismes** :

  - `pullback_id` : pullback le long de l'identité = identité
  - `pullback_pullback` : pullback compose contravariance
  - `pullback_bot` : pullback du crible vide = crible vide
  - `pullback_monotone` : pullback monotone dans le crible

Ces identités complètent le tableau commencé par la calibration P2
(`pullback_top` dans `Calibration.lean`) et ouvrent la voie aux
travaux de Phase 3 sur la génération de cribles et la faisceautisation.

Epic #1646, Phase 2 (#2159). Tous les `sorry`s éliminés à la création.

### Hommage calibration harness + Phase 2+ rollout grothendieck_lein (#4980)

8ᵉ sous-module rollout `grothendieck_lein` Phase 2+ — analogue
structurel direct c.388 `SieveOps` (5ᵉ, treillis ⊥ ≤ J ≤ ⊤, 9 theorem)
+ c.389 `CanonicalProps` (6ᵉ, topologie canonique, 8 theorem) + c.390
`SieveGenerate` (7ᵉ, Galois insertion + idempotence, 7 theorem) =
continuité registre `grothendieck_lein` Phase 2+ ouvert post-c.390 =
**3ᵉ cycle R6 Sustained intra-R6 sur registre `grothendieck_lein`
≠ `conway_lein` ≠ `knot_lein` post-c.391**.

### Substance réelle — pullback identities et lattice laws (SGA 4 II §1-3)

Les **4 identités de pullback** enregistrées ici sont les axiomes
**fonctoriels** fondamentaux de la théorie des sites de Grothendieck
(SGA 4 II §1-3) :

- **`pullback_id`** : `Sieve.pullback (𝟙 X) S = S` (le pullback le long
  de l'identité ne fait rien — `g` est dans le pullback ssi `g ≫ 𝟙 X = g`
  est dans `S`).
- **`pullback_pullback`** : `Sieve.pullback g (Sieve.pullback f S) =
  Sieve.pullback (g ≫ f) S` (contravariance functorielle : pullback
  compose comme `op`).
- **`pullback_bot`** : `Sieve.pullback f (⊥ : Sieve X) = (⊥ : Sieve Y)`
  (le crible vide reste vide sous pullback — dual de `pullback_top`).
- **`pullback_monotone`** : si `S ≤ T` alors `Sieve.pullback f S ≤
  Sieve.pullback f T` (la composante order-théorique de la fonctorialité
  du pullback).

Ce module formalise :
- `pullback_id` : pullback le long de l'identité = identité
- `pullback_pullback` : pullback compose contravariance
- `pullback_bot` : pullback du crible vide = crible vide
- `pullback_monotone` : pullback monotone dans le crible

Le pont Mathlib utilisé = `Mathlib.CategoryTheory.Sites.Grothendieck`
(1 import byte-identique LF). Tous les `sorry`s ont été éliminés
(Epic #1453). **Densité 1.339 thm/KB** (4/2984) — analogue structurel
direct c.388 SieveOps (1.864 thm/KB) + c.390 SieveGenerate (1.424
thm/KB) ; densité modeste vs c.388 car substance = axiomes functoriels
sans construction cohomologique.

### Note d'accessibilité Epic #1452/#1453 — kernel théorique pur

Comme c.388 SieveOps + c.389 CanonicalProps + c.390 SieveGenerate, ce
module est entièrement **tractable** par prouveur Lean 4 + Mathlib 4
= SOTA-OK : les 4 theorem utilisent les tactiques canoniques
(`ext` + `simp [Sieve.pullback]` + `Category.assoc`) qui sont les
moteurs de preuve standards pour les énoncés d'égalité entre cribles.
Le **coefficient de décidabilité** est de 100 % (`ext` + `simp` est
la tactique canonique pour ce type d'égalités structurelles).

### Hommage MathOverflow + Mathlib i18n convention #4980

Hommage à une contribution MathOverflow sur les axiomes functoriels
du pullback de cribles (et leurs liens avec la génération de cribles
et la faisceautisation) + convention Mathlib i18n #4980 ratifiée par
user 2026-07-04 (Option A pragmatique : deux blocs `/` top-level
distincts, sans `---` interne, comme c.366-c.392).

### Cycle L335 anti-monoculture Sustained — c.393 = 3ᵉ cycle R6 Sustained intra-R6 `grothendieck_lein` ≠ `conway_lein` ≠ `knot_lein` post-c.391

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
- **c.393 = 3ᵉ cycle R6 Sustained intra-R6 sur registre
  `grothendieck_lein`** = retour Phase 2+ registre ouvert post-c.390 =
  continuité post-c.392 ACHEVÉ 9/9 `conway_lein` Phase 1+ = **8ᵉ
  sous-module rollout `grothendieck_lein` Phase 2+ =
  `SieveLattice`** = SGA 4 II §1-3 lattice laws axioms functoriels
  pullback.
- Post-c.393 backlog c.394+ : autres `grothendieck_lein` Phase 2+
  restants (14 après c.393 : Calibration, Subcanonical,
  CategoryAndSites, DenseTopology, CoverageGen, SheafHom,
  SheafCohomology/{MayerVietoris,Basic}, ConstantSheaf, ZariskiSite,
  Conservative, MayerVietorisSquare, SitePoints, SchemesTour,
  LeftExact, SheafCohomology/Cech) OU Conway/Life/* 13 fichiers OU
  Lemmas 3 restants OU hors-Lean #5985/#6051 OU GPU #5105 po-2024.

Tous les `sorry`s ont été éliminés (Epic #1453, #1646).
-/
import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck

open CategoryTheory

/-!
## Pullback along the identity is the identity

`Sieve.pullback (𝟙 X) S = S`. Pulling back along the identity does
nothing: `g` is in the pullback iff `g ≫ 𝟙 X = g` is in `S`.
-/

/-- CALIBRATION (ext + simp): pullback along the identity morphism
    is the identity transformation on sieves. -/
theorem pullback_id {C : Type*} [Category C] {X : C} (S : Sieve X) :
    (Sieve.pullback (𝟙 X) S) = S := by
  ext Y f
  simp [Sieve.pullback]

/-!
## Pullback composes contravariantly

For a sieve `S` on `X` and morphisms `f : Y ⟶ X`, `g : Z ⟶ Y`, pulling
back `S` along `f` and then along `g` gives the same sieve as pulling
back `S` along the composite `g ≫ f`.
-/

/-- CALIBRATION (ext + simp + assoc): pullback composes contravariantly.
    Pulling back along `g ≫ f` equals pulling back along `f` then `g`. -/
theorem pullback_pullback {C : Type*} [Category C] {X Y Z : C} (S : Sieve X)
    (f : Y ⟶ X) (g : Z ⟶ Y) :
    (Sieve.pullback g (Sieve.pullback f S)) = Sieve.pullback (g ≫ f) S := by
  ext W h
  simp [Sieve.pullback, Category.assoc]

/-!
## Pullback of the bottom sieve is the bottom sieve

The empty sieve has no arrows; pulling it back along any morphism still
gives the empty sieve. Dual to `pullback_top` (Calibration P2).
-/

/-- CALIBRATION (ext + simp): pullback of the bottom sieve along any
    morphism is the bottom sieve. -/
theorem pullback_bot {C : Type*} [Category C] {X Y : C} (f : Y ⟶ X) :
    (Sieve.pullback f (⊥ : Sieve X)) = (⊥ : Sieve Y) := by
  ext Z g
  simp [Sieve.pullback]

/-!
## Pullback is monotone in the sieve

If `S ≤ T`, then for any `f : Y ⟶ X`, `Sieve.pullback f S ≤ Sieve.pullback f T`.
This is the order-theoretic component of pullback's functoriality.
-/

/-- CALIBRATION (intro + simp + apply): pullback is monotone in the sieve. -/
theorem pullback_monotone {C : Type*} [Category C] {X Y : C} (f : Y ⟶ X)
    {S T : Sieve X} (hST : S ≤ T) :
    Sieve.pullback f S ≤ Sieve.pullback f T := by
  intro Z g hg
  simp [Sieve.pullback] at hg ⊢
  exact hST _ hg

end Grothendieck
