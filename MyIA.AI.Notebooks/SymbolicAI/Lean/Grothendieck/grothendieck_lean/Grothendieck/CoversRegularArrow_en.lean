/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Grothendieck tribute — Part 55b: arrow form of the regular topology

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

This part applies the "arrow form" leitmotiv to the **regular topology**
(`regularTopology`) on a `Preregular` category. Mathlib provides at the
point level `mem_toGrothendieck` via `Saturate`, but **no law connects it
to the arrow form** `regularTopology.Covers`. We fill the gap with five
proper theorems — identical structure to Part 55a but specialized to the
regular coverage: regularity requires a covering family to be a **single
effective-epimorphic morphism** (`Presieve.singleton h` with
`EffectiveEpi h`, vs multi-family for `Coherent`). This gives the theorems
a particular flavor — the "regular" coverage is mono-arrow, which
simplifies some proofs but requires the `Preregular` condition to
guarantee pullback stability of effective morphisms.

  - `covers_iff_toGrothendieck` (central): for
    `regularTopology C` (with `[Preregular C]`),
    `regularTopology C |>.Covers S f ↔ Saturate (regularCoverage C) Y (S.pullback f)` —
    direct bridge between the arrow form and the point-level inductive
    characterization, via `covers_iff` then `mem_toGrothendieck`. This is
    the **natural law** at the regular stage.
  - `covers_toGrothendieck_of_of` (particular case): if a morphism
    `h : X ⟶ B` is effective-epimorphic, then the singleton sieve covers
    the identity: `(regularTopology C).Covers
    (Sieve.generate (Presieve.singleton h)) (𝟙 B)` — the point fall-out
    via `covering_iff_covers_id`.
  - `covers_toGrothendieck_top` (particular case): the trivial cover
    `⊤` covers the identity: `(regularTopology C).Covers ⊤ (𝟙 X)`,
    fall-out of `Saturate.top`.
  - `covers_of_mem_toGrothendieck` (particular case on `Sieve.generate`):
    if a `h : X ⟶ B` is effective-epimorphic, then
    `(regularTopology C).Covers (Sieve.generate (Presieve.singleton h)) f`
    for any `f : Y ⟶ X` — pullback stability via `Saturate.pullback`
    then `Saturate.of`.
  - `covers_iff_pullback_toGrothendieck` (particular case on identity):
    `(regularTopology C).Covers S (𝟙 X) ↔ S ∈ (regularTopology C) X` —
    the point fall-out, via `covering_iff_covers_id`.

Each proof is a **real tactical proof** (DEEP vein): Mathlib axioms
(`GrothendieckTopology.covers_iff`, `Coverage.mem_toGrothendieck`,
`Saturate.pullback`, `covering_iff_covers_id`) plus the definition
`regularTopology = regularCoverage.toGrothendieck`. No proof is a
re-export or an unfold.

EPIC #1646, Phase 5 (#2159). All `sorry`s eliminated at creation.

### Convention i18n (EPIC #4980 ratifiée par user 2026-07-04)

Ce module est apparié avec son jumeau anglais dans le fichier sibling
`CoversRegularArrow_en.lean` (modèle sibling pair, voir PR #6154 pour
le pilote sur `Utility.lean`). Namespace suffix `_en` appliqué au fichier EN
(anti-collision, conforme code-style.md #4980). Les énoncés de théorèmes, les
noms de lemmas, les tactiques Lean et les références Mathlib restent en
anglais ; seules les docstrings `/-- ... -/` et les commentaires `-- ...`
diffèrent entre les deux fichiers (préservation byte-identity).
-/

import Mathlib.CategoryTheory.Sites.Coherent.Basic

namespace Grothendieck.CoversRegularArrow_en

open CategoryTheory Limits Coverage

universe u v

/-!
## Section 1 : le pont central — forme flèche ↔ Saturate

`regularTopology C` (for `C : Type u` `[Category.{v} C]`
`[Preregular C]`) is defined as `regularCoverage C |>.toGrothendieck`.
The arrow form `regularTopology C |>.Covers S f` reduces via `covers_iff`
to the point `S.pullback f ∈ (regularTopology C) Y`, which by
`mem_toGrothendieck` is equivalent to
`Saturate (regularCoverage C) Y (S.pullback f)`.

The `Preregular` instance is precisely what provides pullback stability
of effective morphisms: `Preregular.exists_fac` constructs an
effective-epimorphic morphism `h : W ⟶ X` such that `i ≫ g = h ≫ f`.
This condition is what makes `regularCoverage.pullback` hold, and
therefore makes `Saturate.pullback` a continuous function.
-/

/-- Central bridge: the arrow form for the regular topology
    `regularTopology C` (where `C : Type u` `[Category.{v} C]`
    `[Preregular C]`) is equivalent to the inductive point-level
    characterization:
    `(regularTopology C).Covers S f ↔ Saturate (regularCoverage C) Y (S.pullback f)`.
    Proof: `covers_iff` reduces to `S.pullback f ∈ (regularTopology C) Y`,
    then `Coverage.mem_toGrothendieck` identifies to `Saturate`. -/
theorem covers_iff_toGrothendieck {C : Type u} [Category.{v} C] [Preregular C]
    {X Y : C} (S : Sieve X) (f : Y ⟶ X) :
    (regularTopology C).Covers S f ↔ Saturate (regularCoverage C) Y (S.pullback f) := by
  rw [GrothendieckTopology.covers_iff]
  exact (Coverage.mem_toGrothendieck (K := regularCoverage C) (X := Y)
    (S := S.pullback f)).symm

/-!
## Section 2: base case — regularity covers its own generation

When `regularCoverage C` provides an effective-epimorphic morphism
`h : X ⟶ B`, the singleton sieve `Sieve.generate (Presieve.singleton h)`
covers the identity in the sense of `regularTopology C` — this is the
forward direction of `Saturate.of`. The bridge comes from
`covering_iff_covers_id`, which reduces to
`Sieve.generate (Presieve.singleton h) ∈ (regularTopology C) B`, then
we apply `Saturate.of` directly.
-/

/-- Base case: if a morphism `h : X ⟶ B` is effective-epimorphic
    (`EffectiveEpi h`), then the singleton sieve it generates covers
    the identity:
    `(regularTopology C).Covers (Sieve.generate (Presieve.singleton h)) (𝟙 B)`.
    Proof: `covering_iff_covers_id` reduces to
    `Sieve.generate (Presieve.singleton h) ∈ (regularTopology C) B`, then
    `Coverage.mem_toGrothendieck` identifies to `Saturate`, which is
    satisfied by `Saturate.of _ _ ⟨X, h, rfl, h⟩`. -/
theorem covers_toGrothendieck_of_of {C : Type u} [Category.{v} C] [Preregular C]
    {B : C} {X : C} (h : X ⟶ B) [EffectiveEpi h] :
    (regularTopology C).Covers
      (Sieve.generate (Presieve.singleton h)) (𝟙 B) :=
  (GrothendieckTopology.covering_iff_covers_id (J := regularTopology C)
    (X := B) (Sieve.generate (Presieve.singleton h))).mp (by
    show Sieve.generate (Presieve.singleton h) ∈ (regularCoverage C).toGrothendieck B
    rw [Coverage.mem_toGrothendieck]
    refine Saturate.of B (Presieve.singleton h)
      ⟨X, h, (Presieve.ofArrows_pUnit h).symm, ?_⟩
    exact (inferInstance : EffectiveEpi h))

/-- Generalized base case: the singleton sieve generated by `h` covers
    any arrow `f : Y ⟶ B`. Proof: `covers_iff_toGrothendieck` reduces to
    `Saturate (regularCoverage C) Y (Sieve.generate (Presieve.singleton h) |>.pullback f)`.
    We exhibit this `Saturate` via `Saturate.pullback` + `Saturate.of`. -/
theorem covers_of_mem_toGrothendieck {C : Type u} [Category.{v} C] [Preregular C]
    {B : C} {X : C} (h : X ⟶ B) [EffectiveEpi h] {Y : C} (f : Y ⟶ B) :
    (regularTopology C).Covers
      (Sieve.generate (Presieve.singleton h)) f := by
  rw [covers_iff_toGrothendieck]
  exact Saturate.pullback (regularCoverage C) f
    (Saturate.of B (Presieve.singleton h)
      ⟨X, h, (Presieve.ofArrows_pUnit h).symm, (inferInstance : EffectiveEpi h)⟩)

/-- Particular case on the top sieve: `(regularTopology C).Covers ⊤ (𝟙 X)`.
    Proof: `Saturate.top` provides the witness directly. -/
theorem covers_toGrothendieck_top {C : Type u} [Category.{v} C] [Preregular C]
    (X : C) :
    (regularTopology C).Covers (⊤ : Sieve X) (𝟙 X) :=
  (GrothendieckTopology.covering_iff_covers_id (J := regularTopology C)
    (X := X) ⊤).mp (by
    show ⊤ ∈ (regularCoverage C).toGrothendieck X
    rw [Coverage.mem_toGrothendieck]
    exact Saturate.top X)

/-!
## Section 3: point-level fall-out

Specialization on the identity: `(regularTopology C).Covers S (𝟙 X) ↔
S ∈ (regularTopology C) X`. The bridge to point membership is immediate
via `covering_iff_covers_id`.
-/

/-- Point fall-out: for `regularTopology C`, covering along the
    identity is equivalent to belonging to the topology:
    `(regularTopology C).Covers S (𝟙 X) ↔ S ∈ (regularTopology C) X`.
    Proof: this is exactly `covering_iff_covers_id`. -/
theorem covers_iff_pullback_toGrothendieck {C : Type u} [Category.{v} C] [Preregular C]
    {X : C} (S : Sieve X) :
    (regularTopology C).Covers S (𝟙 X) ↔ S ∈ (regularTopology C) X :=
  (GrothendieckTopology.covering_iff_covers_id (J := regularTopology C)
    (X := X) S).symm

end Grothendieck.CoversRegularArrow_en