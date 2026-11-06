/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Grothendieck tribute — Part 55c: arrow form of the extensive topology

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

This part applies the "arrow form" leitmotiv to the **extensive topology**
(`extensiveTopology`) on a `FinitaryPreExtensive` category. Mathlib provides
at the point level `mem_toGrothendieck` via `Saturate`, but **no law
connects it to the arrow form** `extensiveTopology.Covers`. We fill the gap
with five proper theorems — identical structure to Part 55a but specialized
to the extensive coverage: extensivity requires a covering family to be a
**finite** family `Presieve.ofArrows X π` whose `Sigma.desc π` is an
isomorphism. This gives the theorems a particular flavor — the extensive
coverage is the combinatorial characterization of disjoint sums (strict
coproducts).

  - `covers_iff_toGrothendieck` (central): for
    `extensiveTopology C` (with `[FinitaryPreExtensive C]`),
    `extensiveTopology C |>.Covers S f ↔ Saturate (extensiveCoverage C) Y (S.pullback f)` —
    direct bridge between the arrow form and the point-level inductive
    characterization, via `covers_iff` then `mem_toGrothendieck`. This is
    the **natural law** at the extensive stage.
  - `covers_toGrothendieck_of_of` (particular case): if a family
    `X : α → C`, `π : (a : α) → (X a ⟶ B)` with `α` finite and
    `IsIso (Sigma.desc π)`, then the sieve
    `Sieve.generate (Presieve.ofArrows X π)` covers the identity:
    `(extensiveTopology C).Covers (Sieve.generate (Presieve.ofArrows X π)) (𝟙 B)`
    — the point fall-out via `covering_iff_covers_id`.
  - `covers_toGrothendieck_top` (particular case): the trivial cover
    `⊤` covers the identity: `(extensiveTopology C).Covers ⊤ (𝟙 X)`,
    fall-out of `Saturate.top`.
  - `covers_of_mem_toGrothendieck` (particular case on `Sieve.generate`):
    if a family `X : α → C`, `π : (a : α) → (X a ⟶ B)` with `α` finite
    and `IsIso (Sigma.desc π)`, then
    `(extensiveTopology C).Covers (Sieve.generate (Presieve.ofArrows X π)) f`
    for any `f : Y ⟶ B` — pullback stability via `Saturate.pullback`
    then `Saturate.of`.
  - `covers_iff_pullback_toGrothendieck` (particular case on identity):
    `(extensiveTopology C).Covers S (𝟙 X) ↔ S ∈ (extensiveTopology C) X` —
    the point fall-out, via `covering_iff_covers_id`.

Each proof is a **real tactical proof** (DEEP vein): Mathlib axioms
(`GrothendieckTopology.covers_iff`, `Coverage.mem_toGrothendieck`,
`Saturate.pullback`, `covering_iff_covers_id`) plus the definition
`extensiveTopology = extensiveCoverage.toGrothendieck`. No proof is a
re-export or an unfold.

EPIC #1646, Phase 5 (#2159). All `sorry`s eliminated at creation.

### Convention i18n (EPIC #4980 ratifiée par user 2026-07-04)

Ce module est apparié avec son jumeau anglais dans le fichier sibling
`CoversExtensiveArrow_en.lean` (modèle sibling pair, voir PR #6154 pour
le pilote sur `Utility.lean`). Namespace suffix `_en` appliqué au fichier EN
(anti-collision, conforme code-style.md #4980). Les énoncés de théorèmes, les
noms de lemmas, les tactiques Lean et les références Mathlib restent en
anglais ; seules les docstrings `/-- ... -/` et les commentaires `-- ...`
diffèrent entre les deux fichiers (préservation byte-identity).
-/

import Mathlib.CategoryTheory.Sites.Coherent.Basic

namespace Grothendieck.CoversExtensiveArrow_en

open CategoryTheory Limits Coverage

universe u v

/-!
## Section 1 : le pont central — forme flèche ↔ Saturate

`extensiveTopology C` (for `C : Type u` `[Category.{v} C]`
`[FinitaryPreExtensive C]`) is defined as
`extensiveCoverage C |>.toGrothendieck`. The arrow form
`extensiveTopology C |>.Covers S f` reduces via `covers_iff` to the point
`S.pullback f ∈ (extensiveTopology C) Y`, which by `mem_toGrothendieck`
is equivalent to `Saturate (extensiveCoverage C) Y (S.pullback f)`.

The `FinitaryPreExtensive` instance is precisely what provides pullback
stability of finite disjoint sums:
`FinitaryPreExtensive.isIso_sigmaDesc_fst` reconstructs an isomorphism
of `Sigma.desc (fun x => pullback.fst (π x) f)` from an isomorphism of
`Sigma.desc π`. This condition is what makes
`extensiveCoverage.pullback` hold, and therefore makes
`Saturate.pullback` a continuous function.
-/

/-- Central bridge: the arrow form for the extensive topology
    `extensiveTopology C` (where `C : Type u` `[Category.{v} C]`
    `[FinitaryPreExtensive C]`) is equivalent to the inductive
    point-level characterization:
    `(extensiveTopology C).Covers S f ↔ Saturate (extensiveCoverage C) Y (S.pullback f)`.
    Proof: `covers_iff` reduces to `S.pullback f ∈ (extensiveTopology C) Y`,
    then `Coverage.mem_toGrothendieck` identifies to `Saturate`. -/
theorem covers_iff_toGrothendieck {C : Type u} [Category.{v} C] [FinitaryPreExtensive C]
    {X Y : C} (S : Sieve X) (f : Y ⟶ X) :
    (extensiveTopology C).Covers S f ↔ Saturate (extensiveCoverage C) Y (S.pullback f) := by
  rw [GrothendieckTopology.covers_iff]
  exact (Coverage.mem_toGrothendieck (K := extensiveCoverage C) (X := Y)
    (S := S.pullback f)).symm

/-!
## Section 2: base case — extensivity covers its own generation

When `extensiveCoverage C` provides a finite family `X : α → C`,
`π : (a : α) → (X a ⟶ B)` with `IsIso (Sigma.desc π)`, the sieve
`Sieve.generate (Presieve.ofArrows X π)` covers the identity in the sense
of `extensiveTopology C` — this is the forward direction of `Saturate.of`.
The bridge comes from `covering_iff_covers_id`, which reduces to
`Sieve.generate (Presieve.ofArrows X π) ∈ (extensiveTopology C) B`,
then we apply `Saturate.of` directly.
-/

/-- Base case: if a finite family `X : α → C`, `π : (a : α) → (X a ⟶ B)`
    has a `Sigma.desc π` which is an isomorphism, then the sieve it
    generates covers the identity:
    `(extensiveTopology C).Covers (Sieve.generate (Presieve.ofArrows X π)) (𝟙 B)`.
    Proof: `covering_iff_covers_id` reduces to
    `Sieve.generate (Presieve.ofArrows X π) ∈ (extensiveTopology C) B`,
    then `Coverage.mem_toGrothendieck` identifies to `Saturate`, which
    is satisfied by `Saturate.of _ _ ⟨α, inferInstance, X, π, rfl, h_iso⟩`. -/
theorem covers_toGrothendieck_of_of {C : Type u} [Category.{v} C] [FinitaryPreExtensive C]
    {B : C} {α : Type} [Finite α] (X : α → C) (π : (a : α) → (X a ⟶ B))
    (h_iso : IsIso (Sigma.desc π)) :
    (extensiveTopology C).Covers
      (Sieve.generate (Presieve.ofArrows X π)) (𝟙 B) :=
  (GrothendieckTopology.covering_iff_covers_id (J := extensiveTopology C)
    (X := B) (Sieve.generate (Presieve.ofArrows X π))).mp (by
    show Sieve.generate (Presieve.ofArrows X π) ∈ (extensiveCoverage C).toGrothendieck B
    rw [Coverage.mem_toGrothendieck]
    exact Saturate.of B (Presieve.ofArrows X π) ⟨α, inferInstance, X, π, rfl, h_iso⟩)

/-- Generalized base case: the sieve generated by the family `X, π`
    covers any arrow `f : Y ⟶ B`. Proof:
    `covers_iff_toGrothendieck` reduces to
    `Saturate (extensiveCoverage C) Y (Sieve.generate (Presieve.ofArrows X π) |>.pullback f)`.
    We exhibit this `Saturate` via `Saturate.pullback` + `Saturate.of`. -/
theorem covers_of_mem_toGrothendieck {C : Type u} [Category.{v} C] [FinitaryPreExtensive C]
    {B : C} {α : Type} [Finite α] (X : α → C) (π : (a : α) → (X a ⟶ B))
    (h_iso : IsIso (Sigma.desc π)) {Y : C} (f : Y ⟶ B) :
    (extensiveTopology C).Covers
      (Sieve.generate (Presieve.ofArrows X π)) f := by
  rw [covers_iff_toGrothendieck]
  exact Saturate.pullback (extensiveCoverage C) f
    (Saturate.of B (Presieve.ofArrows X π) ⟨α, inferInstance, X, π, rfl, h_iso⟩)

/-- Particular case on the top sieve: `(extensiveTopology C).Covers ⊤ (𝟙 X)`.
    Proof: `Saturate.top` provides the witness directly. -/
theorem covers_toGrothendieck_top {C : Type u} [Category.{v} C] [FinitaryPreExtensive C]
    (X : C) :
    (extensiveTopology C).Covers (⊤ : Sieve X) (𝟙 X) :=
  (GrothendieckTopology.covering_iff_covers_id (J := extensiveTopology C)
    (X := X) ⊤).mp (by
    show ⊤ ∈ (extensiveCoverage C).toGrothendieck X
    rw [Coverage.mem_toGrothendieck]
    exact Saturate.top X)

/-!
## Section 3: point-level fall-out

Specialization on the identity: `(extensiveTopology C).Covers S (𝟙 X) ↔
S ∈ (extensiveTopology C) X`. The bridge to point membership is immediate
via `covering_iff_covers_id`.
-/

/-- Point fall-out: for `extensiveTopology C`, covering along the
    identity is equivalent to belonging to the topology:
    `(extensiveTopology C).Covers S (𝟙 X) ↔ S ∈ (extensiveTopology C) X`.
    Proof: this is exactly `covering_iff_covers_id`. -/
theorem covers_iff_pullback_toGrothendieck {C : Type u} [Category.{v} C] [FinitaryPreExtensive C]
    {X : C} (S : Sieve X) :
    (extensiveTopology C).Covers S (𝟙 X) ↔ S ∈ (extensiveTopology C) X :=
  (GrothendieckTopology.covering_iff_covers_id (J := extensiveTopology C)
    (X := X) S).symm

end Grothendieck.CoversExtensiveArrow_en