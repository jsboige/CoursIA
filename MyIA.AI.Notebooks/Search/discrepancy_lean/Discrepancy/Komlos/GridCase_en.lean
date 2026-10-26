/-
Brick k5.2 of the `discrepancy_lean` lake (issue #17845, Karingula–Lovett
distillation, arXiv:2609.20979). i18n convention #4980: `GridCase.lean`
sibling, proofs byte-identical, docstrings alone translated.

No direct counterpart in the `gdahia/Komlos` oracle: the split follows the
lake's usage map. Crank P4 of the #21417 worksite (`SignedSums_en.lean`)
delivers Lemma 1.4 **ready to consume**; this module takes the next step,
the one the oracle leaves implicit — from convex-hull membership to a
**discrepancy bound**.
-/

import Discrepancy.Komlos.SignedSums_en

/-!
# k5.2 — the grid case: from convex hull to the discrepancy bound

Lemma 1.4 (`exists_isColouring_mean_add_sum_mem_convexHull_of_clauseSet`,
crank P4) concludes a **membership**:

```
μ(P) + ∑ i, ε i • v i  ∈  conv (support of P)
```

That is a geometric conclusion, not yet a discrepancy statement: a reader
cannot read a constant off it. The step taken here is the one Theorem 1.2
requires — **locate that point, hence bound the coloured sum**.

The argument is two inequalities, and that is what makes the brick
consumable without extra hypothesis:

1. if the support sits in the closed box of radius `R`, so does its convex
   hull (**convexity** of the box);
2. the moment `μ(P)` is a **convex combination** of the support
   coordinates (mass `1`, nonnegative weights), hence it sits in the same
   box.

The coloured sum is their difference: it is bounded by `2 R`.

## What the brick does not claim

The paper's constant is **not** reproduced here, and the module does not
name it. The radius `R` stays a **parameter**: the caller instantiates it
to the box of the distribution it builds (k5.1 provides the approximation
on the grid `N⁻¹ • ℤ ^ d` through `exists_grid_approx`, whose norm
hypothesis is what the density construction turns into a box). Writing a
constant here would freeze a composition that lemmas 4.1 and 1.5 of the
paper carry, and that this lake has not distilled yet.

## Vocabulary

- `closedCoordBox R`: the box `{x | ∀ j, |x j| ≤ R}` of `Fin d → ℝ`.
- `abs_coordMoment_le`: the moment of a mass-`1` nonnegative distribution
  stays in the box of its support.
- `abs_le_two_mul_of_add_mem_convexHull`: the geometric core, with no
  distance hypothesis at all — `μ + s ∈ conv(support)` and two box bounds
  give `|s j| ≤ 2 R`.
- `exists_signs_abs_sum_smul_le_of_grid`: **the grid case** — the
  composition of both with Lemma 1.4.
-/

namespace Discrepancy.Komlos_en

open Finset

variable {d : ℕ}

/-- The **closed box of radius `R`** in `Fin d → ℝ`: every coordinate is
bounded in absolute value by `R`. This is the framework in which the grid
case locates the support of a distribution: the lake's discrepancy
witnesses live on bounded finite grids. -/
def closedCoordBox (R : ℝ) : Set (Fin d → ℝ) := {x | ∀ j, |x j| ≤ R}

/-- The coordinate box is the product of the intervals `[-R, R]`: the form
that makes its convexity free (product of intervals, `convex_pi`). -/
lemma closedCoordBox_eq_pi (R : ℝ) :
    closedCoordBox (d := d) R = Set.univ.pi (fun _ : Fin d => Set.Icc (-R) R) := by
  ext x
  simp only [closedCoordBox, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Icc, abs_le]

/-- The coordinate box is **convex**, with no hypothesis on `R`: a convex
combination of two points of the box stays in the box, coordinate by
coordinate. -/
lemma convex_closedCoordBox (R : ℝ) : Convex ℝ (closedCoordBox (d := d) R) := by
  rw [closedCoordBox_eq_pi]
  exact convex_pi fun _ _ => convex_Icc _ _

/-- **The convex hull of a support in the box stays in the box.** This is
step 1 of the argument: `conv (support) ⊆ box` as soon as the support is
there, by minimality of the convex hull (`convexHull_min`) and convexity of
the box. -/
lemma convexHull_map_toReal_subset_closedCoordBox {S : Finset (Fin d → ℤ)} {R : ℝ}
    (hbox : ∀ x ∈ S, ∀ j, |(x j : ℝ)| ≤ R) :
    convexHull ℝ ↑(S.map (⟨⇑toReal, toReal_injective⟩ : (Fin d → ℤ) ↪ (Fin d → ℝ)))
      ⊆ closedCoordBox (d := d) R := by
  refine convexHull_min ?_ (convex_closedCoordBox R)
  intro x hx
  simp only [Finset.coe_map, Set.mem_image, Function.Embedding.coeFn_mk] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  intro j
  simpa using hbox y hy j

/-- **The moment of a distribution stays in the box of its support.**
`μ j = ∑ x ∈ S, P x * x j` is a convex combination of coordinates
(`∑ P = 1`, `P ≥ 0`), hence its absolute value is bounded by the radius. -/
lemma abs_coordMoment_le {S : Finset (Fin d → ℤ)} {P : (Fin d → ℤ) → ℝ} {R : ℝ}
    (hP0 : ∀ x, 0 ≤ P x) (hmass : ∑ x ∈ S, P x = 1)
    (hbox : ∀ x ∈ S, ∀ j, |(x j : ℝ)| ≤ R) (j : Fin d) :
    |coordMoment P S j| ≤ R := by
  have h1 : |∑ x ∈ S, P x * (x j : ℝ)| ≤ ∑ x ∈ S, |P x * (x j : ℝ)| :=
    Finset.abs_sum_le_sum_abs (s := S) (f := fun x => P x * (x j : ℝ))
  have h2 : ∑ x ∈ S, |P x * (x j : ℝ)| = ∑ x ∈ S, P x * |(x j : ℝ)| := by
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [abs_mul, abs_of_nonneg (hP0 x)]
  have h3 : ∑ x ∈ S, P x * |(x j : ℝ)| ≤ ∑ x ∈ S, P x * R := by
    refine Finset.sum_le_sum ?_
    intro x hx
    exact mul_le_mul_of_nonneg_left (hbox x hx j) (hP0 x)
  have h4 : ∑ x ∈ S, P x * R = R := by
    rw [← Finset.sum_mul, hmass, one_mul]
  unfold coordMoment
  linarith

/-- **The geometric core of the grid case**: if a point of the form
`μ + s` falls into the convex hull of a support in the box of radius `R`,
and if `μ` is itself in the box, then every coordinate of `s` is bounded
by `2 R`. No distance hypothesis enters here: this is box algebra, split
from Lemma 1.4 to stay reusable. -/
lemma abs_le_two_mul_of_add_mem_convexHull {S : Finset (Fin d → ℤ)}
    {μ s : Fin d → ℝ} {R : ℝ}
    (hmem : (fun j => μ j + s j) ∈
      convexHull ℝ ↑(S.map (⟨⇑toReal, toReal_injective⟩ : (Fin d → ℤ) ↪ (Fin d → ℝ))))
    (hbox : ∀ x ∈ S, ∀ j, |(x j : ℝ)| ≤ R)
    (hμ : ∀ j, |μ j| ≤ R) :
    ∀ j, |s j| ≤ 2 * R := by
  intro j
  have hX : |μ j + s j| ≤ R :=
    convexHull_map_toReal_subset_closedCoordBox (d := d) hbox hmem j
  have hμj : |μ j| ≤ R := hμ j
  have hEq : s j = (μ j + s j) - μ j := by ring
  rw [hEq]
  calc |(μ j + s j) - μ j| ≤ |μ j + s j| + |μ j| := abs_sub _ _
    _ ≤ R + R := add_le_add hX hμj
    _ = 2 * R := by ring

/-- **k5.2 — the grid case.** Composed of Lemma 1.4 (crank P4) and the
geometric core: under the hypotheses of Lemma 1.4 and a box bound `R` on
the support, there exist signs such that the **coloured sum** is bounded
coordinate by coordinate by `2 R`.

This is the form in which Theorem 1.2 consumes Lemma 1.4: Lemma 1.4 gives
the existence of the signs and the hull point, this theorem draws the
inequality from it. `R` stays a parameter — see the module header for what
this brick does not claim. -/
theorem exists_signs_abs_sum_smul_le_of_grid {n : ℕ} (R : ℝ)
    (S : Finset (Fin d → ℤ)) (P : (Fin d → ℤ) → ℝ) (hP0 : ∀ x, 0 ≤ P x)
    (hmass : ∑ x ∈ S, P x = 1) (hPsupp : ∀ x, P x ≠ 0 → x ∈ S)
    (v : Fin n → (Fin d → ℤ))
    (hbox : ∀ x ∈ S, ∀ j, |(x j : ℝ)| ≤ R)
    (hB : SupportContained S P (clauseSet v))
    (hv : ∀ i, shiftDistance S P (6 • v i) ≤ 3⁻¹) :
    ∃ ε : Fin n → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ j, |∑ i, (ε i : ℝ) * (v i j : ℝ)| ≤ 2 * R := by
  obtain ⟨ε, hε, hmem⟩ :=
    exists_isColouring_mean_add_sum_mem_convexHull_of_clauseSet n d S P hP0 hmass hPsupp v hB hv
  exact ⟨ε, hε,
    abs_le_two_mul_of_add_mem_convexHull hmem hbox (abs_coordMoment_le hP0 hmass hbox)⟩

end Discrepancy.Komlos_en
