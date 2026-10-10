/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted to `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, i18n convention #4980.

The original Dahia source lives in the repository `gdahia/Komlos` (module
`Komlos/Pullback.lean`, toolchain v4.34.0, `Finsupp` framework over `E →₀ ℝ`).
The adaptation takes the module over **name for name**, but first delivers only
its **convexity-free** part — see the scope below.

**Scope of this commit** (bricks k2.1 then k2.2, `lake build SUCCESS` required, 0 `sorry`) :

The **pullback step** of Lemma 1.4 decomposes, in Dahia, into three lemmas :
`exists_sign_mul_add_eq` (real arithmetic), `add_smul_mem_convexHull` (convex
hull of a segment) and `pullback` (the full step). The last two **consume
`convexHull`**, which this lake imports nowhere (`convexHull` : 0 occurrence
before this module). This brick therefore delivers the **three ingredients that
do not depend on it**, so that the convexity surface opens on an
already-verified base :

- `exists_sign_mul_add_eq` — the **arithmetic key** : for `β ≥ 1/3` and
  `|a| ≤ 1 − β`, there is a sign `e ∈ {±1}` and a coefficient `c` with
  `|c| ≤ 1` such that `c·β + a = e/3`. This is what produces the sign `ε` of
  k2's conclusion ;
- `segment_repr` — the **segment identity** : any point `x + c·v` with
  `|c| ≤ 1` writes as a convex combination of `x − v` and `x + v`, with weights
  `(1 − c)/2` and `(1 + c)/2`. This is the algebra `add_smul_mem_convexHull`
  wraps in Dahia, but **the algebra alone**, without `convexHull` ;
- `sum_mul_add_split` — the **weighted linearity** consumed by the computation
  of `pullback` : the sum `Σ R y · (h y · c + g y)` splits into
  `c · (Σ R y · h y) + Σ R y · g y`. It is the only sum manipulation of the
  pullback step that is not convexity.

**Brick k2.2 (convexity surface)** — `convexHull` enters this lake (0
occurrence before this commit) through the two generic lemmas the pullback
step consumes :

- `add_smul_mem_convexHull` — the point `x + c • v` of the segment
  `[x − v, x + v]` belongs to the convex hull of any set containing both
  endpoints. Transposed **verbatim** from Dahia (`Komlos/Pullback.lean`,
  l.43-50) : the statement depends only on the `ℝ`-module structure of `E` ;
- `sum_smul_mem_convexHull` — the closing step of the pullback
  (`Convex.sum_mem` applied to `convex_convexHull`, l.83 in Dahia) : a finite
  convex combination of points of a hull stays in the hull.

**Brick k2.4 (the full step)** — `pullback` delivered in the lake's
framework, on the k2.3 dimension transport that lifted the blocker measured
in k2.2 :

- `toRealProd` + `toRealProd_injective` — the **product** embedding : the
  integer grid × `Bool` height into the real grid × `ℝ` (height `false ↦ 0`,
  `true ↦ 1` — that is where the lake's `Bool` height becomes the oracle's
  real coordinate `(y, β)`) ;
- `split_apply_zero_ne_iff` / `split_apply_one_ne_iff` — the **support
  characterizations** of the split under `P ≥ 0`, read point by point (the
  oracle gets them for free via `Finsupp.support` :
  `mk_zero_mem_support_split` / `mk_one_mem_support_split` ; the lake's
  explicit Finset framework requires them as exactness hypotheses on the
  support `SQ` being passed) ;
- `pullback` — **the full step** : if `(z, β)` is in the hull of the
  transported support of `split v P` with `v = 3·w` coordinate by coordinate
  and `β ≥ 1/3`, a sign `e ∈ {±1}` brings `z + e • toReal w` back into the
  hull of the transported support of `P`. Transposed from
  `Komlos/Pullback.lean` l.55-92, the three ingredients delivered in
  k2.1/k2.2 (`exists_sign_mul_add_eq`, `add_smul_mem_convexHull`,
  `sum_smul_mem_convexHull`) and the k2.3 bridges (`toReal_mem_map_iff`)
  being consumed by name.

The detailed state lives in `FORMAL_STATUS.md`.
-/

import Discrepancy.Basic_en
import Discrepancy.Komlos.Split_en
import Discrepancy.Komlos.Transport_en

/-!
# Algebra of the pullback step (Lemma 1.4, Karingula–Lovett)

Lemma 1.4 concludes `μ(P) + Σ ε_i v_i ∈ conv(supp P)`. Its induction step splits
in the direction of the last vector, applies the induction hypothesis in the
product space, then **brings back** the resulting point into `conv(supp P)` :
that is the *pullback*. This module delivers the algebra of that step (k2.1),
then the convexity surface that algebra wraps (k2.2) — both **generic**, the
full step remaining conditioned on the dimension transport.

**Why separate.** Opening `convexHull` in this lake is a structural gesture
(first convex-analysis surface of the lake) ; mixing it with real arithmetic and
sum manipulation would make the diagnosis of a build failure ambiguous.
Delivered separately, the three lemmas of k2.1 are verifiable **without**
`convexHull` — and it is on that verified base that brick k2.2 opened the
surface : a build failure on the convexity lemmas can now only come from them.

**Scope of the result.** `exists_sign_mul_add_eq` is the ingredient that
produces the **signed conclusion** : `e ∈ {±1}` is the sign `ε` of k2's
conclusion, and the bound `|c| ≤ 1` is what allows reading `x + c·v` as a point
of the segment `[x − v, x + v]` — hence `segment_repr`, which makes that
reading explicit. Both lemmas are stated over `ℝ` (no base required) ; only
`segment_repr` needs an abelian group carrying a real module structure, i.e.
the minimal framework in which the statement makes sense.
-/

namespace Discrepancy.Komlos_en

/-- **Arithmetic key of the pullback.** If `β ≥ 1/3` and `|a| ≤ 1 − β`, there
is a sign `e ∈ {±1}` and a coefficient `c` such that `|c| ≤ 1` and
`c * β + a = e / 3`.

This is Dahia's `exists_sign_mul_add_eq` (`Komlos/Pullback.lean`), transposed
verbatim : the statement bears on `ℝ` only, no base structure is required. The
sign `e` is the sign `ε` of Lemma 1.4's conclusion ; the bound `|c| ≤ 1` is what
makes `x + c • v` a point of the segment `[x − v, x + v]` (cf `segment_repr`).

Proof : case analysis on the sign of `a`. For `a ≥ 0`, take `e = 1` and
`c = (1/3 − a) / β` ; the membership `|c| ≤ 1` reduces to `|1/3 − a| ≤ β`, which
`linarith` closes with `hβ` and `|a| ≤ 1 − β`. The case `a < 0` is symmetric
with `e = −1`. -/
lemma exists_sign_mul_add_eq {β a : ℝ} (hβ : 3⁻¹ ≤ β) (ha : |a| ≤ 1 - β) :
    ∃ e c : ℝ, (e = 1 ∨ e = -1) ∧ |c| ≤ 1 ∧ c * β + a = e / 3 := by
  have hβ0 : 0 < β := by linarith
  obtain ⟨ha₁, ha₂⟩ := abs_le.1 ha
  rcases le_total 0 a with h | h
  · refine ⟨1, (3⁻¹ - a) / β, by norm_num, ?_, by field_simp; ring⟩
    rw [abs_div, abs_of_pos hβ0, div_le_one hβ0, abs_le]
    constructor <;> linarith
  · refine ⟨-1, (-3⁻¹ - a) / β, by norm_num, ?_, by field_simp; ring⟩
    rw [abs_div, abs_of_pos hβ0, div_le_one hβ0, abs_le]
    constructor <;> linarith

/-- **Segment identity.** For `|c| ≤ 1`, the point `x + c • v` is the convex
combination of `x − v` and `x + v` with weights `(1 − c) / 2` and
`(1 + c) / 2` :

`((1 − c) / 2) • (x − v) + ((1 + c) / 2) • (x + v) = x + c • v`.

Both weights are nonnegative and sum to 1 as soon as `|c| ≤ 1` — precisely the
hypothesis `hc` of the lemma `add_smul_mem_convexHull` in Dahia, which wraps
this identity in `Convex.add_smul_sub_mem` **without** the convex-hull part
(that one stays with brick k2.2).

The direction of the weights is the one of the statement : `x − v` receives
`(1 − c) / 2` and `x + v` receives `(1 + c) / 2`, so that the coefficient of `v`
is `−(1 − c)/2 + (1 + c)/2 = c`. Swapping the two weights yields `x − c • v`,
not `x + c • v` — the exact mistake made and corrected while drafting this
lemma, recorded here because it is easy to repeat.

Proof : `module` (linearity of `•` and distributivity over `x ± v`). -/
lemma segment_repr {E : Type*} [AddCommGroup E] [Module ℝ E] (x v : E) (c : ℝ) :
    ((1 - c) / 2) • (x - v) + ((1 + c) / 2) • (x + v) = x + c • v := by
  module

/-- **Weighted linearity of a sum.** For a `Finset` `T` and functions
`R`, `h`, `g : ι → ℝ`,

`Σ y ∈ T, R y * (h y * c + g y) = c * (Σ y ∈ T, R y * h y) + Σ y ∈ T, R y * g y`.

This is the sum manipulation of Dahia's `pullback` computation — `mul_sub`,
`sum_sub_distrib`, `mul_sum` — extracted in its reusable form. It depends on
neither the base nor convexity.

Proof : distributivity (`mul_add`), additivity of the sum
(`Finset.sum_add_distrib`), then extraction of the constant factor `c`
(`Finset.mul_sum`) and commutativity. -/
lemma sum_mul_add_split {ι : Type*} (T : Finset ι) (R h g : ι → ℝ) (c : ℝ) :
    ∑ y ∈ T, R y * (h y * c + g y)
      = c * (∑ y ∈ T, R y * h y) + ∑ y ∈ T, R y * g y := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- **Point of a segment in a convex hull.** For `|c| ≤ 1`, the point
`x + c • v` belongs to the convex hull of any set `s` containing both
endpoints `x − v` and `x + v`.

This is Dahia's `add_smul_mem_convexHull` (`Komlos/Pullback.lean`, l.43-50),
transposed **verbatim** : the statement depends only on the `ℝ`-module
structure of `E`. It is the **first occurrence of `convexHull` in this lake**
— the convex-analysis surface opens on the already-verified base of k2.1 : the
bound `|c| ≤ 1` is the one produced by `exists_sign_mul_add_eq`, and
`segment_repr` is the segment identity this lemma wraps.

Proof : `x + c • v` is the convex combination of `x − v` (weight `(1 − c)/2`)
and `x + v` (weight `(1 + c)/2`) ; `Convex.add_smul_sub_mem` (Mathlib
`Analysis.Convex.Basic:492`) produces it for the parameter `t = (1 + c)/2`,
both bounds `0 ≤ t ≤ 1` following from `|c| ≤ 1` by `linarith` ; `convert …
using 1` then `module` close the residual algebraic identity — the same
argument as `segment_repr`. -/
lemma add_smul_mem_convexHull {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} {x v : E} (h₁ : x - v ∈ s) (h₂ : x + v ∈ s) {c : ℝ}
    (hc : |c| ≤ 1) : x + c • v ∈ convexHull ℝ s := by
  obtain ⟨hc₁, hc₂⟩ := abs_le.1 hc
  convert (convex_convexHull ℝ s).add_smul_sub_mem (subset_convexHull ℝ s h₁)
    (subset_convexHull ℝ s h₂) (t := (1 + c) / 2) ⟨by linarith, by linarith⟩ using 1
  module

/-- **Finite convex combination of points of a hull.** If `R` is a family of
nonnegative weights summing to `1` over a `Finset` `T`, and every point `f y`
(for `y ∈ T`) belongs to `convexHull ℝ s`, then the convex combination
`∑ y ∈ T, R y • f y` belongs to `convexHull ℝ s`.

This is the closing step of Dahia's pullback
(`(convex_convexHull ℝ _).sum_mem hR0 hR1`, l.83), extracted in the lake's
`Finset` form : it is what closes the step's proof once every point of the
sum has been brought back into the hull. Generic statement ; the converse
decomposition — reading a hull membership as weights — already exists at this
lake's pin under the name `Finset.centerMass_mem_convexHull` (Mathlib
`Analysis.Convex.Combination:253`).

Proof : `Convex.sum_mem` (Mathlib `Analysis.Convex.Combination:214`) applied
to `convex_convexHull ℝ s` — a convex hull is convex, and a convex
combination of points of a convex set stays in the set. -/
lemma sum_smul_mem_convexHull {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} {ι : Type*} (T : Finset ι) (R : ι → ℝ) (f : ι → E)
    (hR0 : ∀ y ∈ T, 0 ≤ R y) (hR1 : ∑ y ∈ T, R y = 1)
    (hmem : ∀ y ∈ T, f y ∈ convexHull ℝ s) :
    ∑ y ∈ T, R y • f y ∈ convexHull ℝ s :=
  (convex_convexHull ℝ s).sum_mem hR0 hR1 hmem

/-! ### Brick k2.4 : the product embedding and the support characterizations

The full `pullback` step requires two framework ingredients that k2.1-k2.3
have not yet met : the **product** embedding (grid × height → real grid ×
`ℝ`, where the `Bool` height becomes the oracle's `β` coordinate) and the
**support** characterizations of the split (which the oracle gets for free
via `Finsupp.support` and which the lake's explicit Finset framework must
state as hypotheses). -/

/-- **Product embedding.** The integer grid with its `Bool` height embeds
into the real grid × `ℝ` : the spatial component through `toReal` (the
dimension transport of brick k2.3), the height `false ↦ 0`, `true ↦ 1`.

It is this embedding that turns the lake's height — a `Bool` — into the
oracle's real coordinate `(y, β)` : the hull of the oracle's `pullback`
conclusion lives in `E × ℝ`, and it is in `(Fin d → ℝ) × ℝ` that the lake
joins it.

Injectivity is the ticket of the transported support's `Finset.map` :
without it, `SQ.map toRealProdEmb` could contract points and the exactness
hypothesis `hSQ` of the `pullback` theorem would lose information. The
spatial component is injective by `toReal_injective` (k2.3) ; the height
component separates `false` from `true` by `0 ≠ 1`. -/
def toRealProd {d : ℕ} : ((Fin d → ℤ) × Bool) → ((Fin d → ℝ) × ℝ) :=
  fun y => (toReal y.1, if y.2 then (1 : ℝ) else 0)

lemma toRealProd_injective {d : ℕ} : Function.Injective (toRealProd (d := d)) := by
  rintro ⟨x₁, b₁⟩ ⟨x₂, b₂⟩ h
  simp only [toRealProd, Prod.mk.injEq] at h
  obtain ⟨hxe, hbe⟩ := h
  cases b₁ <;> cases b₂ <;> simp_all [toReal_injective.eq_iff]

/-- The `Finset.Embedding` version of `toRealProd`, for the `Finset.map` of
transported supports. -/
def toRealProdEmb {d : ℕ} : ((Fin d → ℤ) × Bool) ↪ ((Fin d → ℝ) × ℝ) :=
  ⟨toRealProd, toRealProd_injective⟩

/-- **Height of a transported support point.** Every point of the image
`SQ.map toRealProdEmb` carries a height in `{0, 1}` — the finite translation
of `snd_eq_zero_or_one_of_mem_support_split` in the oracle. -/
lemma mem_map_toRealProd_snd {d : ℕ} {y : (Fin d → ℝ) × ℝ}
    {SQ : Finset ((Fin d → ℤ) × Bool)} (hy : y ∈ SQ.map toRealProdEmb) :
    y.2 = 0 ∨ y.2 = 1 := by
  rw [Finset.mem_map] at hy
  obtain ⟨y', -, hye⟩ := hy
  have h2 : (if y'.2 then (1 : ℝ) else 0) = y.2 := congrArg Prod.snd hye
  cases b : y'.2 <;> rw [b] at h2 <;> simp_all

/-- **Support characterization, low slice.** Under `P ≥ 0`, the `false`
slice of the split carries nonzero mass exactly when one of the two
translates `P (x ± v)` is nonzero.

This is the point-by-point reading of the oracle's
`mk_zero_mem_support_split` (`(x, 0) ∈ (split v P).support ↔ x + v ∈
P.support ∨ x - v ∈ P.support`) : the oracle's `Finsupp` framework gives it
through the support, the lake's explicit Finset framework states it on the
value. Under `P ≥ 0`, `½ · max a b ≠ 0` is equivalent to `a ≠ 0 ∨ b ≠ 0` :
it is positivity that carries through the `max`. -/
lemma split_apply_zero_ne_iff {d : ℕ} {P : (Fin d → ℤ) → ℝ} (hP : ∀ x, 0 ≤ P x)
    (v x : Fin d → ℤ) :
    split v P (x, false) ≠ 0 ↔ P (x + v) ≠ 0 ∨ P (x - v) ≠ 0 := by
  rw [split_apply_zero]
  constructor
  · intro h
    by_contra hcon
    obtain ⟨h1, h2⟩ := not_or.mp hcon
    rw [not_not.mp h1, not_not.mp h2, max_self] at h
    norm_num at h
  · rintro (h | h)
    · intro hcon
      have hlt : (0 : ℝ) < P (x + v) := lt_of_le_of_ne (hP _) (Ne.symm h)
      exact absurd hcon (ne_of_gt (mul_pos one_half_pos
        (lt_of_lt_of_le hlt (le_max_left _ _))))
    · intro hcon
      have hlt : (0 : ℝ) < P (x - v) := lt_of_le_of_ne (hP _) (Ne.symm h)
      exact absurd hcon (ne_of_gt (mul_pos one_half_pos
        (lt_of_lt_of_le hlt (le_max_right _ _))))

/-- **Support characterization, high slice.** Under `P ≥ 0`, the `true`
slice of the split carries nonzero mass exactly when both translates
`P (x ± v)` are nonzero — the `min` requires the conjunction, where the
`max` of the low slice requires the disjunction.

Point-by-point reading of the oracle's `mk_one_mem_support_split`
(`(x, 1) ∈ (split v P).support ↔ x + v ∈ P.support ∧ x - v ∈ P.support`). -/
lemma split_apply_one_ne_iff {d : ℕ} {P : (Fin d → ℤ) → ℝ} (hP : ∀ x, 0 ≤ P x)
    (v x : Fin d → ℤ) :
    split v P (x, true) ≠ 0 ↔ P (x + v) ≠ 0 ∧ P (x - v) ≠ 0 := by
  rw [split_apply_one]
  constructor
  · intro hcon
    constructor
    · intro hzero
      apply hcon
      rw [hzero, min_eq_left (hP (x - v)), mul_zero]
    · intro hzero
      apply hcon
      rw [hzero, min_eq_right (hP (x + v)), mul_zero]
  · rintro ⟨h, h'⟩
    have hlt : (0 : ℝ) < P (x + v) := lt_of_le_of_ne (hP _) (Ne.symm h)
    have hlt' : (0 : ℝ) < P (x - v) := lt_of_le_of_ne (hP _) (Ne.symm h')
    exact ne_of_gt (mul_pos one_half_pos (lt_min hlt hlt'))

/-! ### Brick k2.4 : the full step -/

/-- **The pullback step (Lemma 1.4).** If the distribution `P` on the
integer grid is nonnegative, with support contained in `SP`, and if
`(z, β)` belongs to the convex hull of the **transported** support of the
split `split v P` — transported by the product embedding `toRealProd` —
with `v = 3 · w` coordinate by coordinate and `β ≥ 1/3`, then a sign
`e ∈ {±1}` brings `z + e • toReal w` back into the convex hull of the
transported support of `P`.

This is the transposition of Dahia's theorem `pullback`
(`Komlos/Pullback.lean`, l.55-92) to the lake's framework. Three framework
gaps are arbitrated :

- **the point `z` lives on the `ℝ` side** : in the oracle, the induction
  hypothesis produces an arbitrary point of `E × ℝ` in the hull ; here the
  final consumer (Lemma 1.4) produces a barycenter on the real grid side,
  hence `z : Fin d → ℝ` and the hypothesis on the hull **in the transported
  image**, not in the integer grid ;
- **`hSQ` is a hypothesis, not a computation** : in the oracle the support
  `(split v P).support` is computed (`mk_zero_mem_support_split`) ; the
  lake's explicit Finset framework requires knowing the support `SQ` of the
  split and its exactness (`∀ y ∈ SQ, split v P y ≠ 0`) — the price of the
  absence of `Finsupp` ;
- **`hPsupp` relays the support of `P`** : likewise, `SP` must contain the
  support of `P` for the endpoints of the segments to land there.

The proof is the oracle's, decomposed over the ingredients delivered in
k2.1-k2.3 : `Finset.mem_convexHull'` decomposes the membership of `(z, β)`
into weights `R` ; `abs_sum_le_sum_abs` bounds the share of height-`0`
weights ; `exists_sign_mul_add_eq` (k2.1) produces the sign `e` and the
coefficient `c` ; every point of the combination is brought back into the
hull of the transported support of `P` by `add_smul_mem_convexHull` (k2.2,
high slices) or by the direct membership of an endpoint (low slices, via
k2.3's `toReal_mem_map_iff`) ; `sum_smul_mem_convexHull` (k2.2) closes. -/
theorem pullback {d : ℕ} {P : (Fin d → ℤ) → ℝ} (hP : ∀ x, 0 ≤ P x)
    {SP : Finset (Fin d → ℤ)} (hPsupp : ∀ x, P x ≠ 0 → x ∈ SP)
    {v w : Fin d → ℤ} (hv : ∀ i, v i = 3 * w i)
    {SQ : Finset ((Fin d → ℤ) × Bool)} (hSQ : ∀ y ∈ SQ, split v P y ≠ 0)
    {β : ℝ} (hβ : 3⁻¹ ≤ β) {z : Fin d → ℝ}
    (hmem : (z, β) ∈ convexHull ℝ
      (↑(SQ.map toRealProdEmb) : Set ((Fin d → ℝ) × ℝ))) :
    ∃ e : ℝ, (e = 1 ∨ e = -1) ∧
      z + e • toReal w ∈ convexHull ℝ
        (↑(SP.map ⟨⇑toReal, toReal_injective⟩) : Set (Fin d → ℝ)) := by
  classical
  -- the transport direction : toReal v = 3 • toReal w
  have hvR : toReal v = (3 : ℝ) • toReal w := by
    funext i
    simp only [toReal_apply, hv i, Int.cast_mul, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  -- decomposing the membership into weights
  obtain ⟨R, hR0, hR1, hRc⟩ := Finset.mem_convexHull'.1 hmem
  have hz : ∑ y ∈ SQ.map toRealProdEmb, R y • y.1 = z := by
    have h := congrArg Prod.fst hRc
    rw [Prod.fst_sum] at h
    exact h
  have hb : ∑ y ∈ SQ.map toRealProdEmb, R y * y.2 = β := by
    have h := congrArg Prod.snd hRc
    rw [Prod.snd_sum] at h
    exact h
  -- the heights of the transported support are in {0, 1}
  have hsnd : ∀ y ∈ SQ.map toRealProdEmb, y.2 = 0 ∨ y.2 = 1 :=
    fun y hy => mem_map_toRealProd_snd hy
  -- every point of the transported support comes from a point of SQ
  have hpre : ∀ y ∈ SQ.map toRealProdEmb, ∃ y' ∈ SQ, toRealProd y' = y := by
    intro y hy
    rw [Finset.mem_map] at hy
    obtain ⟨y', hy', hye⟩ := hy
    exact ⟨y', hy', hye⟩
  -- the endpoints of low slices land in the support of P
  have hfalse : ∀ y ∈ SQ.map toRealProdEmb, y.2 = 0 →
      y.1 + toReal v ∈ (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ)) ∨
      y.1 - toReal v ∈ (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ)) := by
    intro y hy y0
    obtain ⟨y', hy', hye⟩ := hpre y hy
    obtain ⟨x', b'⟩ := y'
    cases b' with
    | false =>
      have hx := (split_apply_zero_ne_iff hP v x').1 (hSQ (x', false) hy')
      have hy1 : toReal x' = y.1 := congrArg Prod.fst hye
      rcases hx with h | h
      · left
        have hmem' := (toReal_mem_map_iff (x' + v) SP).2 (hPsupp _ h)
        rwa [map_add, hy1] at hmem'
      · right
        have hmem' := (toReal_mem_map_iff (x' - v) SP).2 (hPsupp _ h)
        rwa [map_sub, hy1] at hmem'
    | true =>
      exfalso
      have h1 : y.2 = 1 := by
        have := congrArg Prod.snd hye
        simpa [toRealProd] using this.symm
      rw [y0] at h1
      norm_num at h1
  -- the endpoints of high slices land in the support of P
  have htrue : ∀ y ∈ SQ.map toRealProdEmb, y.2 = 1 →
      y.1 + toReal v ∈ (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ)) ∧
      y.1 - toReal v ∈ (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ)) := by
    intro y hy y1
    obtain ⟨y', hy', hye⟩ := hpre y hy
    obtain ⟨x', b'⟩ := y'
    cases b' with
    | true =>
      obtain ⟨h, h'⟩ := (split_apply_one_ne_iff hP v x').1 (hSQ (x', true) hy')
      have hy1 : toReal x' = y.1 := congrArg Prod.fst hye
      constructor
      · have hmem' := (toReal_mem_map_iff (x' + v) SP).2 (hPsupp _ h)
        rwa [map_add, hy1] at hmem'
      · have hmem' := (toReal_mem_map_iff (x' - v) SP).2 (hPsupp _ h')
        rwa [map_sub, hy1] at hmem'
    | false =>
      exfalso
      have h0 : y.2 = 0 := by
        have := congrArg Prod.snd hye
        simpa [toRealProd] using this.symm
      rw [y1] at h0
      norm_num at h0
  -- the bound on the share of height-0 weights : |σ y| = 1 in both branches
  have ha : |∑ y ∈ SQ.map toRealProdEmb, R y * ((1 - y.2) *
      (if y.1 + toReal v ∈ (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ))
        then (1 : ℝ) else -1))| ≤ 1 - β := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum (g := fun y => R y * (1 - y.2)) ?_).trans_eq ?_)
    · intro y hy
      rcases hsnd y hy with h | h
      · rw [h, sub_zero, mul_one, abs_mul, abs_of_nonneg (hR0 y hy)]
        by_cases hyv : y.1 + toReal v ∈
            (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ))
        · rw [if_pos hyv]; simp
        · rw [if_neg hyv]; simp
      · rw [h, sub_self, mul_zero, zero_mul, mul_zero, abs_zero]
    · simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
      rw [hR1, hb]
  -- the sign e and the coefficient c
  obtain ⟨e, c, he, hc, hce⟩ := exists_sign_mul_add_eq hβ ha
  refine ⟨e, he, ?_⟩
  -- the barycentric identity
  have hsum : ∑ y ∈ SQ.map toRealProdEmb,
      R y * (y.2 * c + (1 - y.2) *
        (if y.1 + toReal v ∈ (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ))
          then (1 : ℝ) else -1)) = e / 3 := by
    rw [← hce, ← hb, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  have hzw : ∑ y ∈ SQ.map toRealProdEmb, R y •
      (y.1 + (y.2 * c + (1 - y.2) *
        (if y.1 + toReal v ∈ (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ))
          then (1 : ℝ) else -1)) • toReal v) = z + e • toReal w := by
    simp only [smul_add, smul_smul, Finset.sum_add_distrib]
    rw [← Finset.sum_smul, hsum, hvR, smul_smul]
    have hkey : (e / 3) * (3 : ℝ) = e := div_mul_cancel₀ e (by norm_num)
    rw [hkey, hz]
  rw [← hzw]
  -- every point of the combination is in the hull of P's support
  refine sum_smul_mem_convexHull _ R
    (fun y => y.1 + (y.2 * c + (1 - y.2) *
      (if y.1 + toReal v ∈ (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ))
        then (1 : ℝ) else -1)) • toReal v) hR0 hR1 ?_
  intro y hy
  rcases hsnd y hy with h | h
  · -- low slice : the coefficient is ±1, the corresponding endpoint is in the support
    have hcoef : (y.2 * c + (1 - y.2) *
        (if y.1 + toReal v ∈ (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ))
          then (1 : ℝ) else -1)) • toReal v
        = (if y.1 + toReal v ∈ (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ))
          then (1 : ℝ) else -1) • toReal v := by
      simp only [h, zero_mul, sub_zero, one_mul, zero_add]
    rw [hcoef]
    by_cases hyv : y.1 + toReal v ∈ (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ))
    · rw [if_pos hyv, one_smul]
      exact subset_convexHull ℝ _ hyv
    · rw [if_neg hyv]
      have hyv' : y.1 - toReal v ∈
          (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ)) :=
        ((hfalse y hy h).resolve_left hyv)
      have hconv : y.1 + (-1 : ℝ) • toReal v = y.1 - toReal v := by
        rw [neg_one_smul, sub_eq_add_neg]
      rw [hconv]
      exact subset_convexHull ℝ _ hyv'
  · -- high slice : the coefficient is c, both endpoints are in the support
    have hcoef : (y.2 * c + (1 - y.2) *
        (if y.1 + toReal v ∈ (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ))
          then (1 : ℝ) else -1)) • toReal v = c • toReal v := by
      simp only [h, one_mul, sub_self, zero_mul, add_zero]
    rw [hcoef]
    obtain ⟨hplus, hminus⟩ := htrue y hy h
    exact add_smul_mem_convexHull hminus hplus hc

end Discrepancy.Komlos_en
