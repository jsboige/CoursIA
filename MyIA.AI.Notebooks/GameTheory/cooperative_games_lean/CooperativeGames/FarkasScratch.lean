import CooperativeGames.Basic

/-!
# Bondareva-Shapley backward — Farkas infrastructure via `(Option N) → ℝ`

This file is SCRATCH for proving `hb_witness : ∃ x ∈ P, ∑ i : N, x i ≤ G.v Finset.univ`
in `bondareva_shapley_backward`. It validates the `(Option N) → ℝ` Farkas encoding with
`G : TUGame N` in scope. NOT committed into Basic.lean until the full proof closes
(anti-churn: scaffolding alone does not reduce the sorry count).

Strategy (see docs/BONDAREVA_FARKAS_PLAN.md):
- `none` coordinate carries the value functional `∑ S, w S * G.v S`
- `some i` coordinates carry the coalition-incidence sums `∑_{S ∋ i} w S`
- `hyperplane_separation_point` (Dual.lean:132) on `augCone` ⟹ separating functional
- translate `f : StrongDual ℝ ((Option N) → ℝ)` into balanced weights ⟹ contradict `hb`
-/

open scoped BigOperators
open Set LinearMap Pointwise

namespace BondarevaFarkas

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The augmented incidence map. `some i` = coalition sums; `none` = value functional. -/
noncomputable def phiAugLinear (G : TUGame N) : (Finset N → ℝ) →ₗ[ℝ] ((Option N) → ℝ) where
  toFun w := fun j => match j with
    | some i => ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), w S
    | none   => ∑ S : Finset N, w S * G.v S
  map_add' w1 w2 := by
    ext j
    rcases j with _ | i
    · -- none
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    · -- some i
      simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' r w := by
    ext j
    rcases j with _ | i
    · -- none: ∑ r*(w x*G.v x) = r * ∑ w S*G.v S  — `Finset.mul_sum` (factor LEFT)
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum]
    · -- some i: ∑_{S∋i} r*w S = r * ∑_{S∋i} w S  — `Finset.mul_sum`
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

/-- Finite-dim auto-continuity. -/
noncomputable def phiAugCont (G : TUGame N) : (Finset N → ℝ) →L[ℝ] ((Option N) → ℝ) :=
  LinearMap.toContinuousLinearMap (phiAugLinear G)

/-- The image of the positive cone under the augmented incidence map. -/
noncomputable def augCone (G : TUGame N) : ProperCone ℝ ((Option N) → ℝ) :=
  (ProperCone.positive ℝ (Finset N → ℝ)).map (phiAugCont G)

/-- **Step 2 validated**: `hyperplane_separation_point` (Dual.lean:132) applies directly
on `augCone`. Given any point outside `augCone`, we get a separating functional
`f : StrongDual ℝ ((Option N) → ℝ)` with `0 ≤ f` on `augCone` and `f x₀ < 0`. -/
example (G : TUGame N) (x₀ : (Option N) → ℝ) (h : x₀ ∉ augCone G) :
    ∃ f : StrongDual ℝ ((Option N) → ℝ),
      (∀ x ∈ augCone G, 0 ≤ f x) ∧ f x₀ < 0 :=
  ProperCone.hyperplane_separation_point (augCone G) h

/-- **Step 3 structural insight**: in finite dimensions, `augCone` (which is defined as a
`ClosedSubmodule.map` = closure of image) equals the plain image, because finite-dimensional
subspaces are closed (`Submodule.closed_of_finiteDimensional`). So membership in `augCone`
reduces to `∃ w ≥ 0, phiAugCont w = y`. This makes `x₀ ∉ augCone` provable constructively
(`∀ w ≥ 0, phiAugCont w ≠ x₀`), decoupling step (iii) from the separator translation (iv). -/
example (G : TUGame N) : FiniteDimensional ℝ ((Option N) → ℝ) := by
  infer_instance

/- **Step 3 core lemma (the finite-dim bridge) — ROOT CAUSE PINNED (cycle 8, 2026-06-21):**
In finite dimensions `augCone = ClosedSubmodule.map phiAugCont positive = closure(image)
(`ClosedSubmodule.map`, Topology/Algebra/Module/ClosedSubmodule.lean:221). The bridge
`y in augCone  iff  exists w >= 0 with phiAugCont w = y` needs the image CONE to be closed
(so closure(image) = image), i.e. the *polyhedral / finitely-generated cone is closed* theorem.

**Why this is blocked in Mathlib (v4.30.0-rc2):** the image is an `R>=0`-submodule (a cone,
NOT closed under negation). `Submodule.closed_of_finiteDimensional` (FiniteDimension.lean:414)
is **field-only** (R-subspaces) and does NOT apply. No `conicHull` / `Submodule R>=0`-closed
lemma exists; `Set.Finite.isClosed_convexHull` covers bounded convex hulls, not unbounded
cones. This is the IRREDUCIBLE KERNEL for the Farkas proof of `hb_witness` (Basic.lean:312).

**Decomposition (for the BG-prover / future cycles):** (a) prove this closed-cone lemma
~50-100L (Caratheodory, or explicit finite-basis + mapEquiv-style on a section), then
(b) the bridge closes in ~5-10 lines via `Submodule.mem_map` + `subset_closure`, and (c) the
Farkas argument (hyperplane_separation_point on augCone, x0 not-in via hb) gives hb_witness.
Cycle 9 (2026-06-21) refinement — BIDUAL ROUTE RULED OUT + proof blueprint:
- `ProperCone.dual_dual_flip` (Dual.lean:145, C** = C, proved via hyperplane_separation_point)
  is EQUIVALENT to separation, not a bypass: the C** subset C direction (which would build a
  dual witness from x0 not-in C) REQUIRES x0 not-in C as input = the hard part. And augCone.dual
  is computable (no closure) via the adjoint, but exhibiting y from hb is still the circular
  Farkas content. Bidual does not circumvent cone-closed.
- Proof blueprint for (a) cone-closed [~50-80L, multi-cycle]: cone(v_1..v_n) = finite union over
  Caratheodory-subsets I (linearly independent, |I| <= dim) of simplicial cones cone(v_I). Each
  simplicial cone = injective linear image of the orthant = closed (injective LMAP finite-dim =
  homeo onto closed range, cf ClosedSubmodule.mapEquiv L314 + Submodule.closed_of_finiteDimensional).
  Conic-Caratheodory derivable from Mathlib Convex/Caratheodory.lean (convex version) via the
  homogenization v_i |-> (v_i, 1). Finite union of closed = closed.
Easy direction (exists w => y in closure) is constructive; only (exists) is hard. -/
-- The `augCone_mem_iff` bridge is proven BELOW, after the cone-closed bricks
-- (`conicHull_linearIndependent_isClosed` / `finGenCone_isClosed`), to avoid a
-- forward reference. See the end of this namespace.

/-! ## SIMPLICIAL brick (1st of the cone-closed lemma for `augCone_mem_iff`)

The conic hull of finitely many linearly independent vectors in a finite-dimensional
normed space is closed. This is the building block for the cone-closed kernel: the
general cone (finitely-generated, possibly dependent) is a finite union (Caratheodory)
of such simplicial cones, each closed here. Brick 1 of the ~50-80L blueprint (cycle 10). -/

theorem conicHull_linearIndependent_isClosed
    {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (v : ι → F) (hli : LinearIndependent ℝ v) :
    IsClosed {y : F | ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ y = ∑ i, c i • v i} := by
  -- ψ : (ι → ℝ) →ₗ[ℝ] F is the spanning linear-combination map; LI gives injectivity.
  set ψ : (ι → ℝ) →ₗ[ℝ] F := Fintype.linearCombination ℝ v with hψ_def
  have hψ_inj : Function.Injective ψ :=
    LinearIndependent.fintypeLinearCombination_injective hli
  have hψ_app : ∀ c, ψ c = ∑ i, c i • v i := fun c => Fintype.linearCombination_apply ℝ v c
  -- range ψ is closed (finite-dimensional submodule).
  have hRangeClosed : IsClosed (ψ.range : Set F) := ψ.range.closed_of_finiteDimensional
  -- ψ is a linear equiv onto its range, then a continuous linear equiv (finite-dim).
  set eLE : (ι → ℝ) ≃ₗ[ℝ] ψ.range := LinearEquiv.ofInjective ψ hψ_inj
  set eCLE : (ι → ℝ) ≃L[ℝ] ψ.range := eLE.toContinuousLinearEquiv
  -- key identity: the conic-hull image equals the orthant image, pushed to F.
  have hkey : ∀ c, (ψ.range.subtype : ψ.range → F) (eCLE c) = ∑ i, c i • v i := by
    intro c
    show (ψ.range.subtype : ψ.range → F) (eLE.toContinuousLinearEquiv c) = ∑ i, c i • v i
    simp only [Submodule.subtype_apply, LinearEquiv.coe_toContinuousLinearEquiv']
    rw [LinearEquiv.ofInjective_apply, hψ_app]
  -- the positive orthant is closed (finite intersection of closed half-spaces).
  have hOrthant : IsClosed ({c : ι → ℝ | ∀ i, 0 ≤ c i} : Set (ι → ℝ)) := by
    rw [← Set.iInter_setOf]
    exact isClosed_iInter fun i => IsClosed.preimage (continuous_apply i) isClosed_Ici
  -- image of the closed orthant under the continuous linear equiv is closed in (range ψ).
  have hImg : IsClosed ((eCLE : (ι → ℝ) → ψ.range) '' {c | ∀ i, 0 ≤ c i}) :=
    eCLE.isClosed_image.mpr hOrthant
  -- inclusion (range ψ) ↪ F is a closed map (range is closed).
  have hCM : IsClosedMap (ψ.range.subtype : ψ.range → F) :=
    hRangeClosed.isClosedEmbedding_subtypeVal.isClosedMap
  -- the conic hull set = inclusion '' (eCLE '' orthant).
  have hC_eq :
      {y : F | ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ y = ∑ i, c i • v i} =
        (ψ.range.subtype : ψ.range → F) ''
          ((eCLE : (ι → ℝ) → ψ.range) '' {c | ∀ i, 0 ≤ c i}) := by
    ext y
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨eCLE c, ⟨c, hc, rfl⟩, hkey c⟩
    · rintro ⟨r, ⟨c, hc, hr⟩, hy⟩
      refine ⟨c, hc, ?_⟩
      rw [← hr] at hy
      rw [hkey c] at hy
      exact hy.symm
  rw [hC_eq]
  exact hCM _ hImg

/-! ## Bricks 2+3 — finitely-generated cone is closed (cone-closed kernel, target)

Goal: `finGenCone_isClosed` — a finitely-generated cone `K = {∑ cᵢ vᵢ | cᵢ ≥ 0}` in a
finite-dim normed space is closed. Proof skeleton (cycle-9 blueprint):
  `K = ⋃ { cone(v|_I) : I ⊆ ι, {vᵢ}_{i∈I} linearly independent }`
- **Forward ⊆** = conic-Carathéodory (brick 2): every point of K lies in the
  simplicial cone of an LI sub-family. Classical proof mirrors Mathlib's convex
  `minCardFinsetOfMemConvexHull` + `affineIndependent_minCardFinsetOfMemConvexHull`
  (Convex/Caratheodory.lean:128): among finsets I with `y ∈ cone(v|_I)`, pick one
  of minimal cardinality; if its generators were dependent, a linear relation
  `∑ aᵢ vᵢ = 0` (not all zero) lets one coefficient be zeroed by sliding t along
  `y = ∑(cᵢ + t aᵢ) vᵢ` to a feasibility-polytope endpoint (cᵢ+t aᵢ ≥ 0 ∀i),
  contradicting minimality ⟹ LI.
- **Reverse ⊇** is trivial (any sub-cone ⊆ K).
- Each `cone(v|_I)` is closed (brick 1 `conicHull_linearIndependent_isClosed`).
- **Finite union** (brick 3): `ι` finite ⟹ finitely many LI sub-families ⟹ union
  of finitely many closed sets = closed (`Set.Finite.isClosed_biUnion`).

The forward direction (brick 2) is the self-contained linear-algebra core. It is
isolated below as `mem_cone_iff_exists_li_subset` so the BG-prover / future cycles
attack a clean target; once it closes, `finGenCone_isClosed` assembles in ~15L. -/

/-- **Brick 2 — conic-Carathéodory (independent form), the isolated core.**
Every point of a finitely-generated cone lies in the simplicial cone of some
linearly-independent sub-family. Self-contained (pure finite-dim linear algebra,
no topology). ~100L proof; recipe pinned cycle 12 for the next attempt:

Vehicle = `WellFounded.induction` on `(measure Finset.card)`, motive over a
support finset `s : Finset ι` with `c : ι → ℝ` satisfying `∀ i ∉ s, c i = 0`.
Inductive step on `(s, c)`:
1. **LI case**: if `LinearIndependent ℝ (fun i : ↥s => v i)`, return `I = s`,
   `d i = c i`. Transport `∑ i : ↥s, c i • v i = ∑ i : ι, c i • v i` (c=0 off s)
   via `Fintype.sum_univ` + `Finset.sum_attach` + support-zero.
2. **Drop-zeros (full-support)**: if some `i ∈ s` has `c i = 0`, recurse on
   `s \ {i}` (strictly smaller card) — guarantees the reduction below sees a
   strictly-positive `c` on its support.
3. **Relation extraction** (`¬LI`): `Fintype.linearIndependent_iff` (Defs.lean:771)
   contrapositive gives `∃ a : ↥s → ℝ, (∑ a i • v i = 0) ∧ ∃ i, a i ≠ 0`.
   Negate to assume `∃ i, 0 < a i` (else use `-a`).
4. **Argmin reduction**: `pos := (Finset.univ : Finset ↥s).filter (0 < a·)`,
   `t := (pos.image (fun i => c i / a i)).min' _` — `t ≥ 0` (c ≥ 0, a > 0), and
   by full-support `t > 0` would force a drop, but **t > 0 is NOT required** for
   correctness; `c' i := c i - t·(a i)` satisfies `c' i ≥ 0 ∀i` (cases: `a i > 0`
   ⟹ `c i / a i ≥ t` by `min'`; `a i ≤ 0` ⟹ `c i - t·a i ≥ c i ≥ 0`), `∑ c' i • v i = y`
   (subtract `t·(∑ a i • v i) = 0`), and `∃ j ∈ pos, c j / a j = t` ⟹ `c' j = 0`.
5. **Recurse**: support of `c'` ⊆ `s \ {j}` (strictly smaller) ⟹ apply IH.

Transport bottlenecks (sub-fiddly, pre-identified): sum-over-`↥s` ↔ sum-over-`ι`
(LI case + final witness), and `↥s` ↔ `↥(s \ {j})` coefficient restriction (step 5). -/
theorem mem_cone_iff_exists_li_subset
    {ι F : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (v : ι → F) (y : F)
    (hy : ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ y = ∑ i, c i • v i) :
    ∃ (I : Finset ι), LinearIndependent ℝ (fun i : ↥I => v i) ∧
      ∃ c : ↥I → ℝ, (∀ i, 0 ≤ c i) ∧ y = ∑ i, c i • v i := by
  -- A finset `s` is *good* if it carries a non-negative witness `c` with support ⊆ s summing to y.
  let good : Finset ι → Prop := fun s =>
    ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ (∀ i ∉ s, c i = 0) ∧ y = ∑ i, c i • v i
  have hgood_univ : good Finset.univ := by
    obtain ⟨c, hc, hsum⟩ := hy
    exact ⟨c, hc, fun i hi => (hi (Finset.mem_univ i)).elim, hsum⟩
  -- Strong induction on the cardinality of the carrying finset. Minimal-cardinality ⟹ full
  -- support (a zero coefficient could be dropped to a strictly-smaller good finset), so the
  -- induction hypothesis applies to `s \ {j}` after the argmin reduction below.
  have step : ∀ (s : Finset ι),
      (∀ s', s'.card < s.card → good s' →
        ∃ (I : Finset ι), LinearIndependent ℝ (fun i : ↥I => v i) ∧
          ∃ c : ↥I → ℝ, (∀ i, 0 ≤ c i) ∧ y = ∑ i : ↥I, c i • v i) →
      good s →
    ∃ (I : Finset ι), LinearIndependent ℝ (fun i : ↥I => v i) ∧
      ∃ c : ↥I → ℝ, (∀ i, 0 ≤ c i) ∧ y = ∑ i : ↥I, c i • v i := by
    intro s IH hs
    obtain ⟨c, hc, hcsupp, hsum⟩ := hs
    by_cases hfull : ∀ i ∈ s, c i ≠ 0
    case neg hfull =>
      push_neg at hfull
      obtain ⟨i, his, hci⟩ := hfull
      -- s.erase i is good (the i-term is now zero) and strictly smaller ⟹ IH.
      have hcard : (s.erase i).card < s.card := Finset.card_erase_lt_of_mem his
      refine IH (s.erase i) hcard ⟨c, hc, ?_, hsum⟩
      intro j hj
      by_cases hjeq : j = i
      · rw [hjeq]; exact hci
      by_cases hjs : j ∈ s
      · exact absurd (Finset.mem_erase.mpr ⟨hjeq, hjs⟩) hj
      · exact hcsupp j hjs
    case pos hfull =>
      -- c is strictly positive on s.
      have hcpos : ∀ i : ↥s, 0 < c i.val := fun i =>
        lt_of_le_of_ne (hc i.val) (Ne.symm (hfull i.val i.prop))
      -- transport the sum to the subtype carrier.
      have htrans : ∑ i : ι, c i • v i = ∑ i : ↥s, c i.val • v i.val := by
        -- sum_subset gives ∑s = ∑univ (off-s terms zero); sum_coe_sort gives ∑↥s = ∑s.
        have hssub : ∑ i ∈ s, c i • v i = ∑ i ∈ Finset.univ, c i • v i :=
          Finset.sum_subset (Finset.subset_univ s)
            (fun i _ hi => by rw [hcsupp i hi, zero_smul])
        exact hssub.symm.trans (Finset.sum_coe_sort s (fun i => c i • v i)).symm
      by_cases hli : LinearIndependent ℝ (fun i : ↥s => v i)
      · exact ⟨s, hli, (fun i : ↥s => c i.val), fun i => hc i.val, hsum.trans htrans⟩
      · obtain ⟨g, hgsum, hg_ne⟩ := Fintype.not_linearIndependent_iff.mp hli
        -- [ARGMIN-REDUCTION LEAF (diagnosed)]: from dependency relation `g` on ↥s
        -- (hgsum : ∑ i : ↥s, g i • v i.val = 0, hg_ne : ∃ i, g i ≠ 0) and positive
        -- carrier (hcpos : ∀ i : ↥s, 0 < c i.val), build d + j then
        -- `exact IH (s.erase j) hcardj ⟨d, hd_nonneg, hd_supp, hd_sum⟩`. Recipe:
        --   1. sign-normalize g so ∃ i, 0 < g i (negate if ∀ i, g i ≤ 0); ∑ still 0.
        --   2. pos := (Finset.univ : Finset ↥s).filter (0 < g·); nonempty by (1).
        --      t := (pos.image (fun i => c i.val / g i)).min' ⟨..⟩.
        --   3. d i := if hi : i ∈ s then c i - t * g ⟨i,hi⟩ else 0.
        --      hd_nonneg, hd_sum (= y - t·0), hd_zero (argmin j), supp ⊆ s.erase j.
        --   4. hcardj := (s.erase j).card < s.card (j ∈ s). Then IH closes.
        -- [ARGMIN-REDUCTION implementation, cycle 14]: slide `c` along `g` to zero the
        -- argmin coefficient, then recurse on `s.erase j.val`.
        -- (1) Sign-normalize `g` to `a` with `∑ a•v = 0` and `∃ i, 0 < a i`.
        have ⟨a, ha_sum, ha_pos⟩ :
            ∃ a : ↥s → ℝ, (∑ i : ↥s, a i • v i.val = 0) ∧ ∃ i : ↥s, 0 < a i := by
          by_cases hgp : ∃ i : ↥s, 0 < g i
          · exact ⟨g, hgsum, hgp⟩
          · push_neg at hgp
            refine ⟨-g, ?_, ?_⟩
            · have hng : ∑ i : ↥s, (-g) i • v i.val = -(∑ i : ↥s, g i • v i.val) := by
                simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
              rw [hng, hgsum, neg_zero]
            · obtain ⟨i, hgi⟩ := hg_ne
              exact ⟨i, neg_pos.mpr (lt_of_le_of_ne (hgp i) hgi)⟩
        -- (2) `pos = {i : a i > 0}`, nonempty; `t` = argmin of `c i.val / a i` over `pos`.
        set pos : Finset ↥s := Finset.univ.filter (fun i => 0 < a i) with hpos_def
        have hpos_ne : pos.Nonempty := by
          obtain ⟨i, hi⟩ := ha_pos
          exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
        have himg_ne : (pos.image (fun i => c i.val / a i)).Nonempty :=
          hpos_ne.image (fun i => c i.val / a i)
        set t : ℝ := (pos.image (fun i => c i.val / a i)).min' himg_ne with ht_def
        have ht_nonneg : 0 ≤ t := by
          obtain ⟨k, hk_pos, hk_eq⟩ :=
            Finset.mem_image.mp ((pos.image (fun i => c i.val / a i)).min'_mem himg_ne)
          have hka : 0 < a k := (Finset.mem_filter.mp hk_pos).2
          rw [ht_def, ← hk_eq]; exact div_nonneg (hc k.val) (le_of_lt hka)
        -- (3) argmin-attaining index `j ∈ pos` with `c j.val / a j = t`.
        obtain ⟨j, hj_pos, hj_eq⟩ :=
          Finset.mem_image.mp ((pos.image (fun i => c i.val / a i)).min'_mem himg_ne)
        have hja : 0 < a j := (Finset.mem_filter.mp hj_pos).2
        have hjv_mem : (j : ι) ∈ s := Subtype.prop j
        have htja : t * a j = c j.val := by
          rw [ht_def, ← hj_eq]
          exact div_mul_cancel₀ (c j.val) hja.ne'
        -- `d` = slid witness; zero off `s`, zero at `j.val` (argmin).
        let d : ι → ℝ := fun i => c i - t * (if hi : i ∈ s then a ⟨i, hi⟩ else 0)
        have hdj_zero : d j.val = 0 := by
          show c j.val - t * (if _ : (j : ι) ∈ s then a ⟨(j : ι), _⟩ else 0) = 0
          rw [dif_pos hjv_mem, show a ⟨(j : ι), hjv_mem⟩ = a j from rfl, htja]
          ring
        have hd_nonneg : ∀ i, 0 ≤ d i := by
          intro i
          show 0 ≤ c i - t * (if hi : i ∈ s then a ⟨i, hi⟩ else 0)
          by_cases hi : i ∈ s
          · rw [dif_pos hi]
            by_cases hia : 0 < a ⟨i, hi⟩
            · have hmem : (c i / a ⟨i, hi⟩) ∈ pos.image (fun k => c k.val / a k) :=
                Finset.mem_image.mpr
                  ⟨⟨i, hi⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hia⟩, rfl⟩
              have hle : t ≤ c i / a ⟨i, hi⟩ := by
                rw [ht_def]
                exact Finset.min'_le _ _ hmem
              have htmul : t * a ⟨i, hi⟩ ≤ c i := (le_div_iff₀ hia).mp hle
              exact sub_nonneg.mpr (by linarith [hc i])
            · have hiale : a ⟨i, hi⟩ ≤ 0 := le_of_not_gt hia
              have htmul : t * a ⟨i, hi⟩ ≤ 0 :=
                mul_nonpos_of_nonneg_of_nonpos ht_nonneg hiale
              exact sub_nonneg.mpr (by linarith [hc i])
          · rw [dif_neg hi, mul_zero, sub_zero]; exact hc i
        have hd_supp : ∀ i, i ∉ s.erase j.val → d i = 0 := by
          intro i hi
          by_cases hij : i = j.val
          · rw [hij]; exact hdj_zero
          · by_cases his : i ∈ s
            · exact (hi (Finset.mem_erase.mpr ⟨hij, his⟩)).elim
            · show c i - t * (if _ : i ∈ s then a ⟨i, _⟩ else 0) = 0
              rw [dif_neg his, mul_zero, sub_zero]; exact hcsupp i his
        have hd_sum : y = ∑ i : ι, d i • v i := by
          rw [hsum]
          have hdi_val : ∀ i : ↥s, d i.val = c i.val - t * a i := by
            intro i
            show c i.val - t * (if _ : (i.val : ι) ∈ s then a ⟨(i.val : ι), _⟩ else 0) =
              c i.val - t * a i
            rw [dif_pos i.prop, show a ⟨(i.val : ι), i.prop⟩ = a i from rfl]
          have hdi_zero : ∀ i ∉ s, d i = 0 := by
            intro i hi
            show c i - t * (if _ : i ∈ s then _ else 0) = 0
            rw [dif_neg hi, mul_zero, sub_zero]; exact hcsupp i hi
          have hdtrans : ∑ i : ι, d i • v i = ∑ i : ↥s, d i.val • v i.val := by
            have hssub : ∑ i ∈ s, d i • v i = ∑ i ∈ Finset.univ, d i • v i :=
              Finset.sum_subset (Finset.subset_univ s)
                (fun i _ hi => by rw [hdi_zero i hi, zero_smul])
            exact hssub.symm.trans (Finset.sum_coe_sort s (fun i => d i • v i)).symm
          rw [hdtrans, htrans]
          rw [show ∑ i : ↥s, d i.val • v i.val = ∑ i : ↥s, (c i.val - t * a i) • v i.val from
              Finset.sum_congr rfl (fun i _ => by rw [hdi_val i])]
          simp only [sub_smul]
          rw [Finset.sum_sub_distrib]
          have hsum_ta : ∑ i : ↥s, (t * a i) • v i.val = 0 := by
            have heq : ∀ i : ↥s, (t * a i) • v i.val = t • (a i • v i.val) :=
              fun i => (smul_smul t (a i) (v i.val)).symm
            rw [Finset.sum_congr rfl (fun i _ => heq i), ← Finset.smul_sum, ha_sum,
              smul_zero]
          rw [hsum_ta, sub_zero]
        have hcardj : (s.erase j.val).card < s.card := Finset.card_erase_lt_of_mem hjv_mem
        exact IH (s.erase j.val) hcardj ⟨d, hd_nonneg, hd_supp, hd_sum⟩
  exact (measure Finset.card).wf.induction Finset.univ step hgood_univ

/-- **Brick 3.** A finitely-generated conic hull is closed.
    K = union over all finsets I of the LI-guarded simplicial cone on I.
    Forward (cone ⊆ union) = conic-Carathéodory (brick 2): every combo reduces
    to a combo over a linearly-independent subset. Reverse (union ⊆ cone) =
    extend a `↥I`-indexed combo to `ι` by zeros. Each slice is closed (LI slice:
    brick 1; non-LI slice: empty), and the finite union of closed sets is closed. -/
theorem finGenCone_isClosed
    {ι F : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (v : ι → F) :
    IsClosed {y : F | ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ y = ∑ i, c i • v i} := by
  have hK_eq :
      {y | ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ y = ∑ i, c i • v i} =
        ⋃ (I : Finset ι),
          {y | LinearIndependent ℝ (fun i : ↥I => v i) ∧
                (∃ c : ↥I → ℝ, (∀ i, 0 ≤ c i) ∧ y = ∑ i, c i • v i.val)} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨c, hc, hy⟩
      obtain ⟨J, hJli, d, hd, hdsum⟩ := mem_cone_iff_exists_li_subset v y ⟨c, hc, hy⟩
      exact ⟨J, hJli, d, hd, hdsum⟩
    · rintro ⟨J, hJli, d, hd, hdsum⟩
      let c : ι → ℝ := fun i => if hi : i ∈ J then d ⟨i, hi⟩ else 0
      have hc_val : ∀ i : ↥J, c i.val = d i := by
        intro i
        show (if hi : i.val ∈ J then d ⟨i.val, hi⟩ else 0) = d i
        rw [dif_pos i.prop]
      have hc_zero : ∀ i ∉ J, c i = 0 := by
        intro i hi
        show (if hi : i ∈ J then d ⟨i, hi⟩ else 0) = 0
        rw [dif_neg hi]
      refine ⟨c, ?_, ?_⟩
      · intro i
        show 0 ≤ (if hi : i ∈ J then d ⟨i, hi⟩ else 0)
        by_cases hi : i ∈ J
        · rw [dif_pos hi]; exact hd ⟨i, hi⟩
        · simp only [dif_neg hi]; exact le_refl (0 : ℝ)
      · show y = ∑ i : ι, c i • v i
        have hdtrans : ∑ i : ι, c i • v i = ∑ i : ↥J, c i.val • v i.val := by
          have hssub : ∑ i ∈ J, c i • v i = ∑ i ∈ Finset.univ, c i • v i :=
            Finset.sum_subset (Finset.subset_univ J)
              (fun i _ hi => by rw [hc_zero i hi, zero_smul])
          exact hssub.symm.trans (Finset.sum_coe_sort J (fun i => c i • v i)).symm
        rw [hdtrans]
        rw [show ∑ i : ↥J, c i.val • v i.val = ∑ i : ↥J, d i • v i.val from
            Finset.sum_congr rfl (fun i _ => by rw [hc_val i])]
        rw [← hdsum]
  rw [hK_eq]
  refine isClosed_iUnion_of_finite fun I => ?_
  by_cases hI : LinearIndependent ℝ (fun i : ↥I => v i)
  · have hSet :
        {y | LinearIndependent ℝ (fun i : ↥I => v i) ∧
              (∃ c : ↥I → ℝ, (∀ i, 0 ≤ c i) ∧ y = ∑ i, c i • v i.val)} =
        {y | ∃ c : ↥I → ℝ, (∀ i, 0 ≤ c i) ∧ y = ∑ i, c i • v i.val} := by
      ext y
      simp only [Set.mem_setOf_eq, hI, true_and]
    rw [hSet]
    exact conicHull_linearIndependent_isClosed (fun i : ↥I => v i.val) hI
  · have hSet :
        ({y | LinearIndependent ℝ (fun i : ↥I => v i) ∧
              (∃ c : ↥I → ℝ, (∀ i, 0 ≤ c i) ∧ y = ∑ i, c i • v i.val)} : Set F) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨hLI, _⟩
      exact hI hLI
    rw [hSet]
    exact isClosed_empty

/-! ## The finite-dim bridge `augCone_mem_iff`

With the cone-closed bricks proven, `augCone G` (a `ProperCone` = `ClosedSubmodule.map
phiAugCont positive`, i.e. the *closure* of the image) equals the plain image: the image
is a finitely-generated cone (standard-basis generators `v S = phiAugCont G (Pi.single S 1)`),
hence closed by `finGenCone_isClosed`, so `closure(image) = image`. Membership then reduces
to `∃ w ≥ 0, phiAugCont G w = y`. This closes the cone-closed kernel. -/
theorem augCone_mem_iff (G : TUGame N) (y : (Option N) → ℝ) :
    y ∈ augCone G ↔ ∃ w : Finset N → ℝ, (∀ S, 0 ≤ w S) ∧ phiAugCont G w = y := by
  -- Standard-basis generators: v S = phiAugCont G (e_S), where e_S = Pi.single S 1.
  let v (S : Finset N) : (Option N) → ℝ := phiAugCont G (Pi.single S 1)
  -- Linearity-in-standard-basis: phiAugCont G w = Σ S, w S • v S, because every
  -- w : Finset N → ℝ is its standard-basis expansion Σ S, w S • Pi.single S 1.
  have hphi_sum (w : Finset N → ℝ) : phiAugCont G w = ∑ S, w S • v S := by
    have hw : w = ∑ S, w S • Pi.single S 1 := by
      ext S₀
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      rw [Fintype.sum_eq_single S₀]
      · simp
      · intro b hb
        rw [if_neg (Ne.symm hb)]
        ring
    conv_lhs => rw [hw]
    simp only [map_sum, map_smul]
    rfl
  -- The image cone as a finitely-generated conic hull on `v` (matches brick-3 exactly).
  set image : Set ((Option N) → ℝ) :=
      {y | ∃ c : Finset N → ℝ, (∀ S, 0 ≤ c S) ∧ y = ∑ S, c S • v S} with himage_def
  have hImgClosed : IsClosed image := finGenCone_isClosed v
  have hImg_eq : image = {y | ∃ w : Finset N → ℝ, (∀ S, 0 ≤ w S) ∧ phiAugCont G w = y} := by
    ext y
    constructor
    · rintro ⟨c, hc, hy⟩; exact ⟨c, hc, by rw [hphi_sum c]; exact hy.symm⟩
    · rintro ⟨w, hw, hy⟩; exact ⟨w, hw, by rw [← hphi_sum w]; exact hy.symm⟩
  -- The Mathlib `PointedCone.map` image carrier equals the bridge RHS set.
  have hmapImg : ((ProperCone.positive ℝ (Finset N → ℝ)).toPointedCone.map
      (phiAugCont G : (Finset N → ℝ) →ₗ[ℝ] ((Option N) → ℝ)) : Set _) =
      {y | ∃ w : Finset N → ℝ, (∀ S, 0 ≤ w S) ∧ phiAugCont G w = y} := by
    ext y
    simp only [SetLike.mem_coe, PointedCone.mem_map, ProperCone.mem_toPointedCone,
      ProperCone.mem_positive]
    constructor
    · rintro ⟨w, hw, hy⟩; exact ⟨w, hw, hy⟩
    · rintro ⟨w, hw, hy⟩; exact ⟨w, hw, hy⟩
  have hRhsClosed : IsClosed
      {y | ∃ w : Finset N → ℝ, (∀ S, 0 ≤ w S) ∧ phiAugCont G w = y} := by
    rw [← hImg_eq]; exact hImgClosed
  constructor
  · -- (→) y ∈ augCone G ≡ y ∈ closure(image) → y ∈ image (image is closed)
    intro hy
    have hy0 : y ∈ closure
        {y | ∃ w : Finset N → ℝ, (∀ S, 0 ≤ w S) ∧ phiAugCont G w = y} := by
      have key : y ∈ closure
          ((ProperCone.positive ℝ (Finset N → ℝ)).toPointedCone.map
            (phiAugCont G : (Finset N → ℝ) →ₗ[ℝ] ((Option N) → ℝ)) : Set _) := by
        have := hy
        simp only [augCone, ProperCone.mem_map, PointedCone.mem_closure] at this
        exact this
      rw [hmapImg] at key
      exact key
    rw [hRhsClosed.closure_eq] at hy0
    exact hy0
  · -- (←) phiAugCont G w ∈ augCone G (image ⊆ closure = augCone)
    rintro ⟨w, hw, rfl⟩
    have h_in_image : (phiAugCont G w) ∈
        ((ProperCone.positive ℝ (Finset N → ℝ)).toPointedCone.map
          (phiAugCont G : (Finset N → ℝ) →ₗ[ℝ] ((Option N) → ℝ)) : Set _) := by
      rw [hmapImg]; exact ⟨w, hw, rfl⟩
    have h_in_closure : (phiAugCont G w) ∈ closure
        ((ProperCone.positive ℝ (Finset N → ℝ)).toPointedCone.map
          (phiAugCont G : (Finset N → ℝ) →ₗ[ℝ] ((Option N) → ℝ)) : Set _) :=
      subset_closure h_in_image
    have : (phiAugCont G w) ∈ augCone G := by
      simp only [augCone, ProperCone.mem_map, PointedCone.mem_closure]
      exact h_in_closure
    exact this

/-! ## Bridge to balanced weights (cycle 18)

These two lemmas are the conic reformulation of the `Balanced` hypothesis. Together they provide
the `x₀ ∉ augCone G` setup that `ProperCone.hyperplane_separation_point` (Dual.lean:132) needs.
The remaining hard step of `bondareva_shapley_backward` is to decode the separating functional
`f : StrongDual ℝ ((Option N) → ℝ)` into a witness `x : N → ℝ` with `x ∈ P` and `∑ x ≤ v(N)`.
-/

/-- The "balanced-unit" point: `1` in every `some i` coordinate, `t` in the `none` (value)
    coordinate. -/
def balancedUnit (t : ℝ) : (Option N) → ℝ := fun j => match j with
  | some _ => 1
  | none   => t

/-- **Bridge lemma**: the balanced-unit point at value `t` lies in `augCone G` iff there exist
    balanced weights `w` realizing value `t`. The `some i` coordinates of `phiAugCont G w` are
    exactly the incidence sums `∑_{S ∋ i} w S` (so `balancedUnit`'s unit entries force
    `BalancedWeights`), and the `none` coordinate reads off `∑_S w S * v(S)`. -/
lemma augCone_balancedUnit_iff (G : TUGame N) (t : ℝ) :
    balancedUnit t ∈ augCone G ↔
      ∃ w : Finset N → ℝ, TUGame.BalancedWeights w ∧ ∑ S : Finset N, w S * G.v S = t := by
  rw [augCone_mem_iff]
  constructor
  · rintro ⟨w, hw, hy⟩
    exact ⟨w, ⟨hw, fun i => congr_fun hy (some i)⟩, congr_fun hy none⟩
  · rintro ⟨w, ⟨hw, hbal⟩, hsum⟩
    refine ⟨w, hw, ?_⟩
    funext j
    rcases j with _ | i
    · exact hsum
    · exact hbal i

/-- **Separating point**: given `G.Balanced`, the point at value `v(N) + t` (any `t > 0`) lies
    strictly outside `augCone G`. By `Balanced` no balanced collection can realize a value above
    `v(N)`, so the bridge lemma excludes it. This is the `x₀ ∉ augCone G` hypothesis for
    `hyperplane_separation_point`. -/
lemma balanced_notIn_augCone (G : TUGame N) (hb : G.Balanced) {t : ℝ} (ht : 0 < t) :
    balancedUnit (G.v Finset.univ + t) ∉ augCone G := by
  intro hmem
  rw [augCone_balancedUnit_iff] at hmem
  obtain ⟨w, hw_bal, hw_sum⟩ := hmem
  have hbnd := hb w hw_bal
  linarith

/-- **Dual characterization of `augCone`** (cycle 19): a continuous linear functional `f`
    is nonnegative on `augCone G` iff it is nonnegative on each of the finitely many
    generators `phiAugCont G (Pi.single S 1)`. The (⟸) direction is the load-bearing one —
    it uses the finite generation (`augCone_mem_iff`): every cone element is a nonneg linear
    combination of the generators, so `f` of it is a nonneg combination of the `f`-of-generators.
    This is the foundation for translating a separating functional `f` (from
    `hyperplane_separation_point`) into the witness structure for `hb_witness`: from
    `0 ≤ f (phiAugCont G (Pi.single S 1))` one reads off the coalitional-rationality of `x`. -/
lemma augCone_dual_iff (G : TUGame N) (f : ((Option N) → ℝ) →L[ℝ] ℝ) :
    (∀ y ∈ augCone G, 0 ≤ f y) ↔
      ∀ S : Finset N, 0 ≤ f (phiAugCont G (Pi.single S 1)) := by
  refine ⟨fun hC S => hC _ ?_, ?_⟩
  · -- each generator `phiAugCont G (Pi.single S 1)` is in `augCone G` (the weight `Pi.single S 1` is ≥ 0)
    rw [augCone_mem_iff]
    refine ⟨Pi.single S 1, fun S' => ?_, rfl⟩
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  · rintro hgen y hy
    obtain ⟨w, hw, hyw⟩ := (augCone_mem_iff G y).mp hy
    rw [← hyw]
    -- `phiAugCont G w = ∑ S, w S • phiAugCont G (Pi.single S 1)` by linearity + standard basis.
    have hphi_sum : phiAugCont G w =
        ∑ S : Finset N, w S • phiAugCont G (Pi.single S 1) := by
      have hw_basis : w = ∑ S, w S • Pi.single S 1 := by
        funext S₀
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
          mul_boole, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      conv_lhs => rw [hw_basis]
      simp only [map_sum, map_smul]
    rw [hphi_sum]
    simp only [map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_nonneg (fun S _ => mul_nonneg (hw S) (hgen S))

/-! ## Witness decoding (cycle 20)

The separating functional `f` from `hyperplane_separation_point` (applied to
`balancedUnit (v(N)+t) ∉ augCone`, which `balanced_notIn_augCone` provides) must be
decoded into the Core witness `x : N → ℝ`. The natural candidate is
`x i := f (Pi.single (some i) 1) / (-f (Pi.single none 1))`, which is well-defined once
we know `f (Pi.single none 1) < 0`. This sign is the first load-bearing decoding step. -/

/-- **Decoding sign condition (cycle 20)** — the separating functional `f` satisfies
    `f (Pi.single none 1) < 0`. Proof: `0 ≤ f` on the grand-coalition generator
    `phiAugCont G (Pi.single ⊤ 1)` (it is in `augCone`, via `augCone_dual_iff`); the
    identity `balancedUnit (v(N)+t) = phiAugCont G (Pi.single ⊤ 1) + t • Pi.single none 1`
    plus linearity turns `f (balancedUnit (v(N)+t)) < 0` into
    `f (phiAugCont G (Pi.single ⊤ 1)) + t * f (Pi.single none 1) < 0`; combined with the
    nonnegativity on the generator, `t * f (Pi.single none 1) < 0`, hence the sign (t > 0). -/
lemma separatingFunctional_none_neg (G : TUGame N) {t : ℝ} (ht : 0 < t)
    (f : ((Option N) → ℝ) →L[ℝ] ℝ)
    (hfCone : ∀ y ∈ augCone G, 0 ≤ f y)
    (hfSep : f (balancedUnit (G.v Finset.univ + t)) < 0) :
    f (Pi.single none 1) < 0 := by
  -- 0 ≤ f on the grand-coalition generator.
  have huniv : 0 ≤ f (phiAugCont G (Pi.single Finset.univ 1)) :=
    (augCone_dual_iff G f).mp hfCone Finset.univ
  -- Coordinate value `phiAugCont G (Pi.single ⊤ 1) (some i) = 1` (incidence of ⊤).
  have hGenSome (i : N) :
      (phiAugCont G (Pi.single Finset.univ 1)) (some i) = (1 : ℝ) := by
    show ∑ S ∈ Finset.univ.filter (fun S => i ∈ S),
        (Pi.single Finset.univ 1 : Finset N → ℝ) S = 1
    exact Finset.sum_eq_single Finset.univ
      (fun b _ hb => by rw [Pi.single_apply, if_neg hb])
      (fun h => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h)
  -- Coordinate value `phiAugCont G (Pi.single ⊤ 1) none = v(N)`.
  have hGenNone :
      (phiAugCont G (Pi.single Finset.univ 1)) none = G.v Finset.univ := by
    have hsum : ∑ S : Finset N,
        (Pi.single Finset.univ 1 : Finset N → ℝ) S * G.v S
        = (Pi.single Finset.univ 1 : Finset N → ℝ) Finset.univ * G.v Finset.univ :=
      Finset.sum_eq_single Finset.univ
        (fun b _ hb => by rw [Pi.single_apply, if_neg hb]; ring)
        (fun h => by simp only [Finset.mem_univ] at h)
    show ∑ S : Finset N, (Pi.single Finset.univ 1 : Finset N → ℝ) S * G.v S = G.v Finset.univ
    rw [hsum, Pi.single_apply, if_pos rfl, one_mul]
  -- Identity: balancedUnit (v(N)+t) = grand-coal generator + t • none-basis.
  have hId : balancedUnit (G.v Finset.univ + t) =
      phiAugCont G (Pi.single Finset.univ 1) + t • Pi.single none 1 := by
    funext j
    rcases j with i | _
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, balancedUnit]
      rw [hGenSome, if_neg (fun h => Option.noConfusion h)]
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, balancedUnit]
      rw [hGenNone, if_pos rfl]
      ring
  -- Linearity + linarith.
  rw [hId, map_add, map_smul, smul_eq_mul] at hfSep
  linarith

end BondarevaFarkas
