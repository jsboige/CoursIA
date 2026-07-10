import Mathlib

/-!
# Cone-closed kernel for Bondareva-Farkas (TUGame-free)

This module is the self-contained, importable kernel of the Bondareva-Shapley
backward proof via the Farkas / hyperplane-separation route. It is deliberately
*TUGame-free*: the augmented-cone machinery is parameterized over a bare
characteristic function `v : Finset N → ℝ`, with no dependency on
`CooperativeGames.Basic` (`TUGame`). This breaks the import cycle that kept the
machinery confined to scratch (`FarkasScratch.lean` imports `Basic` for `TUGame`,
so `Basic` could not import it back), and lets `Basic.lean` import this module
to wire the witness decoding into `bondareva_shapley_backward`.

Contents:
- `conicHull_linearIndependent_isClosed`, `mem_cone_iff_exists_li_subset`,
  `finGenCone_isClosed`: a finitely-generated conic hull in a finite-dimensional
  normed space is closed (simplicial brick + conic-Carathéodory + finite union).
- `phiAugLinear` / `phiAugCont` / `augCone`: the augmented-incidence map and its
  image cone, parameterized over `v`.
- `balancedUnit`: the test point (`1` on `some i`, `t` on `none`).
- `augCone_mem_iff`: membership reduces to `∃ w ≥ 0, phiAugCont v w = y`
  (the cone-closed kernel).
- `augCone_dual_iff`: a continuous linear functional is nonneg on the cone iff
  nonneg on each of the finitely many generators.
- `separatingFunctional_none_neg`: a separating functional satisfies
  `f (Pi.single none 1) < 0` (the decoding sign condition).

All theorems proven, 0 `sorry`. See `docs/BONDAREVA_FARKAS_PLAN.md` for the
overall strategy and issue `#2959` for the epic.
-/

open scoped BigOperators
open Set LinearMap Pointwise

/-!
  Cone-closed kernel for Bondareva-Farkas (TUGame-free) — EN sibling
  ==============================================================
  English mirror of `CooperativeGames/ConeKernel.lean` (FR-first canonical).
  Convention i18n Lean ratifiée par ai-01 (2026-07-04, #4980 comment-4881909354) :
  fichiers `.lean` distincts FR + EN siblings dans le même lake, les deux compilent.
  Drift-CI detectable : contenu non-docstring byte-identique entre siblings.
  Namespace sibling : `BondarevaCone_en` (le FR canonique reste `BondarevaCone`).
  Pas une traduction destructive : le fichier source EN historique est préservé ici
  verbatim depuis `914817a1e` (pre-canonicalisation FR ConeKernel tranche 2) ; seule la
  ligne `namespace` diffère pour éviter la collision de declaration top-level.
  See #4980. Part of #4208 (axe E).
-/

namespace BondarevaCone_en

variable {N : Type*} [Fintype N] [DecidableEq N]

/-! ## Augmented incidence map and cone (parameterized over `v`) -/

/-- The augmented incidence map over a characteristic function `v`.
    `some i` carries the coalition-incidence sums `∑_{S ∋ i} w S`;
    `none` carries the value functional `∑ S, w S * v S`. -/
noncomputable def phiAugLinear (v : Finset N → ℝ) : (Finset N → ℝ) →ₗ[ℝ] ((Option N) → ℝ) where
  toFun w := fun j => match j with
    | some i => ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), w S
    | none   => ∑ S : Finset N, w S * v S
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
    · -- none: ∑ r*(w S*v S) = r * ∑ w S*v S — `Finset.mul_sum` (factor LEFT)
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum]
    · -- some i: ∑_{S∋i} r*w S = r * ∑_{S∋i} w S — `Finset.mul_sum`
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

/-- Finite-dim auto-continuity. -/
noncomputable def phiAugCont (v : Finset N → ℝ) : (Finset N → ℝ) →L[ℝ] ((Option N) → ℝ) :=
  LinearMap.toContinuousLinearMap (phiAugLinear v)

/-- The image of the positive cone under the augmented incidence map. -/
noncomputable def augCone (v : Finset N → ℝ) : ProperCone ℝ ((Option N) → ℝ) :=
  (ProperCone.positive ℝ (Finset N → ℝ)).map (phiAugCont v)

/-- `hyperplane_separation_point` (Mathlib `Analysis.Convex.Cone.Dual`:132) applies
    directly on `augCone v`. Given any point outside `augCone v`, we get a separating
    functional `f : StrongDual ℝ ((Option N) → ℝ)` with `0 ≤ f` on `augCone v` and
    `f x₀ < 0`. This is the Farkas lemma invoked by the witness decoding. -/
example (v : Finset N → ℝ) (x₀ : (Option N) → ℝ) (h : x₀ ∉ augCone v) :
    ∃ f : StrongDual ℝ ((Option N) → ℝ),
      (∀ x ∈ augCone v, 0 ≤ f x) ∧ f x₀ < 0 :=
  ProperCone.hyperplane_separation_point (augCone v) h

/-! ## Simplicial brick (1st of the cone-closed kernel)

The conic hull of finitely many linearly independent vectors in a finite-dimensional
normed space is closed. This is the building block for the cone-closed kernel: the
general (finitely-generated, possibly dependent) cone is a finite union
(Carathéodory) of such simplicial cones, each closed here. -/

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

/-! ## Conic-Carathéodory (brick 2) + finite union (brick 3)

A finitely-generated cone `K = {∑ cᵢ vᵢ | cᵢ ≥ 0}` in a finite-dim normed space is
closed. Forward (`K ⊆ ⋃ LI-subcones`) = conic-Carathéodory: among finsets carrying a
non-negative witness of `y`, one of minimal cardinality must be linearly independent
(a dependency relation would let a coefficient be zeroed by sliding along it,
contradicting minimality). Reverse is trivial (zero extension). Each LI subcone is
closed (brick 1); finite union of closed sets is closed. -/

/-- **Brick 2 — conic-Carathéodory (independent form), the isolated core.**
    Every point of a finitely-generated cone lies in the simplicial cone of some
    linearly-independent sub-family. Proved by well-founded induction on the
    cardinality of the carrying finset (minimal-cardinality ⟹ full support). -/
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
  -- Strong induction on the cardinality of the carrying finset.
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
        have hssub : ∑ i ∈ s, c i • v i = ∑ i ∈ Finset.univ, c i • v i :=
          Finset.sum_subset (Finset.subset_univ s)
            (fun i _ hi => by rw [hcsupp i hi, zero_smul])
        exact hssub.symm.trans (Finset.sum_coe_sort s (fun i => c i • v i)).symm
      by_cases hli : LinearIndependent ℝ (fun i : ↥s => v i)
      · exact ⟨s, hli, (fun i : ↥s => c i.val), fun i => hc i.val, hsum.trans htrans⟩
      · obtain ⟨g, hgsum, hg_ne⟩ := Fintype.not_linearIndependent_iff.mp hli
        -- Sign-normalize g to a with ∑ a•v = 0 and ∃ i, 0 < a i.
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
        -- pos = {i : a i > 0}, nonempty; t = argmin of c i.val / a i over pos.
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
        -- argmin-attaining index j ∈ pos with c j.val / a j = t.
        obtain ⟨j, hj_pos, hj_eq⟩ :=
          Finset.mem_image.mp ((pos.image (fun i => c i.val / a i)).min'_mem himg_ne)
        have hja : 0 < a j := (Finset.mem_filter.mp hj_pos).2
        have hjv_mem : (j : ι) ∈ s := Subtype.prop j
        have htja : t * a j = c j.val := by
          rw [ht_def, ← hj_eq]
          exact div_mul_cancel₀ (c j.val) hja.ne'
        -- d = slid witness; zero off s, zero at j.val (argmin).
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

/-- **Brick 3.** A finitely-generated conic hull is closed. -/
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

With the cone-closed bricks proven, `augCone v` (a `ProperCone` = `ClosedSubmodule.map
phiAugCont positive`, i.e. the *closure* of the image) equals the plain image: the image
is a finitely-generated cone (standard-basis generators `gen S = phiAugCont v (Pi.single S 1)`),
hence closed by `finGenCone_isClosed`, so `closure(image) = image`. Membership reduces to
`∃ w ≥ 0, phiAugCont v w = y`. -/

theorem augCone_mem_iff (v : Finset N → ℝ) (y : (Option N) → ℝ) :
    y ∈ augCone v ↔ ∃ w : Finset N → ℝ, (∀ S, 0 ≤ w S) ∧ phiAugCont v w = y := by
  -- Standard-basis generators: gen S = phiAugCont v (e_S), where e_S = Pi.single S 1.
  let gen (S : Finset N) : (Option N) → ℝ := phiAugCont v (Pi.single S 1)
  -- Linearity-in-standard-basis: phiAugCont v w = Σ S, w S • gen S.
  have hphi_sum (w : Finset N → ℝ) : phiAugCont v w = ∑ S, w S • gen S := by
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
  set image : Set ((Option N) → ℝ) :=
      {y | ∃ c : Finset N → ℝ, (∀ S, 0 ≤ c S) ∧ y = ∑ S, c S • gen S} with himage_def
  have hImgClosed : IsClosed image := finGenCone_isClosed gen
  have hImg_eq : image = {y | ∃ w : Finset N → ℝ, (∀ S, 0 ≤ w S) ∧ phiAugCont v w = y} := by
    ext y
    constructor
    · rintro ⟨c, hc, hy⟩; exact ⟨c, hc, by rw [hphi_sum c]; exact hy.symm⟩
    · rintro ⟨w, hw, hy⟩; exact ⟨w, hw, by rw [← hphi_sum w]; exact hy.symm⟩
  have hmapImg : ((ProperCone.positive ℝ (Finset N → ℝ)).toPointedCone.map
      (phiAugCont v : (Finset N → ℝ) →ₗ[ℝ] ((Option N) → ℝ)) : Set _) =
      {y | ∃ w : Finset N → ℝ, (∀ S, 0 ≤ w S) ∧ phiAugCont v w = y} := by
    ext y
    simp only [SetLike.mem_coe, PointedCone.mem_map, ProperCone.mem_toPointedCone,
      ProperCone.mem_positive]
    constructor
    · rintro ⟨w, hw, hy⟩; exact ⟨w, hw, hy⟩
    · rintro ⟨w, hw, hy⟩; exact ⟨w, hw, hy⟩
  have hRhsClosed : IsClosed
      {y | ∃ w : Finset N → ℝ, (∀ S, 0 ≤ w S) ∧ phiAugCont v w = y} := by
    rw [← hImg_eq]; exact hImgClosed
  constructor
  · -- (→) y ∈ augCone v ≡ y ∈ closure(image) → y ∈ image (image is closed)
    intro hy
    have hy0 : y ∈ closure
        {y | ∃ w : Finset N → ℝ, (∀ S, 0 ≤ w S) ∧ phiAugCont v w = y} := by
      have key : y ∈ closure
          ((ProperCone.positive ℝ (Finset N → ℝ)).toPointedCone.map
            (phiAugCont v : (Finset N → ℝ) →ₗ[ℝ] ((Option N) → ℝ)) : Set _) := by
        have := hy
        simp only [augCone, ProperCone.mem_map, PointedCone.mem_closure] at this
        exact this
      rw [hmapImg] at key
      exact key
    rw [hRhsClosed.closure_eq] at hy0
    exact hy0
  · -- (←) phiAugCont v w ∈ augCone v (image ⊆ closure = augCone)
    rintro ⟨w, hw, rfl⟩
    have h_in_image : (phiAugCont v w) ∈
        ((ProperCone.positive ℝ (Finset N → ℝ)).toPointedCone.map
          (phiAugCont v : (Finset N → ℝ) →ₗ[ℝ] ((Option N) → ℝ)) : Set _) := by
      rw [hmapImg]; exact ⟨w, hw, rfl⟩
    have h_in_closure : (phiAugCont v w) ∈ closure
        ((ProperCone.positive ℝ (Finset N → ℝ)).toPointedCone.map
          (phiAugCont v : (Finset N → ℝ) →ₗ[ℝ] ((Option N) → ℝ)) : Set _) :=
      subset_closure h_in_image
    have this : (phiAugCont v w) ∈ augCone v := by
      simp only [augCone, ProperCone.mem_map, PointedCone.mem_closure]
      exact h_in_closure
    exact this

/-! ## Balanced-unit test point and dual characterization -/

/-- The "balanced-unit" point: `1` in every `some i` coordinate, `t` in the `none`
    (value) coordinate. -/
def balancedUnit (t : ℝ) : (Option N) → ℝ := fun j => match j with
  | some _ => 1
  | none   => t

/-- **Dual characterization of `augCone`**: a continuous linear functional `f` is
    nonnegative on `augCone v` iff it is nonnegative on each of the finitely many
    generators `phiAugCont v (Pi.single S 1)`. The (⟸) direction is load-bearing for
    the witness decoding: it translates a separating functional `f` into coalitional
    rationality of the candidate witness `x`. -/
lemma augCone_dual_iff (v : Finset N → ℝ) (f : ((Option N) → ℝ) →L[ℝ] ℝ) :
    (∀ y ∈ augCone v, 0 ≤ f y) ↔
      ∀ S : Finset N, 0 ≤ f (phiAugCont v (Pi.single S 1)) := by
  refine ⟨fun hC S => hC _ ?_, ?_⟩
  · -- each generator `phiAugCont v (Pi.single S 1)` is in `augCone v` (weight ≥ 0)
    rw [augCone_mem_iff]
    refine ⟨Pi.single S 1, fun S' => ?_, rfl⟩
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  · rintro hgen y hy
    obtain ⟨w, hw, hyw⟩ := (augCone_mem_iff v y).mp hy
    rw [← hyw]
    -- phiAugCont v w = Σ S, w S • phiAugCont v (Pi.single S 1) by linearity + standard basis.
    have hphi_sum : phiAugCont v w =
        ∑ S : Finset N, w S • phiAugCont v (Pi.single S 1) := by
      have hw_basis : w = ∑ S, w S • Pi.single S 1 := by
        funext S₀
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
          mul_boole, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      conv_lhs => rw [hw_basis]
      simp only [map_sum, map_smul]
    rw [hphi_sum]
    simp only [map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_nonneg (fun S _ => mul_nonneg (hw S) (hgen S))

/-! ## Witness decoding — sign condition

The separating functional `f` from `hyperplane_separation_point` (applied to a point
`balancedUnit (v(N)+t) ∉ augCone v`) must be decoded into the Core witness
`x : N → ℝ`. The natural candidate is `x i := f (Pi.single (some i) 1) / (-f (Pi.single none 1))`,
well-defined once we know `f (Pi.single none 1) < 0`. This sign is the first
load-bearing decoding step. -/

/-- **Decoding sign condition** — the separating functional `f` satisfies
    `f (Pi.single none 1) < 0`. Proof: `0 ≤ f` on the grand-coalition generator
    `phiAugCont v (Pi.single ⊤ 1)` (it is in `augCone v`, via `augCone_dual_iff`); the
    identity `balancedUnit (v(N)+t) = phiAugCont v (Pi.single ⊤ 1) + t • Pi.single none 1`
    plus linearity turns `f (balancedUnit (v(N)+t)) < 0` into
    `f (phiAugCont v (Pi.single ⊤ 1)) + t * f (Pi.single none 1) < 0`; combined with the
    nonnegativity on the generator, `t * f (Pi.single none 1) < 0`, hence the sign (t > 0). -/
lemma separatingFunctional_none_neg (v : Finset N → ℝ) {t : ℝ} (ht : 0 < t)
    (f : ((Option N) → ℝ) →L[ℝ] ℝ)
    (hfCone : ∀ y ∈ augCone v, 0 ≤ f y)
    (hfSep : f (balancedUnit (v Finset.univ + t)) < 0) :
    f (Pi.single none 1) < 0 := by
  -- 0 ≤ f on the grand-coalition generator.
  have huniv : 0 ≤ f (phiAugCont v (Pi.single Finset.univ 1)) :=
    (augCone_dual_iff v f).mp hfCone Finset.univ
  -- Coordinate value `phiAugCont v (Pi.single ⊤ 1) (some i) = 1` (incidence of ⊤).
  have hGenSome (i : N) :
      (phiAugCont v (Pi.single Finset.univ 1)) (some i) = (1 : ℝ) := by
    show ∑ S ∈ Finset.univ.filter (fun S => i ∈ S),
        (Pi.single Finset.univ 1 : Finset N → ℝ) S = 1
    -- `rw` (not `exact`) determines the implicit `{s, f}` from the LHS occurrence,
    -- sidestepping the `(Pi.single ⊤ 1) ⊤ ≟ 1` ite-reduction defeq that `exact` demands.
    rw [Finset.sum_eq_single Finset.univ
        (fun b _ hb => by rw [Pi.single_apply, if_neg hb])
        (fun h => by simp at h), Pi.single_eq_same]
  -- Coordinate value `phiAugCont v (Pi.single ⊤ 1) none = v(N)`.
  have hGenNone :
      (phiAugCont v (Pi.single Finset.univ 1)) none = v Finset.univ := by
    have hsum : ∑ S : Finset N,
        (Pi.single Finset.univ 1 : Finset N → ℝ) S * v S
        = (Pi.single Finset.univ 1 : Finset N → ℝ) Finset.univ * v Finset.univ :=
      Finset.sum_eq_single Finset.univ
        (fun b _ hb => by rw [Pi.single_apply, if_neg hb]; ring)
        (fun h => by simp at h)
    show ∑ S : Finset N, (Pi.single Finset.univ 1 : Finset N → ℝ) S * v S = v Finset.univ
    rw [hsum, Pi.single_apply, if_pos rfl, one_mul]
  -- Identity: balancedUnit (v(N)+t) = grand-coal generator + t • none-basis.
  have hId : balancedUnit (v Finset.univ + t) =
      phiAugCont v (Pi.single Finset.univ 1) + t • Pi.single none 1 := by
    funext j
    -- `Option` constructors are `none` then `some`; use explicit `cases` to pin
    -- each arm to its tactic (a positional `rcases ... with i | _` swapped them).
    cases j with
    | none =>
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, balancedUnit]
      rw [hGenNone, Pi.single_eq_same]
      ring
    | some i =>
      have hne : (some i : Option N) ≠ none := Option.some_ne_none i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, balancedUnit]
      rw [hGenSome, Pi.single_apply, if_neg hne]
      ring
  -- Linearity on the separating inequality, then sign (t > 0). `nlinarith` because
  -- the goal `f (Pi.single none 1) < 0` needs dividing `t * f (...) < 0` by `t`.
  rw [hId, map_add, map_smul, smul_eq_mul] at hfSep
  nlinarith [ht, huniv]

end BondarevaCone_en
