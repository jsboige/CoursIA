import Mathlib

/-!
# Noyau cône-fermé pour Bondareva-Farkas (indépendant de TUGame)

Ce module est le noyau autonome et importable de la preuve arrière de
Bondareva-Shapley par la route Farkas / séparation par hyperplan. Il est
délibérément *indépendant de TUGame* : la machinerie du cône augmenté est
paramétrée par une fonction caractéristique nue `v : Finset N → ℝ`, sans
dépendance sur `CooperativeGames.Basic` (`TUGame`). Cela rompt le cycle
d'imports qui confinait la machinerie à un brouillon (`FarkasScratch.lean`
importe `Basic` pour `TUGame`, donc `Basic` ne pouvait pas l'importer en
retour), et permet à `Basic.lean` d'importer ce module pour câbler le
décodage du témoin dans `bondareva_shapley_backward`.

Sommaire :
- `conicHull_linearIndependent_isClosed`, `mem_cone_iff_exists_li_subset`,
  `finGenCone_isClosed` : l'enveloppe conique d'un ensemble fini de vecteurs
  linéairement indépendants dans un espace normé de dimension finie est
  fermée (brique simpliciale + Carathéodory conique + union finie).
- `phiAugLinear` / `phiAugCont` / `augCone` : l'application d'incidence
  augmentée et son cône image, paramétrés par `v`.
- `balancedUnit` : le point-test (`1` sur `some i`, `t` sur `none`).
- `augCone_mem_iff` : l'appartenance se réduit à `∃ w ≥ 0, phiAugCont v w = y`
  (le noyau cône-fermé).
- `augCone_dual_iff` : une fonctionnelle linéaire continue est non-négative
  sur le cône ssi elle est non-négative sur chacun des générateurs en nombre
  fini.
- `separatingFunctional_none_neg` : une fonctionnelle de séparation vérifie
  `f (Pi.single none 1) < 0` (la condition de signe du décodage).

Tous les théorèmes sont prouvés, 0 `sorry`. Voir `docs/BONDAREVA_FARKAS_PLAN.md`
pour la stratégie globale et l'issue `#2959` pour l'épopée.
-/

open scoped BigOperators
open Set LinearMap Pointwise

namespace BondarevaCone

variable {N : Type*} [Fintype N] [DecidableEq N]

/-! ## Application d'incidence augmentée et cône (paramétrés par `v`) -/

/-- L'application d'incidence augmentée sur une fonction caractéristique `v`.
    `some i` porte les sommes d'incidence de coalition `∑_{S ∋ i} w S` ;
    `none` porte la fonctionnelle de valeur `∑ S, w S * v S`. -/
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
    · -- none : ∑ r*(w S*v S) = r * ∑ w S*v S — `Finset.mul_sum` (facteur à GAUCHE)
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum]
    · -- some i : ∑_{S∋i} r*w S = r * ∑_{S∋i} w S — `Finset.mul_sum`
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

/-- Continuité automatique en dimension finie. -/
noncomputable def phiAugCont (v : Finset N → ℝ) : (Finset N → ℝ) →L[ℝ] ((Option N) → ℝ) :=
  LinearMap.toContinuousLinearMap (phiAugLinear v)

/-- L'image du cône positif sous l'application d'incidence augmentée. -/
noncomputable def augCone (v : Finset N → ℝ) : ProperCone ℝ ((Option N) → ℝ) :=
  (ProperCone.positive ℝ (Finset N → ℝ)).map (phiAugCont v)

/-- `hyperplane_separation_point` (Mathlib `Analysis.Convex.Cone.Dual` :132) s'applique
    directement à `augCone v`. Étant donné un point hors de `augCone v`, on obtient
    une fonctionnelle de séparation `f : StrongDual ℝ ((Option N) → ℝ)` avec
    `0 ≤ f` sur `augCone v` et `f x₀ < 0`. C'est le lemme de Farkas invoqué par le
    décodage du témoin. -/
example (v : Finset N → ℝ) (x₀ : (Option N) → ℝ) (h : x₀ ∉ augCone v) :
    ∃ f : StrongDual ℝ ((Option N) → ℝ),
      (∀ x ∈ augCone v, 0 ≤ f x) ∧ f x₀ < 0 :=
  ProperCone.hyperplane_separation_point (augCone v) h

/-! ## Brique simpliciale (1re du noyau cône-fermé)

L'enveloppe conique d'un ensemble fini de vecteurs linéairement indépendants dans
un espace normé de dimension finie est fermée. C'est la brique élémentaire du
noyau cône-fermé : le cône général (engendré par un ensemble fini, éventuellement
dépendant) est une union finie (Carathéodory) de tels cônes simpliciaux, tous
fermés. -/

theorem conicHull_linearIndependent_isClosed
    {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (v : ι → F) (hli : LinearIndependent ℝ v) :
    IsClosed {y : F | ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ y = ∑ i, c i • v i} := by
  -- ψ : (ι → ℝ) →ₗ[ℝ] F est l'application de combinaison linéaire dominante ; LI donne l'injectivité.
  set ψ : (ι → ℝ) →ₗ[ℝ] F := Fintype.linearCombination ℝ v with hψ_def
  have hψ_inj : Function.Injective ψ :=
    LinearIndependent.fintypeLinearCombination_injective hli
  have hψ_app : ∀ c, ψ c = ∑ i, c i • v i := fun c => Fintype.linearCombination_apply ℝ v c
  -- ψ.range est fermé (sous-module de dimension finie).
  have hRangeClosed : IsClosed (ψ.range : Set F) := ψ.range.closed_of_finiteDimensional
  -- ψ est un équiv linéaire sur son image, puis un équiv linéaire continu (dim finie).
  set eLE : (ι → ℝ) ≃ₗ[ℝ] ψ.range := LinearEquiv.ofInjective ψ hψ_inj
  set eCLE : (ι → ℝ) ≃L[ℝ] ψ.range := eLE.toContinuousLinearEquiv
  -- identité-clé : l'image de l'enveloppe conique égale l'image de l'orthant, poussée dans F.
  have hkey : ∀ c, (ψ.range.subtype : ψ.range → F) (eCLE c) = ∑ i, c i • v i := by
    intro c
    show (ψ.range.subtype : ψ.range → F) (eLE.toContinuousLinearEquiv c) = ∑ i, c i • v i
    simp only [Submodule.subtype_apply, LinearEquiv.coe_toContinuousLinearEquiv']
    rw [LinearEquiv.ofInjective_apply, hψ_app]
  -- l'orthant positif est fermé (intersection finie de demi-espaces fermés).
  have hOrthant : IsClosed ({c : ι → ℝ | ∀ i, 0 ≤ c i} : Set (ι → ℝ)) := by
    rw [← Set.iInter_setOf]
    exact isClosed_iInter fun i => IsClosed.preimage (continuous_apply i) isClosed_Ici
  -- l'image de l'orthant fermé sous l'équiv linéaire continu est fermée dans ψ.range.
  have hImg : IsClosed ((eCLE : (ι → ℝ) → ψ.range) '' {c | ∀ i, 0 ≤ c i}) :=
    eCLE.isClosed_image.mpr hOrthant
  -- l'inclusion (ψ.range) ↪ F est une application fermée (l'image est fermée).
  have hCM : IsClosedMap (ψ.range.subtype : ψ.range → F) :=
    hRangeClosed.isClosedEmbedding_subtypeVal.isClosedMap
  -- l'ensemble enveloppe conique = inclusion '' (eCLE '' orthant).
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

/-! ## Carathéodory conique (brique 2) + union finie (brique 3)

Un cône `K = {∑ cᵢ vᵢ | cᵢ ≥ 0}` engendré par un ensemble fini dans un espace
normé de dimension finie est fermé. Le sens direct (`K ⊆ ⋃ sous-cônes-LI`) est
le Carathéodory conique : parmi les ensembles finis qui portent un témoin
non-négatif de `y`, un de cardinalité minimale doit être linéairement
indépendant (une relation de dépendance permettrait d'annuler un coefficient en
glissant le long de celle-ci, contredisant la minimalité). La réciproque est
triviale (extension par zéro). Chaque sous-cône-LI est fermé (brique 1) ;
l'union finie d'ensembles fermés est fermée. -/

/-- **Brique 2 — Carathéodory conique (forme indépendante), le noyau isolé.**
    Tout point d'un cône engendré par un ensemble fini appartient au cône
    simplicial d'une sous-famille linéairement indépendante. Démontré par
    induction bien fondée sur la cardinalité de l'ensemble fini porteur
    (cardinalité minimale ⟹ support plein). -/
theorem mem_cone_iff_exists_li_subset
    {ι F : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (v : ι → F) (y : F)
    (hy : ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ y = ∑ i, c i • v i) :
    ∃ (I : Finset ι), LinearIndependent ℝ (fun i : ↥I => v i) ∧
      ∃ c : ↥I → ℝ, (∀ i, 0 ≤ c i) ∧ y = ∑ i, c i • v i := by
  -- Un ensemble fini `s` est *bon* s'il porte un témoin non-négatif `c` avec support ⊆ s sommant à y.
  let good : Finset ι → Prop := fun s =>
    ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ (∀ i ∉ s, c i = 0) ∧ y = ∑ i, c i • v i
  have hgood_univ : good Finset.univ := by
    obtain ⟨c, hc, hsum⟩ := hy
    exact ⟨c, hc, fun i hi => (hi (Finset.mem_univ i)).elim, hsum⟩
  -- Induction forte sur la cardinalité de l'ensemble fini porteur.
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
      -- s.erase i est bon (le terme-i est maintenant nul) et strictement plus petit ⟹ IH.
      have hcard : (s.erase i).card < s.card := Finset.card_erase_lt_of_mem his
      refine IH (s.erase i) hcard ⟨c, hc, ?_, hsum⟩
      intro j hj
      by_cases hjeq : j = i
      · rw [hjeq]; exact hci
      by_cases hjs : j ∈ s
      · exact absurd (Finset.mem_erase.mpr ⟨hjeq, hjs⟩) hj
      · exact hcsupp j hjs
    case pos hfull =>
      -- c est strictement positif sur s.
      have hcpos : ∀ i : ↥s, 0 < c i.val := fun i =>
        lt_of_le_of_ne (hc i.val) (Ne.symm (hfull i.val i.prop))
      -- transport de la somme vers le porteur du sous-type.
      have htrans : ∑ i : ι, c i • v i = ∑ i : ↥s, c i.val • v i.val := by
        have hssub : ∑ i ∈ s, c i • v i = ∑ i ∈ Finset.univ, c i • v i :=
          Finset.sum_subset (Finset.subset_univ s)
            (fun i _ hi => by rw [hcsupp i hi, zero_smul])
        exact hssub.symm.trans (Finset.sum_coe_sort s (fun i => c i • v i)).symm
      by_cases hli : LinearIndependent ℝ (fun i : ↥s => v i)
      · exact ⟨s, hli, (fun i : ↥s => c i.val), fun i => hc i.val, hsum.trans htrans⟩
      · obtain ⟨g, hgsum, hg_ne⟩ := Fintype.not_linearIndependent_iff.mp hli
        -- Normalisation en signe de g en a avec ∑ a•v = 0 et ∃ i, 0 < a i.
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
        -- pos = {i : a i > 0}, non vide ; t = argmin de c i.val / a i sur pos.
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
        -- indice j ∈ pos qui réalise l'argmin avec c j.val / a j = t.
        obtain ⟨j, hj_pos, hj_eq⟩ :=
          Finset.mem_image.mp ((pos.image (fun i => c i.val / a i)).min'_mem himg_ne)
        have hja : 0 < a j := (Finset.mem_filter.mp hj_pos).2
        have hjv_mem : (j : ι) ∈ s := Subtype.prop j
        have htja : t * a j = c j.val := by
          rw [ht_def, ← hj_eq]
          exact div_mul_cancel₀ (c j.val) hja.ne'
        -- d = témoin glissé ; nul hors de s, nul en j.val (argmin).
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

/-- **Brique 3.** Une enveloppe conique engendrée par un ensemble fini est fermée. -/
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

/-! ## Le pont dimension-finie `augCone_mem_iff`

Les briques cône-fermé établies, `augCone v` (un `ProperCone` = `ClosedSubmodule.map
phiAugCont positive`, c-à-d l'*adhérence* de l'image) coïncide avec l'image brute :
l'image est un cône engendré par un ensemble fini (générateurs de la base standard
`gen S = phiAugCont v (Pi.single S 1)`), donc fermé par `finGenCone_isClosed`, donc
`adhérence(image) = image`. L'appartenance se réduit à `∃ w ≥ 0, phiAugCont v w = y`. -/

theorem augCone_mem_iff (v : Finset N → ℝ) (y : (Option N) → ℝ) :
    y ∈ augCone v ↔ ∃ w : Finset N → ℝ, (∀ S, 0 ≤ w S) ∧ phiAugCont v w = y := by
  -- Générateurs de la base standard : gen S = phiAugCont v (e_S), avec e_S = Pi.single S 1.
  let gen (S : Finset N) : (Option N) → ℝ := phiAugCont v (Pi.single S 1)
  -- Linéarité dans la base standard : phiAugCont v w = Σ S, w S • gen S.
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
  · -- (→) y ∈ augCone v ≡ y ∈ adhérence(image) → y ∈ image (image est fermée)
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
  · -- (←) phiAugCont v w ∈ augCone v (image ⊆ adhérence = augCone)
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

/-! ## Point-test balanced-unit et caractérisation duale -/

/-- Le point « balanced-unit » : `1` dans chaque coordonnée `some i`, `t` dans la
    coordonnée `none` (de valeur). -/
def balancedUnit (t : ℝ) : (Option N) → ℝ := fun j => match j with
  | some _ => 1
  | none   => t

/-- **Caractérisation duale de `augCone`** : une fonctionnelle linéaire continue
    `f` est non-négative sur `augCone v` ssi elle est non-négative sur chacun des
    générateurs en nombre fini `phiAugCont v (Pi.single S 1)`. Le sens (⟸) est
    porteur pour le décodage du témoin : il traduit une fonctionnelle de séparation
    `f` en rationalité coalitionnelle du témoin candidat `x`. -/
lemma augCone_dual_iff (v : Finset N → ℝ) (f : ((Option N) → ℝ) →L[ℝ] ℝ) :
    (∀ y ∈ augCone v, 0 ≤ f y) ↔
      ∀ S : Finset N, 0 ≤ f (phiAugCont v (Pi.single S 1)) := by
  refine ⟨fun hC S => hC _ ?_, ?_⟩
  · -- chaque générateur `phiAugCont v (Pi.single S 1)` est dans `augCone v` (poids ≥ 0)
    rw [augCone_mem_iff]
    refine ⟨Pi.single S 1, fun S' => ?_, rfl⟩
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  · rintro hgen y hy
    obtain ⟨w, hw, hyw⟩ := (augCone_mem_iff v y).mp hy
    rw [← hyw]
    -- phiAugCont v w = Σ S, w S • phiAugCont v (Pi.single S 1) par linéarité + base standard.
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

/-! ## Valeurs en coordonnées du générateur (prérequis du décodage du témoin)

Le générateur de la base standard `phiAugCont v (Pi.single S 1)` est l'objet
porteur du décodage du témoin : `augCone_dual_iff` lit une fonctionnelle de
séparation `f` sur sa valeur en ces générateurs. Ses coordonnées valent `1`
en `some i` exactement quand `i ∈ S` (incidence de coalition) et `v S` en
`none` (valeur de coalition). Ces deux faits généralisent le cas particulier
de la grande coalition utilisé dans `separatingFunctional_none_neg` à une
coalition arbitraire `S` ; ils sont le prérequis du lemme de décodage du témoin
`exists_preimputation_strict` (séparateur `f` ⟹ pré-imputation
`x i := f (base-some i) / (-f (base-none))`). -/

/-- Coordonnée `some i` du générateur-`S` : l'indicateur d'incidence `1` si
    `i ∈ S`, sinon `0`. Généralise le cas particulier de la grande coalition
    à n'importe quel `S`. -/
lemma gen_apply_some (v : Finset N → ℝ) (S : Finset N) (i : N) :
    (phiAugCont v (Pi.single S 1)) (some i) = if i ∈ S then (1 : ℝ) else 0 := by
  -- defeq : `(phiAugCont v (Pi.single S 1)) (some i)` se réduit à la branche `some`,
  -- somme d'incidence filtrée (précédent defeq cycle 18).
  show ∑ T ∈ Finset.univ.filter (fun T => i ∈ T),
      (Pi.single S 1 : Finset N → ℝ) T = if i ∈ S then 1 else 0
  by_cases hs : i ∈ S
  · -- `i ∈ S` : le terme unique `T = S` (qui est dans le filtre) contribue `1`.
    simp only [hs, if_true]
    rw [Finset.sum_eq_single S
        (fun T _ hT => by rw [Pi.single_apply, if_neg hT])
        (fun h => (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)).elim),
        Pi.single_eq_same]
  · -- `i ∉ S` : `S` n'est pas dans le filtre, et tout `T` du filtre vérifie `T ≠ S`,
    -- donc `(Pi.single S 1) T = 0` ; la somme s'annule.
    simp only [hs, if_false]
    rw [Finset.sum_eq_zero]
    intro T hT
    have hiT : i ∈ T := (Finset.mem_filter.mp hT).2
    -- `T ≠ S` : si `T = S`, alors `i ∈ T` donnerait `i ∈ S`, contredisant `hs`.
    -- (Pin `hTS : T = S` via `intro` pour que `▸` voie son type — la forme lambda
    -- anonyme laisse le lieur en metavar à l'élaboration de `▸`.)
    have hTneS : T ≠ S := by intro hTS; exact hs (hTS ▸ hiT)
    rw [Pi.single_apply, if_neg hTneS]

/-- Coordonnée `none` du générateur-`S` : la valeur de coalition `v S`.
    Généralise le cas particulier de la grande coalition à n'importe quel `S`. -/
lemma gen_apply_none (v : Finset N → ℝ) (S : Finset N) :
    (phiAugCont v (Pi.single S 1)) none = v S := by
  -- defeq : la branche `none` est `∑ T, w T * v T` avec `w = Pi.single S 1`.
  have hsum : ∑ T : Finset N, (Pi.single S 1 : Finset N → ℝ) T * v T =
      (Pi.single S 1 : Finset N → ℝ) S * v S :=
    Finset.sum_eq_single S
      (fun T _ hT => by rw [Pi.single_apply, if_neg hT]; ring)
      (fun h => by simp at h)
  show ∑ T : Finset N, (Pi.single S 1 : Finset N → ℝ) T * v T = v S
  rw [hsum, Pi.single_eq_same, one_mul]

/-! ### Décomposition du générateur (clé de linéarité)

Le `S`-générateur `phiAugCont v (Pi.single S 1)` se décompose, comme vecteur de
`Option N → ℝ`, en la combinaison d'incidence `∑ i ∈ S, Pi.single (some i) 1`
plus le multiple de valeur `v S • Pi.single none 1`. L'application de toute
fonctionnelle linéaire `f` produit alors *l'identité de linéarité* que le
décodage du témoin exploite :
`f (générateur S) = ∑ i ∈ S, f (base-some i) + v S * f (base-none)`. Cette
identité est l'étape algébrique porteuse du lemme de décodage ci-dessous : elle
convertit l'inégalité duale du cône `0 ≤ f (générateur S)` (issue de
`augCone_dual_iff`) en l'inégalité de rationalité coalitionnelle
`v S ≤ ∑_{i ∈ S} x i` pour le témoin candidat
`x i := f (base-some i) / (-f (base-none))`. -/

/-- **Décomposition du générateur (forme vectorielle)** — le `S`-générateur
    vaut la combinaison d'incidence sur `S` (un vecteur de base `some i` par
    `i ∈ S`) plus le multiple de valeur `v S • Pi.single none 1` sur l'axe
    `none`. -/
lemma gen_decomp (v : Finset N → ℝ) (S : Finset N) :
    phiAugCont v (Pi.single S 1) =
      (∑ i ∈ S, (Pi.single (some i) 1 : (Option N) → ℝ)) + v S • Pi.single none 1 := by
  -- Miroir du patron `funext`/`cases` de l'identité grande-coalition prouvée
  -- dans `separatingFunctional_none_neg` ; ici pour une coalition arbitraire `S`.
  funext j
  cases j with
  | none =>
    -- LHS : `v S` (`gen_apply_none`). RHS : tout vecteur de base `some i` vaut
    -- `0` en `none` ; seul le multiple de valeur contribue `v S`.
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    rw [gen_apply_none]
    -- Chaque `(Pi.single (some x) 1) none = 0` car `none ≠ some x`.
    have hzero : ∀ x ∈ S, (Pi.single (some x) 1 : (Option N) → ℝ) none = 0 := by
      intro x _; rw [Pi.single_apply, if_neg (Option.some_ne_none x).symm]
    rw [Finset.sum_eq_zero hzero, Pi.single_eq_same, mul_one, zero_add]
  | some i =>
    -- LHS : indicateur d'incidence (`gen_apply_some`). RHS : en `some i`, seul
    -- le i-ème vecteur de base `some` peut contribuer `1` (et seulement si
    -- `i ∈ S`) ; le multiple de valeur est `0` hors de l'axe `none`.
    have hne : (some i : Option N) ≠ none := Option.some_ne_none i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
      Pi.single_apply, hne, if_false]
    rw [gen_apply_some]
    -- Réduire les conditions `some i = some i'` à `i = i'`, puis isoler `i`.
    have hsum : ∑ i' ∈ S, (if some i = some (i' : N) then (1 : ℝ) else 0) =
        if i ∈ S then 1 else 0 := by
      by_cases hs : i ∈ S
      · simp only [hs, if_true, Option.some.injEq]
        -- `if_neg` requiert `¬(i = i')` ; le `hi' : i' ≠ i` fourni est symétrique.
        rw [Finset.sum_eq_single i
            (fun i' _ hi' => by rw [if_neg hi'.symm])
            (fun hi => (hi hs).elim)]
        simp only [if_true]
      · simp only [hs, if_false, Option.some.injEq]
        rw [Finset.sum_eq_zero]
        intro i' hi'
        -- `i ≠ i'` : si `i = i'`, alors `i' ∈ S` donnerait `i ∈ S`, contredisant `hs`.
        have hne : i ≠ i' := by intro hss; exact hs (hss ▸ hi')
        rw [if_neg hne]
    rw [hsum]
    ring

/-- **Identité de linéarité sur le `S`-générateur** — pour toute fonctionnelle
    linéaire `f`, `f (générateur S) = ∑ i ∈ S, f (base-some i) + v S * f (base-none)`.
    C'est la forme algébrique que consomme le décodage du témoin (appliquer `f`
    à `gen_decomp`). -/
lemma gen_apply_linear (v : Finset N → ℝ) (S : Finset N)
    (f : ((Option N) → ℝ) →L[ℝ] ℝ) :
    f (phiAugCont v (Pi.single S 1)) =
      ∑ i ∈ S, f (Pi.single (some i) 1) + v S * f (Pi.single none 1) := by
  rw [gen_decomp, map_add, map_sum, map_smul, smul_eq_mul]

/-! ## Décodage du témoin — condition de signe

La fonctionnelle séparatrice `f` issue de `hyperplane_separation_point` (appliquée
à un point `balancedUnit (v(N)+t) ∉ augCone v`) doit être décodée en le témoin
du Core `x : N → ℝ`. Le candidat naturel est
`x i := f (Pi.single (some i) 1) / (-f (Pi.single none 1))`, bien défini dès
que l'on sait `f (Pi.single none 1) < 0`. Ce signe est la première étape
porteuse du décodage. -/

/-- **Condition de signe du décodage** — la fonctionnelle séparatrice `f`
    vérifie `f (Pi.single none 1) < 0`. Preuve : `0 ≤ f` sur le générateur
    grande-coalition `phiAugCont v (Pi.single ⊤ 1)` (il est dans `augCone v`,
    via `augCone_dual_iff`) ; l'identité
    `balancedUnit (v(N)+t) = phiAugCont v (Pi.single ⊤ 1) + t • Pi.single none 1`
    plus la linéarité transforme `f (balancedUnit (v(N)+t)) < 0` en
    `f (phiAugCont v (Pi.single ⊤ 1)) + t * f (Pi.single none 1) < 0` ;
    combinée à la non-négativité sur le générateur, `t * f (Pi.single none 1) < 0`,
    d'où le signe (t > 0). -/
lemma separatingFunctional_none_neg (v : Finset N → ℝ) {t : ℝ} (ht : 0 < t)
    (f : ((Option N) → ℝ) →L[ℝ] ℝ)
    (hfCone : ∀ y ∈ augCone v, 0 ≤ f y)
    (hfSep : f (balancedUnit (v Finset.univ + t)) < 0) :
    f (Pi.single none 1) < 0 := by
  -- 0 ≤ f sur le générateur grande-coalition.
  have huniv : 0 ≤ f (phiAugCont v (Pi.single Finset.univ 1)) :=
    (augCone_dual_iff v f).mp hfCone Finset.univ
  -- Valeur de coordonnée `phiAugCont v (Pi.single ⊤ 1) (some i) = 1` (incidence de ⊤).
  have hGenSome (i : N) :
      (phiAugCont v (Pi.single Finset.univ 1)) (some i) = (1 : ℝ) := by
    show ∑ S ∈ Finset.univ.filter (fun S => i ∈ S),
        (Pi.single Finset.univ 1 : Finset N → ℝ) S = 1
    -- `rw` (pas `exact`) détermine le `{s, f}` implicite depuis l'occurrence en LHS,
    -- contournant la defeq de réduction ite `(Pi.single ⊤ 1) ⊤ ≟ 1` qu'`exact` exige.
    rw [Finset.sum_eq_single Finset.univ
        (fun b _ hb => by rw [Pi.single_apply, if_neg hb])
        (fun h => by simp at h), Pi.single_eq_same]
  -- Valeur de coordonnée `phiAugCont v (Pi.single ⊤ 1) none = v(N)`.
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
  -- Identité : balancedUnit (v(N)+t) = générateur grande-coalition + t • base-none.
  have hId : balancedUnit (v Finset.univ + t) =
      phiAugCont v (Pi.single Finset.univ 1) + t • Pi.single none 1 := by
    funext j
    -- Les constructeurs d'`Option` sont `none` puis `some` ; on utilise `cases`
    -- explicite pour épingler chaque branche à sa tactique (un `rcases ... with i | _`
    -- positionnel les aurait inversés).
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
  -- Linéarité sur l'inégalité séparatrice, puis signe (t > 0). `nlinarith` car
  -- le but `f (Pi.single none 1) < 0` demande de diviser `t * f (...) < 0` par `t`.
  rw [hId, map_add, map_smul, smul_eq_mul] at hfSep
  nlinarith [ht, huniv]

/-! ### Construction du témoin (séparateur → pré-imputation)

Le cœur du décodage du témoin : une fonctionnelle séparatrice `f` (non-négative
sur `augCone v`, strictement négative sur `balancedUnit (v(N)+t)`) produit une
pré-imputation `x : N → ℝ` qui est coalitionnellement rationnelle
(`∀ S, v S ≤ ∑_{i ∈ S} x i`) et dans le budget strict (`∑ x ≤ v(N) + t`). C'est
le cœur du décodage TUGame-free : l'hypothèse de jeu équilibré n'entre que plus
tard (dans `Basic.lean`, via le pont `balancedUnit_notIn_augCone`, qui *produit*
un tel `f` par `hyperplane_separation_point`). Le témoin candidat est
`x i := f (base-some i) / (-f (base-none))`, bien défini grâce au lemme de signe
qui donne `f (base-none) < 0` ; la rationalité coalitionnelle se lit sur
l'inégalité duale du cône `0 ≤ f (générateur S)` via l'identité de linéarité
`gen_apply_linear`. -/

/-- **Décomposition de `balancedUnit`** — `balancedUnit (v(N)+t)` vaut le
    générateur de la grande coalition plus `t` fois le vecteur de base `none`.
    Sous une fonctionnelle séparatrice, cette identité fournit le budget strict
    `∑ x ≤ v(N) + t`. -/
lemma balancedUnit_decomp (v : Finset N → ℝ) (t : ℝ) :
    balancedUnit (v Finset.univ + t) =
      phiAugCont v (Pi.single Finset.univ 1) + t • Pi.single none 1 := by
  funext j
  cases j with
  | none =>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, balancedUnit]
    rw [gen_apply_none, Pi.single_eq_same]
    ring
  | some i =>
    have hne : (some i : Option N) ≠ none := Option.some_ne_none i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, balancedUnit]
    rw [gen_apply_some, Pi.single_apply, if_neg hne]
    simp only [Finset.mem_univ, if_true]
    ring

/-- **Décodage du témoin (cœur TUGame-free)** — une fonctionnelle séparatrice `f`
    (non-négative sur `augCone v`, négative sur `balancedUnit (v(N)+t)`) produit
    une pré-imputation `x` qui est coalitionnellement rationnelle et dans le
    budget `∑ x ≤ v(N) + t`. L'hypothèse de jeu équilibré n'entre que plus tard,
    dans `Basic.lean`, via le pont qui *produit* un tel `f`. -/
lemma exists_preimputation_strict_core (v : Finset N → ℝ) {t : ℝ} (ht : 0 < t)
    (f : ((Option N) → ℝ) →L[ℝ] ℝ)
    (hfCone : ∀ y ∈ augCone v, 0 ≤ f y)
    (hfSep : f (balancedUnit (v Finset.univ + t)) < 0) :
    ∃ x : N → ℝ,
      (∀ S : Finset N, v S ≤ ∑ i ∈ S, x i) ∧
      ∑ i : N, x i ≤ v Finset.univ + t := by
  -- (A) Signe : `f (base-none) < 0`, d'où `den := -f(base-none) > 0`.
  have hfneg : f (Pi.single none 1) < 0 :=
    separatingFunctional_none_neg v ht f hfCone hfSep
  set den : ℝ := -f (Pi.single none 1) with hden_def
  have hden_pos : 0 < den := by rw [hden_def]; exact neg_pos.mpr hfneg
  have hfnone_eq : f (Pi.single none 1) = -den := by linarith
  refine ⟨fun i => f (Pi.single (some i) 1) / den, ⟨?_, ?_⟩⟩
  · -- (B) Rationalité coalitionnelle : `v S ≤ ∑_{i ∈ S} x i`.
    intro S
    have hfS : 0 ≤ f (phiAugCont v (Pi.single S 1)) :=
      (augCone_dual_iff v f).mp hfCone S
    rw [gen_apply_linear] at hfS
    -- Factoriser la somme divisée, puis éliminer le dénominateur (positif).
    have hfactor : ∑ i ∈ S, f (Pi.single (some i) 1) / den =
        (∑ i ∈ S, f (Pi.single (some i) 1)) / den := by rw [Finset.sum_div]
    rw [hfactor, le_div_iff₀ hden_pos]
    -- `0 ≤ ∑ f(g_i) + v S * f(none)` et `f(none) = -den` ⟹ `v S * den ≤ ∑ f(g_i)`.
    nlinarith [hfS, hfnone_eq]
  · -- (C) Budget : `∑ x i ≤ v(N) + t`.
    -- Identité de linéarité grande-coalition.
    have hGuniv : f (phiAugCont v (Pi.single Finset.univ 1)) =
        ∑ i : N, f (Pi.single (some i) 1) + v Finset.univ * f (Pi.single none 1) :=
      gen_apply_linear v Finset.univ f
    -- Séparation + `balancedUnit_decomp` ⟹ `f(générateur univ) + t * f(none) < 0`.
    have hsep_eq : f (balancedUnit (v Finset.univ + t)) =
        f (phiAugCont v (Pi.single Finset.univ 1)) + t * f (Pi.single none 1) := by
      rw [balancedUnit_decomp, map_add, map_smul, smul_eq_mul]
    have hfGuniv : f (phiAugCont v (Pi.single Finset.univ 1)) < t * den := by
      have key : f (phiAugCont v (Pi.single Finset.univ 1)) +
          t * f (Pi.single none 1) < 0 := by rw [← hsep_eq]; exact hfSep
      linarith
    have hfactor : (∑ i : N, f (Pi.single (some i) 1) / den) =
        (∑ i : N, f (Pi.single (some i) 1)) / den := by rw [Finset.sum_div]
    rw [hfactor, div_le_iff₀ hden_pos]
    -- `∑ f(g_i) = f(générateur univ) + v(N) * den` (hGuniv + f(none) = -den) ;
    -- `f(générateur univ) < t * den` (hfGuniv) ⟹ `∑ f(g_i) ≤ (v(N) + t) * den`.
    nlinarith [hfGuniv, hGuniv, hfnone_eq]

end BondarevaCone
