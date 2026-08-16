import Mathlib
import Objective
import Converse

/-!
# Phase 4 — Pont (Bridge) : identité de coût + fragment de converse connecté au ML

Ce module relie l'objectif ML (`mimoObj`, Phase 2) aux briques probabilistes
de la converse (Phase 3b) — le chantier « grains à grignoter » de l'issue
#11148 (suite de #10984). Le converse actuel borne la probabilité d'un
événement d'échappement abstrait ; ici, pour la première fois, un énoncé du
lac relie directement l'objectif au bruit gaussien.

Architecture du fichier :

## Grain 1a — identité de différence de coût (algèbre pure)

1. `cost_diff` — la forme **générique** : dans tout espace de Hilbert réel,
   `‖w + √s•z + √s•v‖² − ‖w + √s•z‖² = s·‖v‖² + 2√s·⟪w,v⟫ + 2s·⟪z,v⟫`.
   C'est `norm_add_sq_two` (Phase 2) réarrangé : passer de `z` à `z + v`
   coûte un terme quadratique en `v` et deux couplages linéaires — l'un au
   bruit `w`, l'autre à la position courante `z` ;
2. `mimoObj_sub_mimoObj` — **Pont 1a** : instancié au canal MIMO,
   `mimoObj A w s u' − mimoObj A w s u = s·‖A v‖² + 2√s·⟪A v,w⟫ + 2s·⟪A v,A u⟫`
   avec `v = u' − u` — l'identité de différence de coût pour **deux
   configurations quelconques** `u, u'` ;
3. `mimoObj_residual_from_zero` — spécialisation **point de départ = vérité**
   (`u = 0`, le résidu est `w`) : `Δ = s·‖A v‖² + 2√s·⟪A v,w⟫` — le terme
   couplé à la position courante disparaît ;
4. `mimo_flip_cost_via_bridge` — **vérification de cohérence** : avec
   `v = flipAt i`, le Bridge redonne exactement le Lemme 11.1
   (`Δ = 4·(s‖hᵢ‖² + √s·⟪hᵢ,w⟫)`, `hᵢ = A eᵢ`) — le Lemme 11.1 devient
   corollaire du Bridge, qui le généralise.

## Grain 1b — fragment de converse concret (connecté au ML)

5. `stdGaussianPi_map_toLp` — **pont de conventions** : la gaussienne produit
   du lake SLT (`stdGaussianPi`, sur `Fin n → ℝ`) poussée par `toLp 2` est
   la gaussienne standard de Mathlib sur l'espace euclidien
   (`map_pi_eq_stdGaussian`) ;
6. `map_inner_stdGaussian` — **transport** : pour `w` gaussien standard sur
   l'espace euclidien, la fonctionnelle linéaire `⟪h, w⟫` a pour loi
   `gaussianReal 0 ‖h‖²`. C'est le morceau techniquement ouvert signalé dans
   #11148, fermé ici par l'API `IsGaussian` de Mathlib (toute forme linéaire
   continue d'une gaussienne est gaussienne de variance `‖L‖²`) ;
7. `flip_bat_prob_lower` — **premier énoncé du type « P(le flip bat) ≥ c »** :
   si `√s·‖hᵢ‖ ≤ 2` (et `s > 0`, `hᵢ ≠ 0` — voir docstring), alors
   `P(w : le flip i bat x*) ≥ (2 − √s·‖hᵢ‖)·φ(2)` où
   `φ(2) = exp(−2)/√(2π)` — via le transport (`⟪hᵢ,w⟫ ~ N(0,‖hᵢ‖²)`, l'événement
   « bat » est `⟪hᵢ,w⟫ < −√s·‖hᵢ‖²`) et la **Brique 1**
   (`gaussian_interval_mass_lower`, Phase 3b) : l'intervalle
   `[−2, −√s·‖hᵢ‖] ⊆ [−2,2]` de largeur `2 − √s·‖hᵢ‖` porte une masse
   `≥ largeur · φ(2)`.
-/

namespace Mimo

open MeasureTheory ProbabilityTheory GaussianMeasure HansonWright Real
open InnerProductSpace
open scoped BigOperators NNReal

section Geometrie

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Identité de différence de coût (forme générique).** Pour un bruit `w`,
une position courante `z`, une déviation `v` et un SNR `s ≥ 0`,

    ‖w + √s•z + √s•v‖² − ‖w + √s•z‖² = s·‖v‖² + 2√s·⟪w, v⟫_ℝ + 2s·⟪z, v⟫_ℝ.

Dérivée de `norm_add_sq_two` (Phase 2) : le déplacement `z ↦ z + v` coûte
un terme quadratique en `v` plus deux couplages linéaires — `2√s·⟪w,v⟫` par
le bruit, `2s·⟪z,v⟫` par la position courante (ce dernier s'annule au résidu
nul, cf `mimoObj_residual_from_zero`). -/
theorem cost_diff (w z v : E) {s : ℝ} (hs : 0 ≤ s) :
    ‖w + √s • z + √s • v‖ ^ 2 - ‖w + √s • z‖ ^ 2
      = s * ‖v‖ ^ 2 + 2 * √s * ⟪w, v⟫_ℝ + 2 * s * ⟪z, v⟫_ℝ := by
  have key := norm_add_sq_two (w + √s • z) (√s • v)
  rw [real_inner_smul_right, inner_add_left, real_inner_smul_left,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg s),
    mul_pow, Real.sq_sqrt hs] at key
  have hss : √s * √s = s := by rw [← sq]; exact Real.sq_sqrt hs
  rw [key]
  linear_combination (norm := ring_nf) (2 * ⟪z, v⟫_ℝ) * hss

end Geometrie

section Pont

variable {N M : ℕ}

/-- **Pont 1a — identité de différence de coût MIMO.** Pour toutes
configurations `u, u'` et `v = u' − u` :

    mimoObj A w s u' − mimoObj A w s u
      = s·‖A v‖² + 2√s·⟪A v, w⟫_ℝ + 2s·⟪A v, A u⟫_ℝ.

Le Bridge généralise le Lemme 11.1 (`mimo_flip_cost`, Phase 2), qui n'est
plus que le cas particulier `u = 0`, `v = flipAt i` (cf
`mimo_flip_cost_via_bridge`). -/
theorem mimoObj_sub_mimoObj (A : (Fin N → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin M))
    (w : EuclideanSpace ℝ (Fin M)) {s : ℝ} (hs : 0 ≤ s) (u u' : Fin N → ℝ) :
    mimoObj A w s u' - mimoObj A w s u
      = s * ‖A (u' - u)‖ ^ 2 + 2 * √s * ⟪A (u' - u), w⟫_ℝ
        + 2 * s * ⟪A (u' - u), A u⟫_ℝ := by
  have hA : A u' = A u + A (u' - u) := by
    rw [← LinearMap.map_add A u (u' - u)]
    congr
    abel
  have hsmul : √s • A u' = √s • A u + √s • A (u' - u) := by
    rw [hA, smul_add]
  have hcd := cost_diff w (A u) (A (u' - u)) hs
  rw [real_inner_comm (A (u' - u)) w, real_inner_comm (A (u' - u)) (A u)] at hcd
  show ‖w + √s • A u'‖ ^ 2 - ‖w + √s • A u‖ ^ 2 = _
  rw [hsmul]
  simpa [add_assoc] using hcd

/-- **Spécialisation point de départ = vérité.** Partant de `u = 0` (la
configuration courante est déjà `x*`, seul le résidu `w` reste), le coût
d'une déviation `v` est

    mimoObj A w s v − mimoObj A w s 0 = s·‖A v‖² + 2√s·⟪A v, w⟫_ℝ.

Le terme `2s·⟪A v, A u⟫` disparaît : à l'origine, seule la corrélation avec
le bruit discrimine les configurations. -/
theorem mimoObj_residual_from_zero (A : (Fin N → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin M))
    (w : EuclideanSpace ℝ (Fin M)) {s : ℝ} (hs : 0 ≤ s) (v : Fin N → ℝ) :
    mimoObj A w s v - mimoObj A w s 0
      = s * ‖A v‖ ^ 2 + 2 * √s * ⟪A v, w⟫_ℝ := by
  have h := mimoObj_sub_mimoObj A w hs 0 v
  simpa [LinearMap.map_zero] using h

/-- **Cohérence : Lemme 11.1 en corollaire du Bridge.** Avec `v = flipAt i`,
l'identité ci-dessus redonne exactement `mimo_flip_cost` (Phase 2) :

    mimoObj A w s (flipAt i) − mimoObj A w s 0
      = 4·(s·‖hᵢ‖² + √s·⟪hᵢ, w⟫_ℝ),   hᵢ = A eᵢ.

Le Bridge est donc une vraie généralisation du Lemme 11.1, pas un énoncé
parallèle : le flip est le cas `u = 0` de l'identité générale. -/
theorem mimo_flip_cost_via_bridge (A : (Fin N → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin M))
    (w : EuclideanSpace ℝ (Fin M)) {s : ℝ} (hs : 0 ≤ s) (i : Fin N) :
    mimoObj A w s (flipAt i) - mimoObj A w s 0
      = 4 * (s * ‖A (Pi.single i 1)‖ ^ 2
             + √s * ⟪A (Pi.single i 1), w⟫_ℝ) := by
  have h := mimoObj_residual_from_zero A w hs (flipAt i)
  have hA : A (flipAt i) = (2 : ℝ) • A (Pi.single i 1) := by
    rw [flipAt]
    exact LinearMap.map_smul A 2 _
  rw [hA, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left] at h
  ring_nf at h ⊢
  exact h

end Pont

section Converse

variable {N M : ℕ}

/-- **Pont de conventions.** La gaussienne produit du lake SLT
(`stdGaussianPi`, mesure sur `Fin n → ℝ`) poussée par l'identification
`toLp 2` est exactement la gaussienne standard de Mathlib sur l'espace
euclidien — instance directe de `map_pi_eq_stdGaussian`. Le fragment converse
ci-dessous vit côté Mathlib (même convention que la Phase 3a, `Lmmse`) ;
ce pont ramène l'énoncé à la convention produit du lake SLT. -/
lemma stdGaussianPi_map_toLp :
    (stdGaussianPi M).map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℝ (Fin M)) :=
  map_pi_eq_stdGaussian

/-- **Transport de la fonctionnelle linéaire.** Pour `w` gaussien standard
sur l'espace euclidien (Mathlib `stdGaussian`, image de `stdGaussianPi` par
`toLp 2` — cf `stdGaussianPi_map_toLp`), la forme linéaire `⟪h, w⟫` a pour
loi `gaussianReal 0 ‖h‖²`. C'est le morceau techniquement ouvert signalé dans
#11148, fermé ici en une étape par l'API `IsGaussian` de Mathlib : toute forme
linéaire continue d'une gaussienne est gaussienne, de moyenne `μ[L] = 0`
(`integral_strongDual_stdGaussian`) et de variance `Var[L; μ] = ‖L‖²`
(`variance_dual_stdGaussian`) ; la forme `w ↦ ⟪h, w⟫` est `innerSL ℝ h`, de
norme `‖h‖` (`innerSL_apply_norm`). -/
lemma map_inner_stdGaussian (h : EuclideanSpace ℝ (Fin M)) :
    Measure.map (fun w : EuclideanSpace ℝ (Fin M) => ⟪h, w⟫_ℝ)
      (stdGaussian (EuclideanSpace ℝ (Fin M)))
      = gaussianReal 0 ((‖h‖ ^ 2).toNNReal) := by
  have hmap := (isGaussian_stdGaussian (E := EuclideanSpace ℝ (Fin M)) :
    IsGaussian _).map_eq_gaussianReal (L := innerSL ℝ h)
  rw [integral_strongDual_stdGaussian (E := EuclideanSpace ℝ (Fin M))
      (L := innerSL ℝ h),
    variance_dual_stdGaussian (E := EuclideanSpace ℝ (Fin M)) (L := innerSL ℝ h),
    innerSL_apply_norm] at hmap
  simpa [innerSL_apply_apply] using hmap

/-- **Variante ouverte de la Brique 1.** Tout intervalle **ouvert** inclus dans
`[−2, 2]` porte une masse gaussienne `≥ largeur · φ(2)`. La Brique 1 de la
Phase 3b énonce ce résultat pour `Ioc a b` ; le fragment converse du Bridge
a besoin d'un intervalle strictement contenu dans l'événement `y < c`, donc
d'un `Ioo a b` (l'extrémité droite d'un `Ioc` n'est pas dans `Iio`). Même
preuve que `gaussian_interval_mass_lower`, avec `volume_Ioo`. -/
theorem gaussian_interval_mass_lower_open {a b : ℝ} (hab : a ≤ b)
    (ha : |a| ≤ 2) (hb : |b| ≤ 2) :
    (b - a) * Real.exp (-2) / Real.sqrt (2 * Real.pi) ≤
      (gaussianReal 0 1 (Set.Ioo a b)).toReal := by
  have hk : 0 ≤ Real.exp (-2) / Real.sqrt (2 * Real.pi) := by positivity
  have hmeasure : gaussianReal 0 1 (Set.Ioo a b) =
      ∫⁻ x in Set.Ioo a b, ENNReal.ofReal (gaussianPDFReal 0 1 x) ∂volume := by
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
      withDensity_apply _ measurableSet_Ioo]
    rfl
  have hsplit : ∀ x ∈ Set.Ioo (a : ℝ) b, |x| ≤ 2 := by
    intro x hx
    rw [abs_le]
    constructor <;> nlinarith [(abs_le.mp ha).1, (abs_le.mp ha).2,
      (abs_le.mp hb).1, (abs_le.mp hb).2, hx.1.le, hx.2.le]
  have hpoint : ∀ x, (Set.Ioo a b).indicator (fun _ => ENNReal.ofReal
      (Real.exp (-2) / Real.sqrt (2 * Real.pi))) x ≤
      (Set.Ioo a b).indicator (fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x)) x := by
    intro x
    by_cases hx : x ∈ Set.Ioo a b
    · simp only [Set.indicator_of_mem hx]
      exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_lower_two x (hsplit x hx))
    · rw [Set.indicator_apply, if_neg hx, Set.indicator_apply, if_neg hx]
  have hmono : (∫⁻ _x in Set.Ioo a b,
        ENNReal.ofReal (Real.exp (-2) / Real.sqrt (2 * Real.pi)) ∂volume) ≤
      ∫⁻ x in Set.Ioo a b, ENNReal.ofReal (gaussianPDFReal 0 1 x) ∂volume := by
    rw [← lintegral_indicator measurableSet_Ioo
        (fun _ => ENNReal.ofReal (Real.exp (-2) / Real.sqrt (2 * Real.pi))),
      ← lintegral_indicator measurableSet_Ioo
        (fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x))]
    exact lintegral_mono hpoint
  have hchain : ENNReal.ofReal ((b - a) * (Real.exp (-2) / Real.sqrt (2 * Real.pi))) ≤
      gaussianReal 0 1 (Set.Ioo a b) := by
    rw [hmeasure]
    calc ENNReal.ofReal ((b - a) * (Real.exp (-2) / Real.sqrt (2 * Real.pi)))
        = ∫⁻ _x in Set.Ioo a b,
            ENNReal.ofReal (Real.exp (-2) / Real.sqrt (2 * Real.pi)) ∂volume := by
          rw [setLIntegral_const, Real.volume_Ioo,
            ← ENNReal.ofReal_mul (by nlinarith [hab, hk]), mul_comm]
      _ ≤ ∫⁻ x in Set.Ioo a b, ENNReal.ofReal (gaussianPDFReal 0 1 x) ∂volume := hmono
  have hnn : 0 ≤ (b - a) * (Real.exp (-2) / Real.sqrt (2 * Real.pi)) := by
    nlinarith [hab, hk]
  have hlhs : (b - a) * Real.exp (-2) / Real.sqrt (2 * Real.pi) =
      (ENNReal.ofReal ((b - a) * (Real.exp (-2) / Real.sqrt (2 * Real.pi)))).toReal := by
    rw [ENNReal.toReal_ofReal hnn]
    ring
  rw [hlhs]
  exact (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (measure_ne_top _ _)).mpr hchain

/-- **Premier énoncé du type « P(le flip bat x*) ≥ c ».** Soit `hᵢ = A eᵢ`. Si
`√s·‖hᵢ‖ ≤ 2` (avec `s > 0` et `‖hᵢ‖ > 0` — deux hypothèses absentes de
l'énoncé de l'issue #11148, mais nécessaires : pour `s = 0` ou `‖hᵢ‖ = 0`
l'événement a probabilité `0` alors que la borne `(2 − √s‖hᵢ‖)·φ(2)` est
strictement positive), alors

    P(w : le flip i bat x*) ≥ (2 − √s·‖hᵢ‖)·φ(2)

où `φ(2) = exp(−2)/√(2π)`. Enchaînement : le coût d'un flip
(`mimo_flip_cost_via_bridge`) montre que l'événement « bat » est
`⟪hᵢ, w⟫ < −√s·‖hᵢ‖²` ; le transport (`map_inner_stdGaussian`) donne la loi
`⟪hᵢ, w⟫ ~ N(0, ‖hᵢ‖²)` ; la mise à l'échelle ramène à `N(0,1)` et l'intervalle
`(−2, −√s·‖hᵢ‖) ⊆ {y < −√s·‖hᵢ‖}` porte la masse `≥ (2 − √s·‖hᵢ‖)·φ(2)`
(variante ouverte de la Brique 1). -/
theorem flip_bat_prob_lower (A : (Fin N → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin M))
    {s : ℝ} (hs : 0 < s) (i : Fin N) (hσ : 0 < ‖A (Pi.single i 1)‖)
    (hbound : √s * ‖A (Pi.single i 1)‖ ≤ 2) :
    (2 - √s * ‖A (Pi.single i 1)‖) * Real.exp (-2) / Real.sqrt (2 * Real.pi)
      ≤ (stdGaussian (EuclideanSpace ℝ (Fin M))
          {w : EuclideanSpace ℝ (Fin M) | mimoObj A w s (flipAt i) < mimoObj A w s 0}).toReal := by
  set hᵢ : EuclideanSpace ℝ (Fin M) := A (Pi.single i 1) with hhᵢ
  have hsqrt : 0 < √s := by positivity
  have hss : √s * √s = s := by rw [← sq]; exact Real.sq_sqrt hs.le
  have hmono : √s * (-√s * ‖hᵢ‖ ^ 2) = -s * ‖hᵢ‖ ^ 2 := by
    linear_combination (norm := ring_nf) (-(‖hᵢ‖ ^ 2)) * hss
  have hsqrt_nonneg : 0 ≤ √s * ‖hᵢ‖ := mul_nonneg (Real.sqrt_nonneg s) (norm_nonneg _)
  have hev : {w : EuclideanSpace ℝ (Fin M) | mimoObj A w s (flipAt i) < mimoObj A w s 0}
      = {w : EuclideanSpace ℝ (Fin M) | ⟪hᵢ, w⟫_ℝ < -√s * ‖hᵢ‖ ^ 2} := by
    ext w
    simp only [Set.mem_setOf_eq]
    have hfc : mimoObj A w s (flipAt i) - mimoObj A w s 0
        = 4 * (s * ‖hᵢ‖ ^ 2 + √s * ⟪hᵢ, w⟫_ℝ) := by
      simpa [hhᵢ] using mimo_flip_cost_via_bridge A w hs.le i
    constructor <;> intro hw
    · rw [← sub_lt_zero, hfc] at hw
      have hsum : s * ‖hᵢ‖ ^ 2 + √s * ⟪hᵢ, w⟫_ℝ < 0 := by
        nlinarith [hw]
      have hstep : √s * ⟪hᵢ, w⟫_ℝ < -s * ‖hᵢ‖ ^ 2 := by
        linarith
      have hbr : √s * ⟪hᵢ, w⟫_ℝ < √s * (-√s * ‖hᵢ‖ ^ 2) := by
        rw [hmono]; exact hstep
      exact lt_of_mul_lt_mul_left hbr hsqrt.le
    · have hbr : √s * ⟪hᵢ, w⟫_ℝ < √s * (-√s * ‖hᵢ‖ ^ 2) :=
        mul_lt_mul_of_pos_left hw hsqrt
      rw [hmono] at hbr
      have hsum : s * ‖hᵢ‖ ^ 2 + √s * ⟪hᵢ, w⟫_ℝ < 0 := by
        linarith
      rw [← sub_lt_zero, hfc]
      linarith
  have hmap := map_inner_stdGaussian hᵢ
  have hmass : (stdGaussian (EuclideanSpace ℝ (Fin M)))
      {w : EuclideanSpace ℝ (Fin M) | ⟪hᵢ, w⟫_ℝ < -√s * ‖hᵢ‖ ^ 2}
      = (gaussianReal 0 ((‖hᵢ‖ ^ 2).toNNReal)) (Set.Iio (-√s * ‖hᵢ‖ ^ 2)) := by
    rw [← hmap]
    rw [Measure.map_apply (by fun_prop :
        Measurable (fun w : EuclideanSpace ℝ (Fin M) => ⟪hᵢ, w⟫_ℝ)) measurableSet_Iio]
    rfl
  have hscale : Measure.map (fun z : ℝ => ‖hᵢ‖ * z) (gaussianReal 0 1)
      = gaussianReal 0 ((‖hᵢ‖ ^ 2).toNNReal) := by
    rw [gaussianReal_map_const_mul (μ := 0) (v := (1 : ℝ≥0)) ‖hᵢ‖]
    simpa [Real.toNNReal_of_nonneg, sq_nonneg]
  have hmass1 : (gaussianReal 0 ((‖hᵢ‖ ^ 2).toNNReal)) (Set.Iio (-√s * ‖hᵢ‖ ^ 2))
      = (gaussianReal 0 1) (Set.Iio (-√s * ‖hᵢ‖)) := by
    rw [← hscale]
    rw [Measure.map_apply (by fun_prop : Measurable (fun z : ℝ => ‖hᵢ‖ * z))
      measurableSet_Iio]
    congr 1
    ext z
    constructor <;> intro hz
    · have hz' : ‖hᵢ‖ * z < ‖hᵢ‖ * (-√s * ‖hᵢ‖) := by
        simpa [mul_comm, mul_left_comm, mul_assoc, sq] using hz
      exact lt_of_mul_lt_mul_left hz' (norm_nonneg _)
    · have hz' : ‖hᵢ‖ * z < ‖hᵢ‖ * (-√s * ‖hᵢ‖) :=
        mul_lt_mul_of_pos_left hz hσ
      simpa [mul_comm, mul_left_comm, mul_assoc, sq] using hz'
  have hab : -2 ≤ -√s * ‖hᵢ‖ := by nlinarith [hbound]
  have hb' : |-√s * ‖hᵢ‖| ≤ 2 := by
    rw [neg_mul, abs_of_nonpos (neg_nonpos.mpr hsqrt_nonneg)]
    linarith
  have hbrick := gaussian_interval_mass_lower_open (a := -2) (b := -√s * ‖hᵢ‖) hab
    (by norm_num) hb'
  have hsub : Set.Ioo (-2 : ℝ) (-√s * ‖hᵢ‖) ⊆ Set.Iio (-√s * ‖hᵢ‖) := by
    intro y hy
    exact hy.2
  have hmassmono : (gaussianReal 0 1) (Set.Ioo (-2 : ℝ) (-√s * ‖hᵢ‖))
      ≤ (gaussianReal 0 1) (Set.Iio (-√s * ‖hᵢ‖)) := by
    exact measure_mono hsub
  rw [hev, hmass, hmass1]
  calc
    (2 - √s * ‖hᵢ‖) * Real.exp (-2) / Real.sqrt (2 * Real.pi)
        = ((-√s * ‖hᵢ‖) - (-2)) * Real.exp (-2) / Real.sqrt (2 * Real.pi) := by
          ring
    _ ≤ (gaussianReal 0 1 (Set.Ioo (-2) (-√s * ‖hᵢ‖))).toReal := hbrick
    _ ≤ (gaussianReal 0 1 (Set.Iio (-√s * ‖hᵢ‖))).toReal := by
        exact (ENNReal.toReal_le_toReal (measure_ne_top _ _)
          (measure_ne_top _ _)).mpr hmassmono

end Converse

end Mimo
