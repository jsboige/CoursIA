import Mathlib

/-!
# DaysCircle — le cercle des jours : une représentation irréductible de C₇

Tranche **R10** du corpus Tegmark (EPIC #16741, claim #16752) :
*Not All Language Model Features Are One-Dimensionally Linear*
(Engels, Michaud, Liao, Gurnee, Tegmark, arXiv:2405.14860).

L'observation centrale du papier : la feature « jour de la semaine » n'est pas
une direction unidimensionnelle de l'espace latent, mais un **cercle** dans un
plan 2D — chaque jour est la rotation d'angle `2π/7` du précédent, et les 7
jours occupent 7 positions distinctes sur le cercle unité.

Ce module formalise la structure mathématique (Annexe C du papier) :

1. **L'orbite des jours** — `zeta = exp (2πi/7)` est une racine primitive
   7-ième de l'unité (`zeta_primitive`), donc les 7 jours `day k = zeta ^ k`
   sont **distincts** (`day_distinct`) et vivent tous sur le **cercle
   unité** (`days_on_circle`).
2. **La rotation des jours** — `dayRep k : ℂ →ₗ[ℝ] ℂ` (multiplication par
   `zeta ^ k`, ℂ vu comme plan réel de dimension 2) est l'action de
   `C₇ = ZMod 7` sur le plan ; elle envoie chaque jour sur un autre jour
   (`dayRep_day`) : le cercle est une orbite homogène sous `C₇`.
3. **Irréductibilité (Annexe C)** — le plan des jours n'admet **aucune droite
   réelle stable** (`zeta_smul_eq_real_smul_imp` : la rotation ζ n'a pas de
   vecteur propre réel), donc tout sous-espace réel stable par l'action de
   `C₇` est nul ou plein (`stable_eq_bot_or_top`). C'est exactement
   l'irréductibilité de la représentation 2D réelle de `C₇` : le papier note
   que la réductibilité équivaudrait à une décomposition en produit tensoriel
   de sous-représentations — irréductible, le cercle des jours est
   **véritablement bidimensionnel**, impossible à décomposer en deux features
   unidimensionnelles indépendantes.

Le plan réel est `ℂ` (structure naturelle de ℝ-espace de dimension 2) ; la
rotation d'angle `2π/7` est la multiplication par `zeta`.

Hors scope : les autres cercles du papier (mois, saisons), la construction
multi-tête, et la direction « produit tensoriel » de l'Annexe C (discursive —
l'irréductibilité en est le contenu mathématique). -/

namespace DaysCircle

open Complex

/-- La rotation élémentaire du cercle des jours : racine primitive 7-ième de
l'unité. Le jour `k+1` est obtenu en multipliant par `zeta`. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I * (1 / 7))

/-- `zeta` est une racine **primitive** 7-ième de l'unité : son orbite
`1, zeta, …, zeta ^ 6` parcourt exactement les 7 jours avant de boucler. -/
theorem zeta_primitive : IsPrimitiveRoot zeta 7 := by
  simpa [zeta] using
    Complex.isPrimitiveRoot_exp_of_coprime 1 7 (by norm_num) (by norm_num)

/-- La rotation des jours boucle : 7 rotations d'affilée rapportent chaque
jour sur lui-même. -/
theorem zeta_pow_seven : zeta ^ 7 = 1 :=
  zeta_primitive.pow_eq_one

private theorem two_pi_div_seven_pos : 0 < 2 * Real.pi / 7 :=
  div_pos Real.two_pi_pos (by norm_num)

private theorem two_pi_div_seven_lt_pi : 2 * Real.pi / 7 < Real.pi := by
  rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 7)]
  nlinarith [Real.pi_pos]

private theorem zeta_exp_form :
    zeta = Complex.exp (((2 * Real.pi / 7 : ℝ) : ℂ) * Complex.I) := by
  unfold zeta
  congr 1
  rw [Complex.ofReal_div, Complex.ofReal_mul]
  norm_num
  field_simp

/-- Partie imaginaire de la rotation : `sin (2π/7)`, strictement positif. -/
theorem zeta_im : zeta.im = Real.sin (2 * Real.pi / 7) := by
  rw [zeta_exp_form]
  simp only [Complex.exp_ofReal_mul_I, Complex.add_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_add, add_zero, mul_one]

/-- La rotation `zeta` n'est **pas réelle** : aucun nombre réel ne peut
l'incarner. Une rotation d'angle non nul (et non plat) ne se projette pas sur
l'axe réel — c'est ce qui empêchera toute droite réelle stable. -/
theorem zeta_not_real : ¬∃ r : ℝ, zeta = (r : ℂ) := by
  rintro ⟨r, hr⟩
  have h0 : zeta.im = 0 := by rw [hr]; simp
  rw [zeta_im] at h0
  exact absurd h0 (ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi two_pi_div_seven_pos two_pi_div_seven_lt_pi))

/-- Le jour `k` : position sur le cercle unité obtenue par `k` rotations
élémentaires depuis le jour `0` (= `1`). -/
noncomputable def day (k : ZMod 7) : ℂ := zeta ^ k.val

/-- Les 7 jours sont des points **distincts** du cercle : la primitivité
garantit qu'aucune rotation non triviale ne fixe un jour. -/
theorem day_distinct : Function.Injective day := by
  intro k l h
  have hζ0 : zeta ≠ 0 := Complex.exp_ne_zero _
  have hk : k.val < 7 := ZMod.val_lt k
  have hl : l.val < 7 := ZMod.val_lt l
  unfold day at h
  rcases le_total k.val l.val with hle | hle
  · have hd : zeta ^ (l.val - k.val) = 1 := by
      have hkl : k.val + (l.val - k.val) = l.val := by omega
      refine mul_left_cancel₀ (pow_ne_zero k.val hζ0) ?_
      rw [← pow_add, hkl, h, mul_one]
    rcases Nat.eq_zero_or_pos (l.val - k.val) with h0 | hpos
    · exact ZMod.val_injective 7 (by omega)
    · obtain ⟨c, hc⟩ := zeta_primitive.dvd_of_pow_eq_one _ hd
      omega
  · have hd : zeta ^ (k.val - l.val) = 1 := by
      have hkl : l.val + (k.val - l.val) = k.val := by omega
      refine mul_left_cancel₀ (pow_ne_zero l.val hζ0) ?_
      rw [← pow_add, hkl, h, mul_one]
    rcases Nat.eq_zero_or_pos (k.val - l.val) with h0 | hpos
    · exact ZMod.val_injective 7 (by omega)
    · obtain ⟨c, hc⟩ := zeta_primitive.dvd_of_pow_eq_one _ hd
      omega

/-- Tous les jours vivent sur le **cercle unité** : la rotation préserve la
norme. -/
theorem days_on_circle (k : ZMod 7) : ‖day k‖ = 1 := by
  have hz : ‖zeta‖ = 1 := by
    rw [zeta_exp_form, Complex.norm_exp]
    have h0 : (((2 * Real.pi / 7 : ℝ) : ℂ) * Complex.I).re = 0 := by
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
    rw [h0, Real.exp_zero]
  unfold day
  rw [Complex.norm_pow, hz, one_pow]

private theorem zeta_pow_mod_seven (m : ℕ) : zeta ^ (m % 7) = zeta ^ m := by
  conv_rhs =>
    rw [show m = 7 * (m / 7) + m % 7 from (Nat.div_add_mod m 7).symm]
  rw [pow_add, pow_mul, zeta_pow_seven, one_pow, one_mul]

/-- La représentation des jours : l'action de `C₇ = ZMod 7` sur le plan réel
`ℂ` — le jour `k` agit comme la rotation `z ↦ zeta ^ k * z` (multiplication
complexe, linéaire réelle). -/
noncomputable def dayRep (k : ZMod 7) : ℂ →ₗ[ℝ] ℂ where
  toFun z := zeta ^ k.val * z
  map_add' _ _ := by ring
  map_smul' r z := by
    show zeta ^ k.val * (r • z) = r • (zeta ^ k.val * z)
    simp only [Complex.real_smul]
    ring

/-- Lemme d'évaluation : `dayRep` est la multiplication par `zeta ^ k`. -/
theorem dayRep_apply (k : ZMod 7) (z : ℂ) :
    dayRep k z = zeta ^ k.val * z := rfl

/-- La représentation fait tourner les jours entre eux : agir par `k` sur le
jour `l` donne le jour `k + l`. Le cercle est une orbite homogène sous `C₇`. -/
theorem dayRep_day (k l : ZMod 7) : dayRep k (day l) = day (k + l) := by
  simp only [dayRep_apply, day]
  have hv : (k + l).val = (k.val + l.val) % 7 := ZMod.val_add k l
  rw [hv, ← pow_add]
  exact (zeta_pow_mod_seven _).symm

/-- **Irréductibilité, étape clé (Annexe C)** : la rotation `zeta` n'a aucun
vecteur propre réel non nul — toute droite réelle du plan est déployée par la
rotation. C'est l'obstruction à une feature « unidimensionnelle ». -/
theorem zeta_smul_eq_real_smul_imp {v : ℂ} {r : ℝ} (h : zeta * v = r • v) :
    v = 0 := by
  by_contra hv
  have hz : zeta = (r : ℂ) := by
    have hmul : (zeta - (r : ℂ)) * v = 0 := by
      rw [sub_mul, ← Complex.real_smul]
      linear_combination h
    rcases mul_eq_zero.mp hmul with h1 | h2
    · exact sub_eq_zero.mp h1
    · exact absurd h2 hv
  exact zeta_not_real ⟨r, hz⟩

/-- **Irréductibilité de la représentation des jours (Annexe C)** : tout
sous-espace réel du plan stable par l'action de `C₇` (la rotation des jours)
est nul ou plein. Le plan des jours est **véritablement bidimensionnel** :
aucune direction réelle — aucune « feature unidimensionnelle » — ne porte
l'action du groupe. -/
theorem stable_eq_bot_or_top {p : Submodule ℝ ℂ}
    (hstab : ∀ k : ZMod 7, Submodule.map (dayRep k) p ≤ p) :
    p = ⊥ ∨ p = ⊤ := by
  by_contra hcon
  have hbot : p ≠ ⊥ := fun hb => hcon (Or.inl hb)
  have htop : p ≠ ⊤ := fun ht => hcon (Or.inr ht)
  have hfact : Fact (1 < 7) := ⟨by norm_num⟩
  obtain ⟨v, hvmem, hv0⟩ := (Submodule.ne_bot_iff p).mp hbot
  -- la rotation envoie p dans p : zeta * v ∈ p
  have hζmem : zeta * v ∈ p := by
    refine (hstab 1) ((Submodule.mem_map).mpr ⟨v, hvmem, ?_⟩)
    rw [dayRep_apply, ZMod.val_one, pow_one]
  -- p est propre non nul dans un plan : dimension exactement 1 (une droite)
  have hlt : Module.finrank ℝ ↥p < Module.finrank ℝ ℂ :=
    Submodule.finrank_lt htop
  rw [Complex.finrank_real_complex] at hlt
  have hspanle : (ℝ ∙ v) ≤ p :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvmem)
  have hone : Module.finrank ℝ ↥(ℝ ∙ v) = 1 := finrank_span_singleton hv0
  have hge : 1 ≤ Module.finrank ℝ ↥p :=
    le_trans hone.symm.le (Submodule.finrank_mono hspanle)
  have hdim : Module.finrank ℝ ↥p = 1 := by omega
  -- donc p = ℝ ∙ v : une droite
  have hpe : (ℝ ∙ v) = p :=
    Submodule.eq_of_le_of_finrank_eq hspanle
      (by rw [finrank_span_singleton hv0, hdim])
  -- et zeta * v, élément de p, serait colinéaire à v : vecteur propre réel
  rw [← hpe] at hζmem
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hζmem
  exact absurd (zeta_smul_eq_real_smul_imp hr.symm) hv0

end DaysCircle
