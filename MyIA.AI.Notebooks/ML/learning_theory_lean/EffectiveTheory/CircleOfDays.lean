import Mathlib

/-!
# CircleOfDays — R10 : le cercle des jours, représentation irréductible de C₇

Tranche **R10** de l'arc « théorie effective » (#16741, issue #16752) :
*Engels, Liao & Tegmark, Not All Language Model Features Are
One-Dimensionally Linear* (arXiv:2405.14860, ICLR 2025 ; PDF GDrive sha8
`7DEAC929`).

Le papier reconstruit par SAE des **features circulaires** — jours de la
semaine, mois — et identifie (§3, App. C, Def. 7) ces cercles à des
**représentations irréductibles de dimension 2** : pour un groupe fini, sa
définition de réductibilité « implique la définition standard de
l'irréductibilité — spécifiquement la réductibilité en produit tensoriel ».
Le LLM « a ré-appris la théorie des représentations ».

Contenu formalisé — le cœur mathématique du claim, pour le cercle des jours
`C₇ = ZMod 7` :

1. `rotation` : la matrice de rotation d'angle `θ` ; `rotation_mul` et
   `rotation_cyclicSeven` en font une **représentation** de `C₇`
   (l'action d'un jour est la rotation d'une fraction `val/7` de tour,
   compatible avec l'addition modulo 7).
2. `rotation_charPoly` : la rotation satisfait son polynôme caractéristique
   `R² − 2·cos θ·R + I = 0`.
3. `circleOfDays_irreducible` : **le cercle des jours est irréductible** —
   tout sous-espace de `Fin 2 → ℝ` stable par la rotation d'ordre 7
   (l'image du générateur) est `⊥` ou `⊤`. La preuve est l'argument du
   papier vu par la théorie des représentations : un sous-espace stable
   propre serait une droite propre ; mais `μ² − 2μ cos(2π/7) + 1 = 0` n'a
   pas de racine réelle car `0 < cos(2π/7) < 1` (discriminant négatif), et
   une droite stable exigerait une valeur propre réelle.

Dépendances : Mathlib uniquement (`Matrix.mulVec`, `Submodule.span`,
`basisOfLinearIndependentOfCardEqFinrank`, `Real.cos_two_mul`,
`Real.cos_pos_of_mem_Ioo`, `Real.cos_lt_cos_of_nonneg_of_le_pi`).
-/

namespace LearningTheory.EffectiveTheory

/-- Matrice de rotation d'angle `θ` dans le plan euclidien — le « cercle »
du papier : chaque jour de `C₇` agit comme rotation d'une fraction de tour. -/
noncomputable def rotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

theorem rotation_mul (θ₁ θ₂ : ℝ) :
    rotation θ₁ * rotation θ₂ = rotation (θ₁ + θ₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Matrix.cons_val', Matrix.head_cons,
      Matrix.cons_val, Real.cos_add, Real.sin_add] <;> ring

/-- Les rotations sont 2π-périodiques. -/
theorem rotation_periodic (θ : ℝ) (m : ℤ) :
    rotation (θ + m * (2 * Real.pi)) = rotation θ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.cons_val', Matrix.head_cons, Matrix.cons_val,
      Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-- **Représentation de `C₇`** : l'action d'un jour `(a : ZMod 7)` comme
rotation d'une fraction `a.val / 7` de tour est compatible avec l'addition
modulo 7 — le morphisme de `ZMod 7` vers les rotations du plan. -/
theorem rotation_cyclicSeven (a b : ZMod 7) :
    rotation (2 * Real.pi * (((a + b).val : ℕ) : ℝ) / 7)
      = rotation (2 * Real.pi * ((a.val : ℕ) : ℝ) / 7)
        * rotation (2 * Real.pi * ((b.val : ℕ) : ℝ) / 7) := by
  obtain ⟨q, hq⟩ : ∃ q : ℕ, a.val + b.val = 7 * q + (a.val + b.val) % 7 :=
    ⟨(a.val + b.val) / 7, by omega⟩
  have hcast : ((a.val : ℕ) : ℝ) + ((b.val : ℕ) : ℝ)
      = 7 * ((q : ℕ) : ℝ) + (((a.val + b.val) % 7 : ℕ) : ℝ) := by
    push_cast
    exact_mod_cast hq
  have hangle : 2 * Real.pi * ((a.val : ℕ) : ℝ) / 7
        + 2 * Real.pi * ((b.val : ℕ) : ℝ) / 7
      = 2 * Real.pi * (((a + b).val : ℕ) : ℝ) / 7 + ((q : ℕ) : ℝ) * (2 * Real.pi) := by
    rw [ZMod.val_add]
    push_cast
    linear_combination (2 * Real.pi / 7) * hcast
  calc rotation (2 * Real.pi * (((a + b).val : ℕ) : ℝ) / 7)
      = rotation (2 * Real.pi * ((a.val : ℕ) : ℝ) / 7
          + 2 * Real.pi * ((b.val : ℕ) : ℝ) / 7) := by
        rw [hangle]
        have hqz : ((q : ℕ) : ℝ) = ((q : ℤ) : ℝ) := by
          push_cast
          ring
        rw [hqz, rotation_periodic]
    _ = rotation (2 * Real.pi * ((a.val : ℕ) : ℝ) / 7)
        * rotation (2 * Real.pi * ((b.val : ℕ) : ℝ) / 7) := (rotation_mul _ _).symm

/-- Le polynôme caractéristique annule la rotation :
`R² − 2·cos θ·R + I = 0` (Cayley–Hamilton explicite pour les rotations). -/
theorem rotation_charPoly (θ : ℝ) :
    rotation θ * rotation θ - (2 * Real.cos θ) • rotation θ + 1 = 0 := by
  have h2 : rotation θ * rotation θ = rotation (2 * θ) := by
    rw [rotation_mul, two_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h2, rotation, Matrix.cons_val', Matrix.head_cons, Matrix.cons_val,
      Matrix.one_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Real.cos_two_mul, Real.sin_two_mul] <;>
    linarith [Real.sin_sq_add_cos_sq θ]

private theorem bounds_2pi7 : 0 < 2 * Real.pi / 7 ∧ 2 * Real.pi / 7 ≤ Real.pi := by
  refine ⟨?_, ?_⟩
  · field_simp
    linarith [Real.pi_pos]
  · field_simp
    linarith [Real.pi_pos]

private theorem cos_2pi7_bounds :
    0 < Real.cos (2 * Real.pi / 7) ∧ Real.cos (2 * Real.pi / 7) < 1 := by
  obtain ⟨h1, h2⟩ := bounds_2pi7
  refine ⟨?_, ?_⟩
  · exact Real.cos_pos_of_mem_Ioo (by
      constructor <;> field_simp <;> linarith [Real.pi_pos])
  · have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (x := (0 : ℝ))
        (y := 2 * Real.pi / 7) (le_refl (0 : ℝ)) h2 h1
    simpa using hcos

/-- Aucune valeur propre réelle pour la rotation d'ordre 7 : si `R x = μ x`
avec `x ≠ 0`, le polynôme caractéristique `μ² − 2μ cos(2π/7) + 1 = 0`
contredit `0 < cos(2π/7) < 1` (discriminant `4(cos² − 1) < 0`). -/
private theorem eigen_impossible {x : Fin 2 → ℝ} (hx : x ≠ 0) {μ : ℝ}
    (hμ : (rotation (2 * Real.pi / 7)).mulVec x = μ • x) : False := by
  have hcp := rotation_charPoly (2 * Real.pi / 7)
  have h1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M.mulVec x) hcp
  simp only [Matrix.zero_mulVec, Matrix.sub_mulVec, Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
  -- h1 : R *ᵥ (R *ᵥ x) - (2 * cos(2π/7)) • (R *ᵥ x) + x = 0
  have hRR : (rotation (2 * Real.pi / 7)).mulVec
      ((rotation (2 * Real.pi / 7)).mulVec x) = μ ^ 2 • x := by
    rw [hμ, Matrix.mulVec_smul, hμ, smul_smul, ← pow_two]
  have hsm : (2 * Real.cos (2 * Real.pi / 7))
      • (rotation (2 * Real.pi / 7)).mulVec x = (2 * Real.cos (2 * Real.pi / 7) * μ) • x := by
    rw [hμ, smul_smul]
  rw [hRR, hsm] at h1
  obtain ⟨i, hxine⟩ := Function.ne_iff.mp hx
  simp only [Pi.zero_apply] at hxine
  have h1i := congrFun h1 i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply] at h1i
  have hfac : (μ ^ 2 - 2 * Real.cos (2 * Real.pi / 7) * μ + 1) * x i = 0 := by
    nlinarith [h1i]
  rcases mul_eq_zero.mp hfac with hcoef | hxi
  · obtain ⟨hcos, hcoslt⟩ := cos_2pi7_bounds
    have hc2 : Real.cos (2 * Real.pi / 7) ^ 2 < 1 := by
      nlinarith [sq_nonneg (Real.cos (2 * Real.pi / 7)), hcos, hcoslt]
    have hkey : (μ - Real.cos (2 * Real.pi / 7)) ^ 2 + (1 - Real.cos (2 * Real.pi / 7) ^ 2)
        = 0 := by nlinarith [hcoef]
    nlinarith [sq_nonneg (μ - Real.cos (2 * Real.pi / 7)), hc2, hkey]
  · exact absurd hxi hxine

/-- **Le cercle des jours est une représentation irréductible de dimension 2
de `C₇`** : tout sous-espace `W` de `Fin 2 → ℝ` stable par la rotation
d'ordre sept `R = rotation (2π/7)` (l'image du générateur de `C₇`) est
trivial ou plein.

Preuve : si `W` contient `v ≠ 0`, alors soit `R v` reste sur la droite
`span v` — auquel cas `v` est vecteur propre de `R` pour une valeur propre
réelle, exclu par `eigen_impossible` — soit `R v` sort de la droite, et
`![v, R v]` est libre de cardinal 2 : c'est une base de `Fin 2 → ℝ`, et
`W` la contient tout entière. -/
theorem circleOfDays_irreducible
    (W : Submodule ℝ (Fin 2 → ℝ))
    (hW : ∀ v ∈ W, (rotation (2 * Real.pi / 7)).mulVec v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hWbot : W = ⊥
  · exact Or.inl hWbot
  · right
    obtain ⟨v, hvW, hv0⟩ : ∃ v ∈ W, v ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact absurd ((Submodule.eq_bot_iff W).mpr fun x hx => hcon x hx) hWbot
    by_cases hspan : (rotation (2 * Real.pi / 7)).mulVec v
        ∈ Submodule.span ℝ ({v} : Set (Fin 2 → ℝ))
    · exfalso
      obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hspan
      exact eigen_impossible hv0 hμ.symm
    · -- Cas base : ![v, R v] est libre de cardinal 2, donc une base
      have hli : LinearIndependent ℝ ![v, (rotation (2 * Real.pi / 7)).mulVec v] := by
        rw [LinearIndependent.pair_iff]
        intro s t hst
        rcases eq_or_ne t 0 with ht0 | ht0
        · have hz : s • v = 0 := by
            rw [ht0, zero_smul, add_zero] at hst
            exact hst
          rcases smul_eq_zero.mp hz with h | h
          · exact ⟨h, ht0⟩
          · exact absurd h hv0
        · exfalso
          apply hspan
          have h3 : t • (rotation (2 * Real.pi / 7)).mulVec v = -(s • v) :=
            eq_neg_of_add_eq_zero_right hst
          have hRv : (rotation (2 * Real.pi / 7)).mulVec v = (-(s / t)) • v := by
            calc (rotation (2 * Real.pi / 7)).mulVec v
                = t⁻¹ • (t • (rotation (2 * Real.pi / 7)).mulVec v) :=
                  (inv_smul_smul₀ ht0 _).symm
              _ = t⁻¹ • -(s • v) := by rw [h3]
              _ = (-(s / t)) • v := by module
          exact Submodule.mem_span_singleton.mpr ⟨-(s / t), hRv.symm⟩
      have hle : Submodule.span ℝ
          (Set.range ![v, (rotation (2 * Real.pi / 7)).mulVec v]) ≤ W := by
        rw [Submodule.span_le]
        rintro w ⟨i, hi⟩
        fin_cases i
        · simp only [Matrix.cons_val_zero] at hi
          subst hi
          exact hvW
        · simp only [Matrix.cons_val_one, Matrix.head_cons] at hi
          subst hi
          exact hW v hvW
      have htop : Submodule.span ℝ
          (Set.range ![v, (rotation (2 * Real.pi / 7)).mulVec v]) = ⊤ :=
        LinearIndependent.span_eq_top_of_card_eq_finrank hli (by
          simp [Module.finrank_fin_fun])
      exact le_antisymm le_top (by rw [← htop]; exact hle)

end LearningTheory.EffectiveTheory
