import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Certificat algébrique du point de quart

Cette couche déduit l'identité préfixe d'une récurrence locale.
L'identification `tᵢ = (2i+1)aᵢ` est intégrée au terme sommé. Elle ne
formalise ni Cartier, ni Frobenius.

La brique P3+ (candidat 3 du P2) y ajoute la base j=1728 : la courbe de
Weierstrass d'invariant `j = 1728` via `WeierstrassCurve`, invariant j établi
formellement via `c₄^3 / Δ`.

-/

namespace CartierMiller

open Finset

variable {F : Type*} [Field F]

/-- Le certificat découle de la seule récurrence locale. -/
theorem telescoping_certificate (a b x : F)
    (recurrence : 4 * (x + 1) * b = (2 * x + 1) * a) :
    ((2 * x + 1)^2 - 8) * a =
      -4 * (x + 1) * (2 * x + 7) * b + 4 * x * (2 * x + 5) * a := by
  calc
    _ = -(2 * x + 7) * ((2 * x + 1) * a) + 4 * x * (2 * x + 5) * a := by ring
    _ = _ := by rw [← recurrence]; ring

/-- Les sommes préfixes vérifient l'identité de télescopage pour toute suite
satisfaisant la récurrence sur les indices utilisés. -/
theorem prefix_sum_identity (a : ℕ → F) (h : F) (L : ℕ)
    (half : 2 * h + 1 = 0)
    (recurrence : ∀ i < L, 4 * ((i : F) + 1) * a (i + 1) =
      (2 * (i : F) + 1) * a i) :
    (∑ i ∈ range L, (h + 1 + (i : F)) * ((2 * (i : F) + 1) * a i)) =
      4 * (∑ i ∈ range L, a i) - 2 * (L : F) * (2 * (L : F) + 5) * a L := by
  induction L with
  | zero => simp
  | succ L ih =>
    have prev := ih (fun i hi => recurrence i (Nat.lt_succ_of_lt hi))
    have cert := telescoping_certificate (a L) (a (L + 1)) (L : F)
      (recurrence L (Nat.lt_succ_self L))
    have hh := congrArg (fun y : F => y * ((2 * (L : F) + 1) * a L)) half
    rw [sum_range_succ, sum_range_succ]
    simp only [Nat.cast_succ]
    have two_ne : (2 : F) ≠ 0 := by
      intro h2
      simp [h2] at half
    apply (mul_left_cancel₀ two_ne)
    linear_combination 2 * prev + hh + cert

/-- Au point de quart, le coefficient frontière vaut neuf quarts. -/
theorem quarter_point_coefficient (n : F) (quarter : 4 * n + 1 = 0)
    (four_ne : (4 : F) ≠ 0) : -2 * n * (2 * n + 5) = 9 / 4 := by
  field_simp
  linear_combination (-4 * n - 9) * quarter

/-- Spécialisation de l'identité préfixe au point de quart. -/
theorem quarter_point_identity (a : ℕ → F) (h : F) (n : ℕ)
    (half : 2 * h + 1 = 0)
    (recurrence : ∀ i < n, 4 * ((i : F) + 1) * a (i + 1) =
      (2 * (i : F) + 1) * a i)
    (quarter : 4 * (n : F) + 1 = 0) (four_ne : (4 : F) ≠ 0) :
    (∑ i ∈ range n, (h + 1 + (i : F)) * ((2 * (i : F) + 1) * a i)) =
      4 * (∑ i ∈ range n, a i) + (9 / 4 : F) * a n := by
  have hp := prefix_sum_identity a h n half recurrence
  have hq := quarter_point_coefficient (n : F) quarter four_ne
  calc
    _ = 4 * (∑ i ∈ range n, a i) + (-2 * (n : F) * (2 * (n : F) + 5)) * a n := by
      rw [hp]; ring
    _ = _ := by rw [hq]

/-!
## La base j=1728 (brique P3+, candidat 3 du P2)

La congruence (36) se lit sur la courbe de Weierstrass d'invariant
`j = 1728`. Cette base construit cette courbe et établit formellement son
invariant j ; le branchement de la suite `a_n` sur la trace de Frobenius de
cette courbe (et la preuve de la congruence sur elle) est la suite de la
brique.
-/

/-- La courbe de Weierstrass courte `y^2 = x^3 + x` (coefficient `a_4 = 1`).
Les cinq coefficients de Weierstrass sont `a₁ a₂ a₃ a₄ a₆` ; ici `a₄ = 1`
et les autres sont nuls. -/
abbrev E1728 (K : Type*) [Field K] : WeierstrassCurve K :=
  ⟨(0 : K), (0 : K), (0 : K), (1 : K), (0 : K)⟩

/-- La courbe `y^2 = x^3 + x` est elliptique : son discriminant `Δ = -64`
est non nul, donc une unité, dans un corps de caractéristique 0. -/
theorem e1728_is_elliptic {K : Type*} [Field K] [CharZero K] :
    WeierstrassCurve.IsElliptic (E1728 K) :=
  ⟨by
    have hne : (E1728 K).Δ ≠ 0 := by
      simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂,
        WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      norm_num
    exact isUnit_iff_ne_zero.mpr hne⟩

/-- L'invariant j de la courbe `y^2 = x^3 + x` vaut 1728.
Pour `y^2 = x^3 + A x + B`, `c₄ = -48·A` et `Δ = -16·(4·A^3 + 27·B^2)` ;
avec `A = 1`, `B = 0`, `c₄ = -48` et `Δ = -64`, et
`j = c₄^3 / Δ = (-48)^3 / (-64) = 1728`. -/
theorem e1728_j_is_1728 {K : Type*} [Field K] [CharZero K]
    [WeierstrassCurve.IsElliptic (E1728 K)] :
    (E1728 K).j = 1728 := by
  have hc₄ : (E1728 K).c₄ = -48 := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄]
    norm_num
  have hΔ : (E1728 K).Δ = -64 := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    norm_num
  simp [WeierstrassCurve.j, WeierstrassCurve.coe_Δ', hΔ, hc₄]
  norm_num

instance : Fact (Nat.Prime 97) := ⟨by decide⟩

/-- La suite binomiale de l'oracle du dépôt, réduite modulo 97. -/
def oracle97 (i : ℕ) : ZMod 97 :=
  ((Nat.factorial (2 * i) / (Nat.factorial i * Nat.factorial (2 * i - i)) : ℕ) : ZMod 97) * 85 ^ i

theorem oracle97_binomial (i : ℕ) :
    oracle97 i = (Nat.choose (2 * i) i : ZMod 97) / 8 ^ i := by
  rw [Nat.choose_eq_factorial_div_factorial (by omega : i ≤ 2 * i)]
  have inv8 : (8 : ZMod 97)⁻¹ = 85 := by
    apply inv_eq_of_mul_eq_one_left
    decide
  unfold oracle97
  rw [div_eq_mul_inv, ← inv_pow, inv8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- La récurrence est vérifiée sur les 24 indices utiles. -/
theorem oracle97_recurrence : ∀ i : Fin 24,
    4 * ((i.val : ZMod 97) + 1) * oracle97 (i.val + 1) =
      (2 * (i.val : ZMod 97) + 1) * oracle97 i.val := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Trois valeurs calculées et un contrôle négatif. -/
theorem oracle97_values :
    oracle97 24 = 79 ∧ (∑ i ∈ range 24, oracle97 i) = 33 ∧
    (∑ i ∈ range 24, (48 + 1 + (i : ZMod 97)) *
      ((2 * (i : ZMod 97) + 1) * oracle97 i)) = 43 ∧
    (43 : ZMod 97) ≠ 4 * 33 := by
  decide

/-- La spécialisation générale s'applique à une suite non nulle. -/
theorem oracle97_quarter :
    (∑ i ∈ range 24, (48 + 1 + (i : ZMod 97)) *
      ((2 * (i : ZMod 97) + 1) * oracle97 i)) =
    4 * (∑ i ∈ range 24, oracle97 i) + (9 / 4 : ZMod 97) * oracle97 24 := by
  apply quarter_point_identity oracle97 48 24
  · decide
  · intro i hi
    exact oracle97_recurrence ⟨i, hi⟩
  · decide
  · decide

end CartierMiller
