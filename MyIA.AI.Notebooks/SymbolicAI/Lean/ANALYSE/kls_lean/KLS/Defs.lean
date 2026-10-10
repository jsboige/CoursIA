import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Socle KLS : log-concavité, isotropie, constantes de Poincaré et Cheeger

Premières pierres du socle manquant identifié par l'audit #19765 (ANALYSE-05) :
au pin Mathlib `v4.32.1` (520045a), aucune des notions de la chaîne
Bizeul–Klartag–Lehec (*Presenting a proof of the Kannan–Lovász–Simonovits
conjecture*, arXiv:2610.05474) n'existe — ni mesure log-concave, ni constante
de Poincaré d'une mesure, ni constante de Cheeger, ni thin-shell.

Ce module pose les **définitions** :

* `IsLogConcaveFun` — log-concavité **fonctionnelle** (convexité de `-log f`)
  sur `EuclideanSpace ℝ (Fin n)` ;
* `IsLogConcaveOnRR` — la même notion sur `ℝ`, pour les tranches ;
* `IsLogConcaveMeasure` — log-concavité **au sens de Borell** (inégalité
  ensembliste `μ(pA+(1-p)B) ≥ μ(A)^p μ(B)^(1-p)`), l'objet que manipule KLS ;
* `IsIsotropicMeasure` — centrage et covariance identité ;
* `poincareConstant` — meilleure constante via le sup des variances des
  fonctions 1-lipschitziennes ;
* `cheegerConstant` — constante isopérimétrique via le rapport mesure de la
  frontière sur la plus petite moitié.

Deux preuves réelles accompagnent les définitions :

* `convexOn_half_sq` — convexité de `t ↦ t²/2` sur `ℝ` (identité
  `a x² + b y² − (ax+by)² = ab (x−y)²` sous `a + b = 1`) ;
* `gaussProfile_logConcave` — le **profil gaussien** `t ↦ exp(−t²/2)` est
  log-concave : `-log(exp(−t²/2)) = t²/2` est convexe. L'extension à la
  densité `n`-dimensionnelle suit de la même identité coordonnée par
  coordonnée ; elle vivra dans un module ultérieur avec l'API somme de
  PiLp.

Les **énoncés** de la chaîne (Théorème 1.1 BKL : `∃ C, C_P(μ) ≤ C` pour toute
log-concave isotrope ; thin-shell Chen–Klartag `Var |X|² ≤ 8n` ; germe
quadratique Letwin) restent volontairement hors du module : leur preuve
n'existe dans aucun lac au pin, et une coquille `sorry` ne se commet pas
(règle anti-régression). Ils vivent en prose et en expérience numérique dans
`ANALYSE-05-KLS-Lean-Python.ipynb`.
-/

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace KLS

variable {n : ℕ}

/-! ## Log-concavité fonctionnelle -/

/-- Log-concavité d'une densité au sens fonctionnel : `-log f` est convexe.
C'est la forme la plus directe — pour une densité positive, elle entraîne la
forme ensembliste de Borell sous des hypothèses de régularité. -/
def IsLogConcaveFun (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ConvexOn ℝ (univ : Set (EuclideanSpace ℝ (Fin n))) fun x => -Real.log (f x)

/-- Log-concavité fonctionnelle sur `ℝ`, pour les tranches unidimensionnelles
d'une densité : `-log f` est convexe. -/
def IsLogConcaveOnRR (f : ℝ → ℝ) : Prop :=
  ConvexOn ℝ (univ : Set ℝ) fun t => -Real.log (f t)

/-- Convexité de `t ↦ t²/2` sur `ℝ`. L'identité clef sous `a + b = 1` :
`a x² + b y² − (a x + b y)² = a b (x − y)² ≥ 0`. Aucun lemme de convexité du
carré n'existe au pin (audit du 2026-10-07) — la preuve est autonome. -/
theorem convexOn_half_sq : ConvexOn ℝ (univ : Set ℝ) fun t => (1 / 2) * t ^ 2 :=
  ⟨convex_univ, by
    intros
    rename_i x _hx y _hy a b ha hb hab
    simp only [smul_eq_mul]
    have hkey : (a * x + b * y) ^ 2 ≤ a * x ^ 2 + b * y ^ 2 := by
      nlinarith [mul_nonneg ha hb, sq_nonneg (x - y), hab]
    calc (1 / 2) * (a * x + b * y) ^ 2
        ≤ (1 / 2) * (a * x ^ 2 + b * y ^ 2) :=
          mul_le_mul_of_nonneg_left hkey (by norm_num)
      _ = a * (1 / 2 * x ^ 2) + b * (1 / 2 * y ^ 2) := by ring⟩

/-- Le profil gaussien `t ↦ exp(−t²/2)` (non normalisé : la constante
`(2π)^(−1/2)` ne joue aucun rôle en log-concavité) est log-concave :
`-log (exp (−t²/2)) = t²/2` est convexe. -/
theorem gaussProfile_logConcave :
    IsLogConcaveOnRR fun t => Real.exp (-(t ^ 2 / 2)) := by
  have hfun : (fun t : ℝ => -Real.log (Real.exp (-(t ^ 2 / 2))))
      = fun t : ℝ => (1 / 2) * t ^ 2 := by
    funext t
    rw [Real.log_exp]
    ring
  unfold IsLogConcaveOnRR
  rw [hfun]
  exact convexOn_half_sq

/-! ## Log-concavité ensembliste (Borell) -/

/-- Log-concavité d'une mesure au sens de Borell : pour tous mesurables `A`,
`B` et tout `p ∈ (0,1)`, la mesure de la combinaison convexe domine le produit
des puissances. C'est la forme que manipule la conjecture KLS. -/
def IsLogConcaveMeasure (μ : Measure (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ (A B : Set (EuclideanSpace ℝ (Fin n))), MeasurableSet A → MeasurableSet B →
    ∀ p : ℝ, 0 < p → p < 1 →
      μ (p • A + (1 - p) • B) ≥ (μ A) ^ p * (μ B) ^ (1 - p)

/-! ## Isotropie -/

/-- Une mesure est isotrope si elle est centrée et de covariance identité :
chaque coordonnée est de moyenne nulle, et `∫ xᵢ xⱼ ∂μ = δᵢⱼ`. C'est la
normalisation sous laquelle l'énoncé KLS `C_P(μ) ≤ C` a un sens. -/
def IsIsotropicMeasure (μ : Measure (EuclideanSpace ℝ (Fin n))) : Prop :=
  (∀ i : Fin n, ∫ x : EuclideanSpace ℝ (Fin n), x i ∂μ = 0) ∧
    (∀ i j : Fin n,
      ∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂μ = if i = j then 1 else 0)

/-! ## Constante de Poincaré -/

/-- Constante de Poincaré d'une mesure : le sup des variances des fonctions
1-lipschitziennes. Pour les mesures où `Var(f) ≤ C_P · E|∇f|²` avec `|∇f| ≤ 1`
pour les 1-lipschitziennes, ce sup EST la meilleure constante. L'énoncé BKL
dit que ce sup est uniformément borné sur les log-concaves isotropes. -/
noncomputable def poincareConstant (μ : Measure (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  sSup {c : ℝ≥0∞ | ∃ f : EuclideanSpace ℝ (Fin n) → ℝ, LipschitzWith 1 f ∧
    c = ENNReal.ofReal (∫ x : EuclideanSpace ℝ (Fin n),
      (f x - (∫ y : EuclideanSpace ℝ (Fin n), f y ∂μ)) ^ 2 ∂μ)}

/-! ## Constante de Cheeger -/

open Classical in
/-- Constante de Cheeger (version frontière) : l'inf sur les mesurables non
triviaux du rapport mesure de la frontière sur la plus petite des deux
moitiés. L'inégalité de Cheeger `C_P ≤ C_Ch²/4` (avec la bonne définition de
la « surface ») relie les deux constantes ; la version frontière ci-dessous en
est la première pierre pédagogique. -/
noncomputable def cheegerConstant (μ : Measure (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨅ A : Set (EuclideanSpace ℝ (Fin n)),
    (if _h : MeasurableSet A ∧ μ A ≠ 0 ∧ μ Aᶜ ≠ 0 then
      μ (frontier A) / min (μ A) (μ Aᶜ)
    else ⊤)

/-! ## Constante de Cheeger, version Minkowski -/

/-- Épaississement (voisinage `ε` au sens de la distance) d'une partie d'un
espace métrique : `A ^ ε = {x | ∃ a ∈ A, dist x a ≤ ε}`. Définition générique
— elle s'applique aussi bien à `ℝ` (exemples unidimensionnels) qu'à
`EuclideanSpace ℝ (Fin n)` (mesures de la conjecture). -/
def thick {X : Type*} [PseudoMetricSpace X] (A : Set X) (ε : ℝ) : Set X :=
  {x | ∃ a ∈ A, dist x a ≤ ε}

/-- Toute partie est contenue dans son épaississement (`dist a a = 0 ≤ ε`). -/
theorem thick_subset {X : Type*} [PseudoMetricSpace X] (A : Set X) (ε : ℝ) (hε : 0 ≤ ε) :
    A ⊆ thick A ε := by
  intro x hx
  exact ⟨x, hx, by simpa using hε⟩

/-- L'épaississement est croissant pour l'inclusion des parties. -/
theorem thick_mono {X : Type*} [PseudoMetricSpace X] {A B : Set X} (h : A ⊆ B) (ε : ℝ) :
    thick A ε ⊆ thick B ε := by
  rintro x ⟨a, ha, hdist⟩
  exact ⟨a, h ha, hdist⟩

/-- L'identité calculatoire de référence : l'épaississement d'un intervalle
compact est l'intervalle épaissi. C'est le calcul qui porte l'exemple exact
unidimensionnel du carnet — pour la mesure uniforme sur `[-1, 1]`, la
dérivée de Minkowski `μ (A ^ ε) - μ A = ε / 2` est constante, et la
constante de Cheeger vaut `1` (atteinte par la moitié `[-1, 0]`). -/
theorem thick_Icc (ε : ℝ) (hε : 0 ≤ ε) :
    thick ((Icc (-1) 1 : Set ℝ)) ε = Icc (-1 - ε) (1 + ε) := by
  ext x
  simp only [thick, mem_setOf_eq, mem_Icc]
  constructor
  · rintro ⟨a, ⟨ha1, ha2⟩, hdist⟩
    rw [Real.dist_eq] at hdist
    have habs : x - a ≤ |x - a| := le_abs_self (x - a)
    have habs' : a - x ≤ |x - a| := by
      rw [abs_sub_comm]
      exact le_abs_self (a - x)
    constructor
    · linarith [ha1, habs', hdist]
    · linarith [ha2, habs, hdist]
  · intro hx
    by_cases hx1 : x < -1
    · refine ⟨-1, ⟨by norm_num, by norm_num⟩, ?_⟩
      rw [Real.dist_eq, abs_of_nonpos (by linarith : x - (-1) ≤ 0)]
      linarith
    · by_cases hx2 : 1 < x
      · refine ⟨1, ⟨by norm_num, by norm_num⟩, ?_⟩
        rw [Real.dist_eq, abs_of_nonneg (by linarith : (0:ℝ) ≤ x - 1)]
        linarith
      · exact ⟨x, ⟨by linarith, by linarith⟩, by simp only [dist_self]; exact hε⟩

/-- Rapport isopérimétrique de Minkowski d'une partie `A` à l'échelle `ε` :
l'accroissement relatif de masse de l'épaississement, normalisé par la plus
petite des deux moitiés. C'est la dérivée discrète dont la limite `ε → 0`
redonne la « surface » pour les mesures continues — là où `μ (frontier A)`
est nul et la version `cheegerConstant` s'effondre. -/
noncomputable def minkowskiRatio (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (A : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ) : ℝ≥0∞ :=
  (μ (thick A ε) - μ A) / (ENNReal.ofReal ε * min (μ A) (μ Aᶜ))

open Classical in
/-- Constante de Cheeger au sens de Minkowski : l'inf sur les parties non
triviales de la limite supérieure du rapport isopérimétrique quand `ε → 0`
par valeurs positives. Pour une mesure à densité, c'est la constante
d'isopérimétrie sensible (théorème de Bobkov–Houdré : en dimension 1,
`h = f(m)` au point médian `m`) ; l'inégalité de Cheeger relie `h` à la
constante de Poincaré (`C_P ≤ D / h²`, `D` constante de dimension). C'est
la version que le grain 2 du carnet incarne expérimentalement. -/
noncomputable def cheegerMinkowski (μ : Measure (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨅ A : Set (EuclideanSpace ℝ (Fin n)),
    (if _h : MeasurableSet A ∧ μ A ≠ 0 ∧ μ Aᶜ ≠ 0 then
      Filter.limsup (fun ε : ℝ => minkowskiRatio μ A ε) (nhdsWithin (0:ℝ) (Ioi (0:ℝ)))
    else ⊤)

end KLS
