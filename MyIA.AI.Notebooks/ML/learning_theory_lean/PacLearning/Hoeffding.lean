import Mathlib
import PacLearning.Data
import PacLearning.Sample
import PacLearning.SampleExpect
import PacLearning.UnionBound

/-!
# PacLearning.Hoeffding — concentration de Hoeffding-for-Bernoulli (brique 2c/3, en cours)

Sous-module de `PacLearning` : la **moitié analytique** du flagship
`pac_finite_class_bound` (l'autre moitié, combinatoire = union bound, est livrée dans
`UnionBound.lean`). On prouve la **concentration de Hoeffding** pour la moyenne
d'indicateurs i.i.d. :

    ℙ_S [ |empError − trueError| > ε ] ≤ 2·exp(−2·n·ε²).

Méthode de Chernoff (ℝ-weight pédagogique, pas le cadre Mathlib Kernel/Measure) :

1. **Chernoff-Markov** (ce livrable, brique 1/5) — `ℙ[Y ≥ a] ≤ e^{−t·a}·E[e^{t·Y}]` pour
   `t > 0` : Markov sur la variable positive `Z = e^{t·Y}` au seuil `e^{t·a}`, via
   `{Z ≥ e^{t·a}} = {Y ≥ a}` (car `x ↦ e^{t·x}` strictement croissante pour `t > 0`).
2. **MGF Bernoulli** (OPEN, brique 2/5) — `E_D[exp(t·(ind − μ))] ≤ exp(t²/8)` (lemme de
   Hoeffding, `X ∈ [0,1]` ⟹ variance `≤ 1/4` ⟹ log-MGF `≤ t²/8`).
3. **Indépendance produit** (OPEN, brique 3/5) — `E_S[exp(t·Σᵢ(ind(Sᵢ) − μ))] =
   ∏ᵢ E_D[...] ≤ exp(n·t²/8)` (technique `sampleExpect_coord` étendue aux produits).
4. **Optimisation** (OPEN, brique 4/5) — `min_t e^{−t·n·ε}·e^{n·t²/8} = e^{−2·n·ε²}`
   (atteint en `t = 4ε`).
5. **Bilatéral** (OPEN, brique 5/5) — `|empError − trueError| ≥ ε = (· ≥ ε) ∪ (· ≤ −ε)` →
   borne `· 2` via `sampleProb_union_bound` (UnionBound.lean).

Ce livrable pose la **brique 1 (Chernoff-Markov)** `chernoff_ineq`, ingrédient fondamental
de toute la chaîne, entièrement prouvé (0 sorry). On reste dans le style **ℝ-weight
pédagogique** : la probabilité est une somme pondérée (`sampleProb`), l'espérance aussi
(`sampleExpect`), et la méthode de Chernoff ne fait appel qu'à la monotonie de
`sampleExpect` et à la croissance de l'exponentielle.
-/

namespace PacLearning

open Finset
open scoped Classical

variable {X : Type*} [Fintype X]
variable (D : Distribution X)
variable {D}

/-- **Linéarité en un facteur scalaire à droite** : `E[g · c] = E[g] · c` (le scalaire
sort de la somme pondérée via `Finset.sum_mul`). Variante à droite de `sampleExpect_smul`
(qui sort le scalaire à gauche). Réutilisé par `chernoff_ineq` (pour factoriser la
constante `e^{−t·a}` hors de l'espérance de `e^{t·Y}`). -/
theorem sampleExpect_mul_const {n : ℕ} (c : ℝ) (g : (Fin n → X) → ℝ) :
    sampleExpect D (fun S ↦ g S * c) = sampleExpect D g * c := by
  dsimp only [sampleExpect]
  simp only [show ∀ S, sampleWeight D S * (g S * c) = (sampleWeight D S * g S) * c from
               fun _ ↦ by ring]
  rw [← Finset.sum_mul]

/-- **Chernoff-Markov (inégalité de Chernoff sur l'exponentielle)** : pour `t > 0`, la
probabilité que `Y ≥ a` est majorée par `e^{−t·a} · E[e^{t·Y}]`.

    ℙ_S [ Y S ≥ a ] ≤ e^{−t·a} · E_{S∼D^m} [ e^{t·Y S} ].

C'est Markov appliqué à la variable positive `Z = e^{t·Y}` au seuil `e^{t·a}` :
`{Z ≥ e^{t·a}} = {Y ≥ a}` (car `x ↦ e^{t·x}` est strictement croissante pour `t > 0`),
donc `ℙ[Y ≥ a] = ℙ[Z ≥ e^{t·a}] ≤ E[Z] / e^{t·a} = e^{−t·a} · E[e^{t·Y}]`.

Preuve directe en ℝ-weight : point par point, l'indicateur `𝟙{a ≤ Y S}` est
`≤ e^{t·(Y S − a)}` (cas `a ≤ Y` : `t·(Y−a) ≥ 0` ⟹ `e^{t·(Y−a)} ≥ e⁰ = 1 = 𝟙` par
croissance de l'exponentielle ; cas `¬(a ≤ Y)` : `𝟙 = 0 ≤ e^{...}`, l'exponentielle étant
strictement positive). On passe alors par `sampleExpect` (monotonie `sampleExpect_mono`),
puis on factorise `e^{t·(Y−a)} = e^{t·Y} · e^{−t·a}` (`Real.exp_add`) où `e^{−t·a}` est
constant en `S`, sorti via `sampleExpect_mul_const`.

C'est l'**ingrédient #1** de la concentration de Hoeffding (brique 1/5) : borne
générique de Chernoff, valable pour toute fonction `Y : (Fin n → X) → ℝ`, indépendante
de la structure Bernoulli (qui n'intervient qu'à la brique 2 via la MGF). -/
theorem chernoff_ineq {n : ℕ} (Y : (Fin n → X) → ℝ) (a : ℝ) (t : ℝ) (ht : 0 < t) :
    sampleProb D (fun S ↦ a ≤ Y S) ≤
      sampleExpect D (fun S ↦ Real.exp (t * Y S)) * Real.exp (-(t * a)) := by
  -- (1) Point par point : `𝟙{a ≤ Y S} ≤ e^{t·(Y S − a)}` (le seul `if`, isolé dans un
  -- `have` hors du calc des sommes, évitant les frictions d'instance `Decidable`).
  have hind : ∀ S : Fin n → X,
      (if a ≤ Y S then (1 : ℝ) else 0) ≤ Real.exp (t * (Y S - a)) := by
    intro S
    by_cases h : a ≤ Y S
    · -- `Y ≥ a` ⟹ `t·(Y−a) ≥ 0` ⟹ `e^{t·(Y−a)} ≥ e⁰ = 1`.
      rw [if_pos h, ← Real.exp_zero]
      exact Real.exp_le_exp.mpr
        (mul_nonneg (le_of_lt ht) (sub_nonneg.mpr h))
    · -- `Y < a` ⟹ `𝟙 = 0 ≤ e^{...}` (exponentielle strictement positive).
      rw [if_neg h]
      exact (Real.exp_pos _).le
  -- (2) `e^{t·(Y−a)} = e^{t·Y} · e^{−t·a}` point par point (`Real.exp_add`).
  have hexp : ∀ S : Fin n → X,
      Real.exp (t * (Y S - a)) = Real.exp (t * Y S) * Real.exp (-(t * a)) := by
    intro S
    rw [show t * (Y S - a) = t * Y S + (-(t * a)) from by ring, Real.exp_add]
  -- (3) Assemblage : `ℙ = E[𝟙] ≤ E[e^{t(Y−a)}] = E[e^{tY}·e^{−ta}] = e^{−ta}·E[e^{tY}]`.
  calc sampleProb D (fun S ↦ a ≤ Y S)
      = sampleExpect D (fun S ↦ (if a ≤ Y S then (1 : ℝ) else 0)) :=
          sampleProb_eq_sampleExpect _
    _ ≤ sampleExpect D (fun S ↦ Real.exp (t * (Y S - a))) :=
        sampleExpect_mono hind
    _ = sampleExpect D (fun S ↦ Real.exp (t * Y S) * Real.exp (-(t * a))) :=
        congr_arg (sampleExpect D) (funext hexp)
    _ = sampleExpect D (fun S ↦ Real.exp (t * Y S)) * Real.exp (-(t * a)) :=
        sampleExpect_mul_const (Real.exp (-(t * a))) (fun S ↦ Real.exp (t * Y S))

end PacLearning
