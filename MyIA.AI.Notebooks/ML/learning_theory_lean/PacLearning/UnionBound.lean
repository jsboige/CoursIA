import Mathlib
import PacLearning.Data
import PacLearning.Sample
import PacLearning.SampleExpect

/-!
# PacLearning.UnionBound — probabilité d'échantillon + union bound (Bornes de Boole)

Sous-module de `PacLearning` : la **moitié combinatoire** du flagship
`pac_finite_class_bound`. On définit la **probabilité d'un événement** sur
l'espace des échantillons `Fin n → X` (sous la distribution produit `D^m`) et on
prouve l'**union bound** (inégalité de Boole) sur une classe finie d'hypothèses.

    sampleProb D (Q : (Fin n → X) → Prop) := ∑ S, sampleWeight D S · 𝟙{Q S}

L'union bound dit que la probabilité d'une union d'événements est **majorée** par
la somme des probabilités :

    ℙ_S [ ∃ h ∈ H, Q h S ] ≤ ∑_{h ∈ H} ℙ_S [ Q h S ].

C'est l'ingrédient combinatoire de la borne de Valiant : pour borner la probabilité
qu'**au moins une** hypothèse de `H` dévie de son erreur vraie, on somme les
probabilités de déviation (chacune bornée par Hoeffding, brique 2c/3-concentration,
encore OPEN). Le flagship `pac_finite_class_bound` (brique 3/3) combine
l'`union_bound` ci-dessous avec une concentration Hoeffding générique.

On reste dans le style **ℝ-weight pédagogique** (pas de `ℝ≥0∞` / `Measure`) :
l'indicateur `𝟙{Q S}` est `if Q S then (1 : ℝ) else 0`, et la probabilité est une
somme pondérée (l'espérance de l'indicateur, `sampleExpect D (𝟙 ∘ Q)`).
-/

namespace PacLearning

open Finset
open scoped Classical

variable {X : Type*} [Fintype X]
variable (D : Distribution X)

/-- **Probabilité d'un événement** sur l'espace des échantillons `Fin n → X` sous
`D^m` : somme pondérée de l'indicateur `𝟙{Q S}`. C'est l'espérance empirique de
l'indicateur de `Q` (cf `sampleExpect`). Le domaine `Fin n → X` de `Q` pinne `n`. -/
noncomputable def sampleProb {n : ℕ} (Q : (Fin n → X) → Prop) [DecidablePred Q] : ℝ :=
  ∑ S : Fin n → X, sampleWeight D S * (if Q S then (1 : ℝ) else 0)

variable {D}

/-- Lien avec `sampleExpect` : la probabilité de `Q` est l'espérance empirique de
l'indicateur `𝟙{Q}`. Pont entre probabilité (mesure) et espérance (linéaire). -/
theorem sampleProb_eq_sampleExpect {n : ℕ} (Q : (Fin n → X) → Prop) [DecidablePred Q] :
    sampleProb D Q = sampleExpect D (fun S ↦ if Q S then (1 : ℝ) else 0) := by
  rfl

/-- La probabilité est non négative (somme de poids `≥ 0` fois `0` ou `1`). -/
theorem sampleProb_nonneg {n : ℕ} (Q : (Fin n → X) → Prop) [DecidablePred Q] :
    0 ≤ sampleProb D Q := by
  dsimp only [sampleProb]
  apply sum_nonneg
  intro S _
  exact mul_nonneg (sampleWeight_nonneg (D := D) S) (by
    by_cases h : Q S <;> simp [h])

/-- La probabilité est au plus `1` (masse totale des échantillons `= 1` par
`sampleWeight_sum_one`, et chaque indicateur est `≤ 1`). -/
theorem sampleProb_le_one {n : ℕ} (Q : (Fin n → X) → Prop) [DecidablePred Q] :
    sampleProb D Q ≤ 1 := by
  dsimp only [sampleProb]
  have h_le : ∀ S, sampleWeight D S * (if Q S then (1 : ℝ) else 0) ≤ sampleWeight D S := by
    intro S
    by_cases h : Q S
    · simp [h]
    · simp [h]; exact sampleWeight_nonneg (D := D) S
  calc ∑ S : Fin n → X, sampleWeight D S * (if Q S then (1 : ℝ) else 0)
      ≤ ∑ S : Fin n → X, sampleWeight D S := sum_le_sum (fun S _ ↦ h_le S)
    _ = 1 := sampleWeight_sum_one n

/-- **Probabilité du complémentaire** : `ℙ[¬Q] = 1 − ℙ[Q]` (l'indicateur du
complément est `1 − 𝟙{Q}`, et `E[1] = 1` par `sampleExpect_const`). -/
theorem sampleProb_compl {n : ℕ} (Q : (Fin n → X) → Prop) [DecidablePred Q]
    [DecidablePred (fun S ↦ ¬ Q S)] :
    sampleProb D (fun S ↦ ¬ Q S) = 1 - sampleProb D Q := by
  -- Indicateur du complément = `1 − indicateur` point par point.
  have hind : ∀ S : Fin n → X,
      sampleWeight D S * (if ¬ Q S then (1 : ℝ) else 0) =
        sampleWeight D S * 1 - sampleWeight D S * (if Q S then (1 : ℝ) else 0) := by
    intro S
    by_cases h : Q S <;> simp [h]
  dsimp only [sampleProb]
  rw [Finset.sum_congr rfl (fun S _ ↦ hind S), Finset.sum_sub_distrib,
      ← Finset.sum_mul, sampleWeight_sum_one, one_mul]

/-- **Linéarité en une somme Finset-indexée** : l'espérance empirique d'une somme
indexée par un `Finset` est la somme des espérances (comme `sampleExpect_sum` mais
sur `s : Finset ι` plutôt que sur tout `ι`). Pas d'instance `Decidable` en jeu
(`F : ι → ℝ`, on ne manipule pas d'indicateurs). -/
theorem sampleExpect_finset_sum {ι : Type*} [Fintype ι] {n : ℕ}
    (s : Finset ι) (F : ι → ((Fin n → X) → ℝ)) :
    sampleExpect D (fun S ↦ ∑ i ∈ s, F i S) = ∑ i ∈ s, sampleExpect D (F i) := by
  dsimp only [sampleExpect]
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

/-- **Union bound (Bornes de Boole)** sur un `Finset` indexé : la probabilité qu'un
échantillon `S` satisfasse `P i S` pour **au moins un** `i ∈ s` est majorée par la
somme des probabilités `ℙ[P i]`.

Preuve : point par point, l'indicateur `𝟙{∃ i ∈ s, P i S}` est `≤ ∑_i 𝟙{P i S}`
(si un témoin `i₀` existe, il contribue `1` à la somme, et les autres termes sont
`≥ 0` ; sinon l'indicateur vaut `0`). On passe alors par `sampleExpect` :
`ℙ[∃] = E[𝟙_{∃}] ≤ E[∑ 𝟙_{P i}]` (monotonie) `= ∑ E[𝟙_{P i}]` (linéarité Finset)
`= ∑ ℙ[P i]`. La monotonie isole le seul indicateur (`if`) dans un `have`, hors du
calc des sommes — évitant les frictions d'instance `Decidable` dans les sommes
pondérées. -/
theorem sampleProb_union_bound {n : ℕ} {ι : Type*} [Fintype ι] (s : Finset ι) [DecidableEq ι]
    (P : ι → ((Fin n → X) → Prop)) :
    sampleProb D (fun S ↦ ∃ i ∈ s, P i S) ≤ ∑ i ∈ s, sampleProb D (P i) := by
  -- `open scoped Classical` (en tête de namespace) fournit `Decidable` pour tout
  -- prédicat : la décidabilité est un détail computationnel, pas mathématique (la
  -- probabilité d'un événement ne dépend pas de savoir décider le prédicat). C'est
  -- l'idiome Mathlib standard pour les résultats probabilistes.
  -- Indicateur(∃) ≤ ∑ indicateurs(P i), point par point (le seul `if` de la preuve).
  have hind_le : ∀ S : Fin n → X,
      (if ∃ i ∈ s, P i S then (1 : ℝ) else 0) ≤ ∑ i ∈ s, (if P i S then 1 else 0) := by
    intro S
    by_cases h : ∃ i ∈ s, P i S
    · -- Un témoin `i₀` existe : il contribue `1` à la somme, les autres `≥ 0`.
      obtain ⟨i₀, hi₀, hPi₀⟩ := h
      -- Tous les indicateurs sont `≥ 0`.
      have hge : ∀ i ∈ s, 0 ≤ (if P i S then (1 : ℝ) else 0) := fun i _ ↦ by
        by_cases hpi : P i S <;> simp [hpi]
      calc (if ∃ i ∈ s, P i S then (1 : ℝ) else 0)
          = 1 := if_pos ⟨i₀, hi₀, hPi₀⟩
        _ = (if P i₀ S then 1 else 0) := (if_pos hPi₀).symm
        _ ≤ ∑ i ∈ s, (if P i S then 1 else 0) := Finset.single_le_sum hge hi₀
    · -- Aucun témoin : indicateur(∃) = `0 ≤` somme (de termes `≥ 0`).
      simp only [if_neg h]
      exact sum_nonneg (fun i _ ↦ by by_cases hpi : P i S <;> simp [hpi])
  -- Assemblage via `sampleExpect` (monotonie + linéarité Finset), sans `if`
  -- dans les sommes pondérées.
  calc sampleProb D (fun S ↦ ∃ i ∈ s, P i S)
      = sampleExpect D (fun S ↦ (if ∃ i ∈ s, P i S then (1 : ℝ) else 0)) :=
          sampleProb_eq_sampleExpect _
    _ ≤ sampleExpect D (fun S ↦ ∑ i ∈ s, (if P i S then (1 : ℝ) else 0)) :=
        sampleExpect_mono hind_le
    _ = ∑ i ∈ s, sampleExpect D (fun S ↦ (if P i S then (1 : ℝ) else 0)) :=
        sampleExpect_finset_sum s _
    _ = ∑ i ∈ s, sampleProb D (P i) := by
          exact Finset.sum_congr rfl (fun i _ ↦ (sampleProb_eq_sampleExpect (P i)).symm)

end PacLearning
