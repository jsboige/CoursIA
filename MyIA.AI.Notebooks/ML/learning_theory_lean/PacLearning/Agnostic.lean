import Mathlib
import PacLearning.Data
import PacLearning.Sample
import PacLearning.SampleExpect
import PacLearning.UnionBound
import PacLearning.MGF
import PacLearning.BernoulliMGF
import PacLearning.Hoeffding
import PacLearning.UniformConcentration
import PacLearning.ERM

/-!
# PacLearning.Agnostic — borne de généralisation PAC agnostic (flagship iter-2)
## assemblage uniform_concentration + erm_error_bound

Sous-module de `PacLearning` : le **flagship agnostic** de l'itération 2 — la borne de
généralisation PAC pour une classe d'hypothèses finie `Hs` dans le régime **agnostic**
(l'hypothèse cible `f` n'est pas nécessairement dans `Hs`). On prouve que, pour un ERM `ĥ`
(sélectionné en fonction de l'échantillon `S`) et toute hypothèse de référence `hOpt ∈ Hs`,

    ℙ_{S∼D^n} [ trueError D f (ĥ S) ≤ trueError D f hOpt + 2·ε ] ≥ 1 − 2·|Hs|·exp(−2·n·ε²).

C'est la **borne de généralisation agnostic** : avec probabilité ≥ 1−δ sur l'échantillon,
l'erreur vraie de l'ERM ne dépasse pas celle de la meilleure hypothèse de la classe de plus de
`2ε`. En spécialisant `hOpt` à `argmin_{h∈Hs} trueError D f h` (le meilleur de la classe), cela
donne le théorème de généralisation standard. En inversant `1−δ = 1−2|Hs|exp(−2nε²)`, on obtient
la complexité d'échantillon PAC **agnostique** `m ≥ (1/ε²)(ln|H|+ln(1/δ))` — à comparer au
réalisable `m ≥ (1/ε)(ln|H|+ln(1/δ))` (`pac_finite_class_bound`, PR #4580), où le facteur `1/ε`
(vs `1/ε²`) traduit la concentration géométrique `(1−μ)^n ≤ e^{−εn}` plutôt que la concentration
quadratique de Hoeffding.

**Assemblage** (les deux ingrédients sont livrés sur main) :
1. `uniform_concentration` (UniformConcentration.lean, brique 6a) borne la probabilité du
   « mauvais » événement (il existe une hypothèse mal concentrée) :
   `ℙ[∃ h ∈ Hs, ε ≤ |empError − trueError|] ≤ 2·|Hs|·exp(−2nε²)`.
2. `erm_error_bound` (ERM.lean, brique 6b) est l'argument déterministe : sur le « bon »
   événement (`∀ h ∈ Hs, |empError − trueError| ≤ ε`), l'ERM généralise :
   `trueError(ĥ) ≤ trueError(hOpt) + 2ε`.
3. Ce module connecte les deux : par contraposée de `erm_error_bound`, l'événement
   `trueError(ĥ) > trueError(hOpt) + 2ε` implique `∃ h ∈ Hs, ε < |empError − trueError|`
   (la concentration uniforme a échoué), qui est inclus dans l'événement borné par
   `uniform_concentration`. D'où `ℙ[trueError(ĥ) > ...] ≤ 2|Hs|exp(...)`, et par passage au
   complément `ℙ[trueError(ĥ) ≤ ...] ≥ 1 − 2|Hs|exp(...)`.

On reste dans le style **ℝ-weight pédagogique** : aucune machine `ℝ≥0∞`/`Measure`/`iIndepFun`.
-/

namespace PacLearning

open Finset
open scoped Classical

variable {X : Type*} [Fintype X]
variable (D : Distribution X)
variable {D}

/-- **Monotonie de `sampleProb` par inclusion d'événements** : si `P S ⟹ Q S` pour tout
échantillon `S`, alors `ℙ[P] ≤ ℙ[Q]` (l'indicateur `𝟙_P ≤ 𝟙_Q` point par point, puis monotonie
de la somme pondérée). Utilisée par `pac_agnostic_generalization` pour remonter l'inclusion
`{mauvaise conclusion} ⊆ {mauvaise concentration uniforme}` à une inégalité de probabilités. -/
theorem sampleProb_mono {n : ℕ} (P Q : (Fin n → X) → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ S, P S → Q S) : sampleProb D P ≤ sampleProb D Q := by
  -- Indicateur `𝟙_P ≤ 𝟙_Q` point par point (le seul `if`, isolé hors des sommes).
  have hind : ∀ S : Fin n → X,
      (if P S then (1 : ℝ) else 0) ≤ (if Q S then (1 : ℝ) else 0) := by
    intro S
    by_cases hP : P S
    · -- `P S` ⟹ `Q S` (par `h`) ⟹ `𝟙_P = 1 = 𝟙_Q`.
      have hQ : Q S := h S hP
      simp [hP, hQ]
    · -- `¬ P S` ⟹ `𝟙_P = 0 ≤ 𝟙_Q` (indicateur `≤ 1`).
      by_cases hQ : Q S <;> simp [hP, hQ]
  -- Assemblage : on multiplie l'inégalité d'indicateurs par le poids `≥ 0` (point par point),
  -- puis monotonie de la somme pondérée.
  dsimp only [sampleProb]
  exact sum_le_sum (fun S _ ↦ mul_le_mul_of_nonneg_left (hind S) (sampleWeight_nonneg (D := D) S))

/-- **Flagship agnostic — borne de généralisation PAC** (iter-2 capstone) : pour `n ≥ 1` tirages
i.i.d. et `ε > 0`, un ERM `ĥ` (sélectionné en fonction de l'échantillon `S`, minimisant l'erreur
empirique sur `Hs`) a une erreur vraie contrôlée par celle de n'importe quelle hypothèse de
référence `hOpt ∈ Hs`, à `2ε` près, **avec haute probabilité** sur l'échantillon :

    ℙ_{S∼D^n} [ trueError D f (ĥ S) ≤ trueError D f hOpt + 2·ε ] ≥ 1 − 2·|Hs|·exp(−2·n·ε²).

**Spécialisation** : en prenant `hOpt = argmin_{h∈Hs} trueError D f h` (la meilleure hypothèse de
la classe), la borne dit que l'ERM ne fait pas plus de `2ε` de pire que l'optimum de la classe,
avec probabilité ≥ 1−δ — le théorème de généralisation agnostic standard. En inversant
`δ = 2·|Hs|·exp(−2·n·ε²)`, on obtient la complexité d'échantillon PAC **agnostique**
`m ≥ (1/ε²)(ln|H|+ln(1/δ))`.

**Modélisation de l'ERM** : `ĥ : (Fin n → X) → Hypothesis X` est une fonction de sélection (à
chaque échantillon `S`, elle renvoie une hypothèse ERM sur `S`), avec les deux hypothèses
naturelles `hĥ_mem` (l'ERM est dans la classe) et `hĥ_erm` (elle minimise l'erreur empirique). On
n'a pas besoin de construire l'argmin (existence via `Finset` est déléguée) — on raisonne sur
n'importe quelle sélection ERM.

Preuve (assemblage de `uniform_concentration` + `erm_error_bound`) :
1. **Contraposée de l'ERM** : sur l'événement « mauvaise conclusion » `trueError(ĥ S) >
   trueError(hOpt) + 2ε`, la concentration uniforme a nécessairement échoué, i.e.
   `∃ h ∈ Hs, ε ≤ |empError − trueError|` (sinon `erm_error_bound` donnerait la conclusion).
   C'est l'inclusion `{mauvaise conclusion} ⊆ {mauvaise concentration}`.
2. **Monotonie** (`sampleProb_mono`) : `ℙ[mauvaise conclusion] ≤ ℙ[mauvaise concentration]`.
3. **Concentration uniforme** (`uniform_concentration`) : `ℙ[mauvaise concentration] ≤ 2|Hs|exp(...)`.
4. **Complément** (`sampleProb_compl`) : `ℙ[bonne conclusion] = 1 − ℙ[mauvaise conclusion] ≥ 1 − 2|Hs|exp(...)`. -/
theorem pac_agnostic_generalization (f : Hypothesis X) (Hs : Finset (Hypothesis X)) {n : ℕ}
    (hn : 0 < n) {ε : ℝ} (hε : 0 < ε)
    (ĥ : (Fin n → X) → Hypothesis X) (hOpt : Hypothesis X) (hOpt_mem : hOpt ∈ Hs)
    (hĥ_mem : ∀ S, ĥ S ∈ Hs)
    (hĥ_erm : ∀ S, ∀ h ∈ Hs, empError f (ĥ S) S ≤ empError f h S) :
    1 - ↑Hs.card * (2 * Real.exp (-(2 * ↑n * ε ^ 2))) ≤
      sampleProb D (fun S : Fin n → X ↦ trueError D f (ĥ S) ≤ trueError D f hOpt + 2 * ε) := by
  -- (1) Contraposée de l'ERM : « mauvaise conclusion » ⟹ « mauvaise concentration ».
  --   Si `trueError(ĥ) > trueError(hOpt)+2ε`, alors la concentration uniforme a échoué
  --   (sinon `erm_error_bound` contredirait). D'où `∃ h ∈ Hs, ε ≤ |empError−trueError|`.
  have hcontra : ∀ S : Fin n → X,
      (trueError D f (hOpt) + 2 * ε < trueError D f (ĥ S)) →
        ∃ h ∈ Hs, ε ≤ |empError f h S - trueError D f h| := by
    intro S hbad
    -- Par l'absurde : supposons la concentration uniforme tenir sur tout `Hs`.
    by_contra hno
    -- `hno : ¬(∃ h ∈ Hs, ε ≤ |...|)`. On en déduit `∀ h ∈ Hs, |...| ≤ ε` (concentration).
    have hconc : ∀ h ∈ Hs, |empError f h S - trueError D f h| ≤ ε := by
      intro h hHs
      -- `¬(ε ≤ |...|)` ⟺ `|...| < ε` (via `not_le`) ⟹ `|...| ≤ ε`.
      have : ¬(ε ≤ |empError f h S - trueError D f h|) := by
        intro hh; exact hno ⟨h, hHs, hh⟩
      linarith [not_le.mp this]
    -- `erm_error_bound` (brique 6b) : sur le bon événement, `trueError(ĥ) ≤ trueError(hOpt)+2ε`.
    have herb := erm_error_bound f Hs hn S hε (ĥ S) hOpt (hĥ_mem S) hOpt_mem hconc (hĥ_erm S)
    -- Contradiction avec `hbad : trueError(hOpt)+2ε < trueError(ĥ)`.
    linarith
  -- (2) Monotonie : `ℙ[mauvaise conclusion] ≤ ℙ[mauvaise concentration]`.
  --   On donne le type au `have` car `D` (variable de section implicite de `sampleProb_mono`)
  --   n'apparaît que dans la conclusion, pas dans les args `P`/`Q` — donc non-synthétisable
  --   depuis les seuls prédicats ; le type fourni permet l'unification de `D`.
  have hmono :
      sampleProb D (fun S : Fin n → X ↦ trueError D f (hOpt) + 2 * ε < trueError D f (ĥ S)) ≤
        sampleProb D (fun S : Fin n → X ↦ ∃ h ∈ Hs, ε ≤ |empError f h S - trueError D f h|) :=
    sampleProb_mono _ _ hcontra
  -- `C = 2|Hs|exp(...)` la borne.
  set C : ℝ := ↑Hs.card * (2 * Real.exp (-(2 * ↑n * ε ^ 2)))
  -- (3) Concentration uniforme (brique 6a) : `ℙ[mauvaise concentration] ≤ C`.
  --   `uniform_concentration` a `D` implicite (section var) et le prédicat `∃ h ∈ Hs, ...`
  --   est figé dans son énoncé — on ne passe donc QUE `f Hs hn hε`. Type explicite au `have`
  --   pour unifier `D` (non-synthétisable depuis les seuls args `f Hs hn hε`).
  have hunif :
      sampleProb D (fun S : Fin n → X ↦ ∃ h ∈ Hs, ε ≤ |empError f h S - trueError D f h|) ≤ C :=
    uniform_concentration f Hs hn hε
  -- (4) Complément : `ℙ[¬(mauvaise conclusion)] = 1 − ℙ[mauvaise conclusion]` (`sampleProb_compl`).
  --   La bonne conclusion `trueError(ĥ S) ≤ ...` est exactement `¬(mauvaise conclusion)`.
  have hcompl :
      sampleProb D (fun S : Fin n → X ↦ ¬(trueError D f (hOpt) + 2 * ε < trueError D f (ĥ S))) =
        1 - sampleProb D (fun S : Fin n → X ↦ trueError D f (hOpt) + 2 * ε < trueError D f (ĥ S)) :=
    sampleProb_compl _
  -- Assemblage : `ℙ[mauvaise conclusion] ≤ ℙ[mauvaise concentration] ≤ C`, donc
  -- `ℙ[bonne conclusion] = 1 − ℙ[mauvaise conclusion] ≥ 1 − C`.
  have hbad_le_C :
      sampleProb D (fun S : Fin n → X ↦ trueError D f (hOpt) + 2 * ε < trueError D f (ĥ S)) ≤ C :=
    le_trans hmono hunif
  -- `ℙ[bonne] = 1 − ℙ[mauvaise] ≥ 1 − C` (arithmétique finale) :
  --   `¬bad ↔ good` point par point (`not_le`), donc `sampleProb_congr` transporte les probabilités.
  calc 1 - C
      ≤ 1 - sampleProb D (fun S : Fin n → X ↦ trueError D f (hOpt) + 2 * ε < trueError D f (ĥ S)) := by
            linarith [hbad_le_C]
    _ = sampleProb D (fun S : Fin n → X ↦ ¬(trueError D f (hOpt) + 2 * ε < trueError D f (ĥ S))) :=
          hcompl.symm
    _ = sampleProb D (fun S : Fin n → X ↦ trueError D f (ĥ S) ≤ trueError D f hOpt + 2 * ε) :=
          sampleProb_congr _ _ (fun S ↦ ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩)

end PacLearning
