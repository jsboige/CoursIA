import Mathlib
import PacLearning.Data
import PacLearning.Sample
import PacLearning.SampleExpect
import PacLearning.UnionBound
import PacLearning.MGF
import PacLearning.BernoulliMGF
import PacLearning.Hoeffding

/-!
# PacLearning.UniformConcentration — concentration uniforme sur une classe finie
## (iter-2 brique 6/6-agnostic, étape a)

Sous-module de `PacLearning` : la **concentration uniforme** de l'erreur empirique sur une
**classe d'hypothèses finie** `Hs`. C'est l'ingrédient-clé du cas **agnostic** du théorème PAC
(le cas réalisable, `m ≥ (1/ε)(ln|H|+ln(1/δ))`, est livré dans `UnionBound.lean` /
`pac_finite_class_bound`, PR #4580).

On prouve :

    ℙ_{S∼D^n} [ ∃ h ∈ Hs, |empError f h S − trueError D f h| ≥ ε ] ≤ 2 · |Hs| · exp(−2·n·ε²).

C'est le **doublement fini** du flagship ponctuel `hoeffding_concentration` (brique 5/5,
`Hoeffding.lean`) : chaque `h ∈ Hs` contribue individuellement `2·exp(−2nε²)` (Hoeffding), et
l'union bound `sampleProb_union_bound` (`UnionBound.lean`) somme ces contributions sur la classe
finie. L'argument ERM (brique 6b, cycle suivant : `ĥ = argmin empError` ⟹ `trueError ĥ ≤
trueError h* + 2ε`) comblera l'écart avec la borne de complexité d'échantillon agnostic finale
`m ≥ (1/ε²)(ln|H|+ln(1/δ))`.

On reste dans le style **ℝ-weight pédagogique** : aucune machine `ℝ≥0∞`/`Measure`/`iIndepFun`.
-/

namespace PacLearning

open Finset
open scoped Classical

variable {X : Type*} [Fintype X]
variable (D : Distribution X)
variable {D}

/-- **Concentration uniforme sur une classe finie d'hypothèses** (brique 6/6-agnostic, étape a) :
pour un concept cible `f`, une classe finie `Hs` d'hypothèses, `n ≥ 1` tirages i.i.d. et `ε > 0`,
la probabilité qu'**il existe** une hypothèse `h ∈ Hs` dont l'erreur empirique dévie de son erreur
vraie d'au moins `ε` est majorée par `2 · |Hs| · exp(−2·n·ε²)`.

    ℙ_{S∼D^n} [ ∃ h ∈ Hs, |empError f h S − trueError D f h| ≥ ε ] ≤ 2 · |Hs| · exp(−2·n·ε²).

C'est le **doublement fini** du flagship ponctuel (brique 5/5, `hoeffding_concentration`) :
chaque `h ∈ Hs` contribue `2·exp(−2nε²)` (Hoeffding ponctuel), et l'union bound
`sampleProb_union_bound` (UnionBound.lean) somme ces contributions sur la classe finie.

Preuve : `sampleProb_union_bound Hs _` (Bornes de Boole) borne `ℙ[∃]` par
`∑_{h∈Hs} ℙ[|empError−trueError| ≥ ε]`, chaque terme est borné par `hoeffding_concentration f h`
(`2·exp(−2nε²)`), puis la somme constante se factorise en `|Hs| · 2·exp(−2nε²)`
(`Finset.sum_const`).

C'est l'ingrédient exact qui, combiné à l'argument ERM (brique 6b), donne la borne de complexité
d'échantillon PAC **agnostique** `m ≥ (1/ε²)(ln|H|+ln(1/δ))` (à comparer au réalisable
`m ≥ (1/ε)(ln|H|+ln(1/δ))`, où le `1/ε` traduit la concentration géométrique `(1−μ)^n ≤ e^{−εn}`
plutôt que la concentration quadratique de Hoeffding). -/
theorem uniform_concentration (f : Hypothesis X) (Hs : Finset (Hypothesis X)) {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) :
    sampleProb D (fun S : Fin n → X ↦ ∃ h ∈ Hs, ε ≤ |empError f h S - trueError D f h|) ≤
      ↑Hs.card * (2 * Real.exp (-(2 * ↑n * ε ^ 2))) := by
  -- (1) Union bound (Bornes de Boole) sur la classe finie :
  --     ℙ[∃ h ∈ Hs, |empError−trueError| ≥ ε] ≤ ∑_{h∈Hs} ℙ[|empError−trueError| ≥ ε].
  have hunion :
      sampleProb D (fun S : Fin n → X ↦ ∃ h ∈ Hs, ε ≤ |empError f h S - trueError D f h|) ≤
        ∑ h ∈ Hs, sampleProb D (fun S : Fin n → X ↦ ε ≤ |empError f h S - trueError D f h|) :=
    sampleProb_union_bound Hs (fun h (S : Fin n → X) ↦ ε ≤ |empError f h S - trueError D f h|)
  -- (2) Chaque terme ≤ 2·exp(−2nε²) (concentration ponctuelle de Hoeffding, brique 5/5).
  have hhoef : ∀ h ∈ Hs,
      sampleProb D (fun S : Fin n → X ↦ ε ≤ |empError f h S - trueError D f h|) ≤
        (2 * Real.exp (-(2 * ↑n * ε ^ 2)) : ℝ) :=
    fun h _ ↦ hoeffding_concentration f h hn hε
  -- (3) Assemblage : borne la somme terme à terme, puis factorise la constante.
  calc sampleProb D (fun S : Fin n → X ↦ ∃ h ∈ Hs, ε ≤ |empError f h S - trueError D f h|)
      ≤ ∑ h ∈ Hs, sampleProb D (fun S : Fin n → X ↦ ε ≤ |empError f h S - trueError D f h|) :=
        hunion
    _ ≤ ∑ h ∈ Hs, (2 * Real.exp (-(2 * ↑n * ε ^ 2)) : ℝ) := by
          exact Finset.sum_le_sum hhoef
    _ = ↑Hs.card * (2 * Real.exp (-(2 * ↑n * ε ^ 2))) := by
          -- `Finset.sum_const` donne `card • c` ; `ring` (via `ring_nf`) normalise le `nsmul`
          -- en multiplication et ferme le but (`push_cast` est inutile, `ring` suffit).
          rw [Finset.sum_const]
          ring

end PacLearning
