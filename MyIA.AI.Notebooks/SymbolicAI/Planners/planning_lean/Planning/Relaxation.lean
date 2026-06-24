import Mathlib
import Planning.Strips

/-!
# Planning.Relaxation — exécution relaxée des plans, atteignabilité monotone

La **relaxation sans-delete** (h⁺) ignore les effets `del` des actions STRIPS :
`stepR a s = s ∪ a.add`. On définit l'**exécution relaxée** `runR` d'une séquence
d'actions et l'**exécution réelle** `run` (qui applique `del`).

Le fait central est la **monotonie de l'atteignabilité relaxée** : un état initial plus
grand ne peut qu'élargir l'ensemble atteignable (`runR_mono`). Cette monotonie est ce qui
rend la résolution du plan relaxé **polynomiale** (atteignabilité croissante → calcul de
point fixe en temps polynomial) et garantit l'admissibilité h⁺ ≤ h* (prouvée dans
`Admissibility.lean`). Voir l'issue #4053.
-/

namespace PlanningLean

open PlanningLean

variable {F : Type} [DecidableEq F]

/-- Exécution **réelle** d'un plan (séquence d'actions) depuis l'état initial `s`. -/
def run : List (Action F) → State F → State F
  | [], s => s
  | a :: π, s => run π (step a s)

/-- Exécution **relaxée** (sans-delete) d'un plan depuis `s`. -/
def runR : List (Action F) → State F → State F
  | [], s => s
  | a :: π, s => runR π (stepR a s)

/-- Un plan `π` **atteint** le but `g` depuis `s` (exécution réelle). -/
def reaches (π : List (Action F)) (s g : State F) : Prop := goalSatisfied g (run π s)

/-- Un plan `π` atteint `g` depuis `s` (exécution relaxée). -/
def reachesR (π : List (Action F)) (s g : State F) : Prop := goalSatisfied g (runR π s)

/-- Monotonie de l'exécution réelle : `s ⊆ s'` entraîne `run π s ⊆ run π s'`. -/
lemma run_mono (π : List (Action F)) {s s' : State F} (h : s ⊆ s') : run π s ⊆ run π s' := by
  induction π generalizing s s' with
  | nil => exact h
  | cons a π ih => exact ih (step_mono a h)

/-- **Monotonie de l'atteignabilité relaxée** : `s ⊆ s'` entraîne `runR π s ⊆ runR π s'`.
    C'est ce qui rend le calcul du plan relaxé polynomial (atteignabilité croissante). -/
theorem runR_mono (π : List (Action F)) {s s' : State F} (h : s ⊆ s') :
    runR π s ⊆ runR π s' := by
  induction π generalizing s s' with
  | nil => exact h
  | cons a π ih => exact @ih (stepR a s) (stepR a s') (stepR_mono a h)

/-- **Lemme central** : toute exécution réelle est incluse dans l'exécution relaxée.
    `run π s ⊆ runR π s`. Suit de `step ⊆ stepR` par induction sur la longueur du plan. -/
theorem run_subset_runR (π : List (Action F)) (s : State F) : run π s ⊆ runR π s := by
  induction π generalizing s with
  | nil =>
    rw [Finset.subset_iff]
    intro x hx
    exact hx
  | cons a π ih =>
    -- run (a::π) s = run π (step a s) ⊆ runR π (step a s) ⊆ runR π (stepR a s) = runR (a::π) s
    calc run (a :: π) s
        = run π (step a s) := rfl
      _ ⊆ runR π (step a s) := ih (step a s)
      _ ⊆ runR π (stepR a s) := runR_mono π (step_subset_stepR a s)
      _ = runR (a :: π) s := rfl

end PlanningLean
