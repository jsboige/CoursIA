import Mathlib
import Planning.Strips_en

/-!
# Planning.Relaxation — relaxed plan execution, monotone reachability

The **delete-free relaxation** (h⁺) ignores the `del` effects of STRIPS actions:
`stepR a s = s ∪ a.add`. We define the **relaxed execution** `runR` of an action
sequence and the **real execution** `run` (which applies `del`).

The central fact is the **monotonicity of relaxed reachability**: a larger initial
state can only enlarge the reachable set (`runR_mono`). This monotonicity is what
makes solving the relaxed plan **polynomial** (increasing reachability → polynomial
fixpoint computation) and guarantees the admissibility h⁺ ≤ h* (proved in
`Admissibility.lean`). See issue #4053.
-/

namespace PlanningLean_en

variable {F : Type} [DecidableEq F]

/-- **Real** execution of a plan (action sequence) from the initial state `s`. -/
def run : List (Action F) → State F → State F
  | [], s => s
  | a :: π, s => run π (step a s)

/-- **Relaxed** (delete-free) execution of a plan from `s`. -/
def runR : List (Action F) → State F → State F
  | [], s => s
  | a :: π, s => runR π (stepR a s)

/-- A plan `π` **reaches** goal `g` from `s` (real execution). -/
def reaches (π : List (Action F)) (s g : State F) : Prop := goalSatisfied g (run π s)

/-- A plan `π` reaches `g` from `s` (relaxed execution). -/
def reachesR (π : List (Action F)) (s g : State F) : Prop := goalSatisfied g (runR π s)

/-- Monotonicity of the real execution: `s ⊆ s'` entails `run π s ⊆ run π s'`. -/
lemma run_mono (π : List (Action F)) {s s' : State F} (h : s ⊆ s') : run π s ⊆ run π s' := by
  induction π generalizing s s' with
  | nil => exact h
  | cons a π ih => exact ih (step_mono a h)

/-- **Monotonicity of relaxed reachability**: `s ⊆ s'` entails `runR π s ⊆ runR π s'`.
    This is what makes relaxed-plan computation polynomial (increasing reachability). -/
theorem runR_mono (π : List (Action F)) {s s' : State F} (h : s ⊆ s') :
    runR π s ⊆ runR π s' := by
  induction π generalizing s s' with
  | nil => exact h
  | cons a π ih => exact @ih (stepR a s) (stepR a s') (stepR_mono a h)

/-- **Central lemma**: every real execution is included in the relaxed execution.
    `run π s ⊆ runR π s`. Follows from `step ⊆ stepR` by induction on the plan length. -/
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

end PlanningLean_en
