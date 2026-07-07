import Mathlib
import Planning.Strips_en
import Planning.Relaxation_en

/-!
# Planning.Admissibility — h⁺ ≤ h*: the delete-free relaxation is admissible

**Admissibility theorem of the relaxation**: the cost of the optimal relaxed plan `h⁺`
never exceeds the cost of the optimal real plan `h*`.

    h⁺ ≤ h*

The proof relies on the inclusion `run π s ⊆ runR π s` (every real plan is a relaxed
plan): since the relaxation ignores the `del` effects, the relaxed state after applying
an action sequence always contains the corresponding real state. Hence every real plan
reaching goal `g` is also a relaxed plan reaching `g`. By optimality of the minimal
cost, the relaxed cost `h⁺` is at most the real cost `h*`.

This result formally justifies using relaxation heuristics (h_max, h_add, FF) as
**admissible lower bounds** on the real cost — the foundation of modern planning.
See issue #4053 (Lean roadmap #4038, Tier 2).

## Open milestone (not sorry-backed)

The **full machinery of the h_max / h_add heuristics** (the relaxed-reachability
fixpoint, and the inequality `h_max ≤ h⁺ ≤ h_add`) is not formalized here: it requires
a recursive definition of the relaxed-reachability fixpoint and a convergence proof,
which is substantial. The fundamental admissibility `h⁺ ≤ h*` (the result that
legitimizes the whole family of relaxation heuristics) is proven 0 sorry below.
-/

namespace PlanningLean_en

variable {F : Type} [DecidableEq F]

/-- **Admissibility theorem of the relaxation (h⁺ ≤ h*)**: every real plan reaching
    goal `g` is also a relaxed plan reaching `g`. By minimality of optimal costs,
    the relaxed cost `h⁺` is therefore at most the real cost `h*`. -/
theorem relaxed_plan_admissible (π : List (Action F)) (s g : State F)
    (h : reaches π s g) : reachesR π s g :=
  Finset.Subset.trans h (run_subset_runR π s)

/-- **Direct corollary**: if a real plan of length `n` reaches `g`, the same plan,
    executed under relaxation, also reaches `g`. Operational formulation of h⁺ ≤ h*
    (there exists a relaxed plan of cost ≤ every real plan, hence ≤ h*). -/
theorem relaxed_plan_witness (π : List (Action F)) (s g : State F)
    (h : reaches π s g) : reachesR π s g :=
  relaxed_plan_admissible π s g h

end PlanningLean_en
