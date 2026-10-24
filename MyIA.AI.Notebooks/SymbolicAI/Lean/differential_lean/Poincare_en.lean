/-
  Witness — Poincare conjecture (qinz1yang/differential-geometry v0.1.3)
  ======================================================================

  English companion to `Poincare.lean` (FR canonical) per the i18n #4980
  sibling-pair convention. Only docstrings/comments differ; imports and the
  `#print axioms` command are byte-identical to the canonical file.

  Companion to `DifferentialTour.lean`, for Pli 1 sub-grain 2 of EPIC #18205.
  This file reimplements nothing and copies nothing: it imports the upstream
  module that states the theorem and asks the Lean kernel for the axioms the
  statement depends on.

  Upstream statement, `Topology/ThreeManifold/Poincare.lean` line 12:

    theorem poincare_conjecture
        (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [T2Space M] [CompactSpace M] [SimplyConnectedSpace M] :
        Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)

  Every closed simply connected 3-manifold is homeomorphic to the 3-sphere.

  What `#print axioms` measures here is not the conjecture: it is the
  *dependency* of the statement as upstream carries it. A theorem depending on
  a forbidden axiom (`sorryAx`, `native_decide.*`) shows up in the open,
  without any proof having been rewritten.

  Repository : https://github.com/qinz1yang/differential-geometry
  License    : Apache-2.0
-/

import DifferentialGeometry.Topology.ThreeManifold.Poincare

-- Poincare conjecture: closed simply connected 3-manifold = 3-sphere.
#print axioms DifferentialGeometry.Topology.poincare_conjecture
