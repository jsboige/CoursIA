/-
  Witness — the proof chain of Poincare (qinz1yang/differential-geometry v0.1.3)
  ==============================================================================

  English companion to `PoincareChain.lean` (FR canonical) per the i18n #4980
  sibling-pair convention. Only docstrings/comments differ; imports and the
  `#print axioms` commands are byte-identical to the canonical file.

  Companion to `Poincare.lean`, for Pli 2 of EPIC #18205. Where
  `Poincare.lean` asks for the axioms of the statement alone, this file walks
  down the chain the proof actually takes, link by link, and asks the kernel
  for the axiomatic dependency of each.

  The proof of the statement fits in five tactic lines (measured 2026-10-30: 23
  lines of module, 11 for the theorem block including the statement, 5 after
  `:= by`), in
  `Topology/ThreeManifold/Poincare.lean`:

    obtain ⟨C, hC⟩ := PiecewiseLinear.exists_isManifold_three (M := M)
    let := C
    let : IsManifold (𝓡 3) ∞ M := hC
    obtain ⟨f⟩ := PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_holds M
    exact ⟨f.toHomeomorph⟩

  Three steps, and they are not symmetric:

    1. Moise (`exists_isManifold_three`) produces a smooth structure on the
       topological 3-manifold. This is the entry gate: Ricci flow requires
       `IsManifold (𝓡 3) ∞ M`, which the topological hypotheses of the
       statement do not provide.
    2. Ricci flow with surgery yields a DIFFEOMORPHISM onto the 3-sphere
       (`smoothPoincareConjecture_holds`) — strictly stronger than the
       topological statement.
    3. `toHomeomorph` brings the result back to the topological world.

  What `#print axioms` measures here, link by link, is the *dependency* of
  each step as upstream carries it. A link depending on a forbidden axiom
  (`sorryAx`, `native_decide.*`) shows up in the open, without any proof
  having been rewritten. This file therefore does not prove the conjecture:
  it proves that the published chain does not cheat.

  Repository : https://github.com/qinz1yang/differential-geometry
  License    : Apache-2.0

  Build note: the closure of this statement cost 22 909 jobs and 11 253 s
  locally (#21916). This witness file adds no proof work, but it shares the
  upstream build cache.
-/

import DifferentialGeometry.Topology.PiecewiseLinear.Moise352Producer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Skeleton.PoincareEndgame
import DifferentialGeometry.Topology.ThreeManifold.Poincare

-- 1. Moise: every topological 3-manifold admits a smooth structure.
#print axioms DifferentialGeometry.Topology.PiecewiseLinear.exists_isManifold_three

-- 2. Hamilton's link: finite-time extinction under positive Ricci.
#print axioms DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.exists_hamilton_finite_time_flow_on_closed_open

-- 3. Controlled extinction, assembled by surgery.
#print axioms DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction

-- 4. The smooth Poincare conjecture: a diffeomorphism onto the 3-sphere.
#print axioms DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_holds

-- 5. The topological Poincare conjecture: a homeomorphism.
#print axioms DifferentialGeometry.Topology.poincare_conjecture
