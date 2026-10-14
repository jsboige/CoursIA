/-
  Tour — three small closures of qinz1yang/differential-geometry v0.1.3
  ====================================================================

  English companion to `DifferentialTour.lean` (FR canonical) per the i18n
  #4980 sibling-pair convention. Only docstrings/comments differ; Lean code,
  imports and `#print axioms` commands are byte-identical to the canonical.

  This file reimplements nothing and copies nothing: it imports three modules
  of the upstream package — declared as a Lake dependency in lakefile.lean —
  and asks the Lean kernel for the axiom list each headline theorem depends on,
  for the three closures cited by EPIC #18205:

  1. Morse lemma          Topology/Morse/ExtremumChart.lean
  2. de Rham cohomology   Tensor/Exterior/Cochain.lean
  3. Bonnet-Myers         Geometry/Comparison/BonnetMyers/Diameter.lean

  The `#print axioms` output is this tour's witness: a theorem depending on a
  forbidden axiom (`sorryAx`, `native_decide.*`) shows up here, in the open,
  without any proof having been rewritten.

  The upstream claims to use only `propext`, `Classical.choice` and
  `Quot.sound`. This file measures that claim at three entry points; it does
  not take it on faith.

  Repository : https://github.com/qinz1yang/differential-geometry
  License    : Apache-2.0
-/

import DifferentialGeometry.Topology.Morse.ExtremumChart
import DifferentialGeometry.Tensor.Exterior.Cochain
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.Diameter

-- 1. Morse lemma: existence of a quadratic chart at a local minimum.
#print axioms DifferentialGeometry.Topology.Morse.exists_quadratic_chart_of_isLocalMin

-- 2. de Rham cohomology: the identity induces the identity in cohomology.
#print axioms DifferentialGeometry.DifferentialForm.pullbackCohomologyMap_id

-- 3. Bonnet-Myers: diameter bound under a lower Ricci curvature bound.
#print axioms DifferentialGeometry.Geometry.Riemannian.BonnetMyers.bonnet_myers_diameter_le_of_complete_metric
