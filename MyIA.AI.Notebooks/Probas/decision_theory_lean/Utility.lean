import Utility.Basic
import Utility.Axioms
import Utility.Representation

/-!
# Decision Theory — von Neumann–Morgenstern Expected Utility

Formalisation of the decision-theoretic foundations of expected utility:
lotteries, the four vNM rationality axioms, and the expected-utility
representation theorem.

## Contents
- `Utility.Basic`: lotteries (finite-support distributions), expectation,
  convex mixtures, affine identities (proved, sorry-free).
- `Utility.Axioms`: completeness, transitivity, independence, continuity;
  `IsRational` bundles the four vNM axioms.
- `Utility.Representation`: `IsExpectedUtilityRep`, the sound direction
  (representation ⟹ rationality, proved sorry-free), and affine stability
  (uniqueness up to positive affine transformation). The existence direction
  is documented as an open milestone.

## Status
- Proved sorry-free: expectation algebra, all four axioms under a
  representation, affine stability.
- Open (next milestone): the existence direction `IsRational P → ∃ u,
  IsExpectedUtilityRep u P` (the substantive Herstein–Milnor theorem).

## Cross-references
- Infer-14 (Infer.NET): Bayesian expected utility under posterior uncertainty.
- PyMC-14 (PyMC): expected-utility estimation by posterior sampling.
-/
