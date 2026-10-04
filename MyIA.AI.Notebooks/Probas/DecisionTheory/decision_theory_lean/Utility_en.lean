import Utility.Basic
import Utility.Axioms
import Utility.Representation

/-!
  Decision Theory — von Neumann–Morgenstern Expected Utility
  ==========================================================

  English mirror of `Utility.lean` (FR-first canonical). This file is a
  landing-doc mirror: only the module docstring differs from the FR
  version. Body signatures, proofs, and tactics remain byte-identical
  between the two files.

  Formalization of the decision-theoretic foundations of expected utility:
  lotteries, the four vNM rationality axioms, and the expected-utility
  representation theorem.

  ## Contents
  - `Utility.Basic`: lotteries (finite-support distributions), expectation,
    convex mixtures, affine identities (proved, sorry-free).
  - `Utility.Axioms`: completeness, transitivity, independence, continuity;
    `IsRational` bundles the four vNM axioms.
  - `Utility.Representation`: `IsExpectedUtilityRep`, the sound direction
    (representation ⟹ rationality, proved sorry-free), affine stability
    (uniqueness up to positive affine transformation), and the order-theoretic
    algebra of `≻` / `~` (strict order, equivalence relation, trichotomy). The
    existence direction is documented as an open milestone.

  ## Status
  - Proved sorry-free: expectation algebra, all four axioms under a
    representation, affine stability, and the order-theoretic algebra of strict
    preference and indifference (strict order + equivalence + trichotomy).
  - Open (next milestone): the existence direction `IsRational P → ∃ u,
    IsExpectedUtilityRep u P` (the substantive Herstein–Milnor theorem).

  ## Cross-references
  - Infer-14 (Infer.NET): Bayesian expected utility under posterior uncertainty.
  - PyMC-1 (PyMC): expected-utility estimation by posterior sampling.

  Convention i18n (EPIC #4980, decision ratified 2026-07-04, see
  `code-style.md` §Lean i18n): distinct FR+EN sibling files (`Utility.lean`
  / `Utility_en.lean`) — no inline bilingual block in a single file
  (Option B rejected: double cost + FR/EN drift + quality bias).
-/
