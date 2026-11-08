# =============================================================================
# Verbatim copy from EPITA-IS (2025-Epita-Intelligence-Symbolique)
# Source file : argumentation_analysis/agents/core/logic/belief_revision_handler.py
# Source SHA1 : 2b02bd64800e9b8c47489cba94ba03cd42b8948d (158L @ a8025f60)
# Source LICENSE: MIT (Copyright (c) 2025 jsboigeEpita)
# CoursIA copy: MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/argumentation_lib/_belief_revision_handler.py
# Copy LICENSE : MIT (inherited from upstream)
# Volet B etape 4 sub-tranche C186e -- See EPIC #4960
#
# DEPENDENCY NOTICE (G.9 honest caveat):
# This verbatim port has NO upstream `argumentation_analysis.*` imports AND
# NO sibling upstream imports -- only stdlib (`jpype`, `logging`, `typing`).
# The class symbol is therefore import-safe today; ONLY JPype-Tweety
# singletons are referenced (`jpype.JClass`, plus several
# `org.tweetyproject.logics.pl.syntax.*` and
# `org.tweetyproject.beliefdynamics.*` FQNs at construction time).
#
# G.9 surface test verified: top-level
# `from argumentation_lib._belief_revision_handler import BeliefRevisionHandler`
# succeeds (no upstream sibling imports). Failing import would mean the
# verbatim block was modified.
#
# Instantiation WILL FAIL at runtime until the JPype bridge singleton from
# C184 (`argumentation_lib.initialize_jvm`) is initialized and the target
# classes (`org.tweetyproject.logics.pl.syntax.PlBeliefSet`,
# `org.tweetyproject.beliefdynamics.operators.RandomKernelContractionOperator`,
# `org.tweetyproject.beliefdynamics.DefaultMultipleBaseExpansionOperator`,
# `org.tweetyproject.beliefdynamics.LeviMultipleBaseRevisionOperator`, ...)
# are exposed by the JVM. Until the JPype-Tweety bridge is properly
# initialized (sub-tranche C186g runtime bridge shim), the lazy accessor
# `argumentation_lib.get_belief_revision_handler_symbol()` returns the
# BeliefRevisionHandler class symbol without triggering instantiation.
#
# Chain anchor: a8025f60 (consistent with C186a #5237 MERGED, C186b #5234
# MERGED, C186c #5242 MERGED, C186d #5251 OPEN MERGEABLE). No upstream
# commits on belief_revision_handler.py between a8025f60 and HEAD (verified
# via `git log a8025f60..HEAD -- belief_revision_handler.py` = 0 commits).
"""Handler for Belief Revision via TweetyProject.

Implements AGM-style belief revision operators:
- Dalal revision (distance-based)
- Levi revision (contraction + expansion)
- Kernel contraction
- Credibility-based multi-agent revision (CrMas)

All operators work on propositional logic belief sets.
"""

import jpype
import logging
from typing import List, Dict, Any, Optional

logger = logging.getLogger(__name__)


class BeliefRevisionHandler:
    """AGM belief revision using Tweety's beliefdynamics module."""

    REVISION_METHODS = {"dalal", "levi"}

    def __init__(self, initializer_instance=None):
        if initializer_instance and not initializer_instance.is_jvm_ready():
            raise RuntimeError(
                "BeliefRevisionHandler instantiated before JVM is ready."
            )
        # PL classes
        self.PlBeliefSet = jpype.JClass(
            "org.tweetyproject.logics.pl.syntax.PlBeliefSet"
        )
        self.PlParser = jpype.JClass("org.tweetyproject.logics.pl.parser.PlParser")
        self.PlFormula = jpype.JClass("org.tweetyproject.logics.pl.syntax.PlFormula")
        self.Proposition = jpype.JClass(
            "org.tweetyproject.logics.pl.syntax.Proposition"
        )
        self.PlNegation = jpype.JClass("org.tweetyproject.logics.pl.syntax.Negation")
        # Revision operators. NB: a prior revision referenced a fabricated
        # ``org.tweetyproject.beliefdynamics.revops.DalalRevision`` class here
        # — that class does NOT exist in Tweety 1.28 (there is no ``revops``
        # package at all). The lookup crashed __init__ on every real run → the
        # ``belief_revision`` phase FAILED, and because it is the FIRST
        # revision operator loaded, the 4 valid operators below were never
        # reached. A second, deeper bug was hidden behind it: the prior code
        # constructed ``KernelContractionOperator(RandomIncision())`` but that
        # ctor requires (IncisionFunction, KernelProvider) — 2 args, not 1.
        # The self-contained ctor is
        # ``org.tweetyproject.beliefdynamics.operators.RandomKernelContractionOperator``
        # (no-arg: wires its own incision + kernel provider), so we use that.
        # Tweety exposes no distance-based ``DalalRevision`` operator class;
        # the ``dalal`` method maps to the same Levi pattern as ``levi``. See
        # ``revise()`` below.
        self.KernelContraction = jpype.JClass(
            "org.tweetyproject.beliefdynamics.operators.RandomKernelContractionOperator"
        )
        self.DefaultExpansion = jpype.JClass(
            "org.tweetyproject.beliefdynamics.DefaultMultipleBaseExpansionOperator"
        )
        self.LeviRevision = jpype.JClass(
            "org.tweetyproject.beliefdynamics.LeviMultipleBaseRevisionOperator"
        )

    def _parse_belief_set(self, formulas: List[str]) -> Any:
        """Parse a list of PL formula strings into a PlBeliefSet."""
        parser = self.PlParser()
        bs = self.PlBeliefSet()
        for formula_str in formulas:
            formula = parser.parseFormula(formula_str)
            bs.add(formula)
        return bs

    def revise(
        self,
        belief_set: List[str],
        new_belief: str,
        method: str = "dalal",
    ) -> Dict[str, Any]:
        """Revise a belief set with new information.

        Args:
            belief_set: List of PL formula strings (current beliefs).
            new_belief: Formula to incorporate.
            method: Revision method ("dalal", "levi").

        Returns:
            Dict with revised belief set and statistics.
        """
        try:
            bs = self._parse_belief_set(belief_set)
            parser = self.PlParser()
            new_formula = parser.parseFormula(new_belief)

            # Both ``dalal`` and ``levi`` methods use the Levi pattern
            # (contraction + expansion) — the only AGM revision operator
            # family Tweety 1.28 exposes. ``dalal`` has no dedicated Tweety
            # class (see __init__ note), so it maps to the same path. We do
            # NOT fabricate a DalalRevision class. RandomKernelContractionOperator
            # is no-arg (self-contained incision + kernel provider).
            contraction = self.KernelContraction()
            expansion = self.DefaultExpansion()
            operator = self.LeviRevision(contraction, expansion)

            revised = operator.revise(bs, new_formula)

            revised_formulas = [str(f) for f in revised]

            return {
                "method": method,
                "original": belief_set,
                "new_belief": new_belief,
                "revised": sorted(revised_formulas),
                "statistics": {
                    "original_size": len(belief_set),
                    "revised_size": len(revised_formulas),
                },
            }
        except jpype.JException as e:
            logger.error(f"Java exception in belief revision: {e}")
            raise RuntimeError(f"Belief revision failed: {e}") from e

    def contract(
        self,
        belief_set: List[str],
        formula_to_remove: str,
    ) -> Dict[str, Any]:
        """Contract a belief set by removing a formula.

        Args:
            belief_set: List of PL formula strings.
            formula_to_remove: Formula to contract.

        Returns:
            Dict with contracted belief set.
        """
        try:
            bs = self._parse_belief_set(belief_set)
            parser = self.PlParser()
            formula = parser.parseFormula(formula_to_remove)

            contraction = self.KernelContraction()
            contracted = contraction.contract(bs, formula)

            contracted_formulas = [str(f) for f in contracted]

            return {
                "operation": "contraction",
                "original": belief_set,
                "removed": formula_to_remove,
                "contracted": sorted(contracted_formulas),
                "statistics": {
                    "original_size": len(belief_set),
                    "contracted_size": len(contracted_formulas),
                },
            }
        except jpype.JException as e:
            logger.error(f"Java exception in belief contraction: {e}")
            raise RuntimeError(f"Belief contraction failed: {e}") from e
