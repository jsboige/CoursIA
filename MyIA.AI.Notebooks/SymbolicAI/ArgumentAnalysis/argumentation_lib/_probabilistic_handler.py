# =============================================================================
# Verbatim copy from EPITA-IS (2025-Epita-Intelligence-Symbolique)
# Source file : argumentation_analysis/agents/core/logic/probabilistic_handler.py
# Source SHA1 : 069b33d5911dde5f48afbcd594e60a8ccf11abff (152L @ a8025f60)
# Source LICENSE: MIT (Copyright (c) 2025 jsboigeEpita)
# CoursIA copy: MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/argumentation_lib/_probabilistic_handler.py
# Copy LICENSE : MIT (inherited from upstream)
# Volet B etape 4 sub-tranche C186e -- See EPIC #4960
#
# DEPENDENCY NOTICE (G.9 honest caveat):
# This verbatim port has NO upstream `argumentation_analysis.*` imports AND
# NO sibling upstream imports -- only stdlib (`jpype`, `logging`, `typing`).
# The class symbol is therefore import-safe today; ONLY JPype-Tweety
# singletons are referenced (`jpype.JClass`, plus several
# `org.tweetyproject.arg.dung.syntax.*`,
# `org.tweetyproject.math.probability.*`, and
# `org.tweetyproject.arg.dung.reasoner.SimpleGroundedReasoner` FQNs at
# construction/lazy-load time).
#
# G.9 surface test verified: top-level
# `from argumentation_lib._probabilistic_handler import ProbabilisticHandler`
# succeeds (no upstream sibling imports). Failing import would mean the
# verbatim block was modified.
#
# Instantiation WILL FAIL at runtime until the JPype bridge singleton from
# C184 (`argumentation_lib.initialize_jvm`) is initialized and the target
# classes (`org.tweetyproject.arg.dung.syntax.DungTheory`,
# `org.tweetyproject.math.probability.Probability`, ...) are exposed by the
# JVM. Until the JPype-Tweety bridge is properly initialized (sub-tranche
# C186g runtime bridge shim), the lazy accessor
# `argumentation_lib.get_probabilistic_handler_symbol()` returns the
# ProbabilisticHandler class symbol without triggering instantiation.
#
# Chain anchor: a8025f60 (consistent with C186a #5237 MERGED, C186b #5234
# MERGED, C186c #5242 MERGED, C186d #5251 OPEN MERGEABLE). No upstream
# commits on probabilistic_handler.py between a8025f60 and HEAD (verified
# via `git log a8025f60..HEAD -- probabilistic_handler.py` = 0 commits).
"""Handler for Probabilistic Argumentation via TweetyProject.

Extends Dung frameworks with probability distributions over arguments,
enabling probabilistic reasoning about argument acceptance.
"""

import jpype
import logging
from typing import List, Dict, Any, Tuple

logger = logging.getLogger(__name__)


class ProbabilisticHandler:
    """Probabilistic argumentation framework analysis using Tweety."""

    def __init__(self, initializer_instance=None):
        if initializer_instance and not initializer_instance.is_jvm_ready():
            raise RuntimeError("ProbabilisticHandler instantiated before JVM is ready.")
        self.DungTheory = jpype.JClass("org.tweetyproject.arg.dung.syntax.DungTheory")
        self.Argument = jpype.JClass("org.tweetyproject.arg.dung.syntax.Argument")
        self.Attack = jpype.JClass("org.tweetyproject.arg.dung.syntax.Attack")
        self.Probability = jpype.JClass(
            "org.tweetyproject.math.probability.Probability"
        )
        # NB: a prior revision referenced a fabricated
        # ``org.tweetyproject.arg.prob.reasoner.ProbabilisticReasoner`` class
        # here — that class does NOT exist in Tweety 1.28 (the real reasoners
        # are SimplePafReasoner / MonteCarloPafReasoner). The attribute was
        # dead code: never read by any method (the acceptance computation
        # uses org.tweetyproject.arg.dung.reasoner.SimpleGroundedReasoner at
        # runtime, loaded lazily in _compute_acceptance_probabilities). The
        # fabricated JClass lookup crashed __init__ on every real run → the
        # ``probabilistic`` phase FAILED. Removed (anti-pendule: subtract the
        # bug, do not replace it with another speculative class).

    def analyze_probabilistic_framework(
        self,
        arguments: List[str],
        attacks: List[List[str]],
        probabilities: Dict[str, float],
    ) -> Dict[str, Any]:
        """Analyze a probabilistic argumentation framework.

        Args:
            arguments: List of argument names.
            attacks: List of [source, target] attack pairs.
            probabilities: Dict mapping argument name -> probability of existence.

        Returns:
            Dict with probabilistic analysis results.
        """
        try:
            theory = self.DungTheory()
            arg_map = {name: self.Argument(name) for name in arguments}
            for arg in arg_map.values():
                theory.add(arg)
            for src, tgt in attacks:
                if src in arg_map and tgt in arg_map:
                    theory.add(self.Attack(arg_map[src], arg_map[tgt]))

            # Build probability assignment
            prob_assignment = {}
            for arg_name, prob_val in probabilities.items():
                if arg_name in arg_map:
                    prob_assignment[arg_name] = prob_val

            # Compute acceptance probabilities based on subgraph enumeration
            # For each argument, enumerate subgraphs where it's in a grounded extension
            acceptance_probs = self._compute_acceptance_probabilities(
                arguments, attacks, probabilities
            )

            return {
                "arguments": sorted(arguments),
                "probabilities": probabilities,
                "acceptance_probabilities": acceptance_probs,
                "statistics": {
                    "arguments_count": len(arguments),
                    "attacks_count": len(attacks),
                },
            }
        except jpype.JException as e:
            logger.error(f"Java exception in probabilistic analysis: {e}")
            raise RuntimeError(f"Probabilistic analysis failed: {e}") from e

    def _compute_acceptance_probabilities(
        self,
        arguments: List[str],
        attacks: List[List[str]],
        probabilities: Dict[str, float],
    ) -> Dict[str, float]:
        """Compute acceptance probability for each argument via subgraph enumeration.

        Simple approach: for each subset of arguments (weighted by probabilities),
        compute grounded extension and check if argument is in it.
        Limited to small frameworks (<15 arguments) for efficiency.
        """
        if len(arguments) > 15:
            logger.warning(
                "Framework too large for exact probabilistic computation, using approximation"
            )
            return {arg: probabilities.get(arg, 1.0) for arg in arguments}

        from itertools import combinations

        GroundedReasoner = jpype.JClass(
            "org.tweetyproject.arg.dung.reasoner.SimpleGroundedReasoner"
        )

        acceptance = {arg: 0.0 for arg in arguments}
        n = len(arguments)

        # Enumerate all 2^n subsets
        for size in range(n + 1):
            for subset in combinations(arguments, size):
                subset_set = set(subset)
                # Probability of this subset occurring
                prob = 1.0
                for arg in arguments:
                    p = probabilities.get(arg, 1.0)
                    if arg in subset_set:
                        prob *= p
                    else:
                        prob *= 1.0 - p

                if prob < 1e-10:
                    continue

                # Build sub-framework
                sub_theory = self.DungTheory()
                sub_arg_map = {}
                for arg_name in subset:
                    a = self.Argument(arg_name)
                    sub_theory.add(a)
                    sub_arg_map[arg_name] = a
                for src, tgt in attacks:
                    if src in sub_arg_map and tgt in sub_arg_map:
                        sub_theory.add(self.Attack(sub_arg_map[src], sub_arg_map[tgt]))

                # Compute grounded extension
                reasoner = GroundedReasoner()
                grounded = reasoner.getModel(sub_theory)
                grounded_args = (
                    {str(a.getName()) for a in grounded} if grounded else set()
                )

                for arg in grounded_args:
                    if arg in acceptance:
                        acceptance[arg] += prob

        return acceptance
