# =============================================================================
# Verbatim copy from EPITA-IS (2025-Epita-Intelligence-Symbolique)
# Source file : argumentation_analysis/agents/core/logic/ranking_handler.py
# Source SHA1 : da43f9777805bbaac40a7d7335b92cf7019bbd5b (120L @ a8025f60)
# Source LICENSE: MIT (Copyright (c) 2025 jsboigeEpita)
# CoursIA copy: MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/argumentation_lib/_ranking_handler.py
# Copy LICENSE : MIT (inherited from upstream)
# Volet B etape 4 sub-tranche C186d — See EPIC #4960
#
# DEPENDENCY NOTICE (G.9 honest caveat):
# This verbatim port has NO upstream `argumentation_analysis.*` imports AND
# NO sibling upstream imports — only stdlib (`jpype`, `logging`, `typing`).
# The class symbol is therefore import-safe today; ONLY JPype-Tweety
# singletons are referenced (`jpype.JClass`, `jpype.JException`, plus 5
# `org.tweetyproject.arg.*` FQNs at construction time).
#
# G.9 surface test verified: top-level
# `from argumentation_lib._ranking_handler import RankingHandler` succeeds
# (no upstream sibling imports). Failing import would mean the verbatim
# block was modified.
#
# Instantiation WILL FAIL at runtime until the JPype bridge singleton from
# C184 (`argumentation_lib.initialize_jvm`) is initialized and the target
# classes (`org.tweetyproject.arg.dung.syntax.DungTheory` and 11 ranking
# reasoners in REASONERS dict) are exposed by the JVM. Until the JPype-Tweety
# bridge is properly initialized (sub-tranche C186g runtime bridge shim),
# the lazy accessor `argumentation_lib.get_ranking_handler_symbol()` returns
# the RankingHandler class symbol without triggering instantiation.
#
# Chain anchor: a8025f60 (consistent with C186a #5237 MERGED, C186b #5234
# MERGED, C186c #5242). No upstream commits on ranking_handler.py between
# a8025f60 and HEAD (verified via
# `git log a8025f60..HEAD -- ranking_handler.py` = 0 commits).
# =============================================================================
"""Handler for Ranking Semantics via TweetyProject.

Provides qualitative argument ranking using Dung frameworks.
12 ranking reasoners from Tweety arg.rankings module:
- Categorizer (Besnard & Hunter)
- Burden-based
- Discussion-based
- Counting
- Tuples
- Strategy-based
- Propagation
- SAF (Social Abstract Argumentation Framework)
- Counter-Transitivity
- Probabilistic ranking
- Iterated Graded Defense
- Serialisable wrapper

Each reasoner takes a DungTheory and returns a ranking (ordering) over arguments.
"""

import jpype
import logging
from typing import List, Dict, Any

logger = logging.getLogger(__name__)


class RankingHandler:
    """Argument ranking using Tweety's ranking semantics reasoners."""

    REASONERS = {
        "categorizer": "org.tweetyproject.arg.rankings.reasoner.CategorizerRankingReasoner",
        "burden": "org.tweetyproject.arg.rankings.reasoner.BurdenBasedRankingReasoner",
        "discussion": "org.tweetyproject.arg.rankings.reasoner.DiscussionBasedRankingReasoner",
        "counting": "org.tweetyproject.arg.rankings.reasoner.CountingRankingReasoner",
        "tuples": "org.tweetyproject.arg.rankings.reasoner.TuplesRankingReasoner",
        "strategy": "org.tweetyproject.arg.rankings.reasoner.StrategyBasedRankingReasoner",
        "propagation": "org.tweetyproject.arg.rankings.reasoner.PropagationRankingReasoner",
        "saf": "org.tweetyproject.arg.rankings.reasoner.SAFRankingReasoner",
        "counter_transitivity": "org.tweetyproject.arg.rankings.reasoner.CounterTransitivityReasoner",
        "probabilistic_ranking": "org.tweetyproject.arg.rankings.reasoner.ProbabilisticRankingReasoner",
        "iterated_graded_defense": "org.tweetyproject.arg.rankings.reasoner.IteratedGradedDefenseReasoner",
        "serialisable": "org.tweetyproject.arg.rankings.reasoner.SerialisableRankingReasoner",
    }

    def __init__(self, initializer_instance=None):
        if initializer_instance and not initializer_instance.is_jvm_ready():
            raise RuntimeError("RankingHandler instantiated before JVM is ready.")
        self.DungTheory = jpype.JClass("org.tweetyproject.arg.dung.syntax.DungTheory")
        self.Argument = jpype.JClass("org.tweetyproject.arg.dung.syntax.Argument")
        self.Attack = jpype.JClass("org.tweetyproject.arg.dung.syntax.Attack")
        self._reasoner_cache = {}

    def _get_reasoner(self, name: str):
        if name not in self._reasoner_cache:
            if name not in self.REASONERS:
                raise ValueError(
                    f"Unknown ranking reasoner: {name}. Available: {list(self.REASONERS.keys())}"
                )
            cls = jpype.JClass(self.REASONERS[name])
            self._reasoner_cache[name] = cls()
        return self._reasoner_cache[name]

    def rank_arguments(
        self,
        arguments: List[str],
        attacks: List[List[str]],
        method: str = "categorizer",
    ) -> Dict[str, Any]:
        """Rank arguments using the specified ranking semantics.

        Args:
            arguments: List of argument names.
            attacks: List of [source, target] pairs.
            method: Ranking method name (categorizer, burden, discussion, counting, tuples).

        Returns:
            Dict with ranking results including ordered arguments and scores.
        """
        try:
            theory = self.DungTheory()
            arg_map = {name: self.Argument(name) for name in arguments}
            for arg in arg_map.values():
                theory.add(arg)
            for src, tgt in attacks:
                if src in arg_map and tgt in arg_map:
                    theory.add(self.Attack(arg_map[src], arg_map[tgt]))

            reasoner = self._get_reasoner(method)
            ranking = reasoner.getModel(theory)

            # Extract ordering from the NumericalPartialOrder / LatticePartialOrder
            ranked_args = []
            for arg_name, arg_obj in arg_map.items():
                ranked_args.append(arg_name)

            # Try to extract pairwise comparisons
            comparisons = {}
            for a_name, a_obj in arg_map.items():
                for b_name, b_obj in arg_map.items():
                    if a_name != b_name:
                        try:
                            if ranking.isStrictlyMoreAcceptableThan(a_obj, b_obj):
                                comparisons[f"{a_name}>{b_name}"] = True
                        except Exception:
                            pass

            return {
                "method": method,
                "arguments": sorted(ranked_args),
                "comparisons": comparisons,
                "statistics": {
                    "arguments_count": len(arguments),
                    "attacks_count": len(attacks),
                    "comparisons_found": len(comparisons),
                },
            }
        except jpype.JException as e:
            logger.error(f"Java exception in ranking analysis: {e}")
            raise RuntimeError(f"Ranking analysis failed: {e}") from e
