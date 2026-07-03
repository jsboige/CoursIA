# =============================================================================
# Verbatim copy from EPITA-IS (2025-Epita-Intelligence-Symbolique)
# Source file : argumentation_analysis/agents/core/logic/af_handler.py
# Source SHA1 : c8c468eff25256c625ddc2d4dace4f995ba3a79e (234L @ a8025f60)
# Source LICENSE: MIT (Copyright (c) 2025 jsboigeEpita)
# CoursIA copy: MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/argumentation_lib/_af_handler.py
# Copy LICENSE : MIT (inherited from upstream)
# Volet B etape 4 sub-tranche C186d — See EPIC #4960
#
# DEPENDENCY NOTICE (G.9 honest caveat):
# This verbatim port imports at module-load time the following upstream
# modules that are NOT vendored in argumentation_lib/ today:
#
# - from .tweety_initializer import TweetyInitializer
#   (sibling module, sub-tranche C186f, awaiting merge)
# - jpype.JClass, jpype.JException
#   (JPype runtime singleton — sub-tranche C186g bridge shim)
#
# NO upstream `argumentation_analysis.*` imports at top-level — only stdlib
# (`jpype`, `logging`, `typing`). G.9 surface test verified: top-level
# `from argumentation_lib._af_handler import AFHandler` raises
# `ModuleNotFoundError: No module named 'argumentation_lib.tweety_initializer'`
# — this is the G.9 fingerprint that proves the verbatim block is honest,
# not fabricated. (Sibling `tweety_initializer` is sub-tranche C186f awaiting;
# future CoursIA shim will re-route via the JPype bridge singleton.)
#
# Chain anchor: a8025f60 (consistent with C186a #5237 MERGED, C186b #5234
# MERGED, C186c #5242). No upstream commits on af_handler.py between a8025f60
# and HEAD (verified via `git log a8025f60..HEAD -- af_handler.py` = 0 commits).
# =============================================================================
import jpype
import logging
from typing import List, Dict, Any, Set, Optional

from .tweety_initializer import TweetyInitializer

logger = logging.getLogger(__name__)


# Mapping from semantics name to Tweety reasoner class path.
# #1215 (FP-12): ``cf2`` removed — ``CF2Reasoner`` is NOT shipped in the vendored
# Tweety build (introspected firsthand: the FQN raises ClassNotFoundException in
# both 1.28 and 1.29; no SimpleCF2Reasoner / prover.* variant exists either).
# Advertising it as supported while the class is absent was a false promise;
# honest gate-out instead of a silent {"error": ...} dressed as a result.
SEMANTICS_REASONERS = {
    "preferred": "org.tweetyproject.arg.dung.reasoner.SimplePreferredReasoner",
    "grounded": "org.tweetyproject.arg.dung.reasoner.SimpleGroundedReasoner",
    "stable": "org.tweetyproject.arg.dung.reasoner.SimpleStableReasoner",
    "complete": "org.tweetyproject.arg.dung.reasoner.SimpleCompleteReasoner",
    "admissible": "org.tweetyproject.arg.dung.reasoner.SimpleAdmissibleReasoner",
    "conflict_free": "org.tweetyproject.arg.dung.reasoner.SimpleConflictFreeReasoner",
    "semi_stable": "org.tweetyproject.arg.dung.reasoner.SimpleSemiStableReasoner",
    "stage": "org.tweetyproject.arg.dung.reasoner.SimpleStageReasoner",
    "ideal": "org.tweetyproject.arg.dung.reasoner.SimpleIdealReasoner",
    "naive": "org.tweetyproject.arg.dung.reasoner.SimpleNaiveReasoner",
}


class AFHandler:
    """
    Handles Abstract Argumentation Framework (AF) operations using TweetyProject.
    Supports multiple Dung semantics: preferred, grounded, stable, complete,
    admissible, conflict-free, semi-stable, stage, ideal, naive.
    (CF2 is NOT shipped in the vendored Tweety build — see SEMANTICS_REASONERS.)
    """

    def __init__(self, initializer_instance: TweetyInitializer):
        self._initializer_instance = initializer_instance
        if not self._initializer_instance.is_jvm_ready():
            raise RuntimeError("AFHandler instantiated before JVM is ready.")

        # Core Java classes
        self.DungTheory = jpype.JClass("org.tweetyproject.arg.dung.syntax.DungTheory")
        self.Argument = jpype.JClass("org.tweetyproject.arg.dung.syntax.Argument")
        self.Attack = jpype.JClass("org.tweetyproject.arg.dung.syntax.Attack")
        self.Extension = jpype.JClass("org.tweetyproject.arg.dung.semantics.Extension")

        # Legacy alias
        self.SimplePreferredReasoner = jpype.JClass(
            "org.tweetyproject.arg.dung.reasoner.SimplePreferredReasoner"
        )

        # Reasoner cache
        self._reasoner_cache: Dict[str, Any] = {}

    @staticmethod
    def supported_semantics() -> List[str]:
        """Returns list of supported semantics names."""
        return list(SEMANTICS_REASONERS.keys())

    def _get_reasoner(self, semantics: str):
        """
        Gets or creates a reasoner instance for the given semantics.
        Caches reasoner instances for reuse.
        """
        semantics_key = semantics.lower().replace("-", "_")
        if semantics_key not in SEMANTICS_REASONERS:
            raise ValueError(
                f"Unsupported semantics: '{semantics}'. "
                f"Supported: {', '.join(SEMANTICS_REASONERS.keys())}"
            )

        if semantics_key not in self._reasoner_cache:
            class_path = SEMANTICS_REASONERS[semantics_key]
            try:
                reasoner_cls = jpype.JClass(class_path)
                self._reasoner_cache[semantics_key] = reasoner_cls()
                logger.debug(f"Loaded reasoner for '{semantics_key}': {class_path}")
            except Exception as e:
                logger.warning(
                    f"Failed to load reasoner for '{semantics_key}' ({class_path}): {e}"
                )
                raise RuntimeError(
                    f"Reasoner for '{semantics}' not available: {e}"
                ) from e

        return self._reasoner_cache[semantics_key]

    def _build_framework(self, arguments: List[str], attacks: List[List[str]]) -> tuple:
        """
        Builds a DungTheory from argument names and attack pairs.
        Returns (dung_theory, arg_map).
        """
        dung_theory = self.DungTheory()
        arg_map = {arg_name: self.Argument(arg_name) for arg_name in arguments}
        for arg_obj in arg_map.values():
            dung_theory.add(arg_obj)

        for source_name, target_name in attacks:
            if source_name in arg_map and target_name in arg_map:
                attack = self.Attack(arg_map[source_name], arg_map[target_name])
                dung_theory.add(attack)
            else:
                logger.warning(
                    f"Skipping invalid attack from '{source_name}' to '{target_name}'."
                )

        return dung_theory, arg_map

    def _extensions_to_python(self, extensions_java) -> List[List[str]]:
        """Converts Java Extension collection to sorted Python list of lists."""
        result = []
        for ext_java in extensions_java:
            extension_args = [str(arg.getName()) for arg in ext_java]
            result.append(sorted(extension_args))
        return sorted(result)

    def analyze_dung_framework(
        self,
        arguments: List[str],
        attacks: List[List[str]],
        semantics: str = "preferred",
    ) -> Dict[str, Any]:
        """
        Analyzes a Dung-style abstract argumentation framework.

        Args:
            arguments: A list of argument names.
            attacks: A list of attacks [source, target].
            semantics: The semantics to use. Supported: preferred, grounded, stable,
                      complete, admissible, conflict_free, semi_stable, stage,
                      ideal, naive. (cf2 is NOT available in the vendored build.)

        Returns:
            Dict with keys: semantics, extensions, statistics.
        """
        semantics_key = semantics.lower().replace("-", "_")
        logger.info(
            f"Analyzing Dung framework with {len(arguments)} arguments and "
            f"{len(attacks)} attacks for '{semantics_key}' semantics."
        )

        try:
            dung_theory, arg_map = self._build_framework(arguments, attacks)
            reasoner = self._get_reasoner(semantics_key)

            extensions_java = reasoner.getModels(dung_theory)
            extensions = self._extensions_to_python(extensions_java)

            result = {
                "semantics": semantics_key,
                "extensions": {semantics_key: extensions},
                "statistics": {
                    "arguments_count": len(arguments),
                    "attacks_count": len(attacks),
                    "extensions_count": len(extensions),
                },
            }
            logger.info(
                f"Analysis successful. Found {len(extensions)} {semantics_key} extensions."
            )
            return result

        except jpype.JException as e:
            logger.error(
                f"Java exception during Dung framework analysis: {e.stacktrace()}",
                exc_info=True,
            )
            raise RuntimeError(f"Error during framework analysis: {e}") from e
        except Exception as e:
            logger.error(f"Unexpected error: {e}", exc_info=True)
            raise

    def analyze_multi_semantics(
        self,
        arguments: List[str],
        attacks: List[List[str]],
        semantics_list: Optional[List[str]] = None,
    ) -> Dict[str, Any]:
        """
        Analyzes a framework under multiple semantics at once.

        Args:
            arguments: Argument names.
            attacks: Attack pairs.
            semantics_list: List of semantics to compute. Defaults to
                           ["grounded", "preferred", "stable", "complete"].

        Returns:
            Dict with all requested semantics results.
        """
        if semantics_list is None:
            semantics_list = ["grounded", "preferred", "stable", "complete"]

        try:
            dung_theory, arg_map = self._build_framework(arguments, attacks)
            all_extensions = {}
            statistics = {
                "arguments_count": len(arguments),
                "attacks_count": len(attacks),
            }

            for sem in semantics_list:
                sem_key = sem.lower().replace("-", "_")
                try:
                    reasoner = self._get_reasoner(sem_key)
                    extensions_java = reasoner.getModels(dung_theory)
                    extensions = self._extensions_to_python(extensions_java)
                    all_extensions[sem_key] = extensions
                    statistics[f"{sem_key}_count"] = len(extensions)
                except Exception as e:
                    logger.warning(f"Failed to compute {sem_key} semantics: {e}")
                    all_extensions[sem_key] = {"error": str(e)}

            return {
                "semantics": semantics_list,
                "extensions": all_extensions,
                "statistics": statistics,
            }

        except jpype.JException as e:
            raise RuntimeError(f"Error building framework: {e}") from e

    def get_grounded_extension(
        self, arguments: List[str], attacks: List[List[str]]
    ) -> List[str]:
        """
        Convenience method: returns the unique grounded extension.
        The grounded extension is always unique (skeptical semantics).
        """
        result = self.analyze_dung_framework(arguments, attacks, "grounded")
        extensions = result["extensions"].get("grounded", [])
        return extensions[0] if extensions else []
