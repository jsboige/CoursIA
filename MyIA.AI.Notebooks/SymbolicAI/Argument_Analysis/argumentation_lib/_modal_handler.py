# =============================================================================
# Verbatim copy from EPITA-IS (2025-Epita-Intelligence-Symbolique)
# Source file : argumentation_analysis/agents/core/logic/modal_handler.py
# Source SHA1 : ea424fff87cccd77c322d5a97ff0c516190f0f54 (327L @ a8025f60)
# Source LICENSE: MIT (Copyright (c) 2025 jsboigeEpita)
# CoursIA copy: MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/argumentation_lib/_modal_handler.py
# Copy LICENSE : MIT (inherited from upstream)
# Volet B etape 4 sub-tranche C186c — See EPIC #4960
#
# DEPENDENCY NOTICE (G.9 honest caveat):
# This verbatim port imports at module-load time the following upstream
# modules that are NOT vendored in argumentation_lib/ today:
#
# - from .modal_kb_identifier_normalizer import ModalIdentifierNormalizer
#   (sibling module handling MlParser underscore-normalization #1326,
#   not vendored — separate scope, not part of C186 chain)
# - from .tweety_initializer import TweetyInitializer
#   (sub-tranche C186f, awaiting merge)
# - from argumentation_analysis.core.config import settings, ModalSolverChoice
#   (upstream internal settings module, not vendored)
# - jpype.JClass, jpype.JException
#   (JPype runtime singleton — sub-tranche C186g bridge shim)
#
# G.9 surface test verified: top-level
# `from argumentation_lib._modal_handler import ModalHandler` raises
# `ModuleNotFoundError: No module named
# 'argumentation_lib.modal_kb_identifier_normalizer'` — this is the G.9
# fingerprint that proves the verbatim block is honest, not fabricated.
# (Sibling `modal_kb_identifier_normalizer` is NOT part of the C186 chain
# and is not vendored; future CoursIA shim will re-route or stub this.)
#
# Chain anchor: a8025f60 (consistent with C186a #5237, C186b #5234 MERGED).
# 1 upstream commit (f5ce8bd9 SPASS routing fix #1339) post-a8025f60 affects
# this file; pinned to a8025f60 for chain consistency. The verbatim copy is the
# reference contract for the eventual CoursIA shim that re-routes via the
# resolved solver choice (#1339).
# =============================================================================
import jpype
import logging
from typing import Optional, Tuple

from .modal_kb_identifier_normalizer import ModalIdentifierNormalizer
from .tweety_initializer import TweetyInitializer
from argumentation_analysis.core.config import settings, ModalSolverChoice

logger = logging.getLogger(__name__)


def _get_spass_path() -> "str | None":
    """Return the detected SPASS binary path, or None if not wired.

    Reads the module-level registry populated by
    ``jvm_setup._configure_external_tools``. Centralised here (mirroring
    ``fol_handler._get_eprover_path``) so the Modal handler does not duplicate
    the detection logic and the wiring is testable in isolation (#1205).

    #1205: the previous ``_get_spass_reasoner`` called ``SPASSMlReasoner()`` with
    no argument — but in Tweety 1.28+/1.29 the only constructors are
    ``SPASSMlReasoner(String)`` and ``SPASSMlReasoner(String, Shell)`` (verified
    via ``javap`` on the bundled jar). The no-arg call raised a Java
    construction error, swallowed by the surrounding ``except`` → SPASS was
    never wired, yet the pipeline reported it as the configured modal solver
    (formal theater, same class as the EProver regression #1196/#1202).
    """
    try:
        from argumentation_analysis.core.jvm_setup import EXTERNAL_TOOL_PATHS

        return EXTERNAL_TOOL_PATHS.get("spass")
    except Exception:  # pragma: no cover - import guard
        return None


class ModalHandler:
    """
    Handles Modal Logic operations using TweetyProject.
    Supports two reasoners:
    - SimpleMlReasoner (default, pure Tweety)
    - SPASSMlReasoner (backed by external SPASS binary, more powerful)
    """

    def __init__(self, initializer_instance: TweetyInitializer):
        """
        Initializes the ModalHandler.
        """
        self._initializer_instance = initializer_instance
        self._modal_parser = initializer_instance.get_modal_parser()
        self._modal_reasoner = initializer_instance.get_modal_reasoner()
        self._spass_reasoner = None  # Lazy-loaded

        if self._modal_parser is None or self._modal_reasoner is None:
            logger.error(
                "Modal Logic components not initialized. Ensure TweetyInitializer is configured for Modal Logic."
            )
            raise RuntimeError(
                "ModalHandler initialized before TweetyInitializer completed Modal Logic setup."
            )

    def _get_spass_reasoner(self):
        """Lazy-load SPASSMlReasoner, wired with the detected binary path.

        #1205 (anti-theater #1019): the previous implementation called
        ``SPASSMlReasoner()`` with no argument — but Tweety 1.28+/1.29 only
        exposes ``SPASSMlReasoner(String)`` / ``SPASSMlReasoner(String, Shell)``
        (verified via ``javap``), so the construction raised and the bare
        ``except`` swallowed it into a generic ``RuntimeError``. The detected
        SPASS path (``EXTERNAL_TOOL_PATHS['spass']``) was never passed to the
        constructor — mirroring the EProver regression #1196/#1202.

        Now reads the registered path and instantiates
        ``SPASSMlReasoner(JString(path))`` (1-arg ctor). If the path is unset
        (binary absent), this raises ``RuntimeError`` **fail-loud** — it does
        NOT silently fall back to ``SimpleMlReasoner``: a missing SPASS binary
        must surface as an honest "could not decide" (``None``/degraded), never
        as a fabricated verdict.
        """
        if self._spass_reasoner is None:
            spass_path = _get_spass_path()
            if spass_path is None:
                raise RuntimeError(
                    "SPASS binary not detected (EXTERNAL_TOOL_PATHS['spass'] "
                    "unset) — modal axis cannot decide via SPASS. Install "
                    "SPASS under ext_tools/spass/ or use a non-SPASS modal "
                    "solver (anti-theater #1019: no silent fallback)."
                )
            try:
                SPASSMlReasoner = jpype.JClass(
                    "org.tweetyproject.logics.ml.reasoner.SPASSMlReasoner"
                )
                JString = jpype.JClass("java.lang.String")
                self._spass_reasoner = SPASSMlReasoner(JString(spass_path))
                logger.info(
                    f"SPASSMlReasoner loaded successfully (binary: {spass_path})."
                )
            except Exception as e:
                logger.warning(f"Failed to load SPASSMlReasoner: {e}")
                raise RuntimeError(f"SPASS reasoner not available: {e}") from e
        return self._spass_reasoner

    def _get_active_reasoner(self):
        """Returns the active reasoner based on configuration."""
        if settings.modal_solver == ModalSolverChoice.SPASS:
            return self._get_spass_reasoner()
        return self._modal_reasoner

    @staticmethod
    def _normalize_for_parse(belief_set_content: str) -> str:
        """Normalize modal KB identifiers so ``MlParser`` accepts them (#1326).

        ``MlParser`` forbids underscores/separators in predicate declarations
        (``[a-zA-Z][a-zA-Z0-9]*``), but producers such as the spectacular-path
        ``_construct_modal_kb_from_json`` and LLM-generated identifiers emit
        underscored multi-word atoms (``joke_teleprompter``) — which raised
        ``ParserException: Illegal characters in predicate definition`` so the
        KB never parsed and consistency was never decided (R519: 3/3 modal axes
        undecided). Applied here, *amont* de ``parseBeliefBase``, it protects
        every caller regardless of upstream producer (defense-in-depth).

        Idempotent on already-legal atoms: the nl path pre-sanitizes via
        ``invoke_callables._legal_symbol`` and the second pass is a no-op.
        Anti-pendule: normalizes sort-name SYNTAX only (PascalCase stem
        survives), no heuristic masking a parse-fail (#1019 fail-loud).
        """
        normalized, reverse = ModalIdentifierNormalizer().normalize_belief_set(
            belief_set_content
        )
        if reverse:
            logger.debug(
                "Modal KB identifiers normalized for MlParser (#1326): %s",
                reverse,
            )
        return normalized

    def validate_modal_formula(self, formula_str: str) -> Tuple[bool, str]:
        """
        Validates the syntax of a modal logic formula by attempting to parse it.
        """
        logger.debug(f"Validating modal formula: '{formula_str}'")
        try:
            java_formula_str = jpype.JClass("java.lang.String")(formula_str)
            self._modal_parser.parseFormula(java_formula_str)
            return True, "Formula syntax is valid."
        except jpype.JException as e:
            error_message = f"Invalid modal formula syntax: {e.getMessage()}"
            logger.warning(error_message)
            return False, error_message
        except Exception as e:
            logger.error(
                f"Unexpected error validating modal formula '{formula_str}': {e}",
                exc_info=True,
            )
            return False, "An unexpected error occurred during validation."

    def execute_modal_query(self, belief_set_content: str, query_string: str) -> str:
        """
        Executes a modal logic query against a given belief set.
        Uses the configured reasoner (SimpleMlReasoner or SPASSMlReasoner).
        """
        reasoner = self._get_active_reasoner()
        reasoner_name = (
            type(reasoner).__name__
            if hasattr(reasoner, "__class__")
            else settings.modal_solver.value
        )
        logger.debug(f"Executing modal query '{query_string}' with {reasoner_name}")
        try:
            StringReader = jpype.JClass("java.io.StringReader")

            # #1326: normalize identifiers amont de parseBeliefBase so
            # underscored atoms (joke_teleprompter) become MlParser-legal
            # (JokeTeleprompter). One shared normalizer maps belief-set and
            # query atoms consistently so query names match the KB signature.
            normalizer = ModalIdentifierNormalizer()
            belief_set_content, _bs_rev = normalizer.normalize_belief_set(
                belief_set_content
            )
            query_string, _q_rev = normalizer.normalize_belief_set(query_string)
            if _bs_rev:
                logger.debug(
                    "Modal query KB identifiers normalized (#1326): %s", _bs_rev
                )

            # Parse belief set
            belief_set_reader = StringReader(belief_set_content)
            belief_set = self._modal_parser.parseBeliefBase(belief_set_reader)

            # Parse query
            query_formula = self._modal_parser.parseFormula(
                jpype.JClass("java.lang.String")(query_string)
            )

            # Execute query
            result = reasoner.query(belief_set, query_formula)

            if bool(result):
                return f"Tweety Result ({reasoner_name}): Modal Query '{query_string}' is ACCEPTED (True)."
            else:
                return f"Tweety Result ({reasoner_name}): Modal Query '{query_string}' is REJECTED (False)."

        except jpype.JException as e:
            error_msg = f"Error executing modal query: {e.getMessage()}"
            logger.error(error_msg, exc_info=True)
            return f"FUNC_ERROR: {error_msg}"
        except Exception as e:
            error_msg = (
                f"An unexpected error occurred during modal query execution: {e}"
            )
            logger.error(error_msg, exc_info=True)
            return f"FUNC_ERROR: {error_msg}"

    def _build_contradiction_probe(self, belief_set):
        """Build a ground contradiction ``atom && !atom`` over the KB signature.

        Tweety modal reasoners (``SimpleMlReasoner`` / ``SPASSMlReasoner``)
        expose ``query(beliefSet, formula)`` but **NOT** ``isConsistent`` (#1205,
        verified firsthand via ``javap`` and ``getMethods()`` introspection — the
        only methods are ``query``/``queryProof``). A modal KB is inconsistent
        iff it entails a contradiction (an inconsistent KB has no models, so it
        entails every formula over its signature, including ``atom && !atom``;
        a consistent KB has a model that satisfies the atom one way, so it does
        NOT entail the contradiction).

        Returns the parsed contradiction formula, or ``None`` when the signature
        has no predicates (an empty / modal-constant-only KB is trivially
        consistent). Raises ``RuntimeError`` when a ground atom cannot be built
        (n-ary predicate with no declared constants) — surfaced as honest
        "undecidable" rather than a fabricated verdict (#1019).
        """
        signature = belief_set.getSignature()
        predicates = list(signature.getPredicates())
        if not predicates:
            return None
        predicate = predicates[0]
        name = str(predicate.getName())
        arity = int(predicate.getArity())
        if arity == 0:
            atom = name
        else:
            constants = list(signature.getConstants())
            if not constants:
                raise RuntimeError(
                    f"Cannot build a ground contradiction probe: predicate "
                    f"'{name}' has arity {arity} but the signature declares no "
                    f"constants — modal consistency is undecidable via query here."
                )
            constant = str(constants[0].get())
            atom = f"{name}(" + ",".join([constant] * arity) + ")"
        return self._modal_parser.parseFormula(f"{atom} && !{atom}")

    def is_modal_kb_consistent(
        self, belief_set_content: str
    ) -> Tuple[Optional[bool], str]:
        """
        Checks if a modal logic knowledge base is consistent.

        Uses the configured reasoner (``SimpleMlReasoner`` or
        ``SPASSMlReasoner``) via **query-based consistency** (#1205): the KB is
        inconsistent iff it entails a contradiction (see
        ``_build_contradiction_probe``). The previous implementation called
        ``reasoner.isConsistent(belief_set)`` — a method that exists on NO
        Tweety modal reasoner — so it never decided; the failure was masked by
        fully-mocked unit tests (formal theater, modal side of #1196/#1202).

        Returns ``(True/False, msg)`` on a real decision and ``(None, msg)``
        when consistency cannot be determined — a malformed KB, or a reasoner
        that cannot run (e.g. the SPASS binary is absent or not a runnable CLI
        build). Honest ``None`` (no silent fallback to another reasoner, no
        fabricated verdict) per the anti-theater contract (#1019/#961).
        """
        solver_name = settings.modal_solver.value
        reasoner = self._get_active_reasoner()
        logger.debug(f"Checking modal KB consistency with {solver_name}.")

        # #1326: normalize identifiers amont de parseBeliefBase so underscored
        # atoms (joke_teleprompter) become MlParser-legal (JokeTeleprompter) and
        # the configured solver actually receives a parseable belief set to
        # DECIDE — rather than degrading to None on a ParserException.
        belief_set_content = self._normalize_for_parse(belief_set_content)

        try:
            StringReader = jpype.JClass("java.io.StringReader")
            belief_set = self._modal_parser.parseBeliefBase(
                StringReader(belief_set_content)
            )
        except Exception as e:  # parse failure → undetermined, not "inconsistent"
            error_msg = (
                f"Modal KB parse error (consistency undetermined, {solver_name}): {e}"
            )
            logger.error(error_msg)
            return None, error_msg

        try:
            contradiction = self._build_contradiction_probe(belief_set)
            if contradiction is None:
                return True, (
                    f"Knowledge base is consistent (no predicates, {solver_name})."
                )
            entails_contradiction = reasoner.query(belief_set, contradiction)
            is_consistent = not bool(entails_contradiction)
            message = (
                f"Knowledge base is consistent ({solver_name})."
                if is_consistent
                else f"Knowledge base is inconsistent ({solver_name})."
            )
            return is_consistent, message

        except jpype.JException as e:
            # e.g. the SPASS binary cannot launch (wrong build / elevation) →
            # honest "could not decide" (None), NOT False and NOT a fallback.
            error_msg = (
                f"Modal consistency could not be decided via {solver_name} "
                f"(reasoner unavailable): {e.getMessage()}"
            )
            logger.warning(error_msg)
            return None, error_msg
        except RuntimeError as e:
            error_msg = f"Modal consistency undecidable ({solver_name}): {e}"
            logger.warning(error_msg)
            return None, error_msg
        except Exception as e:
            error_msg = (
                f"Unexpected error during modal consistency check ({solver_name}): {e}"
            )
            logger.error(error_msg, exc_info=True)
            return None, error_msg
