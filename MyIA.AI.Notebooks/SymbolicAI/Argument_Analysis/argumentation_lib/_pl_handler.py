# argumentation_lib/_pl_handler.py — PL (Propositional Logic) handler
#
# Verbatim copy of `argumentation_analysis/agents/core/logic/pl_handler.py`
# from the 2025-Epita-Intelligence-Symbolique repository (EPITA-IS), commit
# a8025f60 (2026-07-02). MIT License, Copyright (c) 2025 jsboigeEpita.
#
# DEPENDENCY NOTICE (G.9 honest caveat — Not standalone-importable today)
# -----------------------------------------------------------------------
# This verbatim port depends on the following upstream modules that are NOT
# vendored in `argumentation_lib/` today:
#
#   - `argumentation_analysis.core.utils.logging_utils.setup_logging`
#     (line ~9 of upstream)
#   - `argumentation_analysis.core.jvm_setup.initialize_jvm_robustly`,
#     `shutdown_jvm`, `is_jvm_started` (line ~16 of upstream, via
#     `from .tweety_initializer import TweetyInitializer`)
#
# Therefore, `from argumentation_lib._pl_handler import PLHandler` today
# raises `ModuleNotFoundError: No module named
# 'argumentation_analysis.core.utils.logging_utils'` (or equivalent).
#
# Runtime usability awaits Volet B etape 4 sub-tranches C186c-f (other
# handlers + tweety_initializer) and C186g (runtime bridge shim).
# See NOTICE-EPITA section C186b.
# -----------------------------------------------------------------------

import jpype
import re
import logging
from typing import Optional, List, Tuple

# La configuration du logging (appel à setup_logging()) est supposée être faite globalement,
# par exemple au point d'entrée de l'application ou dans conftest.py pour les tests.
from argumentation_analysis.core.utils.logging_utils import setup_logging

# Import TweetyInitializer to access its static methods for parser/reasoner
from .tweety_initializer import TweetyInitializer

from argumentation_analysis.core.config import settings, PLSolverChoice

setup_logging()  # Appel de la configuration globale du logging
logger = logging.getLogger(__name__)  # Obtient le logger pour ce module


class PLHandler:
    """
    Handles Propositional Logic (PL) operations using TweetyProject.
    Relies on TweetyInitializer for JVM and PL component setup.
    """

    def __init__(self, initializer_instance: TweetyInitializer):
        self._initializer_instance = initializer_instance
        self._pl_parser = self._initializer_instance.get_pl_parser()
        # Dans la nouvelle architecture, le handler est responsable de créer son propre reasoner.
        # Le nom correct, trouvé dans les sources, est SimplePlReasoner.
        SimplePlReasoner = jpype.JClass(
            "org.tweetyproject.logics.pl.reasoner.SimplePlReasoner"
        )
        self._pl_reasoner = SimplePlReasoner()

        if self._pl_parser is None or self._pl_reasoner is None:
            logger.error(
                "PL components not initialized. Ensure TweetyBridge calls TweetyInitializer first."
            )
            raise RuntimeError(
                "PLHandler initialized before TweetyInitializer completed PL setup."
            )

    def _normalize_formula(self, formula_str: str) -> str:
        """
        Ensures consistent spacing around logical operators and parentheses for Tweety's parser.
        This version uses regex for safer and more robust replacements.
        """
        if not isinstance(formula_str, str):
            return ""

        logger.debug(f"Original formula for normalization: '{formula_str}'")

        # Canonicalise operator variants to Tweety-compatible forms.
        # NB (#1132): Tweety's PlParser accepts the DOUBLE-form conjunction/
        # disjunction ("&&", "||") but REJECTS the single-form ("&", "|") with a
        # "General parsing error". The previous code collapsed "&&"->"&" here,
        # which mangled every LLM formula containing a conjunction/disjunction.
        # Canonicalise any run of & or | (1+) to the double form instead.
        formula_str = re.sub(r"\s*&+\s*", " && ", formula_str)
        formula_str = re.sub(r"\s*\|+\s*", " || ", formula_str)
        # Implication / equivalence variants (longest-first so "<->" wins "->").
        formula_str = formula_str.replace("<->", " <=> ").replace("->", " => ")
        formula_str = formula_str.replace(" NOT ", " ! ").replace(" Not ", " ! ")

        # Space the remaining operators and parentheses that might be stuck
        # together (e.g. "(p=>q)"). Conjunction/disjunction are already
        # canonicalised above and are deliberately excluded here.
        formula_str = re.sub(r"\s*(<=>|=>|!|\(|\))\s*", r" \1 ", formula_str)

        # Sanitize proposition names: replace invalid characters with underscore
        # This is done after operator spacing to avoid corrupting them.
        tokens = formula_str.split(" ")
        sanitized_tokens = []
        operators_and_parentheses = {"=>", "<=>", "&&", "||", "!", "(", ")"}
        for token in tokens:
            if token in operators_and_parentheses or token == "":
                sanitized_tokens.append(token)
            else:
                # It's a proposition name, sanitize it
                # Allow letters, numbers, and underscores. Replace everything else.
                sanitized_token = re.sub(r"[^a-zA-Z0-9_]", "_", token)
                sanitized_tokens.append(sanitized_token)
        formula_str = " ".join(sanitized_tokens)

        # Clean up any resulting multiple spaces
        formula_str = " ".join(formula_str.split())

        logger.debug(f"Normalized formula to: '{formula_str}'")
        return formula_str

    def parse_pl_formula(self, formula_str: str, constants: Optional[List[str]] = None):
        """Parses a PL formula string into a TweetyProject PlFormula object."""
        # Enhanced filtering for markdown artifacts and invalid formulas
        if not isinstance(formula_str, str):
            return None

        formula_str = formula_str.strip()

        # Filter out markdown artifacts and invalid formulas
        invalid_patterns = [
            "",  # Empty string
            "```",  # Markdown code fence
            "```plaintext",  # Markdown code fence with language
            "plaintext",  # Just the language specifier
        ]

        if (
            not formula_str
            or formula_str in invalid_patterns
            or formula_str.startswith("```")
            or formula_str.endswith("```")
            or "```" in formula_str
        ):
            logger.debug(
                f"Skipping parsing of invalid/markdown formula: '{formula_str}'"
            )
            return None

        normalized_formula = self._normalize_formula(formula_str)
        logger.debug(f"Attempting to parse normalized PL formula: {normalized_formula}")

        # Pre-validation via PLFormulaSanitizer (#537)
        try:
            from argumentation_analysis.agents.core.logic.pl_formula_sanitizer import (
                PLFormulaSanitizer,
            )

            sanitizer = PLFormulaSanitizer()
            is_valid, reason = sanitizer.validate_formula(normalized_formula)
            if not is_valid:
                logger.warning(
                    f"Formula failed pre-validation, skipping Tweety parse: "
                    f"'{formula_str}' (normalized: '{normalized_formula}', reason: {reason})"
                )
                return None
        except Exception:
            pass  # Sanitizer unavailable, proceed with existing normalization

        try:
            if constants:
                PlSignature = jpype.JClass(
                    "org.tweetyproject.logics.pl.syntax.PlSignature"
                )
                signature = PlSignature()
                Proposition = jpype.JClass(
                    "org.tweetyproject.logics.pl.syntax.Proposition"
                )
                for const_name in constants:
                    proposition = Proposition(
                        jpype.JClass("java.lang.String")(const_name)
                    )
                    if not signature.contains(proposition):
                        signature.add(proposition)
                pl_formula = self._pl_parser.parseFormula(
                    JString(normalized_formula), signature
                )
            else:
                # Using JString is a good practice to avoid ambiguity.
                pl_formula = self._pl_parser.parseFormula(
                    jpype.JString(normalized_formula)
                )

            logger.info(
                f"Successfully parsed PL formula: '{formula_str}' as '{normalized_formula}' -> {pl_formula}"
            )
            return pl_formula
        except jpype.JException as e:
            logger.error(
                f"JPype JException parsing PL formula '{formula_str}' (normalized to '{normalized_formula}'): {e.getMessage()}",
                exc_info=True,
            )
            raise ValueError(
                f"Error parsing PL formula '{formula_str}': {e.getMessage()}"
            ) from e
        except Exception as e:
            logger.error(
                f"Unexpected error parsing PL formula '{formula_str}' (normalized to '{normalized_formula}'): {e}",
                exc_info=True,
            )
            raise

    def check_consistency(self, belief_set: str) -> Tuple[bool, str]:
        """Uniform handler API mirroring ``FOLHandler.check_consistency``.

        ``TweetyBridge.check_consistency(belief_set, "propositional")`` dispatches
        here. PLHandler previously exposed only ``pl_check_consistency`` /
        ``pl_check_consistency_sat``, so the dispatch raised ``AttributeError`` on
        *every* formula — collapsing the per-formula isolation loop in
        ``_invoke_propositional_logic`` to 0 survivors (PL=0), which RA-8 #1066
        unmasked once it removed the Python-heuristic fallback (#1083).

        Delegates to ``pl_check_consistency_sat`` (PySAT). Consistency of a PL
        knowledge base is a SAT problem; the correct algorithm is Tseitin→CNF
        (linear), never the Tweety reasoner's model enumeration
        (``query(kb, Contradiction())`` walks 2^n models → OOM on 50-100+ atom
        KBs, see #1192). Parse errors propagate unchanged so the per-formula
        isolation keeps valid formulas and rejects unparseable ones rather than
        swallowing the whole batch.

        Returns:
            Tuple[bool, str]: ``(is_consistent, message)``.
        """
        is_consistent = self.pl_check_consistency_sat(belief_set)
        msg = (
            "PL knowledge base is consistent."
            if is_consistent
            else "PL knowledge base entails a contradiction."
        )
        return bool(is_consistent), msg

    def check_consistency_detailed(
        self, belief_set: str
    ) -> Tuple[bool, Optional[dict], str]:
        """Return the PL consistency verdict WITH the real PySAT model.

        #1208 (FP-10): mirrors ``check_consistency`` but does not drop the
        solver witness. ``TweetyBridge.check_consistency_detailed`` dispatches
        here so the invoke-callable can persist the genuine SAT model instead
        of fabricating one. Returns ``(is_consistent, named_model, message)``.
        """
        if self._sat_available():
            return self.pl_check_consistency_detailed(belief_set)
        # Tweety fallback (no PySAT): no structured model to return.
        is_consistent = self.pl_check_consistency_tweety(belief_set)
        msg = (
            "PL knowledge base is consistent."
            if is_consistent
            else "PL knowledge base entails a contradiction."
        )
        return bool(is_consistent), None, msg

    def pl_check_consistency(
        self, knowledge_base_str: str, constants: Optional[List[str]] = None
    ) -> bool:
        """Check PL KB consistency via PySAT (Tseitin→CNF, linear).

        #1192: consistency is a SAT problem. The Tweety reasoner's approach
        (``query(kb, Contradiction())``) enumerates models (2^n) and OOMs on
        50-100+ atom KBs. PySAT is the correct, scalable algorithm and is the
        wired path. ``constants`` are accepted for API compatibility but are
        ignored by the SAT path (atoms are discovered from the formulas).

        Falls back to ``pl_check_consistency_tweety`` only if PySAT is not
        importable (fail-loud via the SATHandler constructor otherwise).
        """
        if not self._sat_available():
            logger.warning(
                "PySAT unavailable; falling back to Tweety consistency "
                "(model enumeration — may OOM on large KBs)."
            )
            return self.pl_check_consistency_tweety(knowledge_base_str, constants)
        return self.pl_check_consistency_sat(knowledge_base_str)

    def _sat_available(self) -> bool:
        """True if the SAT handler (PySAT) can be constructed."""
        try:
            from . import sat_handler as _sh  # local import to avoid hard dep at import time

            return bool(_sh.PYSAT_AVAILABLE)
        except Exception:
            return False

    def pl_check_consistency_tweety(
        self, knowledge_base_str: str, constants: Optional[List[str]] = None
    ) -> bool:
        """
        Checks if a PL knowledge base (string of formulas, semicolon-separated) is consistent.

        #1192: NOT the wired path — kept as a fallback when PySAT is absent.
        Uses Tweety's ``SimplePlReasoner.query(kb, Contradiction())`` which
        enumerates models (2^n); do not use on large KBs.
        """
        logger.debug(f"Checking PL consistency for: {knowledge_base_str}")
        try:
            # Parse the knowledge base string into a PlBeliefSet
            # Tweety's PlParser can parse a belief set directly if formulas are separated by ';'
            # However, it's often safer to parse individual formulas and add them to a knowledge base.
            # For simplicity here, assuming parseBeliefSet handles it or we adapt.

            # Let's refine this: parse individual formulas and add to a PlBeliefSet
            formulas = []
            # Handle potential empty strings or formulas correctly
            formula_strings = [
                f.strip()
                for f in knowledge_base_str.split("\n")
                if f.strip() and f.strip() != "```"
            ]

            if not formula_strings:
                logger.info("Empty knowledge base is considered consistent.")
                return True

            PlBeliefSet = jpype.JClass("org.tweetyproject.logics.pl.syntax.PlBeliefSet")
            kb = PlBeliefSet()

            for f_str in formula_strings:
                # Remove trailing '%' if present, as it was a previous workaround
                cleaned_f_str = f_str.rstrip("%").strip()
                if cleaned_f_str:
                    parsed_formula = self.parse_pl_formula(cleaned_f_str, constants)
                    if parsed_formula:
                        kb.add(parsed_formula)

            logger.info(
                f"DEBUG: Méthodes disponibles pour _pl_reasoner: {dir(self._pl_reasoner)}"
            )

            # Contournement pour le bug JPype avec isConsistent.
            # Une KB est cohérente si elle n'entraîne pas de contradiction (false).
            # On vérifie donc si la KB entraîne la formule "false".
            try:
                Contradiction = jpype.JClass(
                    "org.tweetyproject.logics.pl.syntax.Contradiction"
                )
                parsed_false = Contradiction()

                # self._pl_reasoner.query(kb, formula) retourne true si kb |= formula
                entails_contradiction = self._pl_reasoner.query(kb, parsed_false)
                is_consistent = not entails_contradiction
                logger.info(
                    f"Vérification de cohérence via query(kb, false). Entraîne contradiction: {entails_contradiction}. Cohérent: {is_consistent}"
                )

            except Exception as query_exc:
                logger.error(
                    f"Erreur durant le contournement de isConsistent avec query(false): {query_exc}",
                    exc_info=True,
                )
                # Fallback ou lever une exception ? Pour l'instant, on lève.
                raise RuntimeError(
                    "Échec de la vérification de cohérence alternative."
                ) from query_exc

            logger.info(
                f"PL Knowledge base consistency for '{knowledge_base_str}': {is_consistent}"
            )
            return bool(is_consistent)
        except ValueError as e:  # Catch parsing errors from parse_pl_formula
            logger.error(
                f"Error parsing formula in knowledge base for consistency check: {e}",
                exc_info=True,
            )
            raise
        except jpype.JException as e:
            logger.error(
                f"JPype JException during PL consistency check for '{knowledge_base_str}': {e.getMessage()}",
                exc_info=True,
            )
            raise RuntimeError(f"PL consistency check failed: {e.getMessage()}") from e
        except Exception as e:
            logger.error(
                f"Unexpected error during PL consistency check for '{knowledge_base_str}': {e}",
                exc_info=True,
            )
            raise

    def pl_query(
        self,
        knowledge_base_str: str,
        query_formula_str: str,
        constants: Optional[List[str]] = None,
    ) -> bool:
        """Check PL entailment via PySAT (KB ∧ ¬query is UNSAT).

        #1192: entailment is a SAT problem (negate the query, check
        unsatisfiability). The Tweety reasoner's ``query(kb, formula)``
        enumerates models; PySAT via Tseitin→CNF is the scalable wired path.
        ``constants`` accepted for API compatibility, ignored by the SAT path.
        """
        if not self._sat_available():
            logger.warning(
                "PySAT unavailable; falling back to Tweety query "
                "(model enumeration — may OOM on large KBs)."
            )
            return self.pl_query_tweety(
                knowledge_base_str, query_formula_str, constants
            )
        return self.pl_query_sat(knowledge_base_str, query_formula_str)

    def pl_query_tweety(
        self,
        knowledge_base_str: str,
        query_formula_str: str,
        constants: Optional[List[str]] = None,
    ) -> bool:
        """
        Checks if a query formula is entailed by a PL knowledge base.
        Knowledge base: string of formulas, semicolon-separated.
        Query: single formula string.

        #1192: NOT the wired path — kept as a fallback when PySAT is absent.
        Uses Tweety's ``SimplePlReasoner.query`` (model enumeration).
        """
        logger.debug(
            f"Performing PL query. KB: '{knowledge_base_str}', Query: '{query_formula_str}'"
        )
        try:
            PlBeliefSet = jpype.JClass("org.tweetyproject.logics.pl.syntax.PlBeliefSet")
            kb = PlBeliefSet()

            formula_strings = [
                f.strip()
                for f in knowledge_base_str.split("\n")
                if f.strip() and f.strip() != "```"
            ]
            for f_str in formula_strings:
                cleaned_f_str = f_str.rstrip("%").strip()
                if cleaned_f_str:
                    parsed_formula = self.parse_pl_formula(cleaned_f_str, constants)
                    if parsed_formula:
                        kb.add(parsed_formula)

            # Nettoyer également la chaîne de la requête
            cleaned_query_str = query_formula_str.rstrip("%").strip()
            if not cleaned_query_str or cleaned_query_str == "```":
                logger.warning(
                    f"Query string is invalid or empty after cleaning: '{query_formula_str}'"
                )
                return False  # Ou une autre gestion d'erreur appropriée

            query_formula = self.parse_pl_formula(cleaned_query_str, constants)
            if not query_formula:
                logger.warning(
                    f"Skipping empty or invalid query after parsing: '{cleaned_query_str}'"
                )
                return False

            entails = self._pl_reasoner.query(kb, query_formula)
            logger.info(f"PL Query: KB entails '{query_formula_str}'? {entails}")
            return bool(entails)
        except ValueError as e:  # Catch parsing errors
            logger.error(f"Error parsing formula for PL query: {e}", exc_info=True)
            raise
        except jpype.JException as e:
            logger.error(
                f"JPype JException during PL query (KB: '{knowledge_base_str}', Query: '{query_formula_str}'): {e.getMessage()}",
                exc_info=True,
            )
            raise RuntimeError(f"PL query failed: {e.getMessage()}") from e
        except Exception as e:
            logger.error(f"Unexpected error during PL query: {e}", exc_info=True)
            raise

    # ── SAT solver dispatch ──────────────────────────────────────────

    def _get_sat_handler(self):
        """Lazy-load the SAT handler for PySAT-based solving."""
        if not hasattr(self, "_sat_handler") or self._sat_handler is None:
            from .sat_handler import SATHandler

            self._sat_handler = SATHandler(default_solver=settings.pysat_solver)
        return self._sat_handler

    def pl_check_consistency_sat(self, knowledge_base_str: str) -> bool:
        """Check PL consistency using PySAT instead of Tweety."""
        is_consistent, _model, _msg = self.pl_check_consistency_detailed(
            knowledge_base_str
        )
        return is_consistent

    def pl_check_consistency_detailed(
        self, knowledge_base_str: str
    ) -> Tuple[bool, Optional[dict], str]:
        """Check PL consistency via PySAT and return the real SAT model.

        #1208 (FP-10): ``pl_check_consistency_sat`` returned only the boolean
        verdict, dropping the model that ``SATHandler.solve_formulas`` had
        already computed. The invoke-callable then fabricated a placeholder
        ``{p1: True, p2: True}`` model, so the persisted state carried a real
        decision (sat/unsat) with a fake witness — a silent loss of the real
        solver output (same failure class as a buried solver, #1019).

        This exposes the already-computed named model so callers persist the
        genuine PySAT witness. Returns ``(is_consistent, named_model_or_None,
        message)``. ``named_model`` maps proposition-name -> bool (True/False
        assignment); None when UNSAT.
        """
        formula_strings = [
            f.strip().rstrip("%")
            for f in knowledge_base_str.split("\n")
            if f.strip() and f.strip() != "```"
        ]
        if not formula_strings:
            return True, {}, "Empty knowledge base is consistent."
        normalized = [self._normalize_formula(f) for f in formula_strings]
        handler = self._get_sat_handler()
        is_sat, named_model, stats = handler.solve_formulas(
            normalized, settings.pysat_solver
        )
        is_consistent = bool(is_sat)
        msg = (
            f"Consistent (SAT). Model: {named_model}"
            if is_consistent
            else f"Inconsistent (UNSAT). Solver: {stats.get('solver')}"
        )
        logger.info(f"PySAT consistency check: {msg}")
        return is_consistent, named_model, msg

    def pl_query_sat(self, knowledge_base_str: str, query_formula_str: str) -> bool:
        """Check PL entailment using PySAT instead of Tweety."""
        formula_strings = [
            f.strip().rstrip("%")
            for f in knowledge_base_str.split("\n")
            if f.strip() and f.strip() != "```"
        ]
        normalized_kb = [self._normalize_formula(f) for f in formula_strings]
        normalized_query = self._normalize_formula(
            query_formula_str.rstrip("%").strip()
        )
        handler = self._get_sat_handler()
        return handler.query(normalized_kb, normalized_query, settings.pysat_solver)

    # ── Multi-backend comparison (FP-20 #1244, mandate R468) ──────────

    # PySAT backends that DECIDE firsthand (probe 2026-06-23, synthetic atoms):
    # each returns the correct verdict on BOTH {P}->SAT and {P,!P}->UNSAT.
    # ``cryptominisat5`` is EXCLUDED: it returns UNSAT on a trivially-SAT formula
    # (``AttributeError: 'CryptoMinisat' object has no attribute 'cryptosat'`` —
    # its native binding is broken in this env). Promoting a backend that emits a
    # wrong verdict would fabricate a comparison point — worse than absent (#1019).
    # A future env where cryptominisat5 genuinely decides can re-add it; the
    # per-backend sentinel test guards the decision both ways.
    PL_COMPARISON_PYSAT_BACKENDS: List[str] = [
        "cadical195",
        "glucose42",
        "maplechrono",
        "lingeling",
        "minisat22",
    ]

    async def compare_pl_backends(self, knowledge_base_str: str) -> dict:
        """Run ALL available PL/SAT backends on the same KB and compare verdicts.

        FP-20 #1244, mandate R468 ("tous les solvers handy … pour comparer les
        résultats"). Each backend (5 PySAT + Tweety Sat4j) is run INDEPENDENTLY
        on the same KB; verdicts are cross-validated. DISAGREEMENT is surfaced
        explicitly and NEVER silently reconciled — the comparison is the point
        (#1019).

        Backend set (firsthand-confirmed to decide, synthetic atoms):
        * 5 PySAT solvers (``PL_COMPARISON_PYSAT_BACKENDS``) — Tseitin→CNF→CDCL.
        * Tweety ``Sat4jSolver`` via ``SatReasoner`` — pure-Java, linear.
        * The 3 native DLLs (lingeling/minisat/picosat) are honest-absent
          (removed #1247 — ``UnsatisfiedLinkError: Binding.init()``). PySAT's own
          minisat/lingeling *Python* bindings are independent of those DLLs and DO
          decide here.
        * ``cryptominisat5`` excluded (broken native binding, see class constant).

        Returns a JSON-serialisable dict mirroring ``compare_fol_backends``::

            {
              "backends": {name: {"verdict": Optional[bool], "note": str,
                                  "elapsed_ms": float, "available": bool}},
              "decided":  {name: bool, …},     # only backends that returned a bool
              "agreement": Optional[bool],     # all-agree / disagree / <2 decided
              "disagreement": [str, …],        # explicit, never auto-reconciled
            }
        """
        import time as _time

        formula_strings = [
            f.strip().rstrip("%")
            for f in knowledge_base_str.split("\n")
            if f.strip() and f.strip() != "```"
        ]

        backend_names = [
            *(f"pysat:{s}" for s in self.PL_COMPARISON_PYSAT_BACKENDS),
            "tweety:sat4j",
        ]

        backends: "dict[str, dict]" = {}

        if not formula_strings:
            trivial = {
                "verdict": True,
                "note": "Empty knowledge base is trivially consistent.",
                "elapsed_ms": 0.0,
                "available": True,
            }
            for name in backend_names:
                backends[name] = dict(trivial)
            return {
                "backends": backends,
                "decided": {n: True for n in backends},
                "agreement": True,
                "disagreement": [],
            }

        normalized = [self._normalize_formula(f) for f in formula_strings]

        def _run(name: str, fn) -> None:
            start = _time.perf_counter()
            try:
                is_consistent, note = fn()
                elapsed = (_time.perf_counter() - start) * 1000.0
                backends[name] = {
                    "verdict": is_consistent,
                    "note": str(note),
                    "elapsed_ms": round(elapsed, 1),
                    "available": True,
                }
            except Exception as e:
                elapsed = (_time.perf_counter() - start) * 1000.0
                backends[name] = {
                    "verdict": None,
                    "note": f"unavailable: {e}",
                    "elapsed_ms": round(elapsed, 1),
                    "available": False,
                }

        for sname in self.PL_COMPARISON_PYSAT_BACKENDS:
            _run(
                f"pysat:{sname}",
                lambda s=sname: self._pl_backend_pysat(normalized, s),
            )
        _run("tweety:sat4j", lambda: self._pl_backend_sat4j(normalized))

        decided = {
            name: b["verdict"]
            for name, b in backends.items()
            if isinstance(b["verdict"], bool)
        }
        verdict_values = set(decided.values())
        if len(decided) < 2:
            agreement: "Optional[bool]" = None
        else:
            agreement = len(verdict_values) <= 1

        disagreement: "List[str]" = []
        if agreement is False:
            consistent_backends = sorted(n for n, v in decided.items() if v is True)
            inconsistent_backends = sorted(n for n, v in decided.items() if not v)
            disagreement.append(
                f"DISAGREEMENT (NOT reconciled): {consistent_backends} report "
                f"CONSISTENT (SAT), {inconsistent_backends} report INCONSISTENT "
                "(UNSAT). All backends are sound+complete SAT solvers on PL, so a "
                "disagreement here is a real backend defect — inspect per-backend "
                "notes before drawing a conclusion."
            )

        return {
            "backends": backends,
            "decided": decided,
            "agreement": agreement,
            "disagreement": disagreement,
        }

    def _pl_backend_pysat(
        self, normalized: List[str], solver_name: str
    ) -> Tuple[bool, str]:
        """Run ONE PySAT backend on the normalized KB. Raises on failure.

        The handler is lazy-loaded per call so a broken PySAT install degrades
        this backend independently of the Tweety Sat4j backend (and vice-versa).
        """
        handler = self._get_sat_handler()
        is_sat, _model, stats = handler.solve_formulas(normalized, solver_name)
        is_consistent = bool(is_sat)
        return (
            is_consistent,
            f"{'SAT' if is_consistent else 'UNSAT'} via PySAT {solver_name}",
        )

    def _pl_backend_sat4j(self, normalized: List[str]) -> Tuple[bool, str]:
        """Run Tweety Sat4j (``SatReasoner``) on the normalized KB. Raises on failure.

        ``SatReasoner`` is SAT-based (Tseitin→CNF→Sat4j), linear — distinct from
        ``SimplePlReasoner`` (model enumeration, 2^n, OOM-prone, kept only as the
        no-PySAT fallback). The normalized formulas use Tweety double-form
        (``&&``/``||``) which ``PlParser`` accepts.
        """
        SatReasoner = jpype.JClass("org.tweetyproject.logics.pl.reasoner.SatReasoner")
        PlBeliefSet = jpype.JClass("org.tweetyproject.logics.pl.syntax.PlBeliefSet")
        Contradiction = jpype.JClass(
            "org.tweetyproject.logics.pl.syntax.Contradiction"
        )
        kb = PlBeliefSet()
        for f in normalized:
            parsed = self._pl_parser.parseFormula(jpype.JString(f))
            if parsed is not None:
                kb.add(parsed)
        reasoner = SatReasoner()
        entails_contradiction = reasoner.query(kb, Contradiction())
        is_consistent = not bool(entails_contradiction)
        return (
            is_consistent,
            f"{'SAT' if is_consistent else 'UNSAT'} via Tweety Sat4j",
        )
