# =============================================================================
# Verbatim port from EPITA-IS (2025-Epita-Intelligence-Symbolique)
# Source file: argumentation_analysis/agents/core/logic/fol_handler.py
# Upstream commit: a8025f60 (2026-07-02)
# Source LICENSE: MIT (Copyright (c) 2025 jsboigeEpita)
# Verbatim integrity: body SHA1=f8a70e45b70ece23dd13e680c9d5e9fd54e983f4
#
# CoursIA NOTICE: see ../../../../SymbolicAI/Argument_Analysis/argumentation_lib/NOTICE-EPITA
#                 section "Volet B etape 4 sub-tranche C186b (pl_handler + fol_handler)".
#
# DEPENDENCY NOTICE (G.9 honest caveat):
# This file imports upstream modules NOT vendored in argumentation_lib/ today:
#   - argumentation_analysis.core.utils.logging_utils.setup_logging
#   - from .tweety_initializer import TweetyInitializer  (sub-tranche C186f)
#   - argumentation_analysis.core.jvm_setup.{initialize_jvm_robustly,
#     shutdown_jvm, is_jvm_started}
#   - argumentation_analysis.core.prover9_runner.run_prover9
#     (third-party prover9 binding via shell subprocess)
# The verbatim body is preserved as the authoritative reference contract for the
# eventual CoursIA JPype runtime integration (C186g shim). Runtime usability awaits
# C186c-f sub-tranches.
# =============================================================================

import jpype
import logging
import asyncio
import re
import time

# La configuration du logging (appel à setup_logging()) est supposée être faite globalement.
from argumentation_analysis.core.utils.logging_utils import setup_logging
from .tweety_initializer import TweetyInitializer
from argumentation_analysis.core.prover9_runner import run_prover9
from argumentation_analysis.core.mace4_runner import (
    MACE4_EXECUTABLE,
    interpret_mace4_output,
    run_mace4,
)
from argumentation_analysis.core.config import settings, SolverChoice

setup_logging()
logger = logging.getLogger(__name__)


def _get_eprover_path() -> "str | None":
    """Return the detected EProver binary path, or None if not wired.

    Reads the module-level registry populated by
    ``jvm_setup._configure_external_tools``. Centralised here so the FOL handler
    does not duplicate the detection logic and the wiring is testable in
    isolation (#1196).
    """
    try:
        from argumentation_analysis.core.jvm_setup import EXTERNAL_TOOL_PATHS

        return EXTERNAL_TOOL_PATHS.get("eprover")
    except Exception:  # pragma: no cover - import guard
        return None


# Cache: eprover binary path -> bool (delivery contract verified on this platform).
# The sentinel is a one-off subprocess per binary, not per-query overhead.
_EPROVER_DELIVERY_RELIABLE: "dict[str, bool]" = {}


def _eprover_delivery_is_reliable(reasoner, eprover_path: str) -> bool:
    """Anti-théâtre sentinel guard for the Tweety->EProver delivery contract (#1019, #1204).

    Tweety's ``EFOLReasoner`` builds the command ``<eprover> --auto-schedule
    --tptp3-format <file>`` and runs it through ``NativeShell`` via
    ``Runtime.exec(String)`` (the fragile, non-portable single-String overload
    that re-tokenises on whitespace). On some platform/E-version combinations
    (firsthand-observed on Linux with E 3.x, #1204) the problem file never
    reaches the binary — E reads empty input, proves the *empty* theory
    ``Satisfiable`` and a genuinely **inconsistent** KB is reported *consistent*.
    That is a fabricated verdict, exactly the failure #1019 forbids.

    Before trusting any eprover verdict, run a known-inconsistent sentinel
    ``{P(a), !P(a)}`` through the SAME reasoner. If the contradiction is not
    detected, the delivery is broken here and eprover must not be trusted — the
    caller raises so ``fol_check_consistency`` falls back to the in-JVM Tweety
    reasoner instead of serving a fabricated answer. Result cached per path.

    Returns True iff the sentinel is correctly reported inconsistent.
    """
    cached = _EPROVER_DELIVERY_RELIABLE.get(eprover_path)
    if cached is not None:
        return cached
    reliable = False
    try:
        FolParser = jpype.JClass("org.tweetyproject.logics.fol.parser.FolParser")
        sentinel = FolParser().parseBeliefBase(
            "human = {a}\ntype(P(human))\n\nP(a)\n!P(a)\n"
        )
        probe_parser = FolParser()
        probe_parser.setSignature(sentinel.getMinimalSignature())
        contradiction = probe_parser.parseFormula("-")
        # query returns True iff the KB entails the contradiction (= inconsistent).
        reliable = bool(reasoner.query(sentinel, contradiction))
    except Exception as e:  # parser/JVM hiccup -> unreliable, fail loud
        logger.error(
            f"EProver sentinel self-check raised ({e}); treating eprover as unreliable."
        )
        reliable = False
    _EPROVER_DELIVERY_RELIABLE[eprover_path] = reliable
    if not reliable:
        logger.error(
            "EProver sentinel self-check FAILED: known-inconsistent {P(a),!P(a)} "
            "was not reported inconsistent — the problem is not reaching the solver "
            "on this platform (Tweety<->E delivery contract broken, #1204). EProver "
            "verdicts cannot be trusted here; falling back to the in-JVM reasoner."
        )
    return reliable


# --------------------------------------------------------------------------- #
# Mace4 (LADR model-finder) — FP-19 #1243. The CONSISTENCY side of the FOL
# multi-prover comparison: it proves consistent by exhibiting a finite model
# (sound), complementing EProver/Prover9's refutation (which proves inconsistent).
# --------------------------------------------------------------------------- #

# Operator map Tweety-FOL formula-toString -> LADR (Prover9/Mace4 share LADR).
# Longest tokens first so ``<=>`` is rewritten before ``=>``. Tweety already
# renders negation as ``-`` (LADR's symbol) in its toString, but a parsed formula
# may surface ``!`` — map both.
_TWEETY_TO_LADR_OPS = [
    ("<=>", "<->"),
    ("=>", "->"),
    ("&&", "&"),
    ("||", "|"),
    ("forall ", "all "),
    ("!", "-"),
]


def _tweety_fol_to_ladr(formula_str: str) -> str:
    """Translate ONE Tweety FOL formula ``toString()`` into LADR syntax.

    Operates on an INDIVIDUAL formula (e.g. ``Mortal(socrate)`` or
    ``forall X: (Human(X) => Mortal(X))``), never the whole belief set — the
    belief set's ``toString()`` is set notation ``{ f1, f2 }`` which LADR cannot
    parse ("Set parsing is not available"). Anything still un-parseable surfaces
    as a Mace4 ``Fatal error`` (RuntimeError) → honest fallback, never a
    fabricated verdict (#1019).
    """
    s = formula_str
    for src, dst in _TWEETY_TO_LADR_OPS:
        s = s.replace(src, dst)
    # Tweety renders quantifiers as ``all X:`` / ``exists X:``; LADR wants no
    # colon (``all X ...``). Drop the colon after the bound variable.
    s = re.sub(r"\b(all|exists)\s+(\w+)\s*:", r"\1 \2", s)
    return s


def _belief_set_to_ladr_assumptions(belief_set) -> str:
    """Build a LADR ``formulas(assumptions). … end_of_list.`` block from a Tweety
    ``FolBeliefSet``.

    Iterates the belief set's INDIVIDUAL formulas (a ``FolBeliefSet`` is a Java
    ``Collection``) and translates each to a LADR clause terminated by ``.``.
    This deliberately avoids ``belief_set.toString()`` — that renders the set as
    ``{ f1, f2 }`` (brace + comma), which Mace4/Prover9 reject as "Set parsing is
    not available" (the reason the legacy Prover9 path never genuinely decided
    and always fell back). Mace4 searches for a model of these assumptions.
    """
    clauses = []
    iterator = belief_set.iterator()
    while iterator.hasNext():
        formula = iterator.next()
        ladr = _tweety_fol_to_ladr(str(formula.toString())).strip()
        if ladr:
            clauses.append(ladr.rstrip(".") + ".")
    body = "\n".join(clauses)
    return f"formulas(assumptions).\n{body}\nend_of_list.\n"


# Cache: Mace4 binary path -> bool (delivery contract verified on this platform).
_MACE4_DELIVERY_RELIABLE: "dict[str, bool]" = {}


def _mace4_delivery_is_reliable() -> bool:
    """Anti-théâtre sentinel for the Mace4 delivery contract (#1019, generalizes
    ``_eprover_delivery_is_reliable``).

    A model-finder cannot prove inconsistency, so its sentinel exercises its
    SOUND capability instead: a known-consistent KB ``{ptest(a)}`` MUST yield a
    finite model. If Mace4 fails to find a model for a trivially-satisfiable KB,
    the input is not reaching the binary (or the binary is broken) — Mace4 must
    not be trusted, and the caller falls back / contributes ``None`` rather than
    serving a possibly-degraded verdict. Result cached per binary path.
    """
    key = str(MACE4_EXECUTABLE)
    cached = _MACE4_DELIVERY_RELIABLE.get(key)
    if cached is not None:
        return cached
    reliable = False
    try:
        out = run_mace4("formulas(assumptions).\nptest(a).\nend_of_list.\n")
        verdict, _ = interpret_mace4_output(out)
        reliable = verdict is True
    except Exception as e:  # binary/timeout hiccup -> unreliable, fail loud
        logger.error(
            f"Mace4 sentinel self-check raised ({e}); treating Mace4 as unreliable."
        )
        reliable = False
    _MACE4_DELIVERY_RELIABLE[key] = reliable
    if not reliable:
        logger.error(
            "Mace4 sentinel self-check FAILED: known-consistent {ptest(a)} did not "
            "yield a finite model — the problem is not reaching Mace4 (delivery "
            "broken). Mace4 verdicts cannot be trusted here."
        )
    return reliable


class FOLHandler:
    """
    Handles First-Order Logic (FOL) operations using either TweetyProject or Prover9,
    based on the application's configuration.
    """

    def __init__(self, initializer_instance: TweetyInitializer = None):
        """
        Initializes the FOLHandler.
        The initializer_instance is optional and only required for the Tweety solver path.
        """
        self.logger = logging.getLogger(__name__)
        self._initializer_instance = initializer_instance

        # Le parser et autres composants Tweety ne sont chargés que si nécessaire.
        self._fol_parser = None
        if settings.solver == SolverChoice.TWEETY:
            # La vérification de _initializer_instance est maintenant faite dans chaque méthode tweety
            if self._initializer_instance:
                self._fol_parser = self._initializer_instance.get_fol_parser()
                if self._fol_parser is None:
                    logger.error(
                        "FOL Parser not initialized. Ensure TweetyBridge calls TweetyInitializer first."
                    )
                    raise RuntimeError(
                        "FOLHandler initialized before TweetyInitializer completed FOL setup."
                    )

    def parse_fol_formula(self, formula_str: str, custom_parser=None):
        """
        Parses a single FOL formula string.
        If a custom_parser (with a specific signature) is provided, it uses it.
        Otherwise, it uses the default FOL parser.
        """
        if not isinstance(formula_str, str):
            raise TypeError("Input formula must be a string.")

        parser_to_use = custom_parser if custom_parser else self._fol_parser

        logger.debug(f"Attempting to parse FOL formula: {formula_str}")
        try:
            java_formula_str = jpype.JClass("java.lang.String")(formula_str)
            fol_formula = parser_to_use.parseFormula(java_formula_str)
            logger.info(
                f"Successfully parsed FOL formula: {formula_str} -> {fol_formula}"
            )
            return fol_formula
        except jpype.JException as e:
            logger.error(
                f"JPype JException parsing FOL formula '{formula_str}': {e.getMessage()}",
                exc_info=True,
            )
            raise ValueError(
                f"Error parsing FOL formula '{formula_str}': {e.getMessage()}"
            ) from e
        except Exception as e:
            logger.error(
                f"Unexpected error parsing FOL formula '{formula_str}': {e}",
                exc_info=True,
            )
            raise

    def create_belief_set_from_string(self, tweety_syntax: str):
        """
        Crée un FolBeliefSet directement à partir d'une chaîne de caractères
        utilisant la syntaxe native de Tweety.
        C'est la nouvelle approche privilégiée.

        :param tweety_syntax: Une chaîne contenant la base de connaissances complète.
        :return: Un objet FolBeliefSet de jpype.
        """
        logger.info(
            "Parsing de la base de connaissances FOL à partir de la syntaxe native."
        )
        StringReader = jpype.JClass("java.io.StringReader")
        FolParser = jpype.JClass("org.tweetyproject.logics.fol.parser.FolParser")

        try:
            # CRUCIAL : Créer une instance de parser locale et isolée pour chaque appel.
            # Cela empêche la contamination de la signature entre les tests ou les appels.
            # L'instance partagée self._fol_parser conserve son état, ce qui cause des erreurs
            # de "redéclaration" lors d'appels successifs avec des données similaires.
            local_parser = FolParser()
            reader = StringReader(tweety_syntax)
            belief_set = local_parser.parseBeliefBase(reader)
            logger.info(
                f"Parsing réussi avec un parser local. {belief_set.size()} formules chargées."
            )
            return belief_set
        except jpype.JException as e:
            # Il est crucial de remonter l'exception de parsing pour le feedback au LLM.
            self.logger.error(
                f"Erreur de parsing dans Tweety: {e.getMessage()}", exc_info=True
            )
            raise ValueError(f"Erreur de parsing Tweety: {e.getMessage()}") from e

    def create_belief_set_programmatically(self, builder_plugin_data: dict):
        """
        Crée un FolBeliefSet Java en mémoire à partir des données accumulées
        par le BeliefSetBuilderPlugin.
        C'est la nouvelle approche robuste qui contourne les bizarreries du
        parseur de fichier .fologic.
        """
        from argumentation_analysis.agents.core.logic.fol_logic_agent import (
            BeliefSetBuilderPlugin,
        )

        sorts_data = builder_plugin_data.get("_sorts", {})
        predicates_data = builder_plugin_data.get("_predicates", {})
        formulas = builder_plugin_data.get("_formulas", [])

        FolSignature = jpype.JClass("org.tweetyproject.logics.fol.syntax.FolSignature")
        FolBeliefSet = jpype.JClass("org.tweetyproject.logics.fol.syntax.FolBeliefSet")
        Sort = jpype.JClass("org.tweetyproject.logics.commons.syntax.Sort")
        Constant = jpype.JClass("org.tweetyproject.logics.commons.syntax.Constant")
        Predicate = jpype.JClass("org.tweetyproject.logics.commons.syntax.Predicate")
        String = jpype.JClass("java.lang.String")
        ArrayList = jpype.JClass("java.util.ArrayList")

        import re

        signature = FolSignature()
        sorts_map = {}  # Python-side mapping from name to Java Sort object

        # Étape 1: Collecter tous les sorts, constantes, et prédicats (déclarés et défensifs) en Python d'abord.

        # 1a. Collecter les prédicats déclarés par le LLM.
        # On fait une copie pour pouvoir la modifier sans affecter l'original.
        final_predicates_data = dict(predicates_data)

        # 1b. Scan défensif pour trouver les prédicats utilisés mais non déclarés.
        for formula_str in formulas:
            potential_preds = re.findall(r"([a-zA-Z][a-zA-Z0-9_]*)\(", formula_str)
            for pred_name in potential_preds:
                if pred_name not in final_predicates_data:
                    self.logger.warning(
                        f"Prédicat '{pred_name}' utilisé mais non déclaré. Ajout défensif."
                    )
                    # Estimation de l'arité
                    try:
                        inner_content_match = re.search(
                            re.escape(pred_name) + r"\((.*?)\)", formula_str
                        )
                        if inner_content_match:
                            inner_content = inner_content_match.group(1)
                            arity = inner_content.count(",") + 1 if inner_content else 0
                        else:
                            arity = 0  # Cas comme 'pred()'.
                    except Exception:
                        arity = 1  # Fallback sûr.

                    # Stratégie : tout prédicat non déclaré est de type (thing, thing, ...)
                    thing_sort_name = "thing"
                    final_predicates_data[pred_name] = [thing_sort_name] * arity

                    # S'assurer que 'thing' est bien dans la liste des sorts à créer.
                    if thing_sort_name not in sorts_data:
                        sorts_data[thing_sort_name] = []

        # Étape 2: Construire la signature Java complète en une seule passe.

        # 2a. Créer et ajouter tous les sorts.
        for sort_name in sorts_data.keys():
            try:
                java_sort = Sort(String(sort_name))
                signature.add(java_sort)
                sorts_map[sort_name] = java_sort
                self.logger.debug(f"Sort ajouté par programmation : {sort_name}")
            except jpype.JException as e:
                raise ValueError(
                    f"Échec de la création du sort Java '{sort_name}': {e.getMessage()}"
                ) from e

        # 2b. Créer et ajouter les constantes.
        for sort_name, constants_list in sorts_data.items():
            parent_sort = sorts_map.get(sort_name)
            if parent_sort:
                for const_name in constants_list:
                    try:
                        java_constant = Constant(String(const_name), parent_sort)
                        signature.add(java_constant)
                        self.logger.debug(
                            f"Constante ajoutée: {const_name} de type {sort_name}"
                        )
                    except jpype.JException as e:
                        raise ValueError(
                            f"Échec de la création de la constante '{const_name}': {e.getMessage()}"
                        ) from e

        # 2c. Créer et ajouter la liste COMPLÈTE des prédicats.
        for pred_name, arg_sort_names in final_predicates_data.items():
            java_arg_sorts = ArrayList()
            for arg_sort_name in arg_sort_names:
                java_sort = sorts_map.get(arg_sort_name)
                if not java_sort:
                    raise ValueError(
                        f"Incohérence: Le sort '{arg_sort_name}' du prédicat '{pred_name}' n'a pas été trouvé."
                    )
                java_arg_sorts.add(java_sort)

            try:
                java_predicate = Predicate(String(pred_name), java_arg_sorts)
                signature.add(java_predicate)
                self.logger.debug(
                    f"Prédicat ajouté: {pred_name} avec args {arg_sort_names}"
                )
            except jpype.JException as e:
                raise ValueError(
                    f"Échec de la création du prédicat '{pred_name}': {e.getMessage()}"
                ) from e

        # Étape 3: Créer le parser avec la signature finale et l'utiliser pour parser les formules.
        belief_set = FolBeliefSet()
        belief_set.setSignature(signature)

        FolParser = jpype.JClass("org.tweetyproject.logics.fol.parser.FolParser")
        parser = FolParser()
        parser.setSignature(signature)

        for formula_str in formulas:
            try:
                parsed_formula = self.parse_fol_formula(
                    formula_str, custom_parser=parser
                )
                if parsed_formula:
                    belief_set.add(parsed_formula)
                    self.logger.debug(f"Formule ajoutée: {formula_str}")
                else:
                    self.logger.warning(
                        f"Le parsing de '{formula_str}' a retourné None."
                    )
            except ValueError as e:
                self.logger.error(
                    f"Échec final du parsing de '{formula_str}' avec la signature construite : {e}"
                )
                raise e

        self.logger.info(
            f"Base de connaissances FOL créée par programmation avec {belief_set.size()} formules."
        )
        return belief_set, signature

    async def fol_check_consistency(self, belief_set):
        """
        Checks if an FOL knowledge base is consistent using the configured solver.

        When the configured external solver (eprover/prover9) is unavailable
        (binary absent, RuntimeError), falls back to the in-JVM Tweety FOL
        reasoner — mirroring the modal pattern (modal_handler.py:36-48).
        Returns a ``solver_fallback`` flag in the result so callers can track
        degradation.
        """
        self.logger.debug(
            f"Performing FOL consistency check with solver: {settings.solver.value}"
        )
        if settings.solver == SolverChoice.PROVER9:
            try:
                return await self._fol_check_consistency_with_prover9(belief_set)
            except RuntimeError as e:
                self.logger.warning(
                    f"Prover9 unavailable ({e}), falling back to Tweety FOL reasoner"
                )
                return await self._fol_check_consistency_with_tweety_fallback(
                    belief_set
                )
        elif settings.solver == SolverChoice.EPROVER:
            try:
                return await self._fol_check_consistency_with_eprover(belief_set)
            except RuntimeError as e:
                self.logger.warning(
                    f"EProver unavailable ({e}), falling back to Tweety FOL reasoner"
                )
                return await self._fol_check_consistency_with_tweety_fallback(
                    belief_set
                )
        elif settings.solver == SolverChoice.MACE4:
            try:
                return await self._fol_check_consistency_with_mace4(belief_set)
            except RuntimeError as e:
                self.logger.warning(
                    f"Mace4 unavailable ({e}), falling back to Tweety FOL reasoner"
                )
                return await self._fol_check_consistency_with_tweety_fallback(
                    belief_set
                )
        else:
            return await self._fol_check_consistency_with_tweety(belief_set)

    async def _fol_check_consistency_with_tweety_fallback(self, belief_set):
        """Attempt Tweety FOL consistency check; returns solver_fallback=True on success."""
        try:
            result = await self._fol_check_consistency_with_tweety(belief_set)
            # result is (bool, str) — inject fallback flag
            is_consistent, msg = result
            return is_consistent, msg, True  # solver_fallback=True
        except Exception as tweety_err:
            self.logger.error(
                f"Tweety FOL fallback also failed: {tweety_err}",
                exc_info=True,
            )
            # Both solvers failed — propagate original issue
            raise RuntimeError(
                f"FOL consistency check failed: external solver absent and "
                f"Tweety fallback failed ({tweety_err})"
            ) from tweety_err

    async def _fol_check_consistency_with_prover9(self, belief_set):
        logger.debug(
            f"Checking FOL consistency for belief set of size {belief_set.size()} via external Prover9"
        )
        try:
            formulas_str = belief_set.toString().replace(";", ".\n")
            # FP-8: correct Prover9 syntax — goals must be wrapped in
            # ``formulas(goals).`` (the bare ``goals.`` list header is rejected
            # by Prover9 2009-11A with "Fatal error: Unrecognized command"). A
            # consistency check asks whether the KB entails falsehood ($F): a
            # proof of $F = inconsistent.
            prover9_input = f"formulas(assumptions).\n{formulas_str}\nend_of_list.\n\nformulas(goals).\n$F.\nend_of_list."
            logger.debug(f"Prover9 input for consistency check:\n{prover9_input}")
            prover9_output = await asyncio.to_thread(run_prover9, prover9_input)
            # FP-8: the real proof-found marker emitted by Prover9 2009-11A is
            # "THEOREM PROVED" (the previous code looked for "END OF PROOF" in
            # the wrong case — it never matched, so an inconsistent KB was
            # reported as consistent = théâtre). Proof found (KB entails $F) ⇒
            # inconsistent.
            is_consistent = "THEOREM PROVED" not in prover9_output
            msg = f"Consistency check result: {is_consistent}"
            logger.info(msg)
            return is_consistent, msg
        except Exception as e:
            logger.error(
                f"Error during external FOL consistency check: {e}", exc_info=True
            )
            detailed_error = getattr(e, "stderr", str(e))
            raise RuntimeError(
                f"FOL consistency check failed. Details: {detailed_error}"
            ) from e

    async def _fol_check_consistency_with_tweety(self, belief_set):
        logger.debug(
            f"Performing FOL consistency check via Tweety for belief set of size {belief_set.size()}."
        )
        if not self._initializer_instance:
            raise ValueError(
                "TweetyInitializer instance is required for the 'tweety' solver path."
            )
        try:
            # A KB is inconsistent iff it entails the bottom symbol "-". Build the
            # contradiction with a LOCAL parser carrying the belief set's own
            # signature — NOT ``self.parse_fol_formula`` / ``self._fol_parser``,
            # which is only initialized when ``settings.solver == TWEETY`` and is
            # ``None`` otherwise (so under EPROVER/MACE4/PROVER9 init this method —
            # the external-solver FALLBACK and a comparison backend, FP-19 #1243 —
            # would spuriously fail). This mirrors the robust sync ``check_consistency``
            # and ``_fol_check_consistency_with_eprover`` paths.
            local_parser = jpype.JClass(
                "org.tweetyproject.logics.fol.parser.FolParser"
            )()
            local_parser.setSignature(belief_set.getMinimalSignature())
            contradiction = local_parser.parseFormula("-")

            SimpleFolReasoner = self._initializer_instance.get_reasoner(
                "SimpleFolReasoner"
            )
            inconsistent = SimpleFolReasoner.query(belief_set, contradiction)

            is_consistent = not bool(inconsistent)
            msg = f"Tweety-based consistency check result: {is_consistent}"
            logger.info(msg)
            return is_consistent, msg

        except Exception as e:
            logger.error(
                f"Error during Tweety FOL consistency check: {e}", exc_info=True
            )
            raise NotImplementedError(
                f"The Tweety pathway for consistency checks failed: {e}"
            ) from e

    async def _fol_check_consistency_with_eprover(self, belief_set):
        """Checks FOL consistency using Tweety's EFOLReasoner (backed by EProver binary).

        #1196: the EProver binary path is read from the module-level
        ``EXTERNAL_TOOL_PATHS`` registry populated by ``jvm_setup._configure_external_tools``.
        The ``EFOLReasoner`` constructor takes that path as its single argument
        (Tweety 1.28+ API). Previously this method called ``EFOLReasoner()`` with
        no argument and relied on a global static path that was never set — so
        the EProver path always raised and fell back silently.
        """
        logger.debug(
            f"Performing FOL consistency check via EProver for belief set of size {belief_set.size()}."
        )
        eprover_path = _get_eprover_path()
        if eprover_path is None:
            raise RuntimeError(
                "EProver binary not detected (EXTERNAL_TOOL_PATHS['eprover'] unset); "
                "cannot run the 'eprover' solver path."
            )
        try:
            JString = jpype.JClass("java.lang.String")
            EFOLReasoner = jpype.JClass(
                "org.tweetyproject.logics.fol.reasoner.EFOLReasoner"
            )
            reasoner = EFOLReasoner(JString(eprover_path))

            # #1204 anti-théâtre guard: verify the Tweety->E delivery contract
            # actually carries the problem to the binary on this platform before
            # trusting any verdict. A broken contract silently returns
            # "consistent" on an inconsistent KB (fabrication, #1019).
            if not _eprover_delivery_is_reliable(reasoner, eprover_path):
                raise RuntimeError(
                    "EProver delivery contract broken on this platform "
                    "(sentinel {P(a),!P(a)} not reported inconsistent, #1204) — "
                    "refusing to serve a possibly-fabricated FOL verdict."
                )

            # Check consistency by querying the bottom/contradiction symbol "-"
            local_parser = jpype.JClass(
                "org.tweetyproject.logics.fol.parser.FolParser"
            )()
            local_parser.setSignature(belief_set.getMinimalSignature())
            contradiction = local_parser.parseFormula("-")
            inconsistent = reasoner.query(belief_set, contradiction)

            is_consistent = not bool(inconsistent)
            msg = f"EProver-based consistency check result: {is_consistent}"
            logger.info(msg)
            return is_consistent, msg
        except Exception as e:
            logger.error(
                f"Error during EProver FOL consistency check: {e}", exc_info=True
            )
            raise RuntimeError(f"EProver consistency check failed: {e}") from e

    async def _fol_check_consistency_with_mace4(self, belief_set):
        """Check FOL consistency using the Mace4 model-finder (FP-19 #1243).

        Mace4 is the SOUND CONSISTENT side of the multi-prover comparison: a
        finite model exhibits consistency. ``exhausted`` (no model up to the
        domain bound) is reported inconsistent, but the epistemic status is
        explicit (bounded model search, NOT a refutation proof). A timeout /
        crash surfaces as ``RuntimeError`` so the caller falls back honestly
        — never a fabricated verdict (#1019).

        The per-backend delivery sentinel runs first: if Mace4 cannot even find
        a model for a trivially-consistent KB, it is not reaching the binary and
        must not be trusted (raises → Tweety fallback).
        """
        logger.debug(
            f"Performing FOL consistency check via Mace4 for belief set of size "
            f"{belief_set.size()}."
        )
        if not MACE4_EXECUTABLE.is_file():
            raise RuntimeError(
                f"Mace4 binary not present at {MACE4_EXECUTABLE}; "
                "cannot run the 'mace4' solver path."
            )
        # Anti-théâtre delivery guard (#1019, #1204 generalized): verify Mace4
        # genuinely decides its SOUND direction before trusting any verdict.
        if not _mace4_delivery_is_reliable():
            raise RuntimeError(
                "Mace4 delivery contract broken (sentinel {ptest(a)} did not "
                "yield a finite model) — refusing to serve a possibly-fabricated "
                "FOL verdict."
            )
        try:
            ladr_input = _belief_set_to_ladr_assumptions(belief_set)
            logger.debug(f"Mace4 input for consistency check:\n{ladr_input}")
            mace4_output = await asyncio.to_thread(run_mace4, ladr_input)
            is_consistent, note = interpret_mace4_output(mace4_output)
            if is_consistent is None:
                # Degraded (resource limit, no verdict). Fail loud so the caller
                # falls back instead of fabricating — #1019.
                raise RuntimeError(f"Mace4 returned no verdict (degraded): {note}")
            msg = f"Mace4-based consistency check result: {is_consistent}. {note}"
            logger.info(msg)
            return is_consistent, msg
        except RuntimeError:
            raise
        except Exception as e:
            logger.error(
                f"Error during Mace4 FOL consistency check: {e}", exc_info=True
            )
            raise RuntimeError(f"Mace4 consistency check failed: {e}") from e

    def fol_query(self, belief_set, query_formula_str: str):
        """
        Checks if a query is entailed by a belief base using the configured solver.

        When the external solver is unavailable (binary absent, RuntimeError),
        falls back to the in-JVM Tweety reasoner.  Returns a tuple
        ``(entailed: bool, solver_fallback: bool)`` so callers can track
        degradation.
        """
        logger.debug(f"Performing FOL query with solver: {settings.solver.value}")

        if settings.solver == SolverChoice.PROVER9:
            try:
                return (
                    self._fol_query_with_prover9(belief_set, query_formula_str),
                    False,
                )
            except RuntimeError as e:
                logger.warning(
                    f"Prover9 unavailable ({e}), falling back to Tweety FOL query"
                )
                return self._fol_query_with_tweety(belief_set, query_formula_str), True
        elif settings.solver == SolverChoice.EPROVER:
            try:
                return (
                    self._fol_query_with_eprover(belief_set, query_formula_str),
                    False,
                )
            except RuntimeError as e:
                logger.warning(
                    f"EProver unavailable ({e}), falling back to Tweety FOL query"
                )
                return self._fol_query_with_tweety(belief_set, query_formula_str), True
        else:
            return self._fol_query_with_tweety(belief_set, query_formula_str), False

    def _fol_query_with_prover9(self, belief_set, query_formula_str: str) -> bool:
        """
        Ancienne logique d'interrogation via un processus externe Prover9.
        (Contenu de la méthode fol_query existante)
        """
        logger.debug(
            f"Performing FOL query via external Prover9. Query: '{query_formula_str}'"
        )
        try:
            # Convert belief set and query to Prover9 input format
            formulas_str = belief_set.toString().replace(";", ".\n")
            prover9_goal = query_formula_str.rstrip(".")
            # FP-8: correct Prover9 syntax — ``formulas(goals).`` not bare
            # ``goals.`` (see consistency check above). Validated empirically
            # against Prover9 2009-11A.
            prover9_input = f"formulas(assumptions).\n{formulas_str}\nend_of_list.\n\nformulas(goals).\n{prover9_goal}.\nend_of_list."

            logger.debug(f"Prover9 input for query:\n{prover9_input}")

            # Run Prover9 externally
            prover9_output = run_prover9(prover9_input)

            # FP-8: the real proof-found marker is "THEOREM PROVED" (Prover9
            # 2009-11A). "END OF PROOF" never matched (wrong case) so every
            # entailment query returned False even when the goal was proven.
            entails = "THEOREM PROVED" in prover9_output

            logger.info(f"FOL Query: KB entails '{query_formula_str}'? {entails}")
            return entails
        except Exception as e:
            logger.error(f"Error during external FOL query: {e}", exc_info=True)
            raise RuntimeError(
                f"FOL query failed. Details: {getattr(e, 'stderr', str(e))}"
            ) from e

    def _fol_query_with_tweety(self, belief_set, query_formula_str: str) -> bool:
        """
        Logique d'interrogation via Tweety/JPype.
        """
        logger.debug(f"Performing FOL query via Tweety. Query: '{query_formula_str}'")
        if not self._initializer_instance:
            raise ValueError(
                "TweetyInitializer instance is required for the 'tweety' solver path."
            )
        try:
            query_formula = self.parse_fol_formula(query_formula_str)
            reasoner = self._initializer_instance.get_reasoner("SimpleFolReasoner")
            entails = reasoner.query(belief_set, query_formula)
            return bool(entails)
        except Exception as e:
            logger.error(f"Error during Tweety FOL query: {e}", exc_info=True)
            raise

    def _fol_query_with_eprover(self, belief_set, query_formula_str: str) -> bool:
        """
        FOL query via Tweety's EFOLReasoner (backed by EProver binary).
        Uses the same Tweety parsing as the default path but delegates
        reasoning to the EProver theorem prover.
        """
        logger.debug(f"Performing FOL query via EProver. Query: '{query_formula_str}'")
        if not self._initializer_instance:
            raise ValueError(
                "TweetyInitializer instance is required for the 'eprover' solver path."
            )
        try:
            query_formula = self.parse_fol_formula(query_formula_str)
            eprover_path = _get_eprover_path()
            if eprover_path is None:
                raise RuntimeError(
                    "EProver binary not detected (EXTERNAL_TOOL_PATHS['eprover'] unset)."
                )
            JString = jpype.JClass("java.lang.String")
            EFOLReasoner = jpype.JClass(
                "org.tweetyproject.logics.fol.reasoner.EFOLReasoner"
            )
            reasoner = EFOLReasoner(JString(eprover_path))
            entails = reasoner.query(belief_set, query_formula)
            logger.info(
                f"EProver query: KB entails '{query_formula_str}'? {bool(entails)}"
            )
            return bool(entails)
        except Exception as e:
            logger.error(f"Error during EProver FOL query: {e}", exc_info=True)
            raise

    def check_consistency(self, belief_set_input) -> tuple:
        """
        Check consistency of a FOL belief set.

        Accepts either a Tweety-syntax string (parsed via local FolParser)
        or a pre-built Java FolBeliefSet object.

        #1192 (anti-theater #1019): a parse-only or reasoner-less outcome is
        NOT a consistency verdict. Previously, on a reasoner exception or a
        missing initializer, this method returned ``(True, "Parsed
        successfully...")`` — a fabricated consistent verdict with no
        reasoning behind it. It now returns ``None`` (unknown/degraded) so
        downstream consumers cannot mistake "could not check" for "is
        consistent". Only a Tweety reasoner query determines consistency.

        Returns:
            Tuple[Optional[bool], str]: ``(is_consistent, message)`` where
            ``is_consistent`` is ``True``/``False`` when the reasoner decided,
            or ``None`` when the check is degraded (reasoner unavailable or
            raised). An empty belief set is trivially consistent (``True``).
        """
        try:
            # If it's a string, parse it into a Java belief set first
            if isinstance(belief_set_input, str):
                java_belief_set = self.create_belief_set_from_string(
                    belief_set_input.strip()
                )
            else:
                # Assume it's already a Java FolBeliefSet
                java_belief_set = belief_set_input

            if java_belief_set is None or java_belief_set.size() == 0:
                return True, "Empty belief set is trivially consistent."

            # MACE4 path (FP-19 #1243): the model-finder runs as a subprocess
            # (no in-JVM reasoner), so it is dispatched before the EProver/Tweety
            # reasoner selection. Same anti-théâtre discipline: degraded => None.
            if settings.solver == SolverChoice.MACE4 and MACE4_EXECUTABLE.is_file():
                if not _mace4_delivery_is_reliable():
                    return (
                        None,
                        "Degraded: Mace4 delivery contract broken (sentinel "
                        "{ptest(a)} found no model, #1204); no consistency verdict.",
                    )
                try:
                    ladr_input = _belief_set_to_ladr_assumptions(java_belief_set)
                    mace4_output = run_mace4(ladr_input)
                    is_consistent, note = interpret_mace4_output(mace4_output)
                    if is_consistent is None:
                        return None, f"Degraded (Mace4): {note}"
                    verdict = "consistent" if is_consistent else "inconsistent"
                    return (
                        is_consistent,
                        f"FOL consistency check (Mace4): {verdict}. {note}",
                    )
                except Exception as e:
                    self.logger.warning(
                        f"Mace4 consistency check failed: {e}. Returning degraded "
                        "(None) — no fabricated verdict (#1019)."
                    )
                    return None, f"Degraded: Mace4 unavailable ({e}); no verdict."

            # Select the reasoner: the configured external solver (EProver) when
            # its binary is wired, otherwise Tweety's SimpleFolReasoner (#1196).
            # Previously this hardcoded SimpleFolReasoner regardless of
            # ``settings.solver`` — so a run configured for EProver silently
            # used the in-JVM reasoner (and OOM'd on large KBs), masking the
            # EProver integration as "active" when it never ran.
            eprover_path = _get_eprover_path()
            use_eprover = (
                settings.solver == SolverChoice.EPROVER and eprover_path is not None
            )

            # Use the configured reasoner if available via initializer / registry
            if use_eprover or self._initializer_instance:
                try:
                    if use_eprover:
                        JString = jpype.JClass("java.lang.String")
                        EFOLReasoner = jpype.JClass(
                            "org.tweetyproject.logics.fol.reasoner.EFOLReasoner"
                        )
                        # use_eprover already implies eprover_path is not None
                        # (set above); narrow for the typed sentinel call below.
                        assert eprover_path is not None
                        reasoner = EFOLReasoner(JString(eprover_path))
                        solver_name = "EProver"
                        # #1204/#1232: this SYNC path is what
                        # ``TweetyBridge.check_consistency`` and the #1210 real-
                        # eprover test actually call. The #1232 sentinel guard
                        # was wired only into the ASYNC
                        # ``_fol_check_consistency_with_eprover`` — so on a
                        # platform with a broken Tweety->E delivery contract
                        # (Linux argc=0, firsthand #1204) this path STILL
                        # fabricated "consistent" on an inconsistent KB (#1019).
                        # Apply the SAME sentinel here: if the known-inconsistent
                        # {P(a),!P(a)} is not detected, eprover cannot be trusted
                        # on this platform — fall back to the in-JVM
                        # SimpleFolReasoner, which decides correctly, instead of
                        # serving a fabricated verdict.
                        if not _eprover_delivery_is_reliable(reasoner, eprover_path):
                            if self._initializer_instance is not None:
                                reasoner = self._initializer_instance.get_reasoner(
                                    "SimpleFolReasoner"
                                )
                                solver_name = "SimpleFolReasoner"
                            else:
                                return (
                                    None,
                                    "Degraded: EProver delivery contract broken "
                                    "(#1204) and no in-JVM reasoner available; "
                                    "no consistency verdict.",
                                )
                    else:
                        reasoner = self._initializer_instance.get_reasoner(
                            "SimpleFolReasoner"
                        )
                        solver_name = "SimpleFolReasoner"
                    # Check if KB entails a contradiction
                    # Use "-" (Tweety's built-in contradiction/bottom symbol)
                    # which doesn't require any predicates in the signature
                    local_parser = jpype.JClass(
                        "org.tweetyproject.logics.fol.parser.FolParser"
                    )()
                    local_parser.setSignature(java_belief_set.getMinimalSignature())
                    contradiction = local_parser.parseFormula("-")
                    inconsistent = reasoner.query(java_belief_set, contradiction)
                    is_consistent = not bool(inconsistent)
                    msg = f"FOL consistency check ({solver_name}): {'consistent' if is_consistent else 'inconsistent'}"
                    return is_consistent, msg
                except Exception as e:
                    # Fail-loud (anti-theater): parsing succeeded but the
                    # reasoner could not decide. Do NOT fabricate a consistent
                    # verdict — return degraded (None) so callers know the
                    # check did not run.
                    self.logger.warning(
                        f"Reasoner-based consistency check failed: {e}. "
                        "Returning degraded (None) — no consistency verdict."
                    )
                    return (
                        None,
                        "Degraded: reasoner unavailable; no consistency verdict (parse-only).",
                    )
            else:
                # No initializer — cannot reason about consistency.
                # Fail-loud: degraded, not "consistent".
                return None, "Degraded: no Tweety initializer; no consistency verdict."

        except Exception as e:
            # #1290 (anti-theater #1019/#1278): an exception here means the
            # check could NOT run — most often a Tweety parse failure
            # ("Erreur de parsing Tweety") raised while building the belief set.
            # Returning ``False`` fabricated a *decided* "inconsistent" verdict
            # from a parse error: corpus_C's snapshot then carried
            # ``consistent=False`` and Acte II narrated a real "inconsistance"
            # that never happened. Per this method's own contract (docstring:
            # degraded => None), surface the honest unknown so downstream
            # consumers cannot mistake "could not check" for "is inconsistent".
            error_msg = str(e)
            self.logger.error(f"FOL consistency check failed: {error_msg}")
            return (
                None,
                f"Degraded: FOL consistency check error ({error_msg}); no verdict.",
            )

    async def compare_fol_backends(self, belief_set_input) -> dict:
        """Run ALL available FOL backends on the same belief set and compare.

        FP-19 #1243, mandate R468 ("tous les solvers handy … pour comparer les
        résultats"). Each backend (Tweety SimpleFolReasoner, EProver, Prover9,
        Mace4) is run INDEPENDENTLY on the same KB; verdicts are cross-validated.
        DISAGREEMENT is surfaced explicitly and NEVER silently reconciled — the
        comparison is the point (#1019).

        Soundness asymmetry (made explicit in the disagreement note):
        * EProver / Prover9 are sound on the **INCONSISTENT** side (refutation).
        * Mace4 is sound on the **CONSISTENT** side (a finite model is a witness);
          its "inconsistent" is only "no finite model ≤ domain bound", a bounded
          model search, NOT a refutation proof.
        * Tweety SimpleFolReasoner is the in-JVM baseline.

        Returns a JSON-serialisable dict::

            {
              "backends": {name: {"verdict": Optional[bool], "note": str,
                                  "elapsed_ms": float, "available": bool}},
              "decided":  {name: bool, …},     # only backends that returned a bool
              "agreement": Optional[bool],     # all-agree / disagree / <2 decided
              "disagreement": [str, …],        # explicit, never auto-reconciled
            }
        """
        # Build the Java belief set ONCE — every backend reasons over the same KB.
        if isinstance(belief_set_input, str):
            java_belief_set = self.create_belief_set_from_string(
                belief_set_input.strip()
            )
        else:
            java_belief_set = belief_set_input

        backends: "dict[str, dict]" = {}

        if java_belief_set is None or java_belief_set.size() == 0:
            trivial = {
                "verdict": True,
                "note": "Empty belief set is trivially consistent.",
                "elapsed_ms": 0.0,
                "available": True,
            }
            for name in ("tweety", "eprover", "prover9", "mace4"):
                backends[name] = dict(trivial)
            return {
                "backends": backends,
                "decided": {n: True for n in backends},
                "agreement": True,
                "disagreement": [],
            }

        async def _run(name, coro_factory) -> None:
            start = time.perf_counter()
            try:
                is_consistent, msg = await coro_factory()
                elapsed = (time.perf_counter() - start) * 1000.0
                backends[name] = {
                    "verdict": is_consistent,
                    "note": str(msg),
                    "elapsed_ms": round(elapsed, 1),
                    "available": True,
                }
            except Exception as e:
                elapsed = (time.perf_counter() - start) * 1000.0
                backends[name] = {
                    "verdict": None,
                    "note": f"unavailable: {e}",
                    "elapsed_ms": round(elapsed, 1),
                    "available": False,
                }

        # Each per-backend method builds its own reasoner and applies its own
        # delivery sentinel, so they can be invoked directly regardless of the
        # globally-configured ``settings.solver``.
        await _run(
            "tweety", lambda: self._fol_check_consistency_with_tweety(java_belief_set)
        )
        await _run(
            "eprover", lambda: self._fol_check_consistency_with_eprover(java_belief_set)
        )
        await _run(
            "prover9", lambda: self._fol_check_consistency_with_prover9(java_belief_set)
        )
        await _run(
            "mace4", lambda: self._fol_check_consistency_with_mace4(java_belief_set)
        )

        decided = {
            name: b["verdict"]
            for name, b in backends.items()
            if isinstance(b["verdict"], bool)
        }
        verdict_values = set(decided.values())
        if len(decided) < 2:
            agreement: "bool | None" = None
        else:
            agreement = len(verdict_values) <= 1

        disagreement: "list[str]" = []
        if agreement is False:
            consistent_backends = sorted(n for n, v in decided.items() if v is True)
            inconsistent_backends = sorted(n for n, v in decided.items() if not v)
            disagreement.append(
                f"DISAGREEMENT (NOT reconciled): {consistent_backends} report "
                f"CONSISTENT, {inconsistent_backends} report INCONSISTENT. "
                "Soundness asymmetry — EProver/Prover9 are sound on the "
                "inconsistent (refutation) side; Mace4 is sound on the consistent "
                "(model-witness) side and its 'inconsistent' is only 'no finite "
                "model up to the domain bound', not a refutation proof. Inspect "
                "the per-backend notes before drawing a conclusion."
            )

        return {
            "backends": backends,
            "decided": decided,
            "agreement": agreement,
            "disagreement": disagreement,
        }

    def execute_fol_query(self, belief_set_input, query_str: str) -> tuple:
        """
        Execute a FOL query (entailment check) against a belief set.

        Accepts either a Tweety-syntax string or a pre-built Java object
        for the belief set.

        Returns:
            Tuple[bool, str]: (entailed, message)
        """
        try:
            # Parse belief set if string
            if isinstance(belief_set_input, str):
                java_belief_set = self.create_belief_set_from_string(
                    belief_set_input.strip()
                )
            else:
                java_belief_set = belief_set_input

            if java_belief_set is None:
                return False, "Failed to create belief set."

            # Parse query formula with the belief set's signature
            FolParser = jpype.JClass("org.tweetyproject.logics.fol.parser.FolParser")
            query_parser = FolParser()
            query_parser.setSignature(java_belief_set.getMinimalSignature())
            query_formula = query_parser.parseFormula(query_str)

            # Use reasoner if available
            if self._initializer_instance:
                reasoner = self._initializer_instance.get_reasoner("SimpleFolReasoner")
                entailed = bool(reasoner.query(java_belief_set, query_formula))
                msg = (
                    f"Query '{query_str}': {'entailed' if entailed else 'not entailed'}"
                )
                return entailed, msg
            else:
                return False, "No Tweety initializer available for query."

        except (ValueError, Exception) as e:
            error_msg = str(e)
            self.logger.error(f"FOL query failed: {error_msg}")
            return False, f"FOL query error: {error_msg}"

    def validate_formula_with_signature(
        self, signature, formula_str: str
    ) -> tuple[bool, str]:
        """
        Validates a FOL formula string by creating a dedicated, temporary parser
        configured with the provided signature. This approach is thread-safe and
        avoids state-related issues with a shared parser.
        """
        FolParser = jpype.JClass("org.tweetyproject.logics.fol.parser.FolParser")

        logger.debug(
            f"Validation de la formule '{formula_str}' avec une nouvelle instance de parser."
        )

        try:
            # 1. Create a new, isolated parser instance for this validation task.
            validation_parser = FolParser()

            # 2. Set the provided signature on this isolated parser.
            validation_parser.setSignature(signature)
            self.logger.debug(
                f"Signature (Hash: {signature.hashCode()}) appliquée au parser de validation."
            )

            # 3. Perform the parsing using the dedicated parser. If it succeeds, the formula is valid.
            self.parse_fol_formula(formula_str, custom_parser=validation_parser)
            self.logger.info(
                f"La formule FOL '{formula_str}' est valide avec la signature fournie."
            )
            return True, "Formule valide."

        except (jpype.JException, ValueError) as e:
            # If parse_fol_formula throws an exception, it means the formula is invalid
            # with respect to the given signature.
            error_message = f"Error parsing FOL formula '{formula_str}': {e}"
            self.logger.warning(error_message)
            return False, str(e)
