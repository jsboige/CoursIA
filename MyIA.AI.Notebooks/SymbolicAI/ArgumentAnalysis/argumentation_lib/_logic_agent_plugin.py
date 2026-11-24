# _logic_agent_plugin.py — la moitie verdict de la phase formelle (#18390)
#
# Vendored from EPITA-IS (2025-Epita-Intelligence-Symbolique)
# Source file: argumentation_analysis/plugins/logic_agent_plugin.py
# Upstream commit: 1bce902c44590af8e98d3f506f57b5388ad23bb4 (copie du
#   2026-11-08 ; dernier toucher amont du fichier : 7eaacd0a4, 2026-09-26,
#   #2612 "PL queries run on the real entailment surface")
# Source LICENSE: MIT (Copyright (c) 2025 jsboigeEpita)
# CoursIA NOTICE: see ./NOTICE-EPITA — section "LogicAgentPlugin".
#
# ROLE DANS CoursIA (#18390)
# --------------------------
# Inventaire EPITA du 27/10 (commentaire de jsboigeEpita sur #18390) :
# `LogicAgentPlugin` (8 fonctions moteur seul, zero injection) est la
# moitie VERDICT de la phase formelle, avec `NLToLogicPlugin` (livre par
# #24951) comme moitie traduction. L'amont monte ce plugin via
# `kernel.add_plugin(LogicAgentPlugin(), plugin_name="logic_agents")`.
#
# DELTA DOCUMENTE vs upstream (adaptation, pas recopie)
# ------------------------------------------------------
# 1. L'amont lazy-importe `TweetyBridge` dans chaque methode. Le bridge
#    vendore (`_tweety_bridge.py`) n'est PAS importable dans ce checkout
#    (mesure 2026-11-08 : `ModuleNotFoundError: argumentation_lib.pl_handler`
#    — 3 handlers amont non vendorés + préfixe underscore ; caveat G.9 de
#    `__init__.py`). Une copie verbatim serait une surface morte :
#    `_jvm_available()` avale l'erreur d'import et chaque fonction
#    rendrait `{"error": "JVM/Tweety non disponible"}` — exactement la
#    « capacité sans successeur » que #18390 dénonce.
# 2. La moitié PL (parse_pl_formula, execute_pl_query, check_pl_consistency,
#    validate_formula/propositionnelle) est routée sur le moteur REEL de
#    la série : `TweetyPLEngine` (`_pl_reasoner.py`, SatReasoner/SAT4j).
#    Ce choix hérite des deux incidents mesurés : #23671 (SatReasoner et
#    non SimplePlReasoner, qui meurt en OOM JVM sur les belief sets
#    réels) et #23120 (garde de contenu + réécriture `->` en `=>` AVANT
#    l'appel au solveur).
# 3. `check_pl_consistency` décide par le VRAI solveur (sonde ex falso :
#    un ensemble est incohérent ssi il entraîne une contradiction) — le
#    verdict n'est jamais fabriqué.
# 4. FOL reste indisponible. La logique modale K utilise MlParser et
#    SPASSMlReasoner ; T et S5 restent indisponibles explicitement.
# 5. Pas de couplage registre : le contrat amont rend du JSON ; les
#    verdicts registre-bound du carnet 08b passent par
#    `PLReasonerPlugin.pl_query` (belief_set_id, chaîne `ACCEPTED: ...`).
# 6. La docstring amont annonce une 4e capacité « Translating natural
#    language to formal belief sets (LLM-required) » qu'aucune fonction
#    décorée ne porte (écart relevé par l'inventaire du 27/10) : la
#    docstring d'ici renvoie à `NLToLogicPlugin`, qui porte cette
#    capacité.

"""Plugin SK exposant les opérations logiques PL/FOL/Modales aux agents.

Moitié verdict de la phase formelle (#18390) : les fonctions PL décident
par le VRAI solveur Tweety (SatReasoner), les fonctions modales K utilisent
Tweety/SPASS ; FOL reste indisponible. La traduction texte -> formule vit dans
`NLToLogicPlugin` (`_nl_to_logic_plugin.py`).
"""

from __future__ import annotations

import json
import logging
from typing import Any

from semantic_kernel.functions import kernel_function

logger = logging.getLogger(__name__)

#: Atome de la sonde ex falso : un ensemble de formules est incohérent
#: ssi il entraîne une contradiction. L'atome est choisi hors du langage
#: des carnets pour ne jamais entrer en collision avec une formule réelle.
_CONSISTENCY_PROBE_FORMULA = "pl_consistency_probe && !pl_consistency_probe"


def _error_json(msg: str) -> str:
    return json.dumps({"error": msg}, ensure_ascii=False)


def _fol_unavailable() -> str:
    return _error_json(
        "FOL indisponible dans ce checkout : les handlers amont "
        "(fol_handler via TweetyBridge) ne sont pas importables au pin "
        "actuel (voir NOTICE-EPITA) — aucune requête n'est simulée."
    )


class LogicAgentPlugin:
    """Semantic Kernel plugin exposant les opérations logiques PL/FOL/Modales.

    Fournit des méthodes @kernel_function pour :
    1. Parser et valider des formules pour chaque logique
    2. Exécuter des requêtes sur des ensembles de croyances
    3. Vérifier la cohérence d'ensembles de croyances
    4. Traduire le langage naturel en belief sets — cette capacité vit
       dans `NLToLogicPlugin` (voir `_nl_to_logic_plugin.py`), pas ici.

    Usage :
        kernel.add_plugin(LogicAgentPlugin(), plugin_name="logic_agents")

    Dans ce checkout : les fonctions PL décident par le VRAI solveur
    (`TweetyPLEngine`, SatReasoner) ; la logique modale K utilise SPASS.
    FOL et les autres logiques modales restent indisponibles.
    """

    def __init__(self, engine: Any = None) -> None:
        """Le moteur est injectable pour les tests ; sinon créé à la demande."""
        self._engine = engine

    def _get_engine(self) -> Any:
        if self._engine is None:
            from argumentation_lib._pl_reasoner import TweetyPLEngine

            self._engine = TweetyPLEngine()
        return self._engine

    # --- Propositional Logic (PL) ---

    @kernel_function(
        name="parse_pl_formula",
        description=(
            "Analyser et valider une formule de logique propositionnelle. "
            "Vérifie la syntaxe via TweetyProject. "
            "Entrée: formule PL (ex: 'a => b', '!(p && q)'). "
            "Retourne JSON: {'is_valid', 'formula', 'error'}."
        ),
    )
    def parse_pl_formula(self, formula: str) -> str:
        """Valider la syntaxe d'une formule propositionnelle (vrai parseur)."""
        from argumentation_lib._pl_reasoner import (
            EngineUnavailableError,
            FormulaSyntaxError,
            non_propositional_line,
            normalize_implication,
        )

        formula = normalize_implication(formula)
        # #23120 : la garde précède le parseur — une phrase n'est pas une
        # formule, même si PlParser l'accepte comme conjonction d'atomes-mots.
        if non_propositional_line([formula]) is not None:
            return json.dumps(
                {
                    "is_valid": False,
                    "formula": formula,
                    "error": "la formule n'est pas propositionnelle (une "
                    "phrase n'est pas une formule) ; syntaxe PL : atomes = "
                    "identifiants, connecteurs `!`, `&&`, `||`, `=>`, `<=>`",
                },
                ensure_ascii=False,
            )
        try:
            self._get_engine()._parse(formula)
            return json.dumps(
                {"is_valid": True, "formula": formula, "error": None},
                ensure_ascii=False,
            )
        except FormulaSyntaxError as exc:
            return json.dumps(
                {"is_valid": False, "formula": formula, "error": exc.detail},
                ensure_ascii=False,
            )
        except EngineUnavailableError as exc:
            return _error_json(f"moteur PL indisponible : {exc}")

    @kernel_function(
        name="execute_pl_query",
        description=(
            "Exécuter une requête PL sur un ensemble de croyances. "
            "Entrée: JSON {'belief_set': 'a => b\\nb', 'query': 'b'}. "
            "Retourne JSON: {'result', 'query', 'belief_set', 'accepted'}."
        ),
    )
    def execute_pl_query(self, payload: str) -> str:
        """Exécuter une requête PL sur un belief set (vrai solveur SAT4j)."""
        from argumentation_lib._pl_reasoner import (
            EngineUnavailableError,
            FormulaSyntaxError,
            non_propositional_line,
            normalize_implication,
            split_formulas,
        )

        try:
            params = json.loads(payload) if isinstance(payload, str) else payload
            belief_set = params.get("belief_set", "")
            query = normalize_implication(params.get("query", ""))
        except (TypeError, ValueError) as exc:
            return _error_json(f"payload illisible : {exc}")

        formulas = [normalize_implication(f) for f in split_formulas(belief_set)]
        if not formulas:
            return _error_json("belief set vide : une formule par ligne")
        bad_line = non_propositional_line(formulas)
        if bad_line is not None:
            return _error_json(
                f"ligne non propositionnelle {bad_line[:80]!r} ; une phrase "
                "n'est pas une formule"
            )
        if non_propositional_line([query]) is not None:
            return _error_json(
                f"requête non propositionnelle {query[:80]!r} ; une phrase "
                "n'est pas une formule"
            )
        try:
            accepted = bool(self._get_engine().entails(formulas, query))
        except FormulaSyntaxError as exc:
            return _error_json(str(exc))
        except EngineUnavailableError as exc:
            return _error_json(f"moteur PL indisponible : {exc}")
        message = f"Résultat de l'inférence: {accepted}."
        return json.dumps(
            {
                "result": message,
                "query": query,
                "belief_set": belief_set[:200],
                "truncated": len(belief_set) > 200,
                "accepted": accepted,
            },
            ensure_ascii=False,
        )

    @kernel_function(
        name="check_pl_consistency",
        description=(
            "Vérifier la cohérence d'un ensemble de croyances propositionnelles. "
            "Entrée: ensemble de croyances PL (formules séparées par \\n). "
            "Retourne JSON: {'is_consistent', 'belief_set', 'message'}."
        ),
    )
    def check_pl_consistency(self, belief_set: str) -> str:
        """Vérifier la cohérence d'un belief set PL (décidé par le solveur).

        Sonde ex falso : un ensemble est incohérent ssi il entraîne une
        contradiction. La sonde est une formule du langage décidée par le
        VRAI SatReasoner — le verdict n'est pas calculé en Python.
        """
        from argumentation_lib._pl_reasoner import (
            EngineUnavailableError,
            FormulaSyntaxError,
            non_propositional_line,
            normalize_implication,
            split_formulas,
        )

        formulas = [normalize_implication(f) for f in split_formulas(belief_set)]
        if not formulas:
            return json.dumps(
                {
                    "is_consistent": True,
                    "belief_set": belief_set[:200],
                    "truncated": len(belief_set) > 200,
                    "message": "ensemble vide : cohérent par convention",
                },
                ensure_ascii=False,
            )
        bad_line = non_propositional_line(formulas)
        if bad_line is not None:
            return _error_json(
                f"ligne non propositionnelle {bad_line[:80]!r} ; une phrase "
                "n'est pas une formule"
            )
        try:
            entailed_contradiction = bool(
                self._get_engine().entails(formulas, _CONSISTENCY_PROBE_FORMULA)
            )
        except FormulaSyntaxError as exc:
            return _error_json(str(exc))
        except EngineUnavailableError as exc:
            return _error_json(f"moteur PL indisponible : {exc}")
        is_consistent = not entailed_contradiction
        message = (
            "décidé par SatReasoner (sonde ex falso : un ensemble est "
            "incohérent ssi il entraîne une contradiction)"
        )
        return json.dumps(
            {
                "is_consistent": is_consistent,
                "belief_set": belief_set[:200],
                "truncated": len(belief_set) > 200,
                "message": message,
            },
            ensure_ascii=False,
        )

    # --- First-Order Logic (FOL) ---

    @kernel_function(
        name="execute_fol_query",
        description=(
            "Exécuter une requête FOL sur un ensemble de croyances. "
            "Entrée: JSON {'belief_set': 'forall X: (p(X) => q(X))\\nexists Y: p(Y)', "
            "'query': 'exists Z: q(Z)'}. "
            "Retourne JSON: {'result', 'query', 'accepted'}."
        ),
    )
    def execute_fol_query(self, payload: str) -> str:
        """Exécuter une requête FOL — moteur non câblé au pin actuel."""
        return _fol_unavailable()

    @kernel_function(
        name="check_fol_consistency",
        description=(
            "Vérifier la cohérence d'un ensemble de croyances FOL. "
            "Entrée: ensemble de croyances FOL. "
            "Retourne JSON: {'is_consistent', 'message'}."
        ),
    )
    def check_fol_consistency(self, belief_set: str) -> str:
        """Vérifier la cohérence FOL — moteur non câblé au pin actuel."""
        return _fol_unavailable()

    # --- Modal Logic ---

    @kernel_function(
        name="execute_modal_query",
        description=(
            "Exécuter une requête modale sur un ensemble de croyances. "
            "Entrée: JSON {'belief_set': 'type(a)\\ntype(b)\\n[](a => b)\\n[](a)', "
            "'query': '[](a)', 'logic_type': 'K'}. "
            "Logique K uniquement ; déclarer les prédicats avec type(a). "
            "Retourne JSON: {'result', 'query', 'accepted'}."
        ),
    )
    def execute_modal_query(self, payload: str) -> str:
        """Interroger SPASS via Tweety en logique K."""
        from argumentation_lib._modal_reasoner import TweetyModalEngine
        from argumentation_lib._pl_reasoner import (
            EngineUnavailableError, FormulaSyntaxError,
        )

        try:
            params = json.loads(payload)
            if not isinstance(params, dict):
                raise ValueError("objet JSON attendu")
            belief_set, query = params.get("belief_set", ""), params.get("query", "")
            if not isinstance(belief_set, str) or not isinstance(query, str) or not query.strip():
                raise ValueError("belief_set et query doivent être des chaînes, query non vide")
            if params.get("logic_type", "K") != "K":
                return _error_json("logique modale indisponible : seul K est pris en charge")
            accepted = TweetyModalEngine().entails(belief_set, query)
        except (TypeError, ValueError, EngineUnavailableError, FormulaSyntaxError) as exc:
            return _error_json(str(exc))
        return json.dumps({"result": f"Résultat de l'inférence: {accepted}.",
                           "query": query, "accepted": accepted}, ensure_ascii=False)

    @kernel_function(
        name="check_modal_consistency",
        description=(
            "Vérifier la cohérence d'un ensemble de croyances modales. "
            "Entrée: JSON {'belief_set': '...formulas...', 'logic_type': 'K'}. "
            "Retourne JSON: {'is_consistent', 'message'}."
        ),
    )
    def check_modal_consistency(self, payload: str) -> str:
        """Vérifier la cohérence par une sonde de contradiction SPASS."""
        from argumentation_lib._modal_reasoner import TweetyModalEngine
        from argumentation_lib._pl_reasoner import (
            EngineUnavailableError, FormulaSyntaxError,
        )

        try:
            params = json.loads(payload)
            if not isinstance(params, dict):
                raise ValueError("objet JSON attendu")
            belief_set = params.get("belief_set", "")
            if not isinstance(belief_set, str):
                raise ValueError("belief_set doit être une chaîne")
            if params.get("logic_type", "K") != "K":
                return _error_json("logique modale indisponible : seul K est pris en charge")
            consistent = not TweetyModalEngine().entails(belief_set, "-")
        except (TypeError, ValueError, EngineUnavailableError, FormulaSyntaxError) as exc:
            return _error_json(str(exc))
        return json.dumps({"is_consistent": consistent,
                           "message": "décidé par Tweety SPASSMlReasoner (K)"}, ensure_ascii=False)

    # --- Cross-logic utilities ---

    @kernel_function(
        name="validate_formula",
        description=(
            "Valider la syntaxe d'une formule logique. "
            "Entrée: JSON {'formula': 'a => b', 'logic_type': 'propositional'}. "
            "Types: 'propositional', 'fol', 'modal'. Pour modal, fournir "
            "signature: déclarations type(a) séparées par des retours à la ligne. "
            "Retourne JSON: {'is_valid', 'formula', 'logic_type'}."
        ),
    )
    def validate_formula(self, payload: str) -> str:
        """Valider la syntaxe d'une formule pour le type de logique donné."""
        try:
            params = json.loads(payload) if isinstance(payload, str) else payload
            formula = params.get("formula", "")
            logic_type = params.get("logic_type", "propositional")
        except (TypeError, ValueError) as exc:
            return _error_json(f"payload illisible : {exc}")

        if logic_type == "propositional":
            parsed = json.loads(self.parse_pl_formula(formula))
            return json.dumps(
                {
                    "is_valid": parsed.get("is_valid", False),
                    "formula": formula,
                    "logic_type": logic_type,
                    "error": parsed.get("error"),
                },
                ensure_ascii=False,
            )
        if logic_type == "fol":
            return _fol_unavailable()
        if logic_type == "modal":
            from argumentation_lib._modal_reasoner import TweetyModalEngine
            from argumentation_lib._pl_reasoner import (
                EngineUnavailableError, FormulaSyntaxError,
            )

            try:
                signature = params.get("signature", "")
                if not isinstance(formula, str) or not formula.strip() or not isinstance(signature, str):
                    raise ValueError("formule non vide et signature textuelle attendues")
                TweetyModalEngine().validate(signature, formula)
            except FormulaSyntaxError as exc:
                return json.dumps({"is_valid": False, "formula": formula,
                                   "logic_type": logic_type, "error": str(exc)}, ensure_ascii=False)
            except (ValueError, EngineUnavailableError) as exc:
                return _error_json(str(exc))
            return json.dumps({"is_valid": True, "formula": formula,
                               "logic_type": logic_type, "error": None}, ensure_ascii=False)
        return _error_json(f"Unknown logic_type: {logic_type}")
