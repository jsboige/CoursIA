"""Adaptateur modal K : parseur Tweety et solveur SPASS de la série."""
from __future__ import annotations

import os
import shutil

from argumentation_lib._pl_reasoner import EngineUnavailableError, FormulaSyntaxError


class TweetyModalEngine:
    """Utilise MlParser et SPASSMlReasoner, sans importer le bridge EPITA."""

    def __init__(self) -> None:
        from argumentation_lib._jvm_compat import initialize_jvm

        cwd = os.getcwd()
        try:
            ready = initialize_jvm()
        finally:
            os.chdir(cwd)
        if not ready:
            raise EngineUnavailableError("JVM/Tweety indisponible")
        import jpype

        self._parser_class = jpype.JClass("org.tweetyproject.logics.ml.parser.MlParser")
        self._reasoner_class = jpype.JClass("org.tweetyproject.logics.ml.reasoner.SPASSMlReasoner")

    def _belief_and_parser(self, belief_set: str):
        parser = self._parser_class()
        try:
            belief = parser.parseBeliefBase(belief_set)
        except Exception as exc:
            raise FormulaSyntaxError(belief_set, str(exc)[:200]) from exc
        return belief, parser

    def validate(self, signature: str, formula: str) -> None:
        # La déclaration et la formule doivent être dans le même parseur.
        _, parser = self._belief_and_parser(signature + "\n" + formula)
        self._parse(parser, formula)

    def entails(self, belief_set: str, query: str) -> bool:
        belief, parser = self._belief_and_parser(belief_set)
        parsed = self._parse(parser, query)
        from Tweety.tweety_init import EXTERNAL_TOOLS

        spass = EXTERNAL_TOOLS.get("SPASS") or shutil.which("SPASS")
        if not spass or not os.path.isfile(spass) or not os.access(spass, os.X_OK):
            raise EngineUnavailableError("SPASS introuvable ou non exécutable")
        return bool(self._reasoner_class(spass).query(belief, parsed))

    @staticmethod
    def _parse(parser, formula: str):
        try:
            return parser.parseFormula(formula)
        except Exception as exc:
            raise FormulaSyntaxError(formula, str(exc)[:200]) from exc
