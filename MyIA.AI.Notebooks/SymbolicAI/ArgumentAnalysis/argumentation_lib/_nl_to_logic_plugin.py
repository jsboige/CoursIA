# _nl_to_logic_plugin.py — expose la traduction texte->PL aux agents (#18390)
#
# Vendored from EPITA-IS (2025-Epita-Intelligence-Symbolique)
# Source file: argumentation_analysis/plugins/nl_to_logic_plugin.py
# Upstream commit: adc70d979475d910f93701006f68d4bbecebb305 (2026-11-06)
# Source LICENSE: MIT (Copyright (c) 2025 jsboigeEpita)
# CoursIA NOTICE: see ./NOTICE-EPITA — section "NLToLogicPlugin".
#
# ROLE DANS CoursIA (#18390)
# --------------------------
# Le tronc EPITA definit `NLToLogicPlugin` (5 fonctions LLM de traduction) :
#   translate_to_pl, translate_to_fol, translate_to_modal,
#   translate_batch_to_pl, translate_batch_to_fol.
#
# L'amont importe `argumentation_analysis.services.nl_to_logic.NLToLogicTranslator`
# qui n'existe PAS dans CoursIA. Ce module est donc un ADAPTATEUR minimal :
# il reutilise la chaine `_text_to_pl` (prompts, extraction JSON, validation
# par le vrai parseur) au lieu du service amont absent.
#
# DELTA DOCUMENTE vs upstream (adaptation, pas recopie)
# ------------------------------------------------------
# 1. Le service LLM est le service SK injecte (`AIChatCompletion`), pas un
#    `NLToLogicTranslator` amont absent. Les fonctions sont async.
# 2. La validation syntaxique est deleguee au parseur injecte (`parse_fn`),
#    typiquement `TweetyPLEngine._parse` — le vrai parseur du moteur.
# 3. Seules `translate_to_pl` et `generate_queries` sont exposees (les deux
#    fonctions du chemin texte->PL deja supporte par `_text_to_pl`). Les
#    fonctions FOL et modale de l'amont exigent des moteurs non vendores.
# 4. La baseline deterministe (`filter_formulas`) est conservee comme
#    comparateur : chaque formule affichee est validee par le parseur,
#    jamais fabriquee par le notebook.

"""Plugin SK exposant la traduction texte->PL aux agents (adaptateur #18390).

Reutilise `_text_to_pl` (prompts, extraction, validation) et le service LLM
injecte. Le parseur est injecte aussi : aucune formule n'est affichee sans
avoir ete validee par le vrai moteur.
"""

from __future__ import annotations

import json
import logging
from collections.abc import Mapping
from typing import Any, Callable, List, Optional

from semantic_kernel.contents.chat_history import ChatHistory
from semantic_kernel.functions import kernel_function

from argumentation_lib._pl_reasoner import EngineUnavailableError
from argumentation_lib._text_to_pl import (
    PROMPT_GEN_QUERIES,
    PROMPT_TEXT_TO_PL,
    belief_set_summary,
    filter_formulas,
    parse_query_response,
    parse_translation_response,
    render_prompt,
    validate_with_parser,
)

logger = logging.getLogger("argumentation_lib.nl_to_logic")


class NLToLogicPlugin:
    """Plugin SK : traduction texte->PL par LLM, validee par le vrai parseur.

    Deux fonctions kernel async :
    - `translate_to_pl` : texte -> (propositions, formules) via LLM,
      chaque formule validee par le parseur injecte ;
    - `generate_queries` : belief set -> idees de requetes via LLM.

    Le service SK (`AIChatCompletion`) est injecte a la construction.
    Le parseur `parse_fn(formula)` est injecte aussi (typiquement le
    `_parse` de `TweetyPLEngine`). Sans l'un ni l'autre, le plugin leve
    a la construction — pas de degrade silencieux.

    `execution_settings` est une INSTANCE de `PromptExecutionSettings` (ou
    `None` : elle est alors construite depuis la fabrique du service). Ce
    n'est PAS le dict `{service_id: settings}` de `KernelArguments` — un dict
    est refuse a la construction (cf B1 de la revue de #24951).
    """

    def __init__(
        self,
        llm_service: Any,
        parse_fn: Callable[[str], Any],
        kernel: Any = None,
        execution_settings: Any = None,
    ) -> None:
        if llm_service is None:
            raise ValueError("llm_service est obligatoire")
        if not callable(parse_fn):
            raise TypeError("parse_fn doit etre appelable")
        if isinstance(execution_settings, Mapping):
            # La forme {service_id: settings} est celle de `KernelArguments`
            # (AIServiceSelector indexe par service). Un service SK attend, lui,
            # UNE instance : passe un dict, `get_chat_message_contents` leve
            # `'dict' object has no attribute 'pack_extension_data'` (B1 de la
            # revue de #24951). Le refus est explicite pour que le contrat ne
            # se re-perde pas.
            raise TypeError(
                "execution_settings doit etre une INSTANCE de "
                "PromptExecutionSettings ; la forme {service_id: settings} est "
                "celle de KernelArguments, pas celle de "
                "get_chat_message_contents(settings=...)"
            )
        self._llm_service = llm_service
        self._parse_fn = parse_fn
        self._kernel = kernel
        self._execution_settings = execution_settings
        self._logger = logger

    def _settings(self) -> Any:
        """Reglages a passer a `get_chat_message_contents` : une INSTANCE.

        Trois sources, dans cet ordre : l'instance injectee, la fabrique du
        service resolu (`get_prompt_execution_settings_class`), puis les
        reglages par defaut de SK. Sans SK importable (test a mock minimal), il
        n'y a pas de service reel en face : on rend `None` et l'appel omet le
        parametre.
        """
        if self._execution_settings is not None:
            return self._execution_settings
        factory = getattr(self._llm_service, "get_prompt_execution_settings_class", None)
        if callable(factory):
            return factory()()
        try:
            from semantic_kernel.connectors.ai.prompt_execution_settings import (
                PromptExecutionSettings,
            )
        except Exception:  # pragma: no cover - SK absent, donc service factice
            return None
        return PromptExecutionSettings()

    async def _chat(self, prompt: str) -> str:
        """Appel LLM sur le service SK injecte.

        `settings` est un parametre OBLIGATOIRE de
        `get_chat_message_contents(chat_history, settings, **kwargs)` en SK
        1.44 : il recoit toujours une instance (cf `_settings`).
        """
        history = ChatHistory()
        history.add_user_message(prompt)
        kwargs: dict = {"chat_history": history}
        settings = self._settings()
        if settings is not None:
            kwargs["settings"] = settings
        if self._kernel is not None:
            kwargs["kernel"] = self._kernel
        response = await self._llm_service.get_chat_message_contents(**kwargs)
        if response and len(response) > 0:
            return str(response[0].content) if hasattr(response[0], "content") else str(response[0])
        return ""

    @kernel_function(
        description=(
            "Traduit un texte en logique propositionnelle (PL) via LLM. "
            "Renvoie un objet JSON avec les cles `propositions` (atomes "
            "declares), `formulas` (formules validees par le parseur) et "
            "`rejected` (formules refusees par le parseur). "
            "Syntaxe PL : `!` (non), `&&` (et), `||` (ou), `=>` (implique), "
            "`<=>` (equivalent). Les atomes sont des identifiants snake_case."
        ),
        name="translate_to_pl",
    )
    async def translate_to_pl(self, text: str) -> str:
        """Texte -> belief set PL via LLM + validation par le parseur."""
        prompt = render_prompt(PROMPT_TEXT_TO_PL, input=text)
        raw = await self._chat(prompt)
        propositions, formulas = parse_translation_response(raw)
        formulas = filter_formulas(formulas, propositions)
        accepted, rejected = validate_with_parser(
            formulas, self._parse_fn, fatal_exceptions=(EngineUnavailableError,)
        )
        return json.dumps(
            {
                "propositions": propositions,
                "formulas": accepted,
                "rejected": rejected,
            },
            ensure_ascii=False,
            indent=2,
        )

    @kernel_function(
        description=(
            "Genere des idees de requetes PL a partir d'un texte et d'un "
            "belief set. Renvoie une liste JSON de formules a verifier. "
            "Utilise le LLM pour proposer les requetes pertinentes."
        ),
        name="generate_queries",
    )
    async def generate_queries(self, text: str, propositions: str, formulas: str) -> str:
        """Belief set + texte -> idees de requetes via LLM."""
        prop_list = json.loads(propositions) if propositions else []
        form_list = json.loads(formulas) if formulas else []
        bs_summary = belief_set_summary(prop_list, form_list)
        prompt = render_prompt(PROMPT_GEN_QUERIES, input=text, belief_set=bs_summary)
        raw = await self._chat(prompt)
        queries = parse_query_response(raw)
        return json.dumps(queries, ensure_ascii=False)
