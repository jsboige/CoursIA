"""Reglages LLM partages du shim -- compatibilite generation 5.6 (#20135).

Mesure firsthand du 2026-10-18 : sur /v1/chat/completions, la famille gpt-5.6
(luna, terra, sol) refuse les outils de fonction (FunctionChoiceBehavior) tant
qu'aucun `reasoning_effort` explicite n'est fourni -- 400 « Function tools with
reasoning_effort are not supported ... use /v1/responses ». Avec
`reasoning_effort="none"`, les trois modeles acceptent les outils
(finish=tool_calls). « minimal » n'est pas supporte par luna (valeurs valides :
none/low/medium/high/xhigh).

Le champ type `reasoning_effort` de Semantic Kernel 1.42 n'admet que
low/medium/high : y ecrire "none" leve une ValidationError pydantic. La valeur
passe donc par `extra_body`, que `prepare_settings_dict()` transmet tel quel a
`client.chat.completions.create(...)` -- canal prevu pour les options non
couvertes par la version du connecteur.

Ce module porte le seul point ou l'on force la valeur pour les modeles 5.6 ;
les sites qui construisent des settings avec outils de fonction
(_informal_definitions, _fallacy_workflow_plugin, _runner) l'appellent.
"""

from __future__ import annotations

from typing import Optional

# Familles dont l'endpoint chat/completions exige un reasoning_effort explicite
# pour accepter les outils de fonction (mesure 2026-10-18 sur luna/terra/sol).
REASONING_NONE_PREFIXES = ("gpt-5.6",)


def apply_reasoning_none_for_function_tools(settings, model_id: Optional[str]):
    """Force reasoning_effort="none" si le modele appartient a la famille 5.6.

    Retourne `settings` inchanges pour tout autre modele (aucun effet de bord
    sur les generations qui ne posent pas la contrainte).
    """
    if isinstance(model_id, str) and model_id.startswith(REASONING_NONE_PREFIXES):
        if hasattr(settings, "extra_body"):
            extra = dict(getattr(settings, "extra_body", None) or {})
            extra.setdefault("reasoning_effort", "none")
            settings.extra_body = extra
    return settings