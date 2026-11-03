#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""Adaptation declaree du transport LLM de la couche `LLMValidatorLayer`.

Pourquoi cette adaptation existe
---------------------------------
La couche `llm_validator` d'EPITA s'appuie sur quatre services du runtime EPITA
(`core.llm_service`, `core.reading_window`, `core.utils.llm_completion_guard`,
`services.llm_cache`) qui ne sont **pas** vendoringes dans CoursIA. Plutot que de
reimplementer la couche -- ce qui en aurait fait une copie divergente -- on
**conserve la couche verbatim** et on lui fournit ici les quatre primitives dont
elle a besoin.

Ce que ce module garantit
-------------------------
**Aucun fournisseur LLM n'est cable dans CoursIA** : `resolve_chat_endpoint()`
rend `(None, None, None)`. La couche amont leve alors `LLMValidatorUnavailable`
(sa cle d'absence), que le `Shield` transforme en erreur de couche et que la
politique `fail_open` / `fail_closed` tranche. C'est exactement le cas que le
carnet `Argumentation-09` veut rendre visible : **un validateur qui ne peut pas
tourner ne doit jamais dire "aucune menace"**.

C'est aussi ce qui rend le carnet **reproductible** : aucun appel reseau, aucune
cle, aucun resultat non deterministe dans les sorties commitees.

Point d'extension : le jour ou un fournisseur est cable dans CoursIA, c'est
**ce seul fichier** qu'il faut modifier ; la couche amont reste intacte.

Portage dans le cadre de l'issue #23163 (serie `Argument_Analysis` completee sur
CoursIA). Licence amont : MIT (Copyright (c) 2025 jsboigeEpita) — voir
`argumentation_lib/NOTICE-EPITA`.
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Tuple

__all__ = [
    "resolve_chat_endpoint",
    "selected_text",
    "assert_not_reasoning_starved",
    "cached_raw_chat_completion_sync",
]


def resolve_chat_endpoint() -> Tuple[Optional[str], Optional[str], Optional[str]]:
    """Rend `(api_key, base_url, model)` — toujours `(None, None, None)` ici.

    Aucun fournisseur n'est cable dans CoursIA : la couche doit donc lever
    `LLMValidatorUnavailable` plutot que de rendre un score. Un couplage futur
    se fait ici, et nulle part ailleurs.
    """
    return (None, None, None)


def selected_text(text: str, window: int, site: str) -> str:
    """Tronque le texte analyse a la fenetre autorisee (amont : `reading_window`).

    Le comportement observable de la couche est identique : ce qui compte pour
    le carnet est la **longueur du contexte envoye au validateur**, pas le
    mecanisme de fenetrage.
    """
    if window <= 0:
        return text
    return text[:window]


def assert_not_reasoning_starved(
    finish_reason: Optional[str], content: Optional[str], site: str
) -> None:
    """Leve si le budget de raisonnement a ete epuise sans contenu.

    Contrainte amont preservee : une reponse vide avec `finish_reason == "length"`
    n'est **pas** un zero legitime, c'est une panne. Elle doit etre nommee, pas
    absorbee en "aucune menace".
    """
    if finish_reason == "length" and not (content or "").strip():
        raise RuntimeError(
            f"reasoning starved at {site}: finish_reason='length' with empty content"
        )


def cached_raw_chat_completion_sync(
    client: Any,
    model: Optional[str],
    messages: List[Dict[str, str]],
    max_completion_tokens: Optional[int] = None,
) -> Any:
    """Appel de chat synchrone, sans cache local.

    L'amout memorise la reponse brute dans un cache de service ; CoursIA n'a pas
    ce service. Le contrat observable — une reponse dont on lit
    `choices[0].message.content` et `choices[0].finish_reason` — est preserve.
    """
    kwargs: Dict[str, Any] = {"model": model, "messages": messages}
    if max_completion_tokens is not None:
        kwargs["max_completion_tokens"] = max_completion_tokens
    return client.chat.completions.create(**kwargs)
