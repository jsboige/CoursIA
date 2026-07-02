"""
Client Python pour Claudish — proxy Anthropic-compatible multi-providers.

Claudish expose le wire Anthropic standard (`POST /v1/messages`) derriere
une URL unique (par defaut `http://localhost:3000` en local, ou
`https://models.myia.io` en production). Le client de ce module suit
exactement ce wire : headers `x-api-key`, `anthropic-version`, body
`{model, max_tokens, messages, stream}`.

Le tier budgete par defaut dans le cluster MyIA :

| Tier | Modele visible     | Provider reel               |
|------|--------------------|----------------------------|
| Opus | claude-opus-4-8    | Anthropic natif            |
| Sonnet| glm-5.2           | z.ai GLM Coding Plan       |
| Haiku| qwen3.6-35b-a3b    | vLLM self-heberge (po-2023)|

Voir `docs/Claudish-Proxy.md` section 3 pour le detail du router
no-fallback (3 providers, pas de bascule silencieuse).
"""

import json
import os
from typing import Iterator, List, Optional

import httpx


# URL par defaut : localhost en dev, models.myia.io en prod
DEFAULT_BASE_URL = os.environ.get("CLAUDISH_BASE_URL", "http://localhost:3000")
ANTHROPIC_VERSION = "2023-06-01"

# Modeles exposes par defaut par le deploiement MyIA (cf /v1/models)
KNOWN_MODELS = [
    "claude-opus-4-8",       # Opus -> Anthropic natif
    "glm-5.2",               # Sonnet -> z.ai GLM Coding
    "glm-5.1",               # Sonnet (alias)
    "glm-4.7",               # Sonnet (alias historique)
    "qwen3.6-35b-a3b",       # Haiku -> Qwen vLLM
    "MiniMax-M3",            # Haiku (pool secondaire)
]


def get_endpoint(base_url: Optional[str] = None) -> str:
    """Retourne l'URL complet du endpoint /v1/messages."""
    base = (base_url or DEFAULT_BASE_URL).rstrip("/")
    return f"{base}/v1/messages"


def get_api_key(env_var: str = "ANTHROPIC_AUTH_TOKEN") -> Optional[str]:
    """Recupere la cle Claudish depuis l'environnement (jamais de fallback inline)."""
    key = os.environ.get(env_var)
    if not key:
        return None
    return key


def list_models(base_url: Optional[str] = None, timeout: float = 5.0) -> List[dict]:
    """Liste les modeles exposes par Claudish (endpoint /v1/models)."""
    base = (base_url or DEFAULT_BASE_URL).rstrip("/")
    with httpx.Client(timeout=timeout) as client:
        r = client.get(f"{base}/v1/models")
        r.raise_for_status()
        data = r.json()
    return data.get("data", [])


def chat(
    prompt: str,
    model: str = "glm-5.2",
    max_tokens: int = 256,
    system: Optional[str] = None,
    base_url: Optional[str] = None,
    api_key: Optional[str] = None,
    timeout: float = 60.0,
) -> str:
    """Envoie un prompt a Claudish via le wire Anthropic et retourne le texte.

    Args:
        prompt: Question utilisateur.
        model: Identifiant modele vu du client (ex: ``glm-5.2``).
        max_tokens: Limite de tokens en sortie.
        system: Prompt systeme optionnel.
        base_url: URL de base Claudish (override env).
        api_key: Cle d'authentification (override env ``ANTHROPIC_AUTH_TOKEN``).
        timeout: Timeout HTTP en secondes.

    Returns:
        Le texte de la reponse (champ ``content[0].text`` du wire Anthropic).

    Raises:
        RuntimeError: si la cle API manque, ou si la reponse est en erreur.
    """
    key = api_key or get_api_key()
    if not key:
        raise RuntimeError(
            "Cle Claudish manquante : definir ANTHROPIC_AUTH_TOKEN "
            "(voir configs/claudish.env.secrets.example)."
        )

    messages = [{"role": "user", "content": prompt}]
    payload = {
        "model": model,
        "max_tokens": max_tokens,
        "messages": messages,
    }
    if system:
        payload["system"] = system

    headers = {
        "x-api-key": key,
        "anthropic-version": ANTHROPIC_VERSION,
        "content-type": "application/json",
    }

    with httpx.Client(timeout=timeout) as client:
        r = client.post(get_endpoint(base_url), headers=headers, json=payload)
        if r.status_code >= 400:
            raise RuntimeError(
                f"Claudish HTTP {r.status_code} : {r.text[:500]}"
            )
        data = r.json()

    # Wire Anthropic : content est une liste de blocs {type: "text", text: "..."}
    content = data.get("content", [])
    texts = [block.get("text", "") for block in content if block.get("type") == "text"]
    return "\n".join(texts).strip()


def stream_chat(
    prompt: str,
    model: str = "glm-5.2",
    max_tokens: int = 256,
    base_url: Optional[str] = None,
    api_key: Optional[str] = None,
    timeout: float = 60.0,
) -> Iterator[str]:
    """Version streaming du chat. Yield les deltas de texte au fur et a mesure.

    Le wire Anthropic streaming renvoie des evenements SSE
    (``event: content_block_delta``). Ce helper les parse et yield
    uniquement le texte.
    """
    key = api_key or get_api_key()
    if not key:
        raise RuntimeError(
            "Cle Claudish manquante : definir ANTHROPIC_AUTH_TOKEN."
        )

    payload = {
        "model": model,
        "max_tokens": max_tokens,
        "messages": [{"role": "user", "content": prompt}],
        "stream": True,
    }
    headers = {
        "x-api-key": key,
        "anthropic-version": ANTHROPIC_VERSION,
        "content-type": "application/json",
    }

    with httpx.Client(timeout=timeout) as client:
        with client.stream(
            "POST", get_endpoint(base_url), headers=headers, json=payload
        ) as response:
            for line in response.iter_lines():
                if not line or not line.startswith("data: "):
                    continue
                raw = line[len("data: "):].strip()
                if raw == "[DONE]":
                    break
                try:
                    evt = json.loads(raw)
                except json.JSONDecodeError:
                    continue
                if evt.get("type") == "content_block_delta":
                    delta = evt.get("delta", {})
                    text = delta.get("text", "")
                    if text:
                        yield text