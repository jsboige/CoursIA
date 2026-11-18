"""Structured output client for the v4 audiobook pipeline.

Targets the cluster's local vLLM (Swift) by default -- the chat target of
#22783 -- and uses the OpenAI JSON Schema structured output API
(response_format with type ``json_schema``, strict: true) via the
``requests`` library to avoid the hang issues observed with the openai SDK
in the v3 pipeline.
"""
from __future__ import annotations

import json
import time
from pathlib import Path
from typing import Type
from urllib.parse import urlparse

import requests
from dotenv import load_dotenv
from pydantic import BaseModel, ValidationError

# ---------------------------------------------------------------------------
# Environment
# ---------------------------------------------------------------------------

_GENAI_DIR = Path(__file__).resolve().parents[3]  # GenAI/
load_dotenv(_GENAI_DIR / ".env")

import os  # noqa: E402 — must follow load_dotenv

_API_KEY: str | None = os.getenv("VLLM_API_KEY") or os.getenv("OPENAI_API_KEY")
_API_BASE: str = (
    os.getenv("VLLM_BASE_URL")
    or os.getenv("OPENAI_API_BASE")
    or "http://192.168.0.47:5002/v1"
).rstrip("/")

# Cible par defaut du chat (#22783) : le vLLM local du cluster (Swift), via la
# route LAN du siege ai-01 -- le meme couple (VLLM_BASE_URL, VLLM_API_KEY) que
# les carnets Audio de la serie (04-1-Educational-Audio-Content). Repli : le
# modele de chat courant du mapping (docs/genai/model-mapping-openai.md) quand
# le point d'entree vise n'est pas le service local.
_LOCAL_TARGET_HOSTS = ("192.168.0.47", "models.myia.io")


def _is_local_target(base: str) -> bool:
    """Le point d'entree vise est-il l'un des services locaux du cluster ?

    Comparaison du nom d'hote, pas d'une sous-chaine : une chaine peut
    apparaitre a n'importe quel endroit de l'URL (CodeQL : sanitisation
    incomplete de l'URL).
    """
    host = (urlparse(base).hostname or "").lower()
    return host in _LOCAL_TARGET_HOSTS


def _default_model(base: str) -> str:
    """Modele courant du role demande, selon le point d'entree vise."""
    if _is_local_target(base):
        return "swift-1.5-27b"  # alias servi par le vLLM local (Swift)
    return "gpt-5.6-luna"  # taille mini du mapping, hors service local


# Un .env encore porte sur un identifiant d'une generation remplacee : on le
# substitue, il ne doit jamais passer tel quel dans un appel (#22783).
# Les identifiants ci-dessous ne sont que des CLES de correspondance (la table
# de migration) : ils ne sont jamais envoyes a un service.
# obsolescence: DOC
_OBSOLETE_MODEL_SUBSTITUTIONS = {
    "gpt-3.5": "gpt-5.6-sol",
    "gpt-3.5-turbo": "gpt-5.6-sol",
    "gpt-4": "gpt-5.6-sol",
    "gpt-4-turbo": "gpt-5.6-sol",
    "gpt-4o": "gpt-5.6-sol",
    "gpt-4o-2024-08-06": "gpt-5.6-sol",
    "gpt-4o-mini": "gpt-5.6-luna",
    "gpt-4.1": "gpt-5.6-sol",
    "gpt-4.1-mini": "gpt-5.6-luna",
    "gpt-4.1-nano": "gpt-5.6-luna",
    "gpt-5": "gpt-5.6-sol",
    "gpt-5-mini": "gpt-5.6-luna",
    "gpt-5-nano": "gpt-5.6-luna",
}

_CONFIGURED_MODEL: str = os.getenv("OPENAI_CHAT_MODEL_ID") or _default_model(_API_BASE)
_MODEL: str = _OBSOLETE_MODEL_SUBSTITUTIONS.get(
    _CONFIGURED_MODEL.strip(), _CONFIGURED_MODEL
)

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

_MAX_RETRIES = 3
_BACKOFF_BASE = 2  # seconds — yields 2s, 4s, 8s


def _flatten_schema(schema: dict, defs: dict | None = None) -> dict:
    """Flatten $ref and $defs for OpenAI strict JSON Schema mode.

    OpenAI strict mode requires all schemas to be inline (no ``$ref``) and
    every object to have ``additionalProperties: false``.
    """
    if defs is None:
        defs = schema.pop("$defs", {})
        defs.update(schema.pop("definitions", {}))

    if "$ref" in schema:
        ref_name = schema["$ref"].split("/")[-1]
        return _flatten_schema({**defs.get(ref_name, {})}, defs)

    result = {}
    for key, value in schema.items():
        if key in ("$ref", "$defs", "definitions"):
            continue
        if isinstance(value, dict):
            result[key] = _flatten_schema(value, defs)
        elif isinstance(value, list):
            result[key] = [
                _flatten_schema(item, defs) if isinstance(item, dict) else item
                for item in value
            ]
        else:
            result[key] = value

    if result.get("type") == "object" and "additionalProperties" not in result:
        if "properties" in result:
            result["additionalProperties"] = False

    return result


def _enforce_strict_required(schema: dict) -> dict:
    """Ensure every object with 'properties' has 'required' listing all keys.

    OpenAI strict mode requires ``required`` to be an array including every
    key in ``properties``. Pydantic omits fields with defaults from ``required``,
    so we inject them here.
    """
    if "properties" in schema and isinstance(schema["properties"], dict):
        all_keys = list(schema["properties"].keys())
        schema["required"] = all_keys
        # Recurse into nested properties
        for prop in schema["properties"].values():
            if isinstance(prop, dict):
                _enforce_strict_required(prop)
            if isinstance(prop, dict) and "items" in prop:
                if isinstance(prop["items"], dict):
                    _enforce_strict_required(prop["items"])
    return schema


def build_json_schema_response_format(name: str, schema_cls: Type[BaseModel]) -> dict:
    """Wrap a Pydantic schema into the OpenAI ``response_format`` envelope.

    The schema is flattened (no ``$ref`` / ``$defs``) and enriched with
    ``additionalProperties: false`` on every object to satisfy OpenAI strict
    JSON Schema mode.
    """
    raw_schema = schema_cls.model_json_schema()
    flat = _flatten_schema(raw_schema)
    flat["additionalProperties"] = False

    # Strict mode is incompatible with additionalProperties in nested objects
    # (OpenAI requires required=[] to match all property keys when strict=True).
    has_nested_additional = '"additionalProperties": {' in json.dumps(flat)

    if has_nested_additional:
        use_strict = False
    else:
        use_strict = True
        _enforce_strict_required(flat)

    return {
        "type": "json_schema",
        "json_schema": {
            "name": name,
            "strict": use_strict,
            "schema": flat,
        },
    }


# ---------------------------------------------------------------------------
# Core call
# ---------------------------------------------------------------------------

def call_structured(
    schema_cls: Type[BaseModel],
    system_prompt: str,
    user_prompt: str,
    context_block: str = "",
    timeout: int = 120,
) -> dict:
    """Call the configured chat model with JSON Schema structured output and retry logic.

    Parameters
    ----------
    schema_cls:
        A Pydantic v2 ``BaseModel`` subclass defining the expected response
        shape.  The class itself is used (not an instance) to build the
        JSON Schema via ``model_json_schema()``.
    system_prompt:
        Base system instructions.
    user_prompt:
        The user message (task description, input data, etc.).
    context_block:
        Optional context prepended to the system prompt as a separate
        section (e.g. narrative context, character profiles).

    Returns
    -------
    dict
        The parsed and validated response matching *schema_cls*.

    Raises
    ------
    RuntimeError
        After ``_MAX_RETRIES`` consecutive failures.
    """
    if not _API_KEY:
        raise RuntimeError(
            "VLLM_API_KEY (service local, cible par defaut) ni OPENAI_API_KEY "
            "ne sont definies. Renseigner l'une des deux dans GenAI/.env."
        )

    schema_name = schema_cls.__name__
    response_format = build_json_schema_response_format(schema_name, schema_cls)

    # Build system message with optional context section.
    if context_block:
        full_system = f"<context>\n{context_block}\n</context>\n\n{system_prompt}"
    else:
        full_system = system_prompt

    messages = [
        {"role": "system", "content": full_system},
        {"role": "user", "content": user_prompt},
    ]

    last_error: str = ""

    for attempt in range(1, _MAX_RETRIES + 1):
        resp = None
        try:
            payload: dict = {
                "model": _MODEL,
                "messages": messages,
                "response_format": response_format,
                # 16384 is within the output cap of every model this client
                # can target (the local Swift default AND the .env-configured
                # model); 32768 was rejected against the default (32768 >
                # 16384). Valid for both, so no env knob.
                "max_completion_tokens": 16384,
            }
            resp = requests.post(
                f"{_API_BASE}/chat/completions",
                headers={
                    "Authorization": f"Bearer {_API_KEY}",
                    "Content-Type": "application/json",
                },
                json=payload,
                timeout=timeout,
            )
            resp.raise_for_status()

            content = resp.json()["choices"][0]["message"]["content"]
            parsed = json.loads(content)

            # Validate against the Pydantic model.
            schema_cls.model_validate(parsed)
            return parsed

        except (requests.RequestException, KeyError, json.JSONDecodeError) as exc:
            detail = ""
            if resp is not None and hasattr(resp, "text"):
                detail = resp.text[:500]
            last_error = f"API/parse error (attempt {attempt}): {exc}\n{detail}"

        except ValidationError as exc:
            last_error = f"Schema validation failed (attempt {attempt}): {exc}"
            # Re-feed the validation error to the LLM so it can self-correct.
            messages.append({"role": "assistant", "content": content if "content" in dir() else "{}"})
            messages.append({
                "role": "user",
                "content": (
                    f"Your response failed Pydantic validation:\n{exc}\n\n"
                    "Please fix and return a valid JSON matching the schema."
                ),
            })

        if attempt < _MAX_RETRIES:
            time.sleep(_BACKOFF_BASE ** attempt)

    raise RuntimeError(
        f"call_structured failed after {_MAX_RETRIES} attempts for {schema_name}: {last_error}"
    )
