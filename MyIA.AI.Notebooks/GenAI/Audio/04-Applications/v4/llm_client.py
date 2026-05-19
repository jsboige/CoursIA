"""GPT-5.4-mini structured output client for the v4 audiobook pipeline.

Uses the OpenAI JSON Schema structured output API (response_format with
type ``json_schema``, strict: true) via the ``requests`` library to avoid
the hang issues observed with the openai SDK in the v3 pipeline.
"""
from __future__ import annotations

import json
import time
from pathlib import Path
from typing import Type

import requests
from dotenv import load_dotenv
from pydantic import BaseModel, ValidationError

# ---------------------------------------------------------------------------
# Environment
# ---------------------------------------------------------------------------

_GENAI_DIR = Path(__file__).resolve().parents[2]  # GenAI/
load_dotenv(_GENAI_DIR / ".env")

import os  # noqa: E402 — must follow load_dotenv

_API_KEY: str | None = os.getenv("OPENAI_API_KEY")
_API_BASE: str = os.getenv("OPENAI_API_BASE", "https://api.openai.com/v1").rstrip("/")
_MODEL: str = "gpt-5.4-mini"

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

_MAX_RETRIES = 3
_BACKOFF_BASE = 2  # seconds — yields 2s, 4s, 8s


def build_json_schema_response_format(name: str, schema_cls: Type[BaseModel]) -> dict:
    """Wrap a Pydantic schema into the OpenAI ``response_format`` envelope.

    Parameters
    ----------
    name:
        A short identifier for the schema (used in the ``name`` field).
    schema_cls:
        A Pydantic v2 ``BaseModel`` subclass (not an instance).

    Returns
    -------
    dict
        The ``response_format`` value expected by the chat completions
        endpoint when using JSON Schema structured outputs.
    """
    raw_schema = schema_cls.model_json_schema()
    # OpenAI requires ``additionalProperties: false`` at the top level for
    # strict mode.  Pydantic v2 omits it when no ``extra = "forbid"`` is
    # set, so we force it here.
    raw_schema["additionalProperties"] = False
    return {
        "type": "json_schema",
        "json_schema": {
            "name": name,
            "strict": True,
            "schema": raw_schema,
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
) -> dict:
    """Call GPT-5.4-mini with JSON Schema structured output and retry logic.

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
        raise RuntimeError("OPENAI_API_KEY is not set. Check GenAI/.env.")

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
        try:
            payload: dict = {
                "model": _MODEL,
                "messages": messages,
                "response_format": response_format,
            }
            resp = requests.post(
                f"{_API_BASE}/chat/completions",
                headers={
                    "Authorization": f"Bearer {_API_KEY}",
                    "Content-Type": "application/json",
                },
                json=payload,
                timeout=120,
            )
            resp.raise_for_status()

            content = resp.json()["choices"][0]["message"]["content"]
            parsed = json.loads(content)

            # Validate against the Pydantic model.
            schema_cls.model_validate(parsed)
            return parsed

        except (requests.RequestException, KeyError, json.JSONDecodeError) as exc:
            last_error = f"API/parse error (attempt {attempt}): {exc}"

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
