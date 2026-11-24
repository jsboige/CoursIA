"""Cœur réutilisable d'extraction JSON Schema en mode Structured Outputs."""

from __future__ import annotations

import copy
import json
import os
import re
from typing import Any, TypeVar
from urllib.parse import urlparse

from jsonschema import Draft202012Validator
from jsonschema.exceptions import SchemaError, ValidationError as JsonSchemaValidationError
from openai import OpenAI
from pydantic import BaseModel, ValidationError


ModelT = TypeVar("ModelT", bound=BaseModel)


class StructuredInputError(ValueError):
    """Entrée de l'extraction vide ou JSON Schema incorrect."""


class StructuredExtractionError(RuntimeError):
    """Échec de configuration, d'appel API, de décodage ou de validation."""


def _reject_external_refs(schema: dict[str, Any]) -> None:
    """Refuse les références qui feraient sortir la validation du schéma fourni."""
    pending: list[Any] = [schema]
    while pending:
        node = pending.pop()
        if isinstance(node, dict):
            for key, value in node.items():
                if key in {"$ref", "$dynamicRef", "$recursiveRef"}:
                    if not isinstance(value, str) or not value.startswith("#"):
                        raise StructuredInputError(
                            "les références du schéma JSON doivent être locales au document (#...)"
                        )
                pending.append(value)
        elif isinstance(node, list):
            pending.extend(node)


def _strict_schema(schema: dict[str, Any]) -> dict[str, Any]:
    """Copie le schéma et applique les contraintes strictes utilisées au cours."""
    result = copy.deepcopy(schema)

    def visit(node: Any) -> None:
        if not isinstance(node, dict):
            return
        if node.get("type") == "object":
            properties = node.get("properties", {})
            if not isinstance(properties, dict):
                raise StructuredInputError("schema.properties doit être un objet")
            required = node.get("required", [])
            if not isinstance(required, list) or any(not isinstance(name, str) for name in required):
                raise StructuredInputError("schema.required doit être une liste de noms")
            if not set(required).issubset(properties):
                raise StructuredInputError("schema.required contient un nom absent de schema.properties")
            node["additionalProperties"] = False
            node["required"] = list(properties)
            for child in properties.values():
                visit(child)
        if node.get("type") == "array" and "items" in node:
            visit(node["items"])
        for keyword in ("$defs", "definitions"):
            for child in node.get(keyword, {}).values():
                visit(child)
        for keyword in ("anyOf", "allOf", "oneOf", "prefixItems"):
            for child in node.get(keyword, []):
                visit(child)

    visit(result)
    return result


def _schema_for(schema_or_model: dict[str, Any] | type[ModelT]) -> tuple[dict[str, Any], type[ModelT] | None]:
    if isinstance(schema_or_model, type) and issubclass(schema_or_model, BaseModel):
        try:
            schema = schema_or_model.model_json_schema()
        except Exception as exc:
            raise StructuredInputError("impossible de générer le schéma JSON du modèle Pydantic") from exc
        model_class: type[ModelT] | None = schema_or_model
    elif isinstance(schema_or_model, dict):
        schema = copy.deepcopy(schema_or_model)
        model_class = None
    else:
        raise StructuredInputError("schema doit être un objet JSON Schema ou une classe Pydantic")

    try:
        Draft202012Validator.check_schema(schema)
    except SchemaError as exc:
        raise StructuredInputError(f"schéma JSON invalide : {exc.message}") from exc
    _reject_external_refs(schema)
    if schema.get("type") != "object":
        raise StructuredInputError("le schéma racine doit déclarer type=object")
    return schema, model_class


def _configured_client() -> OpenAI:
    api_key = os.getenv("OPENAI_API_KEY", "").strip()
    if not api_key:
        raise StructuredExtractionError("configuration invalide : OPENAI_API_KEY est absente ou vide")

    base_url = os.getenv("OPENAI_BASE_URL")
    if base_url is not None:
        base_url = base_url.strip()
        parsed = urlparse(base_url)
        if not base_url or parsed.scheme not in {"http", "https"} or not parsed.netloc:
            raise StructuredExtractionError("configuration invalide : OPENAI_BASE_URL doit être une URL HTTP(S)")

    return OpenAI(api_key=api_key, base_url=base_url)


def extract_structured(
    prompt: str,
    schema: dict[str, Any] | type[ModelT],
    model: str | None = None,
    *,
    client: Any | None = None,
) -> dict[str, Any] | ModelT:
    """Appelle un endpoint OpenAI-compatible puis valide sa réponse.

    ``schema`` accepte un JSON Schema racine objet ou une classe Pydantic v2.
    Un client OpenAI-compatible peut être injecté pour les tests et les usages
    qui gèrent eux-mêmes leur cycle de vie. Sans injection, le client est créé
    depuis ``OPENAI_API_KEY`` et ``OPENAI_BASE_URL``.

    Les erreurs de contrat sont distinguées des erreurs d'exécution par
    ``StructuredInputError`` et ``StructuredExtractionError``.
    """
    if not isinstance(prompt, str) or not prompt.strip():
        raise StructuredInputError("prompt doit être une chaîne non vide")

    original_schema, model_class = _schema_for(schema)
    strict_schema = _strict_schema(original_schema)
    try:
        Draft202012Validator.check_schema(strict_schema)
    except SchemaError as exc:
        raise StructuredInputError(f"schéma incompatible avec le mode strict : {exc.message}") from exc
    strict_validator = Draft202012Validator(strict_schema)

    if model is None:
        configured_model = os.getenv("OPENAI_MODEL")
        if configured_model is not None and not configured_model.strip():
            raise StructuredExtractionError("configuration invalide : OPENAI_MODEL est vide")
        selected_model = configured_model if configured_model is not None else "gpt-5-mini"
    else:
        selected_model = model
    if not isinstance(selected_model, str) or not selected_model.strip():
        raise StructuredInputError("model doit être une chaîne non vide")

    try:
        active_client = client if client is not None else _configured_client()
    except StructuredExtractionError:
        raise
    except Exception as exc:
        raise StructuredExtractionError(f"configuration invalide ({type(exc).__name__})") from exc
    raw_name = model_class.__name__ if model_class is not None else str(
        original_schema.get("title") or "structured_output"
    )
    schema_name = re.sub(r"[^A-Za-z0-9_-]", "_", raw_name)[:64]
    if not schema_name:
        raise StructuredInputError("schema.title doit fournir un nom de schéma utilisable")
    try:
        response = active_client.chat.completions.create(
            model=selected_model,
            messages=[{"role": "user", "content": prompt}],
            response_format={
                "type": "json_schema",
                "json_schema": {
                    "name": schema_name,
                    "strict": True,
                    "schema": strict_schema,
                },
            },
        )
        content = response.choices[0].message.content
        if not isinstance(content, str) or not content.strip():
            raise StructuredExtractionError("la réponse du modèle ne contient pas de JSON")
        data = json.loads(content)
        strict_validator.validate(data)
        if model_class is not None:
            return model_class.model_validate(data)
        return data
    except StructuredExtractionError:
        raise
    except (ValidationError, JsonSchemaValidationError, json.JSONDecodeError, IndexError, AttributeError, TypeError) as exc:
        if isinstance(exc, ValidationError):
            reason = "validation Pydantic"
        elif isinstance(exc, JsonSchemaValidationError):
            reason = "validation JSON Schema"
        elif isinstance(exc, json.JSONDecodeError):
            reason = "JSON mal formé"
        else:
            reason = "structure de réponse inattendue"
        raise StructuredExtractionError(f"réponse invalide : {reason}") from exc
    except Exception as exc:
        # Le nom de classe suffit au contrat; le message du SDK peut contenir
        # des détails transport/configuration propres au fournisseur.
        raise StructuredExtractionError(f"échec API ({type(exc).__name__})") from exc
