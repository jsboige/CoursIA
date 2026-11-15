"""Contrats du cœur et du transport REST (sans appel fournisseur)."""

from __future__ import annotations

import asyncio
import socket
import sys
import threading
import time
from pathlib import Path
from types import SimpleNamespace
from typing import Any

import httpx
import pytest
import uvicorn
from pydantic import BaseModel, Field

sys.path.insert(0, str(Path(__file__).resolve().parent))

from structured_outputs_core import (
    StructuredExtractionError,
    StructuredInputError,
    extract_structured,
)
import structured_outputs_service
from structured_outputs_service import create_app


class Evaluation(BaseModel):
    score: int = Field(ge=0, le=100)
    commentaire: str


class OptionalEvaluation(BaseModel):
    score: int
    note: str | None = None


SCHEMA = {
    "type": "object",
    "properties": {
        "score": {"type": "integer", "minimum": 0, "maximum": 100},
        "commentaire": {"type": "string"},
    },
    "required": ["score", "commentaire"],
}


class FakeClient:
    def __init__(self, content: str = '{"score": 88, "commentaire": "Clair."}', error: Exception | None = None):
        self.content = content
        self.error = error
        self.request: dict[str, Any] | None = None
        self.close_count = 0
        self.chat = SimpleNamespace(completions=SimpleNamespace(create=self.create))

    def create(self, **request: Any) -> Any:
        self.request = request
        if self.error:
            raise self.error
        return SimpleNamespace(
            choices=[SimpleNamespace(message=SimpleNamespace(content=self.content))]
        )

    def close(self) -> None:
        self.close_count += 1


def test_extract_structured_supports_json_schema_and_enforces_strict_mode() -> None:
    client = FakeClient()

    result = extract_structured("Évalue ce texte.", SCHEMA, model="modele-test", client=client)

    assert result == {"score": 88, "commentaire": "Clair."}
    assert client.request is not None
    assert client.request["model"] == "modele-test"
    strict = client.request["response_format"]["json_schema"]
    assert strict["strict"] is True
    assert strict["schema"]["additionalProperties"] is False
    assert strict["schema"]["required"] == ["score", "commentaire"]


def test_schema_title_is_normalized_for_provider_name_limit() -> None:
    schema = {**SCHEMA, "title": "Structured output: evaluation"}
    client = FakeClient()

    extract_structured("Évalue.", schema, client=client)

    assert client.request is not None
    assert client.request["response_format"]["json_schema"]["name"] == "Structured_output__evaluation"


def test_extract_structured_supports_pydantic_model() -> None:
    result = extract_structured("Évalue.", Evaluation, client=FakeClient())

    assert isinstance(result, Evaluation)
    assert result.score == 88


def test_pydantic_extra_ignored_by_model_is_rejected_by_strict_schema() -> None:
    content = '{"score": 88, "commentaire": "valide", "extra": true}'

    with pytest.raises(StructuredExtractionError, match="validation JSON Schema"):
        extract_structured("Évalue.", Evaluation, client=FakeClient(content))


def test_pydantic_optional_field_is_required_by_strict_schema() -> None:
    with pytest.raises(StructuredExtractionError, match="validation JSON Schema"):
        extract_structured("Évalue.", OptionalEvaluation, client=FakeClient('{"score": 88}'))


@pytest.mark.parametrize("prompt", ["", "  ", None, 12])
def test_empty_or_non_string_prompt_is_rejected(prompt: Any) -> None:
    with pytest.raises(StructuredInputError, match="prompt"):
        extract_structured(prompt, SCHEMA, client=FakeClient())


@pytest.mark.parametrize(
    "schema",
    [
        {"type": "object", "properties": {"score": {"type": "not-a-json-type"}}},
        {"type": "array", "items": {"type": "string"}},
        {"type": "object", "properties": {"score": {"type": "integer"}}, "required": ["missing"]},
        ["not", "an", "object"],
    ],
)
def test_invalid_schema_is_rejected_before_call(schema: Any) -> None:
    client = FakeClient()

    with pytest.raises(StructuredInputError, match="schéma|schema"):
        extract_structured("prompt", schema, client=client)
    assert client.request is None


def test_response_violating_schema_is_an_extraction_error() -> None:
    with pytest.raises(StructuredExtractionError, match="réponse invalide"):
        extract_structured(
            "prompt",
            SCHEMA,
            client=FakeClient('{"score": 101, "commentaire": "hors limite"}'),
        )


def test_response_with_extra_property_is_rejected_by_the_sent_strict_schema() -> None:
    # Le schéma d'origine autorise les propriétés supplémentaires par défaut.
    # Le mode strict envoyé au fournisseur les interdit; la validation locale
    # doit appliquer ce même contrat.
    content = '{"score": 88, "commentaire": "valide", "extra": true}'

    with pytest.raises(StructuredExtractionError, match="validation JSON Schema"):
        extract_structured("prompt", SCHEMA, client=FakeClient(content))


def test_response_must_include_property_optional_in_the_original_schema() -> None:
    schema = {
        "type": "object",
        "properties": {
            "score": {"type": "integer"},
            "note": {"type": ["string", "null"]},
        },
        "required": ["score"],
    }

    with pytest.raises(StructuredExtractionError, match="validation JSON Schema"):
        extract_structured("prompt", schema, client=FakeClient('{"score": 88}'))


def test_external_schema_reference_is_rejected_before_call() -> None:
    schema = {
        "type": "object",
        "properties": {"entry": {"$ref": "https://example.invalid/entry.json"}},
        "required": ["entry"],
    }
    client = FakeClient()

    with pytest.raises(StructuredInputError, match="références.*locales"):
        extract_structured("prompt", schema, client=client)
    assert client.request is None


def test_provider_failure_is_a_bounded_extraction_error() -> None:
    with pytest.raises(StructuredExtractionError, match=r"échec API \(RuntimeError\)") as error:
        extract_structured("prompt", SCHEMA, client=FakeClient(error=RuntimeError("private detail")))
    assert "private detail" not in str(error.value)


def test_missing_api_key_fails_explicitly_without_fallback(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)

    with pytest.raises(StructuredExtractionError, match="OPENAI_API_KEY"):
        extract_structured("prompt", SCHEMA)


def test_invalid_configured_base_url_fails_explicitly(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("OPENAI_API_KEY", "local-test-key")
    monkeypatch.setenv("OPENAI_BASE_URL", "not-an-url")

    with pytest.raises(StructuredExtractionError, match="OPENAI_BASE_URL"):
        extract_structured("prompt", SCHEMA)


def test_rest_contract_covers_success_invalid_and_upstream_error() -> None:
    async def exercise() -> tuple[
        httpx.Response, httpx.Response, httpx.Response, httpx.Response, httpx.Response
    ]:
        async with httpx.AsyncClient(
            transport=httpx.ASGITransport(app=create_app(FakeClient())),
            base_url="http://testserver",
        ) as http:
            success = await http.post("/texte/extract", json={"prompt": "Évalue.", "schema": SCHEMA})
            invalid = await http.post("/texte/extract", json={"prompt": "  ", "schema": SCHEMA})
            bad_schema = await http.post(
                "/texte/extract", json={"prompt": "Évalue.", "schema": {"type": "array"}}
            )
            key_in_body = await http.post(
                "/texte/extract",
                json={"prompt": "Évalue.", "schema": SCHEMA, "api_key": "must-not-be-accepted"},
            )
        async with httpx.AsyncClient(
            transport=httpx.ASGITransport(app=create_app(FakeClient(error=RuntimeError("private detail")))),
            base_url="http://testserver",
        ) as http:
            failed = await http.post("/texte/extract", json={"prompt": "Évalue.", "schema": SCHEMA})
        return success, invalid, bad_schema, key_in_body, failed

    success, invalid, bad_schema, key_in_body, failed = asyncio.run(exercise())
    assert success.status_code == 200
    assert success.json() == {"status": "ok", "data": {"score": 88, "commentaire": "Clair."}}
    assert invalid.status_code == 422
    assert invalid.json()["status"] == "invalid"
    assert "prompt" in invalid.json()["error"]
    assert bad_schema.status_code == 422
    assert bad_schema.json()["status"] == "invalid"
    assert key_in_body.status_code == 422
    assert key_in_body.json()["status"] == "invalid"

    assert failed.status_code == 502
    assert failed.json() == {"status": "error", "error": "échec de l'extraction structurée"}


def test_rest_errors_do_not_expose_untrusted_details(monkeypatch: pytest.MonkeyPatch) -> None:
    marker = "marqueurmarqueur"

    async def post(app: Any, body: dict[str, Any]) -> httpx.Response:
        async with httpx.AsyncClient(
            transport=httpx.ASGITransport(app=app), base_url="http://testserver"
        ) as http:
            return await http.post("/texte/extract", json=body)

    body = {"prompt": "test", "schema": SCHEMA}
    invalid_schema = {"type": "object", "properties": {"x": {"type": marker}}}
    responses = [
        asyncio.run(post(create_app(FakeClient()), {"prompt": "test", "schema": invalid_schema})),
        asyncio.run(post(create_app(FakeClient()), {**body, marker: "value"})),
        asyncio.run(post(create_app(FakeClient(error=RuntimeError(marker))), body)),
        asyncio.run(post(create_app(FakeClient(content=marker)), body)),
    ]
    for exception_type in (StructuredInputError, StructuredExtractionError, type(marker, (Exception,), {})):
        def fail(**kwargs: Any) -> None:
            raise exception_type(marker)

        monkeypatch.setattr(structured_outputs_service, "extract_structured", fail)
        responses.append(asyncio.run(post(create_app(FakeClient()), body)))

    assert [response.status_code for response in responses] == [422, 422, 502, 502, 422, 502, 502]
    assert all(marker not in response.text for response in responses)
    assert responses[0].json()["error"] == "entrée invalide : vérifiez prompt, schema et model"
    assert responses[1].json()["error"] == "corps invalide : vérifiez prompt, schema et model"


def test_loopback_http_request_reaches_endpoint() -> None:
    """Exerce le vrai transport TCP local, avec une réponse de modèle injectée."""
    client = FakeClient()
    app = create_app(client)
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        port = probe.getsockname()[1]

    server = uvicorn.Server(
        uvicorn.Config(app, host="127.0.0.1", port=port, log_level="critical")
    )
    thread = threading.Thread(target=server.run, daemon=True)
    thread.start()
    try:
        deadline = time.monotonic() + 5
        while not server.started and thread.is_alive() and time.monotonic() < deadline:
            time.sleep(0.01)
        assert server.started, "le serveur local n'a pas démarré"

        response = httpx.post(
            f"http://127.0.0.1:{port}/texte/extract",
            json={"prompt": "Évalue.", "schema": SCHEMA},
            timeout=2,
        )
    finally:
        server.should_exit = True
        thread.join(timeout=5)

    assert not thread.is_alive(), "le serveur local ne s'est pas arrêté"
    assert client.close_count == 0, "le service ne possède pas le client injecté"
    assert response.status_code == 200
    assert response.json() == {"status": "ok", "data": {"score": 88, "commentaire": "Clair."}}


def test_loopback_reuses_and_closes_one_configured_client(monkeypatch: pytest.MonkeyPatch) -> None:
    """Le serveur réutilise son client configuré et le ferme à l'arrêt."""
    monkeypatch.setenv("OPENAI_API_KEY", "local-test-key")
    monkeypatch.delenv("OPENAI_BASE_URL", raising=False)
    created: list[FakeClient] = []

    def make_client(**kwargs: Any) -> FakeClient:
        assert kwargs == {"api_key": "local-test-key", "base_url": None}
        client = FakeClient()
        created.append(client)
        return client

    monkeypatch.setattr("structured_outputs_core.OpenAI", make_client)
    app = create_app()
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        port = probe.getsockname()[1]

    server = uvicorn.Server(
        uvicorn.Config(app, host="127.0.0.1", port=port, log_level="critical")
    )
    thread = threading.Thread(target=server.run, daemon=True)
    thread.start()
    try:
        deadline = time.monotonic() + 5
        while not server.started and thread.is_alive() and time.monotonic() < deadline:
            time.sleep(0.01)
        assert server.started, "le serveur local n'a pas démarré"
        assert len(created) == 1

        responses = [
            httpx.post(
                f"http://127.0.0.1:{port}/texte/extract",
                json={"prompt": "Évalue.", "schema": SCHEMA},
                timeout=2,
            )
            for _ in range(3)
        ]
        assert all(response.status_code == 200 for response in responses)
        assert len(created) == 1, "le client est créé une seule fois pour le lifespan"
        assert created[0].close_count == 0
    finally:
        server.should_exit = True
        thread.join(timeout=5)

    assert not thread.is_alive(), "le serveur local ne s'est pas arrêté"
    assert len(created) == 1
    assert created[0].close_count == 1, "le client du service est fermé au shutdown"
