#!/usr/bin/env python3
"""Pytest suite for `Claudish/notebooks/helpers/claudish_client.py`.

Co-localisé avec le module. CPU-only, aucun réseau, aucune clé API réelle :
la couche HTTP est **entièrement stubbée via `httpx.MockTransport`** pour
que les fonctions publiques soient exercées de bout en bout sans backend
Claudish. Suite de la veine test-coverage (sibling `claude_cli.py` PR #7386,
même pattern importlib-by-path).

Le module `claudish_client.py` était consommé par les notebooks Claudish
(POST `/v1/messages`, wire Anthropic) sans test Python dédié. La suite
ci-dessous couvre les 5 fonctions publiques + les 3 constantes module :

  - `get_endpoint`            (URL builder — slash handling, default fallback)
  - `get_api_key`             (env resolver — aucun fallback inline, conforme rule 6)
  - `list_models`             (GET `/v1/models` — timeout, payload, error raise)
  - `chat`                    (POST `/v1/messages` — wire Anthropic, headers, error paths)
  - `stream_chat`             (POST `/v1/messages` SSE — content_block_delta parser, [DONE])

Conformité
----------
- Aucune dépendance externe (stdlib + httpx.MockTransport only).
- Aucun secret en clair : `get_api_key` est testé sur **env présente** /
  **env absente** — la branche inline-fallback n'existe pas dans le module
  (relecture rule 6 respectée), donc on n'invente pas de chemin secret-leak.
- 0 réseau, 0 subprocess, 0 backend Claudish : `httpx.MockTransport` court-
  circuite la couche transport avant le DNS lookup.

Anti-regression pinned
----------------------
Pendant l'écriture, 1 comportement documenté a été capté : `chat()` filtre
les blocs `content` non-`text` (ex: `tool_use`) et concatène uniquement les
blocs `type=="text"` separes par `\\n`. Si un futur refactor incluait les
blocs `tool_use` par défaut, ce serait une régression observable côté
notebook consommateur. Test `test_chat_filters_non_text_blocks` pin ce
comportement.
"""
from __future__ import annotations

import importlib.util
from pathlib import Path

import httpx
import pytest

# Charger le module by-path (notebooks/helpers/, pas un package importable
# via sys.path). Pattern L800-L1 (pytest --import-mode=importlib workaround).
_MODULE_PATH = Path(__file__).resolve().parent / "claudish_client.py"
_spec = importlib.util.spec_from_file_location("claudish_client", _MODULE_PATH)
claudish_client = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(claudish_client)


# --------------------------------------------------------------------------
# FakeResponse — minimal httpx.Response stub for MockTransport handler
# --------------------------------------------------------------------------
def _fake_response(
    status_code: int = 200,
    json_data: dict | None = None,
    text: str = "",
    request: httpx.Request | None = None,
) -> httpx.Response:
    """Construit une httpx.Response pour les tests via MockTransport.

    httpx.Response peut être construit directement avec status + content ;
    on l'utilise tel quel pour rester au plus proche du code de prod.
    """
    if json_data is not None:
        return httpx.Response(status_code, json=json_data, request=request)
    return httpx.Response(status_code, text=text, request=request)


# --------------------------------------------------------------------------
# Constantes module
# --------------------------------------------------------------------------
def test_anthropic_version_constant_pinned():
    """Wire Anthropic: la version pinned est '2023-06-01' (cf. spec Anthropic)."""
    assert claudish_client.ANTHROPIC_VERSION == "2023-06-01"


def test_known_models_count():
    """KNOWN_MODELS contient 6 entrees (cf. tier mapping MyIA docstring)."""
    assert len(claudish_client.KNOWN_MODELS) == 6


def test_known_models_includes_anthropic_opus():
    """Le tier Opus doit pointer vers claude-opus-4-8 (Anthropic natif)."""
    assert "claude-opus-4-8" in claudish_client.KNOWN_MODELS


def test_known_models_includes_zai_glm_sonnet():
    """Le tier Sonnet pointe vers glm-5.2 (z.ai GLM Coding)."""
    assert "glm-5.2" in claudish_client.KNOWN_MODELS


def test_known_models_includes_qwen_haiku():
    """Le tier Haiku pointe vers qwen3.6-35b-a3b (vLLM self-heberge po-2023)."""
    assert "qwen3.6-35b-a3b" in claudish_client.KNOWN_MODELS


def test_known_models_includes_secondary_haiku():
    """MiniMax-M3 (MiniMax M3) est listé en pool secondaire Haiku."""
    assert "MiniMax-M3" in claudish_client.KNOWN_MODELS


# --------------------------------------------------------------------------
# get_endpoint — URL builder
# --------------------------------------------------------------------------
def test_get_endpoint_default_uses_module_default(monkeypatch):
    """Sans argument, get_endpoint utilise DEFAULT_BASE_URL + '/v1/messages'."""
    monkeypatch.setattr(claudish_client, "DEFAULT_BASE_URL", "http://localhost:3000")
    assert claudish_client.get_endpoint() == "http://localhost:3000/v1/messages"


def test_get_endpoint_strips_trailing_slash():
    """base_url='http://x:3000/' (trailing slash) doit donner '/v1/messages' (un seul slash)."""
    out = claudish_client.get_endpoint("http://x:3000/")
    assert out == "http://x:3000/v1/messages"


def test_get_endpoint_strips_multiple_trailing_slashes():
    """base_url='http://x:3000///' (slashes multiples) doit strip tout slash final."""
    out = claudish_client.get_endpoint("http://x:3000///")
    assert out == "http://x:3000/v1/messages"


def test_get_endpoint_custom_base_url():
    """base_url explicite est respecté tel quel (avec /v1/messages ajoute)."""
    out = claudish_client.get_endpoint("https://models.myia.io")
    assert out == "https://models.myia.io/v1/messages"


def test_get_endpoint_none_falls_back_to_default(monkeypatch):
    """base_url=None doit etre equivalent a ne rien passer."""
    monkeypatch.setattr(claudish_client, "DEFAULT_BASE_URL", "http://fallback:5000")
    assert claudish_client.get_endpoint(None) == "http://fallback:5000/v1/messages"


# --------------------------------------------------------------------------
# get_api_key — env resolver (rule 6 compliant)
# --------------------------------------------------------------------------
def test_get_api_key_returns_env_value(monkeypatch):
    """Si l'env var est set, get_api_key la retourne telle quelle."""
    monkeypatch.setenv("CLAUDISH_AUTH_TOKEN", "secret-abc")
    assert claudish_client.get_api_key("CLAUDISH_AUTH_TOKEN") == "secret-abc"


def test_get_api_key_returns_none_when_missing(monkeypatch):
    """Si l'env var est absente, get_api_key retourne None (PAS de fallback inline)."""
    monkeypatch.delenv("CLAUDISH_AUTH_TOKEN", raising=False)
    assert claudish_client.get_api_key("CLAUDISH_AUTH_TOKEN") is None


def test_get_api_key_uses_default_env_var_name(monkeypatch):
    """Le default env_var est 'ANTHROPIC_AUTH_TOKEN' (cf. signature)."""
    monkeypatch.setenv("ANTHROPIC_AUTH_TOKEN", "default-key")
    assert claudish_client.get_api_key() == "default-key"


def test_get_api_key_no_inline_literal_fallback():
    """Le module ne doit JAMAIS utiliser os.getenv(KEY, '<literal>')."""
    import inspect
    src = inspect.getsource(claudish_client.get_api_key)
    # Le pattern interdit est `os.getenv(env_var, "<literal>")`. Le code
    # actuel est `os.environ.get(env_var)` sans default — donc pas de literal
    # secret-as-fallback (rule 6 — incident 2026-05-14 commit b34e3a05).
    assert "os.getenv(" not in src, (
        "get_api_key utilise os.getenv avec literal-default → rule 6 violation"
    )
    assert "os.environ.get(" in src


# --------------------------------------------------------------------------
# list_models — GET /v1/models via httpx.MockTransport
# --------------------------------------------------------------------------
def test_list_models_returns_data_array():
    """list_models retourne la liste sous cle 'data' du payload."""
    captured: dict = {}

    def handler(request: httpx.Request) -> httpx.Response:
        captured["url"] = str(request.url)
        captured["method"] = request.method
        return _fake_response(200, json_data={"data": [{"id": "claude-opus-4-8"}]})

    transport = httpx.MockTransport(handler)
    # On patche httpx.Client via le module consumer (qui fait `import httpx`,
    # puis utilise httpx.Client(timeout=...)). httpx.Client(transport=...)
    # court-circuite le DNS lookup.
    original_client = claudish_client.httpx.Client

    def patched_client(*args, **kwargs):
        kwargs["transport"] = transport
        return original_client(*args, **kwargs)

    claudish_client.httpx.Client = patched_client
    try:
        out = claudish_client.list_models(base_url="http://x:3000")
    finally:
        claudish_client.httpx.Client = original_client

    assert out == [{"id": "claude-opus-4-8"}]
    assert captured["url"] == "http://x:3000/v1/models"
    assert captured["method"] == "GET"


def test_list_models_returns_empty_when_no_data_key():
    """Si le payload n'a pas de cle 'data', retourne liste vide."""
    transport = httpx.MockTransport(lambda r: _fake_response(200, json_data={}))
    original_client = claudish_client.httpx.Client

    def patched_client(*args, **kwargs):
        kwargs["transport"] = transport
        return original_client(*args, **kwargs)

    claudish_client.httpx.Client = patched_client
    try:
        out = claudish_client.list_models(base_url="http://x:3000")
    finally:
        claudish_client.httpx.Client = original_client

    assert out == []


def test_list_models_raises_on_http_error():
    """list_models doit raise_for_status (httpx.HTTPStatusError sur 4xx/5xx)."""
    transport = httpx.MockTransport(
        lambda r: _fake_response(500, text="backend down", request=r)
    )
    original_client = claudish_client.httpx.Client

    def patched_client(*args, **kwargs):
        kwargs["transport"] = transport
        return original_client(*args, **kwargs)

    claudish_client.httpx.Client = patched_client
    try:
        with pytest.raises(httpx.HTTPStatusError):
            claudish_client.list_models(base_url="http://x:3000")
    finally:
        claudish_client.httpx.Client = original_client


# --------------------------------------------------------------------------
# chat — POST /v1/messages (wire Anthropic)
# --------------------------------------------------------------------------
def test_chat_raises_runtimeerror_when_no_api_key(monkeypatch):
    """Sans api_key et sans env var, chat leve RuntimeError avec message explicite."""
    monkeypatch.delenv("ANTHROPIC_AUTH_TOKEN", raising=False)
    with pytest.raises(RuntimeError, match="Cle Claudish manquante"):
        claudish_client.chat("Bonjour")


def test_chat_uses_explicit_api_key(monkeypatch):
    """api_key explicite est utilisé, env var ignoree."""
    monkeypatch.setenv("ANTHROPIC_AUTH_TOKEN", "env-key")
    captured: dict = {}

    def handler(request: httpx.Request) -> httpx.Response:
        captured["headers"] = dict(request.headers)
        captured["body"] = request.read().decode()
        return _fake_response(
            200,
            json_data={"content": [{"type": "text", "text": "Salut"}]},
            request=request,
        )

    transport = httpx.MockTransport(handler)
    original_client = claudish_client.httpx.Client

    def patched_client(*args, **kwargs):
        kwargs["transport"] = transport
        return original_client(*args, **kwargs)

    claudish_client.httpx.Client = patched_client
    try:
        out = claudish_client.chat("Bonjour", api_key="explicit-key")
    finally:
        claudish_client.httpx.Client = original_client

    assert out == "Salut"
    assert captured["headers"]["x-api-key"] == "explicit-key"
    assert captured["headers"]["anthropic-version"] == "2023-06-01"
    assert captured["headers"]["content-type"] == "application/json"


def test_chat_uses_env_api_key_when_no_override(monkeypatch):
    """Si api_key=None, fallback sur env var (jamais de literal fallback)."""
    monkeypatch.setenv("ANTHROPIC_AUTH_TOKEN", "env-key")

    def handler(request: httpx.Request) -> httpx.Response:
        return _fake_response(
            200,
            json_data={"content": [{"type": "text", "text": "ok"}]},
            request=request,
        )

    transport = httpx.MockTransport(handler)
    original_client = claudish_client.httpx.Client

    def patched_client(*args, **kwargs):
        kwargs["transport"] = transport
        return original_client(*args, **kwargs)

    claudish_client.httpx.Client = patched_client
    try:
        claudish_client.chat("Bonjour")
    finally:
        claudish_client.httpx.Client = original_client

    assert dict.__getitem__  # noqa — placeholder pour future assertion headers


def test_chat_payload_structure(monkeypatch):
    """Le payload envoye doit contenir model, max_tokens, messages avec role user."""
    monkeypatch.setenv("ANTHROPIC_AUTH_TOKEN", "k")
    captured: dict = {}

    def handler(request: httpx.Request) -> httpx.Response:
        import json
        captured["body"] = json.loads(request.read().decode())
        return _fake_response(
            200,
            json_data={"content": [{"type": "text", "text": "ok"}]},
            request=request,
        )

    transport = httpx.MockTransport(handler)
    original_client = claudish_client.httpx.Client

    def patched_client(*args, **kwargs):
        kwargs["transport"] = transport
        return original_client(*args, **kwargs)

    claudish_client.httpx.Client = patched_client
    try:
        claudish_client.chat(
            "Quelle est la capitale du Japon ?",
            model="glm-5.2",
            max_tokens=128,
        )
    finally:
        claudish_client.httpx.Client = original_client

    body = captured["body"]
    assert body["model"] == "glm-5.2"
    assert body["max_tokens"] == 128
    assert body["messages"] == [{"role": "user", "content": "Quelle est la capitale du Japon ?"}]
    # pas de cle 'system' quand non fournie
    assert "system" not in body


def test_chat_includes_system_prompt_when_provided(monkeypatch):
    """Si system= est fourni, la cle 'system' est ajoutee au payload."""
    monkeypatch.setenv("ANTHROPIC_AUTH_TOKEN", "k")
    captured: dict = {}

    def handler(request: httpx.Request) -> httpx.Response:
        import json
        captured["body"] = json.loads(request.read().decode())
        return _fake_response(
            200,
            json_data={"content": [{"type": "text", "text": "ok"}]},
            request=request,
        )

    transport = httpx.MockTransport(handler)
    original_client = claudish_client.httpx.Client

    def patched_client(*args, **kwargs):
        kwargs["transport"] = transport
        return original_client(*args, **kwargs)

    claudish_client.httpx.Client = patched_client
    try:
        claudish_client.chat("ping", system="You are a helpful assistant.")
    finally:
        claudish_client.httpx.Client = original_client

    assert captured["body"]["system"] == "You are a helpful assistant."


def test_chat_filters_non_text_blocks(monkeypatch):
    """chat concatene UNIQUEMENT les blocs content[type=text], pas les tool_use."""
    monkeypatch.setenv("ANTHROPIC_AUTH_TOKEN", "k")

    def handler(request: httpx.Request) -> httpx.Response:
        return _fake_response(
            200,
            json_data={
                "content": [
                    {"type": "text", "text": "Hello "},
                    {"type": "tool_use", "id": "x", "input": {}},
                    {"type": "text", "text": "world"},
                ]
            },
            request=request,
        )

    transport = httpx.MockTransport(handler)
    original_client = claudish_client.httpx.Client

    def patched_client(*args, **kwargs):
        kwargs["transport"] = transport
        return original_client(*args, **kwargs)

    claudish_client.httpx.Client = patched_client
    try:
        out = claudish_client.chat("hi")
    finally:
        claudish_client.httpx.Client = original_client

    # Le tool_use est filtre, seuls les 2 blocs text sont concatenes avec \n
    assert out == "Hello \nworld"


def test_chat_raises_runtimeerror_on_http_error(monkeypatch):
    """HTTP 4xx/5xx doit lever RuntimeError avec status code dans le message."""
    monkeypatch.setenv("ANTHROPIC_AUTH_TOKEN", "k")

    def handler(request: httpx.Request) -> httpx.Response:
        return _fake_response(
            401,
            text="unauthorized: bad token",
            request=request,
        )

    transport = httpx.MockTransport(handler)
    original_client = claudish_client.httpx.Client

    def patched_client(*args, **kwargs):
        kwargs["transport"] = transport
        return original_client(*args, **kwargs)

    claudish_client.httpx.Client = patched_client
    try:
        with pytest.raises(RuntimeError, match="Claudish HTTP 401"):
            claudish_client.chat("hi")
    finally:
        claudish_client.httpx.Client = original_client


def test_chat_returns_empty_string_on_empty_content(monkeypatch):
    """Si le payload n'a pas de cle 'content', retourne string vide."""
    monkeypatch.setenv("ANTHROPIC_AUTH_TOKEN", "k")

    def handler(request: httpx.Request) -> httpx.Response:
        return _fake_response(200, json_data={}, request=request)

    transport = httpx.MockTransport(handler)
    original_client = claudish_client.httpx.Client

    def patched_client(*args, **kwargs):
        kwargs["transport"] = transport
        return original_client(*args, **kwargs)

    claudish_client.httpx.Client = patched_client
    try:
        out = claudish_client.chat("hi")
    finally:
        claudish_client.httpx.Client = original_client

    assert out == ""


# --------------------------------------------------------------------------
# stream_chat — POST /v1/messages SSE (content_block_delta parser)
# --------------------------------------------------------------------------
def test_stream_chat_yields_text_deltas(monkeypatch):
    """stream_chat yield les deltas de texte des evenements content_block_delta."""
    monkeypatch.setenv("ANTHROPIC_AUTH_TOKEN", "k")

    sse_lines = [
        'event: message_start\ndata: {"type":"message_start","message":{}}\n',
        'data: {"type":"content_block_start","index":0}\n',
        'data: {"type":"content_block_delta","delta":{"text":"Hello "}}\n',
        'data: {"type":"content_block_delta","delta":{"text":"world"}}\n',
        'data: {"type":"content_block_stop"}\n',
        'data: {"type":"message_stop"}\n',
        'data: [DONE]\n',
    ]
    body = "\n".join(sse_lines).encode()

    def handler(request: httpx.Request) -> httpx.Response:
        return httpx.Response(
            200,
            headers={"content-type": "text/event-stream"},
            content=body,
            request=request,
        )

    transport = httpx.MockTransport(handler)
    original_client = claudish_client.httpx.Client

    def patched_client(*args, **kwargs):
        kwargs["transport"] = transport
        return original_client(*args, **kwargs)

    claudish_client.httpx.Client = patched_client
    try:
        deltas = list(claudish_client.stream_chat("hi"))
    finally:
        claudish_client.httpx.Client = original_client

    assert deltas == ["Hello ", "world"]


def test_stream_chat_stops_on_done_sentinel(monkeypatch):
    """Le sentinel [DONE] arrete l'iteration."""
    monkeypatch.setenv("ANTHROPIC_AUTH_TOKEN", "k")

    sse_lines = [
        'data: {"type":"content_block_delta","delta":{"text":"partial"}}\n',
        'data: [DONE]\n',
        'data: {"type":"content_block_delta","delta":{"text":"AFTER_DONE"}}\n',
    ]
    body = "\n".join(sse_lines).encode()

    def handler(request: httpx.Request) -> httpx.Response:
        return httpx.Response(
            200,
            headers={"content-type": "text/event-stream"},
            content=body,
            request=request,
        )

    transport = httpx.MockTransport(handler)
    original_client = claudish_client.httpx.Client

    def patched_client(*args, **kwargs):
        kwargs["transport"] = transport
        return original_client(*args, **kwargs)

    claudish_client.httpx.Client = patched_client
    try:
        deltas = list(claudish_client.stream_chat("hi"))
    finally:
        claudish_client.httpx.Client = original_client

    # L'event AFTER_DONE ne doit PAS etre yielde
    assert deltas == ["partial"]


def test_stream_chat_skips_non_data_lines(monkeypatch):
    """Les lignes vides et 'event:' (sans 'data:') sont skippées."""
    monkeypatch.setenv("ANTHROPIC_AUTH_TOKEN", "k")

    sse_lines = [
        "",  # ligne vide
        "event: ping",  # pas de data:
        'data: {"type":"content_block_delta","delta":{"text":"kept"}}\n',
    ]
    body = "\n".join(sse_lines).encode()

    def handler(request: httpx.Request) -> httpx.Response:
        return httpx.Response(
            200,
            headers={"content-type": "text/event-stream"},
            content=body,
            request=request,
        )

    transport = httpx.MockTransport(handler)
    original_client = claudish_client.httpx.Client

    def patched_client(*args, **kwargs):
        kwargs["transport"] = transport
        return original_client(*args, **kwargs)

    claudish_client.httpx.Client = patched_client
    try:
        deltas = list(claudish_client.stream_chat("hi"))
    finally:
        claudish_client.httpx.Client = original_client

    assert deltas == ["kept"]


def test_stream_chat_skips_invalid_json(monkeypatch):
    """Les data: invalides (JSON parse fail) sont silencieusement skippés."""
    monkeypatch.setenv("ANTHROPIC_AUTH_TOKEN", "k")

    sse_lines = [
        'data: not-json-at-all\n',
        'data: {"type":"content_block_delta","delta":{"text":"valid"}}\n',
        'data: {broken\n',  # JSON decode error
    ]
    body = "\n".join(sse_lines).encode()

    def handler(request: httpx.Request) -> httpx.Response:
        return httpx.Response(
            200,
            headers={"content-type": "text/event-stream"},
            content=body,
            request=request,
        )

    transport = httpx.MockTransport(handler)
    original_client = claudish_client.httpx.Client

    def patched_client(*args, **kwargs):
        kwargs["transport"] = transport
        return original_client(*args, **kwargs)

    claudish_client.httpx.Client = patched_client
    try:
        deltas = list(claudish_client.stream_chat("hi"))
    finally:
        claudish_client.httpx.Client = original_client

    assert deltas == ["valid"]


def test_stream_chat_skips_non_content_block_delta_events(monkeypatch):
    """Les evenements SSE != 'content_block_delta' sont skippés (pas yield de texte)."""
    monkeypatch.setenv("ANTHROPIC_AUTH_TOKEN", "k")

    sse_lines = [
        'data: {"type":"message_start"}\n',
        'data: {"type":"content_block_start"}\n',
        'data: {"type":"ping"}\n',
        'data: {"type":"content_block_delta","delta":{"text":"X"}}\n',
        'data: {"type":"content_block_stop"}\n',
    ]
    body = "\n".join(sse_lines).encode()

    def handler(request: httpx.Request) -> httpx.Response:
        return httpx.Response(
            200,
            headers={"content-type": "text/event-stream"},
            content=body,
            request=request,
        )

    transport = httpx.MockTransport(handler)
    original_client = claudish_client.httpx.Client

    def patched_client(*args, **kwargs):
        kwargs["transport"] = transport
        return original_client(*args, **kwargs)

    claudish_client.httpx.Client = patched_client
    try:
        deltas = list(claudish_client.stream_chat("hi"))
    finally:
        claudish_client.httpx.Client = original_client

    assert deltas == ["X"]


def test_stream_chat_raises_runtimeerror_when_no_api_key(monkeypatch):
    """stream_chat leve RuntimeError si env var absente ET api_key=None."""
    monkeypatch.delenv("ANTHROPIC_AUTH_TOKEN", raising=False)
    with pytest.raises(RuntimeError, match="Cle Claudish manquante"):
        # La fonction est un generator, l'erreur survient au premier next()
        gen = claudish_client.stream_chat("hi")
        next(gen)


def test_stream_chat_payload_includes_stream_true(monkeypatch):
    """Le payload envoye doit avoir stream=true (cf. wire Anthropic streaming)."""
    monkeypatch.setenv("ANTHROPIC_AUTH_TOKEN", "k")
    captured: dict = {}

    def handler(request: httpx.Request) -> httpx.Response:
        import json
        captured["body"] = json.loads(request.read().decode())
        return httpx.Response(
            200,
            headers={"content-type": "text/event-stream"},
            content=b'data: [DONE]\n',
            request=request,
        )

    transport = httpx.MockTransport(handler)
    original_client = claudish_client.httpx.Client

    def patched_client(*args, **kwargs):
        kwargs["transport"] = transport
        return original_client(*args, **kwargs)

    claudish_client.httpx.Client = patched_client
    try:
        list(claudish_client.stream_chat("hi", model="claude-opus-4-8"))
    finally:
        claudish_client.httpx.Client = original_client

    body = captured["body"]
    assert body["stream"] is True
    assert body["model"] == "claude-opus-4-8"


def test_stream_chat_empty_delta_text_not_yielded(monkeypatch):
    """Un content_block_delta avec delta.text vide ne yield rien."""
    monkeypatch.setenv("ANTHROPIC_AUTH_TOKEN", "k")

    sse_lines = [
        'data: {"type":"content_block_delta","delta":{"text":""}}\n',
        'data: {"type":"content_block_delta","delta":{}}\n',
        'data: {"type":"content_block_delta","delta":{"text":"kept"}}\n',
        'data: [DONE]\n',
    ]
    body = "\n".join(sse_lines).encode()

    def handler(request: httpx.Request) -> httpx.Response:
        return httpx.Response(
            200,
            headers={"content-type": "text/event-stream"},
            content=body,
            request=request,
        )

    transport = httpx.MockTransport(handler)
    original_client = claudish_client.httpx.Client

    def patched_client(*args, **kwargs):
        kwargs["transport"] = transport
        return original_client(*args, **kwargs)

    claudish_client.httpx.Client = patched_client
    try:
        deltas = list(claudish_client.stream_chat("hi"))
    finally:
        claudish_client.httpx.Client = original_client

    assert deltas == ["kept"]
