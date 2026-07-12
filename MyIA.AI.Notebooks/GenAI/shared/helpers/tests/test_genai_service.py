#!/usr/bin/env python3
"""Tests unitaires pour genai_service.py — wrapper wake-on-demand (#2982).

CI-runnables SANS Docker : `ensure_service_up` et `requests.request` sont
mockes. Valide le contrat du wrapper :
- Resolution du registre (noms connus / inconnus).
- Propagation de la cle API (Bearer) depuis .env.
- Wake-then-call : ensure_service_up appele AVANT requests.request.
- Forward des kwargs (json, data) a requests.request.
"""

import os
import sys
from pathlib import Path
from unittest import mock

import pytest

# Rendre le package `helpers` importable depuis ce fichier de test.
SHARED = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(SHARED))
sys.path.insert(0, str(SHARED.parent))

from helpers import genai_service  # noqa: E402


# --- Registre ---

def test_registry_contains_known_services():
    """Le registre couvre les principaux services GenAI (audio + image/video)."""
    names = genai_service.SERVICE_REGISTRY.keys()
    for expected in ("musicgen", "whisper", "tts-gateway", "demucs", "comfyui-qwen"):
        assert expected in names, f"Service manquant dans le registre: {expected}"


def test_registry_entries_have_required_fields():
    """Chaque entree a container (str), port (int), health (str)."""
    for name, info in genai_service.SERVICE_REGISTRY.items():
        assert isinstance(info["container"], str) and info["container"], name
        assert isinstance(info["port"], int) and 1000 <= info["port"] <= 65535, name
        assert isinstance(info["health"], str) and info["health"].startswith("/"), name


def test_resolve_known_service():
    info = genai_service._resolve_service("musicgen")
    assert info["container"] == "musicgen-api"
    assert info["port"] == 8192
    assert info["health"] == "/health"


def test_resolve_unknown_service_raises_keyerror():
    """Un service inconnu leve KeyError (pas un crash silencieux)."""
    with pytest.raises(KeyError, match="Service GenAI inconnu"):
        genai_service._resolve_service("does-not-exist")


# --- Wake-then-call ---

@mock.patch.object(genai_service, "requests")
@mock.patch.object(genai_service, "_import_ensure_service_up")
def test_call_service_wakes_before_request(mock_import_wake, mock_requests):
    """ensure_service_up est appele AVANT requests.request (wake-then-call)."""
    mock_wake = mock.MagicMock(return_value=True)
    mock_import_wake.return_value = mock_wake
    fake_resp = mock.MagicMock(status_code=200)
    mock_requests.request.return_value = fake_resp

    resp = genai_service.call_service("musicgen", "/v1/models")

    assert resp.status_code == 200
    mock_wake.assert_called_once()
    mock_requests.request.assert_called_once()
    # Le wake doit cibler le bon container (1er arg positionnel d'ensure_service_up).
    assert mock_wake.call_args.args[0] == "musicgen-api"
    assert mock_wake.call_args.args[1] == "http://localhost:8192/health"
    # Et l'URL finale pointe bien sur le port attendu.
    req_args, _ = mock_requests.request.call_args
    assert req_args[1] == "http://localhost:8192/v1/models"


@mock.patch.object(genai_service, "_import_ensure_service_up")
def test_call_service_raises_when_wake_fails(mock_import_wake):
    """Si le warm-up echoue (ensure_service_up=False), RuntimeError avant requete."""
    mock_import_wake.return_value = mock.MagicMock(return_value=False)
    with pytest.raises(RuntimeError, match="non healthy"):
        genai_service.call_service("musicgen", "/v1/models")


@mock.patch.object(genai_service, "requests")
@mock.patch.object(genai_service, "_import_ensure_service_up")
def test_call_service_forwards_kwargs_to_requests(mock_import_wake, mock_requests):
    """Les kwargs (json, data) sont forwardes a requests.request."""
    mock_import_wake.return_value = mock.MagicMock(return_value=True)
    mock_requests.request.return_value = mock.MagicMock(status_code=200)

    genai_service.call_service(
        "tts-kokoro", "/v1/audio/speech", method="POST",
        json={"text": "bonjour"}, request_timeout=5.0,
    )

    _, kwargs = mock_requests.request.call_args
    assert kwargs["json"] == {"text": "bonjour"}
    assert kwargs["timeout"] == 5.0


# --- Cle API (Bearer) ---

@mock.patch.object(genai_service, "requests")
@mock.patch.object(genai_service, "_import_ensure_service_up")
def test_api_key_explicit_sets_bearer_header(mock_import_wake, mock_requests):
    """Une cle API explicite devient un header Authorization: Bearer."""
    mock_import_wake.return_value = mock.MagicMock(return_value=True)
    mock_requests.request.return_value = mock.MagicMock(status_code=200)

    genai_service.call_service("musicgen", "/v1/models", api_key="secret123")

    _, kwargs = mock_requests.request.call_args
    assert kwargs["headers"]["Authorization"] == "Bearer secret123"


@mock.patch.object(genai_service, "requests")
@mock.patch.object(genai_service, "_import_ensure_service_up")
def test_api_key_from_env_when_none_passed(mock_import_wake, mock_requests, monkeypatch):
    """Sans api_key explicite, la cle est derivee du nom de container (MUSICGEN_API_API_KEY)."""
    mock_import_wake.return_value = mock.MagicMock(return_value=True)
    mock_requests.request.return_value = mock.MagicMock(status_code=200)
    monkeypatch.setenv("MUSICGEN_API_API_KEY", "env-secret")
    monkeypatch.setenv("TTS_GATEWAY_API_KEY", "")  # s'assurer qu'on prend la bonne

    genai_service.call_service("musicgen", "/v1/models")

    _, kwargs = mock_requests.request.call_args
    assert kwargs["headers"]["Authorization"] == "Bearer env-secret"


@mock.patch.object(genai_service, "requests")
@mock.patch.object(genai_service, "_import_ensure_service_up")
def test_no_authorization_header_when_no_api_key(mock_import_wake, mock_requests, monkeypatch):
    """Sans aucune cle, pas de header Authorization ajoute."""
    mock_import_wake.return_value = mock.MagicMock(return_value=True)
    mock_requests.request.return_value = mock.MagicMock(status_code=200)
    monkeypatch.delenv("MUSICGEN_API_API_KEY", raising=False)

    genai_service.call_service("musicgen", "/v1/models")

    _, kwargs = mock_requests.request.call_args
    assert "Authorization" not in kwargs.get("headers", {})


# --- Fallback sans service_wake ---

@mock.patch.object(genai_service, "requests")
@mock.patch.object(genai_service, "_import_ensure_service_up")
def test_works_without_service_wake_graceful(mock_import_wake, mock_requests):
    """Si service_wake absent, pas de crash : requete directe avec avertissement."""
    mock_import_wake.return_value = None
    mock_requests.request.return_value = mock.MagicMock(status_code=200)

    resp = genai_service.call_service("musicgen", "/v1/models")
    assert resp.status_code == 200
    mock_requests.request.assert_called_once()


# --- call_service_generic (hors-registre) ---

@mock.patch.object(genai_service, "requests")
@mock.patch.object(genai_service, "_import_ensure_service_up")
def test_generic_call_for_unregistered_service(mock_import_wake, mock_requests):
    """call_service_generic accepte container+port explicites (hors-registre)."""
    mock_import_wake.return_value = mock.MagicMock(return_value=True)
    mock_requests.request.return_value = mock.MagicMock(status_code=200)

    genai_service.call_service_generic(
        container="custom-svc", port=9999, path="/health",
        health_path="/ready", method="GET",
    )

    args, _ = mock_requests.request.call_args
    assert args[0] == "GET"
    assert args[1] == "http://localhost:9999/health"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
