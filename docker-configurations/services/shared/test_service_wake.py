"""Tests unitaires pour service_wake.py (#2982).

Déterministes : mockent `subprocess.run` et `requests.get` (pas de docker réel,
pas de réseau). Conformité H.1 — validation logique pure.
"""

from __future__ import annotations

import subprocess
from unittest.mock import MagicMock, patch

import pytest
import requests

import service_wake


# --- probe_health -----------------------------------------------------------


def test_probe_health_ok():
    resp = MagicMock(status_code=200)
    with patch("service_wake.requests.get", return_value=resp):
        assert service_wake.probe_health("http://localhost:8192/health") is True


def test_probe_health_non_200():
    resp = MagicMock(status_code=503)
    with patch("service_wake.requests.get", return_value=resp):
        assert service_wake.probe_health("http://localhost:8192/health") is False


def test_probe_health_connection_refused():
    with patch(
        "service_wake.requests.get",
        side_effect=requests.exceptions.ConnectionError("refused"),
    ):
        assert service_wake.probe_health("http://localhost:8192/health") is False


def test_probe_health_sends_bearer_when_api_key():
    resp = MagicMock(status_code=200)
    with patch("service_wake.requests.get", return_value=resp) as mock_get:
        service_wake.probe_health("http://h/health", api_key="secret")
        _, kwargs = mock_get.call_args
        assert kwargs["headers"]["Authorization"] == "Bearer secret"


# --- docker_start -----------------------------------------------------------


def test_docker_start_success():
    result = MagicMock(returncode=0, stderr="")
    with patch("service_wake.subprocess.run", return_value=result):
        assert service_wake.docker_start("musicgen-api") is True


def test_docker_start_nonzero_exit():
    result = MagicMock(returncode=1, stderr="No such container")
    with patch("service_wake.subprocess.run", return_value=result):
        assert service_wake.docker_start("ghost") is False


def test_docker_start_invokes_correct_args():
    result = MagicMock(returncode=0)
    with patch("service_wake.subprocess.run", return_value=result) as mock_run:
        service_wake.docker_start("musicgen-api")
        assert mock_run.call_args.args[0] == ["docker", "start", "musicgen-api"]


def test_docker_start_handles_subprocess_error():
    with patch(
        "service_wake.subprocess.run",
        side_effect=subprocess.TimeoutExpired(cmd="docker", timeout=30),
    ):
        assert service_wake.docker_start("musicgen-api") is False


# --- ensure_service_up ------------------------------------------------------


def test_ensure_service_up_fast_path_no_docker_start():
    """Service déjà healthy → on n'appelle jamais docker start."""
    resp = MagicMock(status_code=200)
    with patch("service_wake.requests.get", return_value=resp), patch(
        "service_wake.docker_start"
    ) as mock_start:
        assert service_wake.ensure_service_up("svc", "http://h/health") is True
        mock_start.assert_not_called()


def test_ensure_service_up_cold_start_succeeds():
    """Service down → docker start → poll devient 200 → True."""
    # 1er probe (fast-path) = connection refused, puis probes post-start = 200.
    probe_sequence = [
        False,  # fast-path: down
        False,  # 1er poll après start (warm-up pas fini)
        True,  # 2e poll: healthy
    ]

    def fake_probe(url, api_key=None, timeout=5):
        return probe_sequence.pop(0)

    with patch("service_wake.probe_health", side_effect=fake_probe), patch(
        "service_wake.docker_start", return_value=True
    ) as mock_start, patch("service_wake.time.sleep"):
        assert service_wake.ensure_service_up("svc", "http://h/health") is True
        mock_start.assert_called_once_with("svc")


def test_ensure_service_up_docker_start_fails():
    """docker start échoue → False immédiat (pas de poll)."""
    with patch("service_wake.probe_health", return_value=False), patch(
        "service_wake.docker_start", return_value=False
    ):
        assert service_wake.ensure_service_up("svc", "http://h/health") is False


def test_ensure_service_up_fast_path_forwards_api_key():
    """Contrat sécurité (#16) : api_key doit atteindre probe_health même au
    fast-path — sinon un service auth-actif renvoie 401 et le helper croit le
    service down → déclenche un docker start inutile."""
    received_keys = []

    def fake_probe(url, api_key=None, timeout=5):
        received_keys.append(api_key)
        return True  # fast-path hit

    with patch("service_wake.probe_health", side_effect=fake_probe):
        assert service_wake.ensure_service_up(
            "svc", "http://h/health", api_key="secret"
        ) is True
        assert received_keys == ["secret"], (
            "api_key must propagate to probe_health on the fast-path"
        )


def test_ensure_service_up_cold_path_forwards_api_key():
    """Contrat sécurité (#16) : api_key doit atteindre CHAQUE poll du cold-path
    (fast-path down + post-start polls), pas seulement le 1er."""
    received_keys = []

    def fake_probe(url, api_key=None, timeout=5):
        received_keys.append(api_key)
        return len(received_keys) >= 3  # down, down, then healthy

    with patch("service_wake.probe_health", side_effect=fake_probe), patch(
        "service_wake.docker_start", return_value=True
    ), patch("service_wake.time.sleep"):
        assert service_wake.ensure_service_up(
            "svc", "http://h/health", api_key="secret"
        ) is True
        # All probes (fast-path + cold-path polls) received the key.
        assert received_keys == ["secret", "secret", "secret"], (
            "api_key must propagate to every probe, not just the first"
        )


def test_ensure_service_up_times_out():
    """Service jamais healthy après start → False après timeout."""

    # Fast-path down, puis tous les polls down.
    def fake_probe(url, api_key=None, timeout=5):
        return False

    # Force le timeout en simulant le temps qui s'écoule.
    clock = [0.0]

    def fake_monotonic():
        return clock[0]

    def fake_sleep(seconds):
        clock[0] += seconds

    with patch("service_wake.probe_health", side_effect=fake_probe), patch(
        "service_wake.docker_start", return_value=True
    ), patch("service_wake.time.monotonic", side_effect=fake_monotonic), patch(
        "service_wake.time.sleep", side_effect=fake_sleep
    ):
        result = service_wake.ensure_service_up(
            "svc", "http://h/health", timeout=10, poll_interval=2
        )
        assert result is False


# --- CLI --------------------------------------------------------------------


def test_cli_returns_0_when_healthy():
    with patch("service_wake.ensure_service_up", return_value=True), patch(
        "sys.argv", ["service_wake.py", "svc", "--health-url", "http://h/health"]
    ):
        assert service_wake.main() == 0


def test_cli_returns_1_when_not_healthy():
    with patch("service_wake.ensure_service_up", return_value=False), patch(
        "sys.argv", ["service_wake.py", "svc", "--health-url", "http://h/health"]
    ):
        assert service_wake.main() == 1
