#!/usr/bin/env python3
"""Tests du garde de budget gh (#17201).

Ces tests verrouillent la **detection** sans dependre de l'etat du budget reel
de la machine : un garde qui saute toujours serait pire que pas de garde
(les tests ne prouveraient plus rien). D'ou le controle positif : une sortie
saine ne doit JAMAIS etre classee « budget epuise ».

Executable deux facons :
    python scripts/tests/test_gh_availability.py
    python -m pytest scripts/tests/test_gh_availability.py
"""

from __future__ import annotations

import os
import subprocess
import sys

import pytest

# Import ABSOLU, comme les siblings du repertoire (#17229, reserve Hermes
# 5267953658) : le docstring annonce `py scripts/tests/test_gh_availability.py`,
# et un import relatif casse cette invocation (`attempted relative import with
# no known parent package`). L'alias `gha` est garde volontairement : il evite
# de reecrire les 26 sites d'appel pour une correction d'un caractere.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import _gh_availability as gha  # noqa: E402

# Message mesure le 21/09/2026 (triage #17201) : c'est le texte exact que
# `gh api graphql` et les scripts testes propagent.
REFUSAL = (
    '{"errors":[{"type":"RATE_LIMIT","code":"graphql_rate_limit",'
    '"message":"API rate limit already exceeded for user ID 3159389."}]}'
    "gh: API rate limit already exceeded for user ID 3159389.\n"
)
# Sortie saine : la sonde a abouti (controle positif).
HEALTHY = '{"data":{"viewer":{"login":"jsboige"}}}\n'


class _Proc:
    """CompletedProcess minimal, evite un vrai appel reseau."""

    def __init__(self, returncode: int, stdout: str = "", stderr: str = ""):
        self.returncode = returncode
        self.stdout = stdout
        self.stderr = stderr


@pytest.fixture(autouse=True)
def _reset_probe_cache(monkeypatch):
    """La sonde est cachee au niveau module : la vider entre les tests."""
    monkeypatch.setattr(gha, "_probe_verdict", None)
    yield


class TestIsRateLimited:
    def test_exact_message_from_17201_triage_is_detected(self):
        assert gha.is_rate_limited(REFUSAL) is True

    def test_positive_control_healthy_output_is_not_flagged(self):
        assert gha.is_rate_limited(HEALTHY) is False

    def test_empty_output_is_not_flagged(self):
        assert gha.is_rate_limited("") is False
        assert gha.is_rate_limited(None) is False


class TestGhGraphqlOk:
    def test_ok_when_probe_succeeds(self, monkeypatch):
        monkeypatch.setattr(gha.shutil, "which", lambda _n: "gh")
        monkeypatch.setattr(
            gha.subprocess, "run", lambda *a, **k: _Proc(0, HEALTHY)
        )
        assert gha.gh_graphql_ok() is True

    def test_false_when_probe_refused_on_budget(self, monkeypatch):
        monkeypatch.setattr(gha.shutil, "which", lambda _n: "gh")
        monkeypatch.setattr(
            gha.subprocess, "run", lambda *a, **k: _Proc(1, "", REFUSAL)
        )
        assert gha.gh_graphql_ok() is False

    def test_none_when_gh_missing(self, monkeypatch):
        monkeypatch.setattr(gha.shutil, "which", lambda _n: None)
        assert gha.gh_graphql_ok() is None

    def test_none_when_probe_fails_for_another_reason(self, monkeypatch):
        # Un refus d'auth n'est PAS un budget epuise : ne pas masquer.
        monkeypatch.setattr(gha.shutil, "which", lambda _n: "gh")
        monkeypatch.setattr(
            gha.subprocess,
            "run",
            lambda *a, **k: _Proc(1, "", "gh: authentication required\n"),
        )
        assert gha.gh_graphql_ok() is None

    def test_none_when_probe_times_out(self, monkeypatch):
        monkeypatch.setattr(gha.shutil, "which", lambda _n: "gh")

        def _boom(*a, **k):
            raise subprocess.TimeoutExpired(cmd="gh", timeout=30)

        monkeypatch.setattr(gha.subprocess, "run", _boom)
        assert gha.gh_graphql_ok() is None

    def test_verdict_is_cached_between_calls(self, monkeypatch):
        calls = []
        monkeypatch.setattr(gha.shutil, "which", lambda _n: "gh")

        def _run(*a, **k):
            calls.append(1)
            return _Proc(0, HEALTHY)

        monkeypatch.setattr(gha.subprocess, "run", _run)
        gha.gh_graphql_ok()
        gha.gh_graphql_ok()
        assert len(calls) == 1, "la sonde doit etre faite une fois par session"


class TestGuards:
    def test_skip_if_gh_exhausted_skips_when_refused(self, monkeypatch):
        monkeypatch.setattr(gha, "_probe_verdict", False)
        with pytest.raises(pytest.skip.Exception):
            gha.skip_if_gh_exhausted()

    @pytest.mark.parametrize("verdict", [True, None])
    def test_skip_if_gh_exhausted_does_not_skip_otherwise(
        self, monkeypatch, verdict
    ):
        monkeypatch.setattr(gha, "_probe_verdict", verdict)
        gha.skip_if_gh_exhausted()  # ne doit pas lever

    def test_skip_if_output_rate_limited_skips_on_signature(self):
        with pytest.raises(pytest.skip.Exception):
            gha.skip_if_output_rate_limited("gh error: " + REFUSAL)

    def test_skip_if_output_rate_limited_ignores_healthy_output(self):
        gha.skip_if_output_rate_limited(HEALTHY)  # ne doit pas lever


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
