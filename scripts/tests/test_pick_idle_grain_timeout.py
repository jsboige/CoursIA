"""Tests for scripts/pick_idle_grain.py subprocess timeout coverage (#19643).

Le picker belt, a cache froid, depasse regulierement le timeout par defaut
des outils shell d'agent (~115-120 s). Cause mesuree le 2026-10-07 sur
po-2026 : PR #19646 a pose une borne `timeout=` sur
`scripts/ci/fetch_merged_prs_since.py` (RUN_GH_TIMEOUT_S=60.0) mais le
picker lui-meme est reste sans borne sur 2 appels :

  * `_newest_remote_issue_update()` (L717) -- sonde freshness, devrait
    timeout=15 s.
  * `fetch_pool.fetch_raw()` (L935) -- transport principal du tapis
    (`gh issue list --limit N --json ...`), devrait timeout=120 s.

Un `gh` ralenti (secondary rate limit, backoff silencieux) pouvait faire
pendre l'appel au-dela du timeout de l'outil, et le picker rendait un
verdict vide (rc=124, stdout=stderr=vide). Ces tests ferment les deux
trous : un appel qui timeout leve `subprocess.TimeoutExpired`, et la
fonction appelante rend un verdict explicite (None pour la sonde,
`TransportUnavailable` pour le tapis).

Run:
    python -m pytest scripts/tests/test_pick_idle_grain_timeout.py
"""
import subprocess
import sys
from pathlib import Path
from unittest.mock import patch

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import pick_idle_grain as pig  # noqa: E402


def test_sonde_freshness_timeout_retourne_none():
    """La sonde `_newest_remote_issue_update` timeout=15 s.

    Si `gh api ...` depasse la borne, la fonction rend None (pas d'exception
    propagee) -- l'appelant retombe sur un hit NON verifie et l'annoncera
    via `draw_verdict`. Une sonde qui timeout doit etre muette, pas trompeuse.
    """
    with patch.object(pig.subprocess, "run",
                      side_effect=subprocess.TimeoutExpired(cmd="gh", timeout=15)):
        result = pig._newest_remote_issue_update()
    assert result is None


def test_sonde_freshness_process_error_retourne_none():
    """Garde le comportement OSError / CalledProcessError historique."""
    with patch.object(pig.subprocess, "run",
                      side_effect=OSError("gh absent")):
        result = pig._newest_remote_issue_update()
    assert result is None


def test_fetch_pool_transport_timeout_rend_pool_vide_avec_read_error():
    """Le transport GraphQL principal timeout=120 s.

    Si `gh issue list --json` timeout, la voie REST prend le relais
    (`_rest_pages` -> via `except Exception`). Si elle aussi echoue,
    `fetch_pool` capture `TransportUnavailable` en interne (L993-995) et rend
    ``([], "GraphQL indisponible (TimeoutExpired), REST egalement indisponible (TimeoutExpired)")``
    -- l'appelant `draw_verdict` distingue un pool vide d'un pool non mesurable.
    """
    with patch.object(pig.subprocess, "run",
                      side_effect=subprocess.TimeoutExpired(cmd="gh", timeout=120)):
        pool, read_error = pig.fetch_pool(
            cache=None, cache_mode="off", cache_status=None)
    assert pool == []
    assert read_error is not None
    assert "TimeoutExpired" in read_error
    # Les DEUX voies tombent (GraphQL + REST), le verdict le dit
    assert "GraphQL indisponible" in read_error
    assert "REST egalement indisponible" in read_error


def test_fetch_pool_transport_called_process_error_rend_pool_vide_avec_read_error():
    """Garde le comportement CalledProcessError historique (gh rc != 0).

    `CalledProcessError` en Python 3.13 utilise le kwarg `returncode=`
    (legacy `rc=` rejete en 3.13, cf. PEP 678). Le test verifie que
    l'erreur est bien formee.
    """
    err = subprocess.CalledProcessError(
        returncode=1, cmd="gh", output="", stderr="auth")
    with patch.object(pig.subprocess, "run", side_effect=err):
        pool, read_error = pig.fetch_pool(
            cache=None, cache_mode="off", cache_status=None)
    assert pool == []
    assert read_error is not None
    assert "CalledProcessError" in read_error


def test_timeout_valeur_explicite_15_pour_sonde():
    """Le timeout de la sonde est 15 s, pas la valeur par defaut de gh.

    Casse en silence si quelqu'un retire la borne : pytest capture la valeur
    passee a subprocess.run et la compare. Cf. CC #19643.
    """
    captured = {}

    def fake_run(cmd, **kwargs):
        captured["timeout"] = kwargs.get("timeout")
        # Simule un succes pour ne pas tomber dans le except
        result = subprocess.CompletedProcess(cmd, 0, stdout="2026-10-18T00:00:00Z", stderr="")
        return result

    with patch.object(pig.subprocess, "run", side_effect=fake_run):
        pig._newest_remote_issue_update()
    assert captured["timeout"] == 15


def test_timeout_valeur_explicite_120_pour_transport_principal():
    """Le timeout de fetch_pool.fetch_raw est 120 s (transport principal).

    Une borne inferieure timeout systematiquement sur de gros pools
    (POOL_FETCH_LIMIT=2000). 120 s = 2x la mesure observee a cache chaud.
    """
    timeouts = []

    def fake_run(cmd, **kwargs):
        # On releve TOUS les appels, pas seulement le dernier : `fetch_pool`
        # peut enchainer sur un autre transport, et une sonde bornee par
        # `_clamp_timeout` rend alors un temps restant (`43.79...` mesure en
        # CI, cf #23977). Un scalaire ecrase faisait donc echouer ce test sur
        # un chemin parfaitement correct -- il mesurait l'ordre des appels au
        # lieu de la borne, alors que son enonce dit « au moins un appel ».
        timeouts.append(kwargs.get("timeout"))
        result = subprocess.CompletedProcess(
            cmd, 0, stdout="[]", stderr="")
        return result

    with patch.object(pig.subprocess, "run", side_effect=fake_run):
        try:
            pig.fetch_pool(cache=None, cache_mode="off", cache_status=None)
        except pig.TransportUnavailable:
            # Le second transport (REST) peut aussi timeout selon les mocks ;
            # ce qui compte ici est la borne du 1er transport.
            pass
    # Au moins un appel (le transport GraphQL) doit avoir timeout=120
    assert timeouts, "aucun appel `gh` n'a ete emis -- le test ne mesurerait rien"
    assert 120 in timeouts, (
        f"aucun appel a timeout=120 ; timeouts releves : {timeouts}")
