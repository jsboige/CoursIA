"""Tests unitaires pour comfyui_idle_monitor.py (incident 2026-08-25).

Déterministes : mockent les primitives HTTP du monitor (pas de ComfyUI réel,
pas de réseau). Le incident fondateur : quand l'API devient injoignable
(auth stale post-restart, serveur saturé en génération), l'ancien code
confondait « échec de la requête » et « queue vide vérifiée », devinait un
idle depuis le démarrage du monitor, et tirait /free EN BOUCLE — y compris
dans un serveur en pleine génération, le faisant crasher (exit 0, reboot
7-8 min, 3 restarts en ~30 min ; logs : « no history » + idle croissant
2673→3273s + unload 18→27 toutes les ~67s).

Les tests verrouillent le fail-safe tri-états :
  UNKNOWN (indéterminable)  -> skip, jamais de /free à l'aveugle ;
  None (vide vérifié)        -> fallback monitor_start (boot frais) ;
  garde pré-/free            -> queue relue à l'instant du tir.
"""

from __future__ import annotations

import importlib.util
import time
from pathlib import Path
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
MONITOR = HERE / "comfyui_idle_monitor.py"


def _load():
    spec = importlib.util.spec_from_file_location("comfyui_idle_monitor", MONITOR)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _monitor(mod, idle_timeout: int = 1200):
    return mod.ComfyUIIdleMonitor(
        comfyui_url="http://comfyui-test:8188",
        idle_timeout=idle_timeout,
        check_interval=60,
        auth_token="test-token",
    )


# --- Tri-state des primitives -------------------------------------------------


def test_queue_failure_returns_unknown_not_empty():
    mod = _load()
    m = _monitor(mod)
    with patch.object(m, "session") as sess:
        sess.get.side_effect = ConnectionError("refused")
        r = m.get_running_prompts()
    assert r is mod.UNKNOWN, "un échec de requête n'est PAS une queue vide"


def test_history_failure_returns_unknown_not_empty():
    mod = _load()
    m = _monitor(mod)
    with patch.object(m, "session") as sess:
        sess.get.side_effect = ConnectionError("refused")
        r = m.get_recent_history()
    assert r is mod.UNKNOWN


def test_auth_failure_returns_unknown_not_empty():
    """Le déclencheur réel de l'incident : token stale après restart du serveur."""
    mod = _load()
    m = _monitor(mod)
    m.auth_token = None
    m.username = "admin"
    m.password = "secret"
    m._logged_in = False
    with patch.object(m, "login", return_value=False):
        assert m.get_running_prompts() is mod.UNKNOWN
        assert m.get_recent_history() is mod.UNKNOWN


# --- check_and_unload : fail-safe UNKNOWN -> skip, pas de /free aveugle -------


def test_indeterminate_api_skips_check_no_free():
    """Le cœur du fix : API injoignable -> SKIP, même si l'idle « deviné »
    depuis le start du monitor dépasse largement le timeout."""
    mod = _load()
    m = _monitor(mod)
    m._monitor_start_time = time.time() - 99999  # « idle » astronomique
    with patch.object(m, "get_last_activity_time", return_value=mod.UNKNOWN), \
         patch.object(m, "unload_models") as unload:
        assert m.check_and_unload() is False
        unload.assert_not_called()
    assert m._error_count == 1


def test_indeterminate_api_without_start_time_also_skips():
    mod = _load()
    m = _monitor(mod)
    m._monitor_start_time = None
    with patch.object(m, "get_last_activity_time", return_value=mod.UNKNOWN), \
         patch.object(m, "unload_models") as unload:
        assert m.check_and_unload() is False
        unload.assert_not_called()


# --- Chemins légitimes (non-régression) ----------------------------------------


def test_verified_idle_triggers_free_and_resets_baseline():
    mod = _load()
    m = _monitor(mod)
    old_start = time.time() - 99999
    m._monitor_start_time = old_start
    with patch.object(m, "get_last_activity_time", return_value=time.time() - 99999), \
         patch.object(m, "get_running_prompts", return_value=[]), \
         patch.object(m, "unload_models", return_value=True) as unload:
        assert m.check_and_unload() is True
        unload.assert_called_once()
    assert m._monitor_start_time > old_start, "le reset post-unload doit tenir"


def test_running_prompt_counts_as_active():
    mod = _load()
    m = _monitor(mod)
    m._monitor_start_time = time.time() - 99999
    with patch.object(m, "get_last_activity_time", return_value=time.time()), \
         patch.object(m, "unload_models") as unload:
        assert m.check_and_unload() is False
        unload.assert_not_called()


def test_empty_verified_history_after_boot_falls_back_to_monitor_start():
    """None (vide VÉRIFIÉ, pas UNKNOWN) reste éligible au fallback boot frais."""
    mod = _load()
    m = _monitor(mod, idle_timeout=100)
    m._monitor_start_time = time.time() - 200  # boot il y a 200s, timeout 100s
    with patch.object(m, "get_last_activity_time", return_value=None), \
         patch.object(m, "get_running_prompts", return_value=[]), \
         patch.object(m, "unload_models", return_value=True) as unload:
        assert m.check_and_unload() is True
        unload.assert_called_once()


# --- Garde pré-/free -----------------------------------------------------------


def test_free_aborts_when_queue_started_between_measure_and_fire():
    """Une génération démarre entre la lecture d'historique et le /free :
    le re-check à l'instant du tir doit l'annuler."""
    mod = _load()
    m = _monitor(mod)
    m._monitor_start_time = time.time() - 99999
    with patch.object(m, "get_last_activity_time", return_value=time.time() - 99999), \
         patch.object(m, "get_running_prompts", return_value=["prompt-abc"]), \
         patch.object(m, "unload_models") as unload:
        assert m.check_and_unload() is False
        unload.assert_not_called()


def test_free_aborts_when_precheck_indeterminate():
    mod = _load()
    m = _monitor(mod)
    m._monitor_start_time = time.time() - 99999
    with patch.object(m, "get_last_activity_time", return_value=time.time() - 99999), \
         patch.object(m, "get_running_prompts", return_value=mod.UNKNOWN), \
         patch.object(m, "unload_models") as unload:
        assert m.check_and_unload() is False
        unload.assert_not_called()


def test_free_fires_when_precheck_confirms_empty_queue():
    """Queue relue VIDE à l'instant du tir : le /free légitime passe."""
    mod = _load()
    m = _monitor(mod)
    m._monitor_start_time = time.time() - 99999
    # get_last_activity_time appelle get_running_prompts en interne (première
    # lecture : vide), puis la garde pré-/free relit (deuxième lecture : vide).
    with patch.object(m, "get_last_activity_time", return_value=time.time() - 99999), \
         patch.object(m, "get_running_prompts", return_value=[]), \
         patch.object(m, "unload_models", return_value=True) as unload:
        assert m.check_and_unload() is True
        unload.assert_called_once()
