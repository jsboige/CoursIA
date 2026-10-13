"""Tests de ``check_scheduled_organs`` (scripts/coordination/session_hygiene.py) -- #17748.

Cas fondateur (2026-09-25, ai-01) : le siege ``D:\CoursIA-wt-merge-ready`` purge, la
tache ``merge_ready`` se declenchait toutes les 20 min et mourait avant d'ouvrir son
journal. Les quatre cas ci-dessous pinnent les deux predicats (siege present, journal
qui avance) et le cas « non installe ici ». Aucun appel git : ces tests tournent
aussi sous xdist.
"""

from __future__ import annotations

import importlib.util
import os
import sys
from pathlib import Path

_SCRIPT = Path(__file__).resolve().parent.parent / "coordination" / "session_hygiene.py"
_spec = importlib.util.spec_from_file_location("session_hygiene_organs", _SCRIPT)
sh = importlib.util.module_from_spec(_spec)
sys.modules["session_hygiene_organs"] = sh
_spec.loader.exec_module(sh)

NOW = 1_800_000_000.0


def _install(appdata: Path, repo: Path, log_age_min: float | None) -> Path:
    """Installe un faux organe merge_ready : lanceur VBS + journal date de log_age_min."""
    state = appdata / "CoursIA" / "merge_ready"
    (state / "logs").mkdir(parents=True)
    (state / "run_hidden.vbs").write_text(
        'WScript.Quit WshShell.Run("C:\Python314\python.exe '
        f'{repo}\scripts\coordination\install_merge_ready_task.py --run --repo {repo}", 0, True)\n',
        encoding="utf-8",
    )
    if log_age_min is not None:
        log = state / "logs" / "merge_ready_20260925.log"
        log.write_text("=== run end rc=0 ===\n", encoding="utf-8")
        t = NOW - log_age_min * 60
        os.utime(log, (t, t))
    return state


def _only(checks):
    assert len(checks) == 1
    return checks[0]


def test_not_installed_is_green(tmp_path):
    c = _only(sh.check_scheduled_organs(local_appdata=tmp_path, now=NOW))
    assert c.level == sh.GREEN
    assert "non installe" in c.detail


def test_missing_seat_is_red(tmp_path):
    """Le cas mesure : le lanceur nomme un siege purge -> RED, meme avec un journal frais."""
    _install(tmp_path, tmp_path / "wt-merge-ready-purged", log_age_min=1)
    c = _only(sh.check_scheduled_organs(local_appdata=tmp_path, now=NOW))
    assert c.level == sh.RED
    assert "absent" in c.detail
    assert "git worktree add --detach" in c.fix


def test_silent_log_is_red(tmp_path):
    """Siege present mais journal plus vieux que 3 intervalles (2 h 20 mesurees) -> RED."""
    seat = tmp_path / "seat"
    seat.mkdir()
    _install(tmp_path, seat, log_age_min=140)
    c = _only(sh.check_scheduled_organs(local_appdata=tmp_path, now=NOW))
    assert c.level == sh.RED
    assert c.data["age_min"] == 140


def test_fresh_log_is_green(tmp_path):
    """Controle negatif : siege present, journal a 12 min (< 3 x 20) -> GREEN."""
    seat = tmp_path / "seat"
    seat.mkdir()
    _install(tmp_path, seat, log_age_min=12)
    c = _only(sh.check_scheduled_organs(local_appdata=tmp_path, now=NOW))
    assert c.level == sh.GREEN
    assert c.data["age_min"] == 12


def test_installed_without_any_log_is_amber(tmp_path):
    seat = tmp_path / "seat"
    seat.mkdir()
    _install(tmp_path, seat, log_age_min=None)
    c = _only(sh.check_scheduled_organs(local_appdata=tmp_path, now=NOW))
    assert c.level == sh.AMBER
