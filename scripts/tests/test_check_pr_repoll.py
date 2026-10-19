#!/usr/bin/env python3
"""Tests de l'organe check_pr_repoll.py (#16144, item 2 -- contrat c.6205821308).

Les 7 cas contractuels :
  1. pas de registre          -> check exit 0
  2. re-sondage < N sans signal -> check exit 1
  3. < N avec signal           -> check exit 0
  4. watch vivant              -> check exit 1 (meme si last_read ancien)
  5. watch termine             -> check exit 0
  6. last_read > N             -> check exit 0
  7. registre corrompu         -> check exit 0 + warning, puis record preserve
     le fichier corrompu (backup) et repart propre.
"""

import json
import os
import sys
import tempfile
from datetime import datetime, timedelta, timezone
from pathlib import Path

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_pr_repoll import (  # noqa: E402
    _iso,
    build_parser,
    default_ledger_path,
    evaluate,
    main,
)


def _ts(minutes_ago: float) -> str:
    return _iso(datetime.now(timezone.utc) - timedelta(minutes=minutes_ago))


@pytest.fixture
def ledger(tmp_path: Path) -> Path:
    return tmp_path / "pr-poll-ledger.json"


def _write(ledger: Path, pr: str, **entry) -> None:
    data = json.loads(ledger.read_text(encoding="utf-8")) if ledger.exists() else {}
    data[pr] = entry
    ledger.write_text(json.dumps(data), encoding="utf-8")


def test_1_no_registry_check_passes(ledger: Path, capsys: pytest.CaptureFixture) -> None:
    assert main(["--ledger", str(ledger), "check", "1234"]) == 0
    assert "REFUS" not in capsys.readouterr().out


def test_2_fresh_read_without_signal_refused(ledger: Path, capsys: pytest.CaptureFixture) -> None:
    _write(ledger, "1234", last_read=_ts(5), signals=[])
    assert main(["--ledger", str(ledger), "check", "1234"]) == 1
    assert "B2'" in capsys.readouterr().out


def test_3_fresh_read_with_signal_allowed(ledger: Path, capsys: pytest.CaptureFixture) -> None:
    _write(ledger, "1234", last_read=_ts(5),
           signals=[{"at": _ts(2), "kind": "notification"}])
    assert main(["--ledger", str(ledger), "check", "1234"]) == 0
    assert "changement d'etat" in capsys.readouterr().out


def test_4_live_watch_refuses_even_old_read(ledger: Path, capsys: pytest.CaptureFixture) -> None:
    _write(ledger, "1234", last_read=_ts(600), watch_armed_at=_ts(590),
           watch_ended_at=None, signals=[])
    assert main(["--ledger", str(ledger), "check", "1234"]) == 1
    assert "B2-bis" in capsys.readouterr().out


def test_5_ended_watch_allows(ledger: Path, capsys: pytest.CaptureFixture) -> None:
    _write(ledger, "1234", last_read=_ts(600), watch_armed_at=_ts(590),
           watch_ended_at=_ts(580), signals=[])
    assert main(["--ledger", str(ledger), "check", "1234"]) == 0


def test_6_old_read_allowed(ledger: Path, capsys: pytest.CaptureFixture) -> None:
    _write(ledger, "1234", last_read=_ts(90), signals=[])
    assert main(["--ledger", str(ledger), "check", "1234"]) == 0


def test_7_corrupt_registry_fail_open_then_record_preserves(
        ledger: Path, capsys: pytest.CaptureFixture) -> None:
    ledger.write_text("{corrompu", encoding="utf-8")
    # check : fail-open -- exit 0 + warning stderr, jamais de blocage.
    assert main(["--ledger", str(ledger), "check", "1234"]) == 0
    err = capsys.readouterr().err
    assert "fail-open" in err
    # record : le corrompu est preserve (backup .corrupt-*), pas detruit.
    assert main(["--ledger", str(ledger), "record", "1234"]) == 0
    backups = list(ledger.parent.glob(f"{ledger.name}.corrupt-*"))
    assert len(backups) == 1, "le registre corrompu doit etre preserve avant remplacement"
    assert backups[0].read_text(encoding="utf-8") == "{corrompu"
    # le nouveau registre est propre et consultable.
    data = json.loads(ledger.read_text(encoding="utf-8"))
    assert "last_read" in data["1234"]
    assert main(["--ledger", str(ledger), "check", "1234"]) == 1  # < N sans signal depuis


def test_evaluate_watch_end_signal_beats_fresh_read() -> None:
    """Borne hors contrat strict : la fin de watch est un signal -- sous
    l'age minimal (60 min < 120), la relecture reste LIBRE parce que le
    watcher vient de rendre la main en notifiant (signal >= last_read).
    Sans la regle du signal, ce cas serait refuse : c'est le cas
    discriminant de B2'."""
    now = datetime.now(timezone.utc)
    entry = {
        "last_read": _iso(now - timedelta(minutes=60)),
        "watch_armed_at": _iso(now - timedelta(minutes=120)),
        "watch_ended_at": _iso(now - timedelta(minutes=2)),
        "signals": [{"at": _iso(now - timedelta(minutes=2)), "kind": "watch-end"}],
    }
    assert evaluate(entry, now, 120).refused is False


def test_9_default_ledger_is_stable_not_tempdir() -> None:
    """Review #21060 : le defaut ne doit plus vivre sous le tempdir --
    purge par les regles de scratch de la flotte, il vidait le registre
    et le garde perdait son effet sans le dire."""
    path = default_ledger_path()
    assert path.name == "pr-poll-ledger.json"
    tmp = Path(tempfile.gettempdir()).resolve()
    try:
        path.resolve().relative_to(tmp)
        under = True
    except ValueError:
        under = False
    assert not under, "le defaut ne doit pas vivre sous le tempdir"
    assert "coursia" in [p.lower() for p in path.parts]


def test_10_build_parser_format_help_does_not_crash() -> None:
    """Review coordinateur #21060 : argparse.help= doit etre exempt de % non
    echappes, sinon `format_help()` leve ValueError (3.11) ou la construction
    du parser leve en 3.14+. Regression : `%%LOCALAPPDATA%%` ecrit en clair
    dans le help= de `--ledger`."""
    help_text = build_parser().format_help()
    # verifie que le path documente bien la cible (avec %% reduit a % par argparse)
    assert "LOCALAPPDATA" in help_text, help_text
    # et qu'aucun format involontaire ne reste (le %% est reduit a % par argparse)
    assert "%L" not in help_text.replace("%%", "").replace("LOCALAPPDATA", ""), (
        "le help= doit etre ecrit sans % non echappe susceptible d'etre "
        "interprete par argparse comme un format"
    )
