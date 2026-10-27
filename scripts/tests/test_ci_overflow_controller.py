from __future__ import annotations

import json
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))

import ci_overflow_controller as ctl  # noqa: E402

NOW = datetime(2026, 10, 27, 12, 0, tzinfo=timezone.utc)
# Derniere ecriture de la variable, hors fenetre de dwell : le controleur
# n'est pas bloque par son propre dwell dans ces tests de CLI.
OLD = NOW - timedelta(hours=2)


def hosted(queued: int = 0, old: int = 0, oldest: float = 0.0,
           complete: bool = True, reason: str = "") -> ctl.HostedSample:
    return ctl.HostedSample(queued=queued, old=old, oldest_age_min=oldest,
                             complete=complete, reason=reason)


def local(free: int = 0, online: int = 0, starved: int = 0,
          complete: bool = True, reason: str = "") -> ctl.LocalSample:
    return ctl.LocalSample(online=online, free=free, starved=starved,
                            complete=complete, reason=reason)


# --- Regle de decision (fonction pure) -------------------------------------

def test_offre_saturee_et_parc_local_libre_bascule_vers_true():
    d = ctl.evaluate(hosted(queued=9, old=6, oldest=41.0), local(free=7, online=14),
                     current="false", now=NOW)
    assert d.action == "SWITCH_TRUE" and d.target == "true"


def test_file_hebergee_videe_bascule_vers_false():
    d = ctl.evaluate(hosted(queued=0, old=0, oldest=0.0), local(free=7, online=14),
                     current="true", now=NOW)
    assert d.action == "SWITCH_FALSE" and d.target == "false"


def test_etat_deja_au_bout_ne_bascule_pas():
    d = ctl.evaluate(hosted(queued=9, old=6, oldest=41.0), local(free=7, online=14),
                     current="true", now=NOW)
    assert d.action == "HOLD" and d.target == "true"


def test_parc_local_affame_ne_bascule_pas_vers_true():
    # Garde de securite : on n'envoie pas de debordement vers un parc qui
    # n'absorbe rien, meme si l'offre hebergee est saturee.
    d = ctl.evaluate(hosted(queued=9, old=6, oldest=41.0),
                     local(free=2, online=14, starved=4), current="true", now=NOW)
    assert d.action == "SWITCH_FALSE" and d.target == "false"


def test_parc_local_affame_deja_en_false_ne_bascule_pas():
    d = ctl.evaluate(hosted(queued=9, old=6, oldest=41.0),
                     local(free=2, online=14, starved=4), current="false", now=NOW)
    assert d.action == "HOLD"


def test_parc_local_sature_n_accepte_pas_le_debordement():
    # Le parc local n'a plus de slot libre -> on n'active pas la jambe locale.
    d = ctl.evaluate(hosted(queued=9, old=6, oldest=41.0),
                     local(free=0, online=14), current="false", now=NOW)
    assert d.action == "HOLD"


def test_jeux_de_jobs_en_file_sous_le_seuil_ne_declenchent_pas():
    d = ctl.evaluate(hosted(queued=2, old=1, oldest=20.0), local(free=7, online=14),
                     current="false", now=NOW)
    assert d.action == "HOLD"


def test_mesure_illisible_ne_bascule_jamais():
    d = ctl.evaluate(hosted(complete=False, reason="listing en echec"),
                     local(free=7, online=14), current="false", now=NOW)
    assert d.action == "UNREADABLE"


def test_mesure_locale_illisible_ne_bascule_jamais():
    d = ctl.evaluate(hosted(queued=9, old=6, oldest=41.0),
                     local(complete=False, reason="droit admin absent"),
                     current="false", now=NOW)
    assert d.action == "UNREADABLE"


def test_dwell_differe_la_bascule():
    recent = NOW - timedelta(minutes=5)
    d = ctl.evaluate(hosted(queued=9, old=6, oldest=41.0), local(free=7, online=14),
                     current="false", dwell_minutes=30, last_change_at=recent, now=NOW)
    assert d.action == "HOLD" and "dwell" in d.reason


def test_dwell_derape_une_bascule_ancienne():
    old = NOW - timedelta(minutes=120)
    d = ctl.evaluate(hosted(queued=9, old=6, oldest=41.0), local(free=7, online=14),
                     current="false", dwell_minutes=30, last_change_at=old, now=NOW)
    assert d.action == "SWITCH_TRUE"


# --- CLI --------------------------------------------------------------------

def _env(monkeypatch, token: str | None = "t"):
    for name in ("GH_TOKEN", "GITHUB_TOKEN"):
        monkeypatch.delenv(name, raising=False)
    if token is not None:
        monkeypatch.setenv("GH_TOKEN", token)


def test_cli_sans_jeton_refuse_sans_ecrire(monkeypatch, capsys):
    _env(monkeypatch, None)
    monkeypatch.setattr(ctl, "write_variable", lambda *a, **k: (_ for _ in ()).throw(
        AssertionError("aucune ecriture sans jeton")))
    rc = ctl.main(["--repo", "jsboige/CoursIA", "--apply"])
    assert rc == ctl.EXIT_REFUSED
    assert "variables: write" in capsys.readouterr().err


def test_cli_dry_run_ne_bascule_pas(monkeypatch, capsys):
    _env(monkeypatch)
    monkeypatch.setattr(ctl, "read_variable", lambda *a, **k: ("false", OLD, ""))
    monkeypatch.setattr(ctl, "collect_hosted",
                        lambda *a, **k: hosted(queued=9, old=6, oldest=41.0))
    monkeypatch.setattr(ctl, "collect_local",
                        lambda *a, **k: local(free=7, online=14))
    written = []
    monkeypatch.setattr(ctl, "write_variable",
                        lambda *a, **k: (written.append(a), (True, "ok"))[1])
    rc = ctl.main(["--repo", "jsboige/CoursIA", "--json"])
    assert rc == ctl.EXIT_OK
    assert written == []
    report = json.loads(capsys.readouterr().out)
    assert report["verdict"] == "SWITCH_TRUE"
    assert report["written"] is False and report["mode"] == "dry-run"


def test_cli_apply_bascule_et_ecrit(monkeypatch, capsys):
    _env(monkeypatch)
    monkeypatch.setattr(ctl, "read_variable", lambda *a, **k: ("false", OLD, ""))
    monkeypatch.setattr(ctl, "collect_hosted",
                        lambda *a, **k: hosted(queued=9, old=6, oldest=41.0))
    monkeypatch.setattr(ctl, "collect_local",
                        lambda *a, **k: local(free=7, online=14))
    seen = {}

    def fake_write(repo, name, value, token):
        seen["value"] = value
        return True, "variable mise a jour"

    monkeypatch.setattr(ctl, "write_variable", fake_write)
    rc = ctl.main(["--repo", "jsboige/CoursIA", "--apply", "--json"])
    assert rc == ctl.EXIT_OK
    assert seen["value"] == "true"
    report = json.loads(capsys.readouterr().out)
    assert report["written"] is True and report["verdict"] == "SWITCH_TRUE"


def test_cli_ecriture_refusee_rend_refused(monkeypatch, capsys):
    _env(monkeypatch)
    monkeypatch.setattr(ctl, "read_variable", lambda *a, **k: ("false", OLD, ""))
    monkeypatch.setattr(ctl, "collect_hosted",
                        lambda *a, **k: hosted(queued=9, old=6, oldest=41.0))
    monkeypatch.setattr(ctl, "collect_local",
                        lambda *a, **k: local(free=7, online=14))
    monkeypatch.setattr(ctl, "write_variable",
                        lambda *a, **k: (False, "HTTP 403: Resource not accessible"))
    rc = ctl.main(["--repo", "jsboige/CoursIA", "--apply", "--json"])
    assert rc == ctl.EXIT_REFUSED
    report = json.loads(capsys.readouterr().out)
    assert report["verdict"] == "REFUSED"


def test_cli_lecture_impossible_refuse_sans_mesurer(monkeypatch, capsys):
    _env(monkeypatch)
    monkeypatch.setattr(ctl, "read_variable",
                        lambda *a, **k: (None, None, "HTTP 403: Resource not accessible"))
    monkeypatch.setattr(ctl, "collect_hosted",
                        lambda *a, **k: (_ for _ in ()).throw(
                            AssertionError("aucune mesure si la variable est illisible")))
    rc = ctl.main(["--repo", "jsboige/CoursIA", "--apply", "--json"])
    assert rc == ctl.EXIT_REFUSED
    assert "variables: read" in json.loads(capsys.readouterr().out)["reason"]


def test_cli_mesure_illisible_sort_en_1(monkeypatch, capsys):
    _env(monkeypatch)
    monkeypatch.setattr(ctl, "read_variable", lambda *a, **k: ("false", OLD, ""))
    monkeypatch.setattr(ctl, "collect_hosted",
                        lambda *a, **k: hosted(complete=False, reason="listing en echec"))
    monkeypatch.setattr(ctl, "collect_local",
                        lambda *a, **k: local(free=7, online=14))
    rc = ctl.main(["--repo", "jsboige/CoursIA", "--json"])
    assert rc == ctl.EXIT_UNREADABLE
    assert json.loads(capsys.readouterr().out)["verdict"] == "UNREADABLE"
