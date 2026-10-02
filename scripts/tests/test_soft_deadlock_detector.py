#!/usr/bin/env python3
"""Tests soft_deadlock_detector — conjonction #15511 P2, corpus synthétique.

Le profil fondateur est #14821 : mergeable, 5 jours d'âge, 28 commentaires
humains dont la majorité sans action réparatrice. Chaque test isole UNE
branche de la conjonction (âge, mergeable, fenêtre, humanité des
commentaires) — la détection ne doit tirer que sur la conjonction complète.
"""
from __future__ import annotations

import json
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import soft_deadlock_detector as sdd  # noqa: E402

NOW = datetime(2026, 10, 1, 12, 0, 0, tzinfo=timezone.utc)


class FakeProc:
    def __init__(self, returncode=0, stdout="[]", stderr=""):
        self.returncode = returncode
        self.stdout = stdout
        self.stderr = stderr


def _pr(number, age_hours, mergeable="MERGEABLE", comments=()):
    return {
        "number": number,
        "title": f"PR synthétique #{number}",
        "createdAt": (NOW - timedelta(hours=age_hours)).strftime(
            "%Y-%m-%dT%H:%M:%SZ"),
        "mergeable": mergeable,
        "comments": [
            {
                "author": {"login": c[0]},
                "createdAt": (NOW - timedelta(hours=c[1])).strftime(
                    "%Y-%m-%dT%H:%M:%SZ"),
                "body": c[2],
            }
            for c in comments
        ],
    }


def _humans(n, hours_ago=1, chars=500):
    """n commentaires humains dans la fenêtre, de taille réaliste."""
    return [("myia-po-2027", hours_ago, "x" * chars)] * n


def _bots(n, hours_ago=1):
    return [("github-actions[bot]", hours_ago, "organ output")] * n


# ---------------------------------------------------------------------------
# Conjonction : chaque branche isolée
# ---------------------------------------------------------------------------

def test_canonical_profile_detected():
    """#14821-like : mergeable + 120h + 7 humains/24h -> 1 finding."""
    prs = [_pr(14821, 120, comments=_humans(7))]
    report = sdd.analyze(prs, NOW)
    assert len(report["findings"]) == 1
    f = report["findings"][0]
    assert f["number"] == 14821
    assert f["human_comments_window"] == 7
    assert f["chars_window"] == 7 * 500


def test_fresh_pr_not_detected_despite_churn():
    """Âge 10h : le churn seul ne suffit pas (démarrage sain)."""
    prs = [_pr(1, 10, comments=_humans(7))]
    assert sdd.analyze(prs, NOW)["findings"] == []


def test_conflicted_pr_not_detected():
    """CONFLICTING : candidate réparable par sa lane (picker P0), pas un
    deadlock soft."""
    prs = [_pr(2, 200, mergeable="CONFLICTING", comments=_humans(7))]
    assert sdd.analyze(prs, NOW)["findings"] == []


def test_quiet_pr_not_detected():
    """Âge 200h mais 2 commentaires : stagnation silencieuse — c'est la
    file de réparation/picker, pas la pompe à commentaires."""
    prs = [_pr(3, 200, comments=_humans(2))]
    assert sdd.analyze(prs, NOW)["findings"] == []


def test_bot_churn_does_not_count():
    """6 commentaires de bots + 2 humains dans la fenêtre : pas de finding
    — les organes CI ne sont pas la pompe mesurée."""
    prs = [_pr(4, 100, comments=_bots(6) + _humans(2))]
    assert sdd.analyze(prs, NOW)["findings"] == []


def test_comments_outside_window_do_not_count():
    """7 humains mais vieux de 48h : hors fenêtre 24h, pas de finding."""
    prs = [_pr(5, 200, comments=[("myia-po-2027", 48, "x" * 500)] * 7)]
    assert sdd.analyze(prs, NOW)["findings"] == []


def test_mergeable_unknown_skipped_and_counted():
    """UNKNOWN n'est ni finding ni refus : compté, reporté au tir suivant."""
    prs = [_pr(6, 100, mergeable="UNKNOWN", comments=_humans(7))]
    report = sdd.analyze(prs, NOW)
    assert report["findings"] == []
    assert report["skipped_mergeable_unknown"] == 1


def test_boundary_age_is_strict():
    """âge == 72h exactement : strictement supérieur exigé -> pas de finding."""
    prs = [_pr(7, 72, comments=_humans(7))]
    assert sdd.analyze(prs, NOW)["findings"] == []


def test_boundary_comments_is_strict():
    """5 humains == min -> refus (le seuil est « > 5 », comme la spec)."""
    prs = [_pr(8, 100, comments=_humans(5))]
    assert sdd.analyze(prs, NOW)["findings"] == []


def test_findings_sorted_by_churn_desc():
    """La PR la plus bruyante d'abord — c'est la priorité de triage."""
    prs = [_pr(9, 100, comments=_humans(6)), _pr(10, 100, comments=_humans(9))]
    numbers = [f["number"] for f in sdd.analyze(prs, NOW)["findings"]]
    assert numbers == [10, 9]


# ---------------------------------------------------------------------------
# Critère 5 — commit dans la fenêtre (instance #18158, mesurée en live)
# ---------------------------------------------------------------------------

def _ts(hours_ago):
    return (NOW - timedelta(hours=hours_ago)).strftime("%Y-%m-%dT%H:%M:%SZ")


def test_active_pr_with_recent_commit_excluded():
    """Commit il y a 2h dans la fenêtre : la PR itère, pas de finding
    (fausse positive #18158 corrigée)."""
    prs = [_pr(18158, 82, comments=_humans(6))]
    report = sdd.analyze(prs, NOW, last_commit_dates={18158: _ts(2)})
    assert report["findings"] == []
    assert report["skipped_active_in_window"] == 1


def test_stale_last_commit_still_detected():
    """Dernier commit il y a 100h (hors fenêtre) : finding conservé."""
    prs = [_pr(11, 120, comments=_humans(7))]
    report = sdd.analyze(prs, NOW, last_commit_dates={11: _ts(100)})
    assert len(report["findings"]) == 1
    assert report["findings"][0]["last_commit_unknown"] is False


def test_missing_commit_date_fails_open_to_signal():
    """Requête view échouée (date None) : candidate conservée, marquée
    inconnue — le triage humain départage."""
    prs = [_pr(12, 120, comments=_humans(7))]
    f = sdd.analyze(prs, NOW, last_commit_dates={12: None})["findings"][0]
    assert f["last_commit_unknown"] is True


def test_fetch_last_commit_dates_parses_and_fails_open():
    """Date extraite de commits[-1] ; échec gh -> None (fail-open)."""
    def runner(cmd, **kwargs):
        if "view" in cmd and cmd[3] == "13":
            return FakeProc(returncode=1, stderr="boom")
        return FakeProc(stdout=json.dumps(
            {"commits": [{"committedDate": _ts(90)}]}))

    dates = sdd.fetch_last_commit_dates([13, 14], "r/x", runner=runner)
    assert dates[13] is None
    assert dates[14] == _ts(90)


# ---------------------------------------------------------------------------
# Format et sortie
# ---------------------------------------------------------------------------

def test_format_finding_line_shape():
    f = sdd.analyze([_pr(14821, 120, comments=_humans(7))], NOW)["findings"][0]
    line = sdd.format_finding(f)
    assert line.startswith("[DEADLOCK] #14821 — ")
    assert "mergeable" in line and "7 commentaires humains" in line


def _patch_runner(monkeypatch, runner):
    """main() résout le runner par défaut via le global du module au moment
    de l'appel : le patch du global suffit (pattern guard_comment_upsert)."""
    monkeypatch.setattr(sdd, "_default_runner", runner)


def test_main_json_and_fail_on_findings_rc2(monkeypatch, capsys):
    """--json rend findings + compteurs ; --fail-on-findings -> rc=2 sur
    détection, rc=0 sans le drapeau. Le fake runner dispatche les deux
    phases : pr list, puis pr view par candidate (dernier commit hors
    fenêtre — la candidate reste un finding).

    Note #18840 : ``main()`` résout ``now = datetime.now(timezone.utc)``,
    alors que les helpers ``_pr``/``_ts`` sont figés sur le ``NOW`` du
    module (2026-10-01 12:00 UTC) — quand le module est importé plus tard
    qu'à l'origine (cache pytest, changement de fuseau, ré-exécution),
    les commentaires « 1 h avant NOW » tombent hors de la fenêtre de 24 h
    mesurée depuis l'horloge réelle, et l'analyse rend 0 finding. Le
    fake_runner doit donc ancrer ses timestamps sur l'horloge qu'utilise
    ``main()``, pas sur le NOW gelé.
    """
    from datetime import datetime, timedelta, timezone as _tz
    live_now = datetime.now(_tz.utc)

    def _live_ts(hours_ago):
        return (live_now - timedelta(hours=hours_ago)).strftime(
            "%Y-%m-%dT%H:%M:%SZ")

    def _live_pr(number, age_hours, comments=()):
        return {
            "number": number,
            "title": f"PR synthétique #{number}",
            "createdAt": _live_ts(age_hours),
            "mergeable": "MERGEABLE",
            "comments": [
                {
                    "author": {"login": c[0]},
                    "createdAt": _live_ts(c[1]),
                    "body": c[2],
                }
                for c in comments
            ],
        }

    def fake_runner(cmd, **kwargs):
        if "list" in cmd:
            return FakeProc(stdout=json.dumps(
                [_live_pr(14821, 120, comments=_humans(7))]))
        return FakeProc(stdout=json.dumps(
            {"commits": [{"committedDate": _live_ts(100)}]}))

    _patch_runner(monkeypatch, fake_runner)
    assert sdd.main(["--fail-on-findings", "--limit", "10"]) == 2
    assert sdd.main(["--limit", "10"]) == 0
    capsys.readouterr()  # vide le buffer : la sortie --json doit être seule
    rc = sdd.main(["--json", "--limit", "10"])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["scanned"] == 1
    assert payload["findings"][0]["number"] == 14821
    assert payload["skipped_active_in_window"] == 0


def test_main_operational_failure_rc1(monkeypatch, capsys):
    """Panne gh -> rc=1 avec [PANNE] sur stderr, jamais un verdict vide."""
    def fake_runner(cmd, **kwargs):
        return FakeProc(returncode=1, stderr="gh: connect refused")

    _patch_runner(monkeypatch, fake_runner)
    rc = sdd.main(["--limit", "10"])
    assert rc == 1
    assert "[PANNE]" in capsys.readouterr().err
