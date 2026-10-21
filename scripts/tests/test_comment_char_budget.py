#!/usr/bin/env python3
"""Tests comment_char_budget — compteur P5 de #15511, corpus synthétique.

Profil fondateur : #14821, 68 101 chars pour 31 commentaires sur une PR de
4 270+/43-. Chaque test isole UNE branche : seuil de taille, ventilation
humain/bot, seuil d'alerte, panne gh, codes retour.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import comment_char_budget as ccb  # noqa: E402


class FakeProc:
    def __init__(self, returncode=0, stdout="[]", stderr=""):
        self.returncode = returncode
        self.stdout = stdout
        self.stderr = stderr


def _comment(login, body):
    return {"author": {"login": login}, "body": body}


def _pr(number, additions=0, deletions=0, comments=()):
    return {
        "number": number,
        "title": f"PR synthetique #{number}",
        "createdAt": "2026-09-05T20:21:00Z",
        "additions": additions,
        "deletions": deletions,
        "comments": list(comments),
    }


def test_empty_plateau_no_alert():
    result = ccb.analyze([])
    assert result["measured_prs"] == 0
    assert result["aggregate_chars"] == 0
    assert result["alert"] is False


def test_small_pr_excluded_from_measure():
    prs = [_pr(1, additions=900, deletions=99,
               comments=[_comment("lane", "x" * 5000)])]
    result = ccb.analyze(prs)
    assert result["measured_prs"] == 0
    assert result["skipped_small"] == 1
    assert result["aggregate_chars"] == 0


def test_qualifying_pr_counted_boundary_inclusive_excluded():
    # 1000 lignes PILE ne qualifie pas : le critere est strictement >
    prs = [_pr(1, additions=600, deletions=400,
               comments=[_comment("lane", "y" * 100)])]
    assert ccb.analyze(prs)["measured_prs"] == 0


def test_diff_size_is_additions_plus_deletions():
    prs = [_pr(1, additions=700, deletions=500,
               comments=[_comment("lane", "z" * 10)])]
    result = ccb.analyze(prs)
    assert result["measured_prs"] == 1
    assert result["aggregate_chars"] == 10


def test_human_bot_ventilation():
    prs = [_pr(14821, additions=4270, deletions=43, comments=[
        _comment("myia-po-2027", "h" * 60000),
        _comment("myia-ai-01", "h" * 8101),
        _comment("github-actions", "b" * 400),
        _comment("dependabot[bot]", "b" * 100),
    ])]
    result = ccb.analyze(prs)
    assert result["aggregate_chars"] == 68601
    assert result["human_chars"] == 68101
    assert result["bot_chars"] == 500
    assert result["prs"][0]["chars_human"] == 68101


def test_alert_over_threshold():
    prs = [_pr(1, additions=2000,
               comments=[_comment("lane", "a" * 31000)])]
    result = ccb.analyze(prs)
    assert result["alert"] is True


def test_no_alert_under_threshold():
    prs = [_pr(1, additions=2000,
               comments=[_comment("lane", "a" * 29999)])]
    result = ccb.analyze(prs)
    assert result["alert"] is False
    assert result["alert_threshold"] == 30000


def test_aggregate_spans_prs_and_sorts_desc():
    prs = [
        _pr(1, additions=1500, comments=[_comment("lane", "a" * 100)]),
        _pr(2, additions=2500, comments=[_comment("lane", "b" * 300)]),
    ]
    result = ccb.analyze(prs)
    assert result["aggregate_chars"] == 400
    assert [e["number"] for e in result["prs"]] == [2, 1]


def test_missing_fields_tolerated():
    # PR sans additions/deletions (forme degradee) : petite, hors mesure
    result = ccb.analyze([{"number": 9, "comments": [
        _comment("lane", "x" * 10)]}])
    assert result["skipped_small"] == 1
    # commentaire sans body : 0 char, pas d'erreur
    prs = [_pr(2, additions=2000, comments=[
        {"author": {"login": "lane"}},
        _comment("lane", None),
    ])]
    assert ccb.analyze(prs)["aggregate_chars"] == 0


def test_fetch_open_prs_gh_failure_raises():
    def runner(cmd, **kwargs):
        return FakeProc(returncode=1, stderr="boom")
    try:
        ccb.fetch_open_prs("x/y", runner=runner)
        raise AssertionError("RuntimeError attendue")
    except RuntimeError as exc:
        assert "boom" in str(exc)


def test_fetch_open_prs_unexpected_shape_raises():
    def runner(cmd, **kwargs):
        return FakeProc(stdout='{"not": "a list"}')
    try:
        ccb.fetch_open_prs("x/y", runner=runner)
        raise AssertionError("RuntimeError attendue")
    except RuntimeError:
        pass


def test_main_json_output_and_rc0():
    payload = json.dumps([_pr(1, additions=2000, comments=[
        _comment("lane", "a" * 10)])])
    def runner(cmd, **kwargs):
        return FakeProc(stdout=payload)
    # monkeypatch du runner par defaut via injection directe de main
    orig = ccb._default_runner
    ccb._default_runner = runner
    try:
        import io, contextlib
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            rc = ccb.main(["--json"])
        out = json.loads(buf.getvalue())
        assert rc == 0
        assert out["aggregate_chars"] == 10
        assert out["alert"] is False
    finally:
        ccb._default_runner = orig


def test_main_fail_on_findings_rc2(capsys):
    payload = json.dumps([_pr(14821, additions=4270, deletions=43, comments=[
        _comment("lane", "h" * 68000)])])
    def runner(cmd, **kwargs):
        return FakeProc(stdout=payload)
    orig = ccb._default_runner
    ccb._default_runner = runner
    try:
        rc = ccb.main(["--fail-on-findings"])
    finally:
        ccb._default_runner = orig
    assert rc == 2
    out = capsys.readouterr().out
    assert "[ALERT] commentaires-pompage" in out
    assert "68000 chars" in out


def test_main_gh_failure_rc1(capsys):
    def runner(cmd, **kwargs):
        return FakeProc(returncode=1, stderr="gh down")
    orig = ccb._default_runner
    ccb._default_runner = runner
    try:
        rc = ccb.main([])
    finally:
        ccb._default_runner = orig
    assert rc == 1
    assert "gh down" in capsys.readouterr().err
