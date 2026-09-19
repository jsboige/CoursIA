#!/usr/bin/env python3
"""Unit tests for the pure core of audit_consolidation_orphans.py (#16473).

The attachment/axis/rendering functions are network-free; only --fetch talks
to gh and is exercised end-to-end at delivery time, not here. Fixtures encode
the semantics fixed by the Epic body: a bare #N mention counts as attachment
(triage, not verdict), word-bounded numbers (#1647 != #16473), and an orphan
with no axis match stays UNCLASSIFIED rather than being force-classified.
"""

import json
import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from audit_consolidation_orphans import (  # noqa: E402
    CHAPERONES,
    attachment_proofs,
    audit,
    classify_axes,
    load_input,
    main,
    mention_lines,
    render_markdown,
)


CHAP_body = "#5081 est le chaperon canon."
CHAPERONES_STATE = {
    5081: {"body": "Programme canonique. Sous-grains : #1001.", "comments": []},
    4362: {"body": "Lakes.", "comments": [{"body": "rattache aussi #1002"}]},
    13737: {"body": "Structure.", "comments": []},
    9535: {"body": "Nettoyage.", "comments": []},
    16473: {"body": "Parapluie.", "comments": []},
}


def _issue(number, title="Une issue", body=""):
    return {"number": number, "title": title, "body": body}


def test_mention_lines_word_boundary():
    text = "cites #16473 ici\nmais pas #1647 la\n#16473 encore"
    assert mention_lines(text, 16473) == ["cites #16473 ici", "#16473 encore"]
    assert mention_lines(text, 1647) == ["mais pas #1647 la"]


def test_attachment_via_issue_body_see():
    issue = _issue(2001, body="Tranche renumerotation. See #5081")
    proofs = attachment_proofs(issue, CHAPERONES_STATE)
    assert any(p["type"] == "body" and p["chaperone"] == 5081 for p in proofs)


def test_attachment_via_chaperone_body():
    issue = _issue(1001, body="rien")
    proofs = attachment_proofs(issue, CHAPERONES_STATE)
    assert any(p["type"] == "chaperone_body" and p["chaperone"] == 5081 for p in proofs)


def test_attachment_via_chaperone_comment():
    issue = _issue(1002, body="rien")
    proofs = attachment_proofs(issue, CHAPERONES_STATE)
    assert any(p["type"] == "chaperone_comment" and p["chaperone"] == 4362 for p in proofs)


def test_attachment_via_issue_comment_deep_only():
    issue = _issue(3001, body="rien")
    assert attachment_proofs(issue, CHAPERONES_STATE) == []
    proofs = attachment_proofs(issue, CHAPERONES_STATE,
                               issue_comments=[{"body": "Part of #9535"}])
    assert any(p["type"] == "issue_comment" and p["chaperone"] == 9535 for p in proofs)


def test_bare_mention_counts_as_attachment():
    # Triage posture: even a negative-prose mention surfaces, human arbitrates.
    issue = _issue(4001, body="ne pas dupliquer la doctrine de #5081")
    assert attachment_proofs(issue, CHAPERONES_STATE) != []


def test_classify_axes_matches():
    assert classify_axes("Renum Search Part3", "") == ["A"]
    assert "C" in classify_axes("Mutualiser les lakes Mathlib", "junctions NTFS")
    assert "E" in classify_axes("Doc sprawl", "consolider 150+ markdown files")
    assert classify_axes("Backtest strategie X", "Sharpe, CAGR") == []


def test_audit_tri_and_chaperone_exclusion(tmp_path):
    issues = [
        _issue(5081, title="chaperon lui-meme", body=CHAP_body),
        _issue(5001, title="Renum Infer", body="voir serie"),
        _issue(5002, title="Backtest QC", body="Sharpe"),
    ]
    report = audit(issues, CHAPERONES_STATE)
    assert report["scanned"] == 2  # 5081 excluded as a chaperone
    assert report["orphans"] == 2
    assert report["attached"] == 0
    axes_5001 = next(o for o in report["orphans_by_axis"]["A"] if o["number"] == 5001)
    assert axes_5001["absence"] == ["body: 0 citation des chaperons (#%s)" % " #".join(map(str, CHAPERONES))]
    assert any(o["number"] == 5002 for o in report["orphans_by_axis"]["UNCLASSIFIED"])


def test_audit_deep_records_comment_absence():
    issues = [_issue(6001, title="Doublons twins", body="")]
    report = audit(issues, CHAPERONES_STATE, issues_comments={6001: [{"body": "rien"}]})
    orphan = next(o for o in report["orphans_by_axis"]["B"] if o["number"] == 6001)
    assert any("comments: 0 citation" in a for a in orphan["absence"])


def test_render_markdown_contains_axes_and_absence_proof():
    issues = [_issue(7001, title="Renum quoi", body="")]
    report = audit(issues, CHAPERONES_STATE)
    md = render_markdown(report)
    assert "## Axe A" in md
    assert "Preuve d'absence" in md
    assert "0 citation des chaperons" in md
    assert "pas un verdict" in md


def test_main_offline_json_and_exit_codes(tmp_path, capsys):
    state = {
        "issues": [_issue(8001, title="Renum test", body="See #5081")],
        "chaperones": {"5081": {"body": "", "comments": []}},
    }
    input_path = tmp_path / "state.json"
    input_path.write_text(json.dumps(state), encoding="utf-8")
    out_path = tmp_path / "report.json"

    rc = main(["--input", str(input_path), "--format", "json", "--out", str(out_path)])
    assert rc == 0
    data = json.loads(out_path.read_text(encoding="utf-8"))
    assert data["attached"] == 1 and data["orphans"] == 0

    state["issues"][0]["body"] = "aucun lien"
    input_path.write_text(json.dumps(state), encoding="utf-8")
    rc_ok = main(["--input", str(input_path), "--format", "json", "--out", str(out_path)])
    rc_fail = main(["--input", str(input_path), "--format", "md",
                    "--fail-on-orphans", "--out", str(tmp_path / "r.md")])
    assert rc_ok == 0  # advisory posture by default
    assert rc_fail == 1  # opt-in ratchet wire


def test_load_input_roundtrip(tmp_path):
    state = {
        "issues": [_issue(9001, title="t", body="")],
        "chaperones": {"5081": {"body": "b", "comments": [{"body": "c"}]}},
        "issues_comments": {"9001": [{"body": "voir #4362"}]},
    }
    path = tmp_path / "s.json"
    path.write_text(json.dumps(state), encoding="utf-8")
    issues, chaperones, comments = load_input(str(path))
    assert issues[0]["number"] == 9001
    assert 5081 in chaperones
    assert comments is not None and 9001 in comments
