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


def test_suggest_chaperon_single_axis():
    from audit_consolidation_orphans import suggest_chaperon
    # A -> #5081 (notebook canon)
    assert suggest_chaperon(["A"]) == [5081]
    # B -> #13737 (structurel)
    assert suggest_chaperon(["B"]) == [13737]
    # C -> #4362 (Lean lakes)
    assert suggest_chaperon(["C"]) == [4362]
    # D -> #9535 (menage)
    assert suggest_chaperon(["D"]) == [9535]
    # E -> #13737 (structurel) par defaut
    assert suggest_chaperon(["E"]) == [13737]
    # F -> #16473 (parapluie)
    assert suggest_chaperon(["F"]) == [16473]


def test_suggest_chaperon_unclassified():
    from audit_consolidation_orphans import suggest_chaperon
    assert suggest_chaperon([]) == []


def test_suggest_chaperon_multi_axis_dedup():
    from audit_consolidation_orphans import suggest_chaperon
    # A+B: A->5081, B->13737, deux chaperons distincts, ordre A-F preserve
    assert suggest_chaperon(["A", "B"]) == [5081, 13737]
    # B+E: B->13737, E->13737 (meme chaperon), dedup
    assert suggest_chaperon(["B", "E"]) == [13737]
    # A+F: A->5081, F->16473, ordre A-F preserve
    assert suggest_chaperon(["A", "F"]) == [5081, 16473]


def test_audit_suggest_rattachement_adds_field():
    from audit_consolidation_orphans import audit
    issues = [
        _issue(5001, title="Doublon detecte par ratchet", body="jumeaux collidant"),
        _issue(5002, title="Backtest strategie X", body="Sharpe, CAGR"),  # unclassified
        _issue(5003, title="Renommer les kernels", body="accretion du suffixe"),  # A
    ]
    report_no = audit(issues, {}, None, suggest=False)
    orphans_no = report_no["orphans_by_axis"]
    for axis_list in orphans_no.values():
        for orphan in axis_list:
            assert "suggested_chaperon" not in orphan
    report_yes = audit(issues, {}, None, suggest=True)
    orphans_yes = report_yes["orphans_by_axis"]
    # Find issue 5001 (axis B -> #13737) and 5003 (axis A -> #5081)
    found_5001 = False
    found_5003 = False
    for axis_list in orphans_yes.values():
        for orphan in axis_list:
            if orphan["number"] == 5001:
                assert orphan["suggested_chaperon"] == [13737]
                found_5001 = True
            if orphan["number"] == 5003:
                assert orphan["suggested_chaperon"] == [5081]
                found_5003 = True
            if orphan["number"] == 5002:
                assert orphan["suggested_chaperon"] == []  # UNCLASSIFIED
    assert found_5001 and found_5003


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


# --- attached_specific (organ v2, issue #21267) ---------------------------
# Classe mesurée sur le lot 4 (c.1651, 2026-10-17) : 7/14 « orphelines »
# citaient un parent EPIC vivant non-chaperon dans leur body (« Part of #N »),
# invisible à la recherche de preuves chaperon.


def test_parent_links_extraction():
    from audit_consolidation_orphans import parent_links
    body = "Tranche du lot.\nPart of #4362 et See #9999.\nRattachée à #13737."
    assert parent_links(body) == {
        4362: "Part of #4362 et See #9999.",
        9999: "Part of #4362 et See #9999.",
        13737: "Rattachée à #13737.",
    }
    assert parent_links("") == {}
    # Frontiere de mot : "Dsee" n'est pas "See"
    assert parent_links("Dsee #5 ne matche pas") == {}


def test_audit_attached_specific_live_parent():
    # Parent EPIC vivant non-chaperon cite dans le body -> attached_specific,
    # pas orpheline ; le parent lui-meme reste une issue a part entiere.
    issues = [
        _issue(7100, title="EPIC vivante", body="parapluie de serie"),
        _issue(7101, title="sous-grain", body="Part of #7100"),
    ]
    report = audit(issues, CHAPERONES_STATE)
    assert report["attached"] == 0
    assert report["attached_specific"] == 1
    entry = report["attached_specific_details"][0]
    assert entry["number"] == 7101
    assert entry["parents"] == [7100]
    assert report["orphans"] == 1  # 7100, sans preuve elle-meme


def test_audit_chaperone_proof_beats_parent_marker():
    # Priorite chaperon > parent specifique : pas de double comptage.
    issues = [
        _issue(7200, title="EPIC vivante", body="parapluie"),
        _issue(7201, title="sous-grain", body="See #5081 aussi\nPart of #7200"),
    ]
    report = audit(issues, CHAPERONES_STATE)
    assert report["attached"] == 1
    assert report["attached_specific"] == 0
    assert any(d["number"] == 7201 for d in report["attached_details"])


def test_audit_stale_parent_stays_orphan():
    # Parent absent du fetch (ferme ou inexistant) : le marqueur ne rattache rien.
    issues = [_issue(7301, title="sous-grain veuf", body="Part of #7399")]
    report = audit(issues, CHAPERONES_STATE)
    assert report["attached_specific"] == 0
    assert report["orphans"] == 1


def test_audit_two_parents_one_entry():
    issues = [
        _issue(7400, title="EPIC A", body="a"),
        _issue(7401, title="EPIC B", body="b"),
        _issue(7402, title="multi-parent", body="Part of #7400 et Rattaché à #7401"),
    ]
    report = audit(issues, CHAPERONES_STATE)
    entry = report["attached_specific_details"][0]
    assert entry["number"] == 7402
    assert entry["parents"] == [7400, 7401]
    assert len(entry["proofs"]) == 2


def test_audit_self_link_ignored_chaperone_parent_reclassified():
    # Auto-reference : pas de rattachement. Parent chaperon : capte par la
    # preuve chaperon (mention simple #9535), pas par attached_specific.
    issues = [
        _issue(7500, title="boucle", body="Part of #7500"),
        _issue(7501, title="vers chaperon", body="Rattachés à #9535"),
    ]
    report = audit(issues, CHAPERONES_STATE)
    assert report["attached_specific"] == 0
    assert report["attached"] == 1
    assert report["orphans"] == 1  # 7500


def test_render_markdown_shows_attached_specific_counter():
    issues = [
        _issue(7600, title="EPIC vivante", body="x"),
        _issue(7601, title="sous-grain", body="Part of #7600"),
    ]
    md = render_markdown(audit(issues, CHAPERONES_STATE))
    assert "rattachées (parent spécifique) : 1" in md
