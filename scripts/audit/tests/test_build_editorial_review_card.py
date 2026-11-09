#!/usr/bin/env python3
"""Tests pour build_editorial_review_card.py — generateur de carte de revue
editoriale (acceptance 2 de #11259). Couvre les fonctions pures (refused_reason,
touched_cells, render_card, render_yaml_entry) et les deux runners reseau
(pr_facts, merge_commit) via injection ; main() est teste de bout en bout avec
pr_facts/merge_commit monkeypatches (aucun acces gh ni git reel)."""

import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
AUDIT_DIR = HERE.parent
sys.path.insert(0, str(AUDIT_DIR))

import build_editorial_review_card as gen  # noqa: E402

NOTEBOOK = "MyIA.AI.Notebooks/Sudoku/Sudoku-12-Z3-CSharp.ipynb"


# --------------------------------------------------------------------------
# touched_cells
# --------------------------------------------------------------------------

def test_touched_cells_detects_present_notebook():
    files = [{"path": NOTEBOOK, "additions": 12, "deletions": 5}]
    assert gen.touched_cells(files, NOTEBOOK) == {
        "touched": True, "additions": 12, "deletions": 5
    }


def test_touched_cells_absent_notebook():
    files = [{"path": "MyIA.AI.Notebooks/Autre/x.ipynb", "additions": 3}]
    assert gen.touched_cells(files, NOTEBOOK)["touched"] is False


# --------------------------------------------------------------------------
# refused_reason — trois refus durs (§3.1)
# --------------------------------------------------------------------------

def _facts(state="MERGED", files=None):
    return {"state": state, "files": files if files is not None
            else [{"path": NOTEBOOK, "additions": 1, "deletions": 1}]}


def test_refused_when_pr_not_merged():
    reason = gen.refused_reason(_facts(state="OPEN"), NOTEBOOK, "rev", "po-2023")
    assert reason is not None and reason.startswith("PR_NOT_MERGED")


def test_refused_when_notebook_untouched():
    facts = _facts(files=[{"path": "Autre/x.ipynb", "additions": 1}])
    reason = gen.refused_reason(facts, NOTEBOOK, "rev", "po-2023")
    assert reason is not None and reason.startswith("PR_DOES_NOT_TOUCH_NOTEBOOK")


def test_refused_when_auto_review():
    reason = gen.refused_reason(_facts(), NOTEBOOK, "po-2023", "po-2023")
    assert reason is not None and reason.startswith("AUTO_REVIEW")


def test_no_refusal_when_valid():
    assert gen.refused_reason(_facts(), NOTEBOOK, "rev", "po-2023") is None


# --------------------------------------------------------------------------
# render_card
# --------------------------------------------------------------------------

def test_card_promotes_for_factual_scope():
    card = gen.render_card(NOTEBOOK, "Titre", "po-2023", "rev", "factual",
                           7801, "15b855b", 12, 5, "note")
    assert "- [x] **PROMOTE**" in card
    assert "- [x] **factual**" in card


def test_card_typo_scope_does_not_promote():
    card = gen.render_card(NOTEBOOK, "Titre", "po-2023", "rev", "typo",
                           7801, "15b855b", 12, 5, "note")
    assert "- [ ] **PROMOTE**" in card
    assert "- [x] **typo**" in card


def test_card_checks_exactly_one_scope_box():
    # Le compte porte sur les cases de portee uniquement : la ligne PROMOTE
    # porte elle aussi le motif "- [x] **", un count brut en compterait deux.
    card = gen.render_card(NOTEBOOK, "Titre", "po-2023", "rev", "substance",
                           7801, "15b855b", 1, 1, "")
    checked = [s for s in gen.REVIEW_SCOPES if f"- [x] **{s}**" in card]
    assert checked == ["substance"]


def test_card_carries_pr_and_merge_sha():
    card = gen.render_card(NOTEBOOK, "Titre", "po-2023", "rev", "factual",
                           7801, "15b855b", 12, 5, "note")
    assert "`#7801`" in card
    assert "`15b855b`" in card


def test_card_marks_missing_sha_instead_of_inventing_one():
    card = gen.render_card(NOTEBOOK, "Titre", "po-2023", "rev", "factual",
                           7801, None, 0, 0, "")
    assert "introuvable" in card


def test_card_rejects_invalid_scope():
    try:
        gen.render_card(NOTEBOOK, "T", "o", "r", "bidon", 1, None, 0, 0, "")
    except ValueError:
        return
    raise AssertionError("scope invalide accepte")


# --------------------------------------------------------------------------
# render_yaml_entry
# --------------------------------------------------------------------------

def test_yaml_entry_matches_registry_schema():
    entry = gen.render_yaml_entry(NOTEBOOK, "rev", "factual", 7801,
                                  "2026-07-22", "note")
    for key in ("notebook_path:", "reviewer:", "review_date:",
                "evidence_pr:", "review_scope:", "notes:"):
        assert key in entry
    assert 'evidence_pr: "#7801"' in entry


def test_yaml_entry_rejects_invalid_scope():
    try:
        gen.render_yaml_entry(NOTEBOOK, "rev", "bidon", 7801, "2026-07-22", "")
    except ValueError:
        return
    raise AssertionError("scope invalide accepte")


# --------------------------------------------------------------------------
# runners — injection, hors reseau
# --------------------------------------------------------------------------

def test_pr_facts_parses_gh_json():
    captured = {}

    def fake_gh(args, repo):
        captured["args"] = args
        captured["repo"] = repo
        return json.dumps({"number": 7801, "state": "MERGED"})

    facts = gen.pr_facts(7801, "jsboige/CoursIA", gh=fake_gh)
    assert facts["state"] == "MERGED"
    assert "--repo" not in captured["args"]  # le repo est passe separement
    assert captured["repo"] == "jsboige/CoursIA"


def test_merge_commit_shortens_sha():
    sha = gen.merge_commit(7801, git=lambda args: "15b855bbbbbbbbbbbb\n")
    assert sha == "15b855b"


def test_merge_commit_none_when_absent():
    assert gen.merge_commit(7801, git=lambda args: "") is None


# --------------------------------------------------------------------------
# main — de bout en bout, sans gh ni git
# --------------------------------------------------------------------------

def test_main_refuses_unmerged_pr(monkeypatch, capsys):
    monkeypatch.setattr(gen, "pr_facts",
                        lambda pr, repo: {"state": "OPEN", "files": []})
    rc = gen.main(["--notebook", NOTEBOOK, "--pr", "1", "--reviewer", "rev",
                   "--scope", "factual", "--owner", "po-2023", "--date", "2026-07-22"])
    assert rc == 1
    assert "REFUS" in capsys.readouterr().err


def test_main_writes_card_and_yaml(monkeypatch, tmp_path):
    monkeypatch.setattr(gen, "pr_facts", lambda pr, repo: {
        "state": "MERGED", "title": "Sudoku-12",
        "files": [{"path": NOTEBOOK, "additions": 12, "deletions": 5}],
    })
    monkeypatch.setattr(gen, "merge_commit", lambda pr: "15b855b")
    card = tmp_path / "card.md"
    yml = tmp_path / "entry.yaml"
    rc = gen.main(["--notebook", NOTEBOOK, "--pr", "7801", "--reviewer", "rev",
                   "--scope", "factual", "--owner", "po-2023",
                   "--date", "2026-07-22", "--card-out", str(card),
                   "--yaml-out", str(yml)])
    assert rc == 0
    assert "- [x] **PROMOTE**" in card.read_text(encoding="utf-8")
    assert 'evidence_pr: "#7801"' in yml.read_text(encoding="utf-8")
