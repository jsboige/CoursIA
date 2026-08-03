#!/usr/bin/env python3
"""Tests pour check_editorial_review.py — validateur du registre de revue
éditoriale (EPIC #8052 / editorial-review-registry). Couvre les fonctions
pures hermétiques (parse_registry, _is_real_entry, load_catalogue, check_entry,
check_promotions) ; gh_pr_state (réseau best-effort) est mocké."""

import json
import sys
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent
AUDIT_DIR = HERE.parent
sys.path.insert(0, str(AUDIT_DIR))

import check_editorial_review as cer  # noqa: E402

# Chemin vers le vrai registre (smoke test). Résolution robuste de la racine
# du dépôt : remonte jusqu'à trouver un marqueur (COURSE_CATALOG.generated.json
# ou docs/) plutôt qu'un index parents[N] cassé par l'arborescence du worktree.
def _find_registry():
    d = AUDIT_DIR
    for _ in range(6):
        cand = d / "docs" / "notebook-metadata" / "editorial-review-registry.md"
        if cand.exists():
            return cand
        d = d.parent
    return None

REGISTRY = _find_registry()


def _write(tmp_path, name, content):
    p = tmp_path / name
    p.write_text(content, encoding="utf-8")
    return p


# --------------------------------------------------------------------------
# _is_real_entry — filtre placeholder <#NNNN> vs #NNNN
# --------------------------------------------------------------------------

def test_is_real_entry_accepts_hash_digits():
    assert cer._is_real_entry({"evidence_pr": "#7904"}) is True


def test_is_real_entry_rejects_placeholder_angle_brackets():
    assert cer._is_real_entry({"evidence_pr": "<#NNNN>"}) is False


def test_is_real_entry_rejects_empty():
    assert cer._is_real_entry({"evidence_pr": ""}) is False
    assert cer._is_real_entry({}) is False


def test_is_real_entry_rejects_non_digits():
    assert cer._is_real_entry({"evidence_pr": "#abc"}) is False
    assert cer._is_real_entry({"evidence_pr": "todo"}) is False


# --------------------------------------------------------------------------
# parse_registry — parser YAML-block (fenced ```yaml), multi-line, comments
# --------------------------------------------------------------------------

def _registry_md(*blocks):
    """Construit un registre markdown avec N blocs yaml."""
    parts = ["# Registry\n", "Intro prose.\n"]
    for b in blocks:
        parts.append("```yaml\n")
        parts.append(b)
        parts.append("```\n\n")
    return "".join(parts)


def test_parse_registry_single_entry_multiline(tmp_path):
    body = (
        "- notebook_path: Foo/Bar.ipynb\n"
        "  reviewer: alice\n"
        "  review_date: 2026-07-22\n"
        "  review_scope: full\n"
        "  evidence_pr: \"#7904\"\n"
    )
    p = _write(tmp_path, "reg.md", _registry_md(body))
    entries = cer.parse_registry(p)
    assert len(entries) == 1
    e = entries[0]
    assert e["notebook_path"] == "Foo/Bar.ipynb"
    assert e["reviewer"] == "alice"
    assert e["review_scope"] == "full"
    assert e["evidence_pr"] == "#7904"  # quotes stripped


def test_parse_registry_multiple_entries(tmp_path):
    body = (
        "- notebook_path: A.ipynb\n"
        "  evidence_pr: \"#1\"\n"
        "  reviewer: x\n"
        "- notebook_path: B.ipynb\n"
        "  evidence_pr: \"#2\"\n"
        "  reviewer: y\n"
    )
    p = _write(tmp_path, "reg.md", _registry_md(body))
    entries = cer.parse_registry(p)
    assert [e["notebook_path"] for e in entries] == ["A.ipynb", "B.ipynb"]


def test_parse_registry_skips_template_placeholder_entries(tmp_path):
    body = (
        "- notebook_path: Template.ipynb\n"
        "  evidence_pr: \"<#NNNN>\"\n"
        "  reviewer: someone\n"
        "- notebook_path: Real.ipynb\n"
        "  evidence_pr: \"#1234\"\n"
        "  reviewer: real\n"
    )
    p = _write(tmp_path, "reg.md", _registry_md(body))
    entries = cer.parse_registry(p)
    assert len(entries) == 1
    assert entries[0]["notebook_path"] == "Real.ipynb"


def test_parse_registry_skips_comment_only_blocks(tmp_path):
    body = "# just a comment, no entry\n# another comment\n"
    p = _write(tmp_path, "reg.md", _registry_md(body))
    assert cer.parse_registry(p) == []


def test_parse_registry_skips_inline_comment_lines(tmp_path):
    body = (
        "- notebook_path: A.ipynb\n"
        "  evidence_pr: \"#5\"\n"
        "  reviewer: x\n"
        "  # inline comment line ignored\n"
    )
    p = _write(tmp_path, "reg.md", _registry_md(body))
    entries = cer.parse_registry(p)
    assert len(entries) == 1
    assert "inline comment" not in str(entries[0])


def test_parse_registry_no_yaml_blocks(tmp_path):
    p = _write(tmp_path, "reg.md", "# Just prose, no code fences\n")
    assert cer.parse_registry(p) == []


def test_parse_registry_strips_single_and_double_quotes(tmp_path):
    body = (
        "- notebook_path: X.ipynb\n"
        "  reviewer: \"bob\"\n"
        "  evidence_pr: '#9'\n"
    )
    p = _write(tmp_path, "reg.md", _registry_md(body))
    e = cer.parse_registry(p)[0]
    assert e["reviewer"] == "bob"
    assert e["evidence_pr"] == "#9"


def test_parse_registry_smoke_real_file():
    """Smoke contre le vrai registre sur origin/main : parsing sans erreur,
    >= 1 entrée réelle, toutes les entrées ont un notebook_path + evidence_pr."""
    if not REGISTRY.exists():
        import pytest
        pytest.skip("real registry not present in this checkout")
    entries = cer.parse_registry(REGISTRY)
    assert len(entries) >= 1
    for e in entries:
        assert e.get("notebook_path")
        assert e.get("evidence_pr", "").lstrip("#").isdigit()


# --------------------------------------------------------------------------
# load_catalogue — results-wrapped vs bare array
# --------------------------------------------------------------------------

def test_load_catalogue_bare_array(tmp_path):
    data = [{"path": "A.ipynb"}, {"path": "B.ipynb"}]
    p = _write(tmp_path, "cat.json", json.dumps(data))
    assert cer.load_catalogue(p) == data


def test_load_catalogue_results_wrapped(tmp_path):
    data = {"results": [{"path": "A.ipynb"}], "meta": "x"}
    p = _write(tmp_path, "cat.json", json.dumps(data))
    assert cer.load_catalogue(p) == [{"path": "A.ipynb"}]


# --------------------------------------------------------------------------
# check_entry — validation : scope, reviewer, pr format, auto-review, alias
# --------------------------------------------------------------------------

def _cat(nb_path, owner=None, editorial=None):
    nb = {"path": nb_path}
    if owner:
        nb["owner_logique"] = owner
    if editorial:
        nb["editorial"] = editorial
    return nb


def test_check_entry_valid_clean(monkeypatch):
    """Entry valide, reviewer != owner, PR merged -> 0 issues."""
    monkeypatch.setattr(cer, "gh_pr_state", lambda *a, **k: "MERGED")
    cat = [_cat("A.ipynb", owner="bob")]
    entry = {"notebook_path": "A.ipynb", "review_scope": "full",
             "reviewer": "alice", "evidence_pr": "#1"}
    assert cer.check_entry(entry, cat) == []


def test_check_entry_notebook_not_found():
    cat = [_cat("A.ipynb")]
    entry = {"notebook_path": "MISSING.ipynb", "evidence_pr": "#1"}
    issues = cer.check_entry(entry, cat)
    assert any(i.startswith("NOTEBOOK_NOT_FOUND") for i in issues)


def test_check_entry_missing_notebook_path():
    issues = cer.check_entry({"evidence_pr": "#1"}, [_cat("A.ipynb")])
    assert issues == ["MISSING_NOTEBOOK_PATH"]


def test_check_entry_invalid_scope(monkeypatch):
    monkeypatch.setattr(cer, "gh_pr_state", lambda *a, **k: "MERGED")
    cat = [_cat("A.ipynb")]
    entry = {"notebook_path": "A.ipynb", "review_scope": "bogus",
             "reviewer": "alice", "evidence_pr": "#1"}
    issues = cer.check_entry(entry, cat)
    assert any(i.startswith("INVALID_SCOPE") for i in issues)


def test_check_entry_missing_reviewer(monkeypatch):
    monkeypatch.setattr(cer, "gh_pr_state", lambda *a, **k: "MERGED")
    cat = [_cat("A.ipynb")]
    entry = {"notebook_path": "A.ipynb", "review_scope": "typo",
             "evidence_pr": "#1"}
    issues = cer.check_entry(entry, cat)
    assert "MISSING_REVIEWER" in issues


def test_check_entry_pr_not_merged(monkeypatch):
    monkeypatch.setattr(cer, "gh_pr_state", lambda *a, **k: "OPEN")
    cat = [_cat("A.ipynb")]
    entry = {"notebook_path": "A.ipynb", "review_scope": "typo",
             "reviewer": "alice", "evidence_pr": "#99"}
    issues = cer.check_entry(entry, cat)
    assert any(i.startswith("PR_NOT_MERGED") and "state=OPEN" in i for i in issues)


def test_check_entry_pr_state_unknown_warns(monkeypatch):
    """gh indisponible -> WARN (non bloquant), pas error."""
    monkeypatch.setattr(cer, "gh_pr_state", lambda *a, **k: None)
    cat = [_cat("A.ipynb")]
    entry = {"notebook_path": "A.ipynb", "review_scope": "typo",
             "reviewer": "alice", "evidence_pr": "#99"}
    issues = cer.check_entry(entry, cat)
    assert any(i.startswith("WARN_PR_STATE_UNKNOWN") for i in issues)


def test_check_entry_invalid_pr_format(monkeypatch):
    monkeypatch.setattr(cer, "gh_pr_state", lambda *a, **k: "MERGED")
    cat = [_cat("A.ipynb")]
    entry = {"notebook_path": "A.ipynb", "review_scope": "typo",
             "reviewer": "alice", "evidence_pr": "not-a-number"}
    issues = cer.check_entry(entry, cat)
    assert any(i.startswith("INVALID_PR_FORMAT") for i in issues)


def test_check_entry_auto_review_reviewer_equals_owner(monkeypatch):
    monkeypatch.setattr(cer, "gh_pr_state", lambda *a, **k: "MERGED")
    cat = [_cat("A.ipynb", owner="alice")]
    entry = {"notebook_path": "A.ipynb", "review_scope": "typo",
             "reviewer": "alice", "evidence_pr": "#1"}
    issues = cer.check_entry(entry, cat)
    assert any(i.startswith("AUTO_REVIEW") for i in issues)


def test_check_entry_warn_reviewer_alias_substring(monkeypatch):
    """Substring heuristic (best-effort) : reviewer substring de owner -> WARN."""
    monkeypatch.setattr(cer, "gh_pr_state", lambda *a, **k: "MERGED")
    cat = [_cat("A.ipynb", owner="jsboigeEpita")]
    entry = {"notebook_path": "A.ipynb", "review_scope": "typo",
             "reviewer": "jsboige", "evidence_pr": "#1"}
    issues = cer.check_entry(entry, cat)
    assert any(i.startswith("WARN_REVIEWER_ALIAS") for i in issues)


# --------------------------------------------------------------------------
# check_promotions — cross-check catalogue (editorial field, PROMOTING_SCOPES)
# --------------------------------------------------------------------------

def test_check_promotions_no_editorial_field_info():
    entries = [{"notebook_path": "A.ipynb", "review_scope": "full",
                "reviewer": "x"}]
    cat = [{"path": "A.ipynb"}]  # pas de champ editorial
    notes = cer.check_promotions(entries, cat)
    assert any("no 'editorial' field" in n for n in notes)


def test_check_promotions_wrong_editorial_note():
    entries = [{"notebook_path": "A.ipynb", "review_scope": "substance",
                "reviewer": "x"}]
    cat = [{"path": "A.ipynb", "editorial": "DRAFT"}]
    notes = cer.check_promotions(entries, cat)
    assert any("expected editorial in (FINAL, BETA)" in n for n in notes)


def test_check_promotions_beta_or_final_clean():
    entries = [{"notebook_path": "A.ipynb", "review_scope": "full",
                "reviewer": "x"}]
    for ok in ("BETA", "FINAL"):
        cat = [{"path": "A.ipynb", "editorial": ok}]
        assert cer.check_promotions(entries, cat) == []


def test_check_promotions_non_promoting_scope_skipped():
    """review_scope typo/pedagogie n'est pas dans PROMOTING_SCOPES -> ignoré."""
    entries = [{"notebook_path": "A.ipynb", "review_scope": "typo",
                "reviewer": "x"}]
    cat = [{"path": "A.ipynb", "editorial": "DRAFT"}]
    assert cer.check_promotions(entries, cat) == []


# --------------------------------------------------------------------------
# main() — end-to-end exit codes (gh mocked, catalogue/registry synthetic)
# --------------------------------------------------------------------------

def test_main_clean_returns_0(monkeypatch, tmp_path):
    monkeypatch.setattr(cer, "gh_pr_state", lambda *a, **k: "MERGED")
    reg = _write(tmp_path, "reg.md", _registry_md(
        "- notebook_path: A.ipynb\n  review_scope: full\n  reviewer: alice\n"
        "  evidence_pr: \"#1\"\n"))
    cat = _write(tmp_path, "cat.json", json.dumps([{"path": "A.ipynb"}]))
    monkeypatch.setattr(sys, "argv",
                        ["check_editorial_review.py", "--registry", str(reg),
                         "--catalogue", str(cat), "--check"])
    rc = cer.main()
    assert rc == 0


def test_main_error_returns_1(monkeypatch, tmp_path):
    monkeypatch.setattr(cer, "gh_pr_state", lambda *a, **k: "MERGED")
    reg = _write(tmp_path, "reg.md", _registry_md(
        "- notebook_path: MISSING.ipynb\n  review_scope: full\n  reviewer: alice\n"
        "  evidence_pr: \"#1\"\n"))
    cat = _write(tmp_path, "cat.json", json.dumps([{"path": "A.ipynb"}]))
    monkeypatch.setattr(sys, "argv",
                        ["check_editorial_review.py", "--registry", str(reg),
                         "--catalogue", str(cat), "--check"])
    rc = cer.main()
    assert rc == 1  # NOTEBOOK_NOT_FOUND = error -> exit 1


def test_main_warn_does_not_block(monkeypatch, tmp_path):
    """WARN_PR_STATE_UNKNOWN (gh indisponible) ne bloque pas --check."""
    monkeypatch.setattr(cer, "gh_pr_state", lambda *a, **k: None)
    reg = _write(tmp_path, "reg.md", _registry_md(
        "- notebook_path: A.ipynb\n  review_scope: full\n  reviewer: alice\n"
        "  evidence_pr: \"#1\"\n"))
    cat = _write(tmp_path, "cat.json", json.dumps([{"path": "A.ipynb"}]))
    monkeypatch.setattr(sys, "argv",
                        ["check_editorial_review.py", "--registry", str(reg),
                         "--catalogue", str(cat), "--check"])
    rc = cer.main()
    assert rc == 0  # WARN only, pas d'error


def test_main_missing_files_returns_1(monkeypatch, tmp_path):
    monkeypatch.setattr(sys, "argv",
                        ["check_editorial_review.py", "--registry",
                         str(tmp_path / "nope.md"), "--catalogue",
                         str(tmp_path / "nope.json")])
    rc = cer.main()
    assert rc == 1
