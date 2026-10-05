"""Offline tests for the EOL/blob attribute guard (#19374).

The class of #19287 : a vendored file with CRLF or mixed line endings is
committed with `.gitattributes` declaring `text` or `eol=lf`. Git renormalizes
the worktree on every checkout but never rewrites the blob. We want to rouge
on the next PR that adds or modifies such a file.
"""
from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "ci" / "check_eol_blob_attribute.py"
spec = importlib.util.spec_from_file_location("check_eol_blob_attribute", SCRIPT)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_eol_blob_attribute"] = mod
spec.loader.exec_module(mod)


# --- parsing layer: the regex on real `git ls-files --eol` output ---


def test_parse_clean_lf_line():
    m = mod.EOL_LINE_RE.match("i/lf\tw/lf\tattr/lf\tMyIA.AI.Notebooks/foo.py")
    assert m is not None
    assert m.group("i_attr") == "lf"
    assert m.group("w_attr") == "lf"
    assert m.group("attr") == "lf"
    assert m.group("path") == "MyIA.AI.Notebooks/foo.py"


def test_parse_mixed_text_eol_lf_line():
    # The exact shape on main for the two #19287 files : mixed blob,
    # `text eol=lf` attribute pair.
    m = mod.EOL_LINE_RE.match(
        "i/mixed\tw/mixed\tattr/text eol=lf\t"
        "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/argumentation_lib/_fallacy_workflow_plugin.py"
    )
    assert m is not None
    assert m.group("i_attr") == "mixed"
    assert m.group("attr") == "text eol=lf"


def test_parse_crlf_empty_attr_line():
    # Real `git ls-files --eol` separates fields by spaces, then a TAB before
    # the path. Empty attribute shows as `attr/ ` with a trailing space; the
    # raw regex captures it as ` `, and the production code `.strip()`s it
    # before testing membership (so the decision layer sees an empty string).
    m = mod.EOL_LINE_RE.match("i/crlf w/crlf attr/ \t.claude/skills/foo/SKILL.md")
    assert m is not None
    assert m.group("i_attr") == "crlf"
    assert m.group("attr").strip() == ""


def test_parse_crlf_minus_text_line():
    m = mod.EOL_LINE_RE.match("i/crlf\tw/crlf\tattr/-text\tMyIA.AI.Notebooks/data/x.csv")
    assert m is not None
    assert m.group("attr") == "-text"


# --- decision matrix (pure function, no subprocess) ---


def _classify(i_attr: str, attr: str) -> bool:
    """Inline replication of the matrix: would this line be flagged?"""
    return i_attr in mod.BAD_INDEX and attr in mod.LF_ATTRS


def test_decision_mixed_with_text_attr_flagged():
    assert _classify("mixed", "text") is True


def test_decision_mixed_with_eol_lf_attr_flagged():
    assert _classify("mixed", "lf") is True


def test_decision_crlf_with_lf_attr_flagged():
    assert _classify("crlf", "lf") is True


def test_decision_crlf_with_text_attr_flagged():
    assert _classify("crlf", "text") is True


def test_decision_crlf_with_empty_attr_NOT_flagged():
    assert _classify("crlf", "") is False


def test_decision_crlf_with_minus_text_NOT_flagged():
    assert _classify("crlf", "-text") is False


def test_decision_lf_with_lf_attr_NOT_flagged():
    assert _classify("lf", "lf") is False


# --- integration: the script against the current repo ---


REPO = Path(__file__).resolve().parents[2]


def test_integration_clean_diff_returns_clean():
    """`origin/main...HEAD` on this branch should be CLEAN (no changes)."""
    cp = subprocess.run(
        [sys.executable, str(SCRIPT), "--diff", "origin/main...HEAD", "--json"],
        cwd=str(REPO),
        check=False,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    assert cp.returncode == 0, f"expected 0, got {cp.returncode} : {cp.stderr}"
    payload = json.loads(cp.stdout.strip())
    assert payload["verdict"] == "CLEAN"
    assert payload["offending"] == []


def test_integration_bogus_diff_returns_clean():
    """A diff range that covers nothing -> CLEAN (no changed files)."""
    cp = subprocess.run(
        [sys.executable, str(SCRIPT), "--diff", "origin/main...origin/main", "--json"],
        cwd=str(REPO),
        check=False,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    assert cp.returncode == 0
    payload = json.loads(cp.stdout.strip())
    assert payload["verdict"] == "CLEAN"
