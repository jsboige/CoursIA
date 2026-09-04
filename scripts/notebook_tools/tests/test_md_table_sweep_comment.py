"""Tests for scripts/notebook_tools/md_table_sweep_comment.py -- distribution of
the nocturnal markdown-table-guard verdict on a rendezvous issue (#13660, See
#13663 implementation).

The scanner `scan_md_table_syntax.py --json` produces
``{total_findings, files:[{path, findings:[{pathology, cell_index|line, detail,
snippet}]}]}``. This script is the DISTRIBUTOR : it builds a marker-guarded
comment (``MD-TABLE-SWEEP:START..END``) and UPSERTS it on an open issue -- one
comment, updated in place, never a daily flood -- following the
GRAIN-ORPHANS-SWEEP pattern (#13086).

Tests cover:
  - ``_code_wrap`` : tolerate internal backticks (CODE_SPAN_PIPE snippets)
  - ``_coverage_note`` : what the report measures AND what it does not
  - ``build_comment`` : total=0 path (clean) vs total>0 path (per-file findings)
  - ``MARKER_START`` / ``MARKER_END`` always delimit the body
  - main() dry-run path (default) prints body and exits 0 without hitting gh
  - main() apply path is best-effort (try/except swallows gh errors, exits 0)

Advisory: the script NEVER blocks a merge, NEVER closes anything. These tests
verify the advisory contract on the comment body and dry-run behaviour; the
apply path is exercised end-to-end in live workflow runs.

See #13660, #13663.
"""

import io
import json
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from md_table_sweep_comment import (  # noqa: E402
    MARKER_END,
    MARKER_START,
    _code_wrap,
    _coverage_note,
    build_comment,
    main,
)

REPO_ROOT = Path(__file__).resolve().parent.parent.parent.parent


# ---------- _code_wrap ----------


def test_code_wrap_no_backticks():
    """Plain text -> wrapped with single backtick fence."""
    out = _code_wrap("hello world")
    assert out == "`hello world`"


def test_code_wrap_one_backtick_picks_double_fence():
    """Internal backtick forces a 2-backtick fence (max_run + 1).

    NB: when text itself starts/ends with a backtick, fence chars touch
    text's outer backtick -- the visual rendering shows 3 backticks each side
    even though fence=2. Validate via length: 2 (fence) + 6 (text) + 2 = 10.
    """
    out = _code_wrap("`pipe`")
    # Validate visually: 2 backticks + backtick of text + ... + ... = 10 chars
    assert len(out) == 10  # 2 fence + 6 text + 2 fence
    # Validate that fence itself is exactly 2 (not 3)
    fence = out[:2]
    assert fence == "``"
    fence_end = out[-2:]
    assert fence_end == "``"


def test_code_wrap_two_backticks_in_a_row_picks_triple_fence():
    """Longest run of N backticks forces N+1 fence (avoid fence clash)."""
    out = _code_wrap("text ``code`` here")
    # longest run of 2 backticks in text -> fence = 3
    assert out.startswith("```")
    assert out.endswith("```")
    # Validate fence length: 3 + text length + 3 = total
    assert len(out) == 3 + len("text ``code`` here") + 3


def test_code_wrap_preserves_text_exactly():
    """No reformatting, no trimming, no escaping."""
    raw = "exemple | avec un pipe"
    out = _code_wrap(raw)
    # raw is inside the fence; pipe stays as-is
    assert raw in out


# ---------- _coverage_note ----------


def test_coverage_note_mentions_scope_and_limit():
    """Coverage note spells out what the verdict measures AND what it does not."""
    note = _coverage_note()
    assert "syntaxe SOURCE" in note
    assert "rendu" in note  # ce qu'on ne mesure PAS
    assert ".md" in note  # limitation explicite
    assert "choix d'auteur" in note  # verdict peut etre faux-positif


def test_coverage_note_cites_issue_reference():
    """Le note reference #13660 (self) + #10097, #3966, #12817 (founders)."""
    note = _coverage_note()
    assert "#13660" in note
    assert "#10097" in note
    assert "#3966" in note
    assert "#12817" in note


# ---------- build_comment ----------


def test_build_comment_zero_findings():
    """Clean run -> human-readable '0 defaults' message + markers + coverage note."""
    body = build_comment(files=[], total=0, window="last-24h", stamp="2026-09-01T03:15Z")
    assert MARKER_START in body
    assert MARKER_END in body
    assert "0" in body
    assert "last-24h" in body
    assert "2026-09-01T03:15Z" in body  # vintage -- ranking-without-vintage = current
    assert _coverage_note().strip().replace("\n", " ").replace("  ", " ")[:30] in (
        body.replace("\n", " ").replace("  ", " ")
    )


def test_build_comment_with_findings_per_file():
    """Per-file findings : path + cell/line + pathology + snippet (wrapped)."""
    payload_files = [
        {
            "path": "MyIA.AI.Notebooks/Foo/Bar.ipynb",
            "findings": [
                {
                    "pathology": "CODE_SPAN_PIPE",
                    "cell_index": 7,
                    "snippet": "use `not |` syntax",
                },
                {
                    "pathology": "COL_MISMATCH",
                    "line": 42,
                    "snippet": "| a | b | c |",
                },
            ],
        },
    ]
    body = build_comment(
        files=payload_files, total=2, window="abc..def (24h)", stamp="2026-09-01T03:15Z"
    )
    assert MARKER_START in body
    assert MARKER_END in body
    assert "2 défaut" in body
    assert "abc..def (24h)" in body
    assert "Foo/Bar.ipynb" in body
    assert "cellule 7" in body  # cell_index path
    assert "ligne 42" in body  # line path (no cell_index)
    assert "CODE_SPAN_PIPE" in body
    assert "COL_MISMATCH" in body
    # Snippet should be wrapped (CODE_SPAN_PIPE has a backtick inside)
    assert "``use `not |` syntax``" in body  # fence=2 (max_run=1 in 'use `not |` syntax')


def test_build_comment_truncates_long_snippets():
    """Snippets >60 chars get truncated to 57 + '...'."""
    long_snippet = "x" * 80
    payload_files = [
        {"path": "p.ipynb", "findings": [{"pathology": "NO_SEP", "line": 1, "snippet": long_snippet}]}
    ]
    body = build_comment(payload_files, 1, "w", "s")
    # 57 x's + '...'
    assert "x" * 57 + "..." in body
    assert "x" * 60 not in body  # not the full 80


def test_build_comment_skips_file_with_empty_findings():
    """File with no findings is omitted from per-file listing."""
    payload_files = [
        {"path": "empty.ipynb", "findings": []},
        {
            "path": "with_defect.ipynb",
            "findings": [{"pathology": "NO_SEP", "line": 1, "snippet": "..."}],
        },
    ]
    body = build_comment(payload_files, 1, "w", "s")
    assert "empty.ipynb" not in body
    assert "with_defect.ipynb" in body


# ---------- main() : dry-run path (no network) ----------


def test_main_dry_run_prints_body_no_gh_calls(tmp_path, monkeypatch, capsys):
    """Default (no --apply) : build + print + exit 0, NO gh CLI invocation."""
    payload = tmp_path / "p.json"
    payload.write_text(json.dumps({"total_findings": 0, "files": []}))
    # Guard : if main() ever calls gh, the dry-run test fails loud.
    def fail_gh(*args, **kwargs):
        raise AssertionError("dry-run must not invoke gh CLI")

    monkeypatch.setattr(subprocess, "run", fail_gh)

    rc = main([
        "--payload", str(payload),
        "--window", "test-window",
        "--issue", "99999",
    ])
    assert rc == 0
    captured = capsys.readouterr()
    assert "test-window" in captured.out
    assert "0" in captured.out  # '0 defaults' text
    assert "dry-run" in captured.out
    assert MARKER_START in captured.out
    assert MARKER_END in captured.out


def test_main_dry_run_with_findings_payload(tmp_path, capsys):
    """Dry-run with findings renders the per-file listing."""
    payload = tmp_path / "p.json"
    payload.write_text(json.dumps({
        "total_findings": 1,
        "files": [{
            "path": "x.ipynb",
            "findings": [{"pathology": "NO_SEP", "line": 3, "snippet": "abc"}],
        }],
    }))
    rc = main([
        "--payload", str(payload),
        "--window", "win",
        "--issue", "1",
    ])
    assert rc == 0
    captured = capsys.readouterr()
    assert "x.ipynb" in captured.out
    assert "NO_SEP" in captured.out
    assert "ligne 3" in captured.out


def test_main_apply_path_swallows_gh_errors(tmp_path, monkeypatch, capsys):
    """With --apply, a gh failure is swallowed (advisory contract : exit 0)."""
    payload = tmp_path / "p.json"
    payload.write_text(json.dumps({"total_findings": 0, "files": []}))

    def fake_run_fail(*args, **kwargs):
        # Simulate gh CLI failure (network, auth, ...).
        raise subprocess.CalledProcessError(returncode=1, cmd=args[0] if args else "gh")

    monkeypatch.setattr(subprocess, "run", fake_run_fail)

    rc = main([
        "--payload", str(payload),
        "--window", "win",
        "--issue", "1",
        "--apply",
    ])
    assert rc == 0  # advisory : jamais non-zero
    captured = capsys.readouterr()
    # The advisory contract : ECHEC avale is logged to stderr but does not propagate.
    assert "ECHEC avale" in captured.err or "ECHEC" in captured.err or "apply" in captured.out


def test_main_missing_payload_file(tmp_path):
    """Missing payload file : FileNotFoundError propagates (Python default).

    The workflow guards with `|| true`, so non-zero exit is absorbed at the
    workflow layer. The script itself does not swallow file-not-found on the
    payload -- the apply path's try/except only covers the gh call. We document
    the current behaviour to prevent silent regressions.
    """
    with pytest.raises(FileNotFoundError):
        main([
            "--payload", str(tmp_path / "nonexistent.json"),
            "--window", "w",
            "--issue", "1",
        ])