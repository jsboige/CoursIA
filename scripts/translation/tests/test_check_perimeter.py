#!/usr/bin/env python3
"""Tests for ``scripts/translation/check_perimeter.py`` — the perimeter gate
of the i18n translation pipeline (Epic #10038 grain E).

Covers :

1. **Perimeter parsing** — bold marker required (``**en**`` vs bare ``en``),
   multiple langs in one row, header column matching, malformed inputs.
2. **CSV scanning** — code cells are skipped (T4 copies them byte-for-byte,
   only markdown counts), text_<lang> filled detection.
3. **Verdict computation** — OK, PERIMETER_VIOLATION, IN_SCOPE_UNUSED,
   PERIMETER_MISSING, PERIMETER_MALFORMED.
4. **CLI exit codes** — 0 (OK), 1 (violation), 2 (missing/malformed).
5. **End-to-end** — invokes ``main()`` with a tmp perimeter + tmp CSVs,
   asserts the verdict + exit code match expectations.

stdlib-only (csv/json/pathlib/re/argparse/pytest). Hermetic — no network,
no filesystem side effects beyond tmp_path fixtures.

Mirror of the test pattern established by ``test_check_translation_sync.py``
and ``test_check_resync_only.py`` for sibling scripts.
"""

from __future__ import annotations

import csv
import io
import json
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
TRANSLATION_DIR = HERE.parent
sys.path.insert(0, str(TRANSLATION_DIR))

import check_perimeter as p  # noqa: E402


# ---------------------------------------------------------------------------
# Helpers — fixtures (CSV + PERIMETER.md content)
# ---------------------------------------------------------------------------

CSV_COLUMNS = (
    ["notebook", "cell_id", "cell_type", "src_lang", "src_hash", "text_fr"]
    + [f"text_{L}" for L in p.TARGET_LANGS]
    + [f"hash_{L}" for L in p.ALL_LANGS]
)


def _row(notebook: str, cell_id: str, cell_type: str = "markdown",
         src_hash: str = "abc", text_fr: str = "texte fr",
         text_en: str = "", text_ru: str = "") -> list[str]:
    """Build a canonical CSV row. ``text_en`` / ``text_ru`` non-empty = filled."""
    # Order: text_en, text_es, text_ar, text_fa, text_zh, text_ru, text_pt
    lang_values = {
        "en": text_en,
        "es": "",
        "ar": "",
        "fa": "",
        "zh": "",
        "ru": text_ru,
        "pt": "",
    }
    row = [notebook, cell_id, cell_type, "fr", src_hash, text_fr]
    row += [lang_values[L] for L in p.TARGET_LANGS]
    row += [src_hash]                  # hash_fr
    row += [""] * len(p.TARGET_LANGS)  # hash_en..hash_pt
    assert len(row) == len(CSV_COLUMNS), f"row len {len(row)} != {len(CSV_COLUMNS)}"
    return row


def _write_csv(path: Path, rows: list[list[str]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(CSV_COLUMNS)
        w.writerows(rows)


def _perimeter_md(rows: list[str]) -> str:
    """Build a minimal PERIMETER.md content. ``rows`` = CSV-row lines."""
    header = "| CSV | en | es | ar | fa | zh | ru | pt | Source |"
    sep = "|---|---|---|---|---|---|---|---|---|"
    return "\n".join([header, sep] + rows) + "\n"


# ---------------------------------------------------------------------------
# parse_perimeter — header + bold marker + lang extraction
# ---------------------------------------------------------------------------

def test_parse_perimeter_extracts_bold_marker():
    """The bold marker ``**en**`` is what declares in-scope. Plain ``en``
    in a cell is NOT in-scope (forces explicit declaration)."""
    content = _perimeter_md([
        "| `translations/genai/finetuning.csv` | **en** | - | - | - | - | - | - | #10017 |",
    ])
    result = p.parse_perimeter(_write_perimeter(content))
    assert "translations/genai/finetuning.csv" in result
    assert result["translations/genai/finetuning.csv"] == {"en"}


def test_parse_perimeter_rejects_bare_lang_marker():
    """A bare ``en`` (without bold) is NOT in-scope. Defensive against
    accidental whitespace / punctuation. The parser looks for ``**en**``."""
    content = _perimeter_md([
        "| `translations/genai/finetuning.csv` | en | - | - | - | - | - | - | #10017 |",
    ])
    result = p.parse_perimeter(_write_perimeter(content))
    assert result["translations/genai/finetuning.csv"] == set()


def test_parse_perimeter_multiple_langs_in_row():
    """A row declaring ``en`` + ``ru`` in-scope returns both."""
    content = _perimeter_md([
        "| `translations/genai/casestudies.csv` | **en** | - | - | - | - | **ru** | - | mixed |",
    ])
    result = p.parse_perimeter(_write_perimeter(content))
    assert result["translations/genai/casestudies.csv"] == {"en", "ru"}


def test_parse_perimeter_skips_non_csv_rows():
    """A row that does not start with ``translations/...csv`` is ignored."""
    content = _perimeter_md([
        "| `translations/README.md` | **en** | - | - | - | - | - | - | doc, not CSV |",
        "| `translations/genai/finetuning.csv` | **en** | - | - | - | - | - | - | real CSV |",
    ])
    result = p.parse_perimeter(_write_perimeter(content))
    assert "translations/README.md" not in result
    assert "translations/genai/finetuning.csv" in result


def test_parse_perimeter_missing_raises(tmp_path):
    """Missing file → FileNotFoundError. Caller maps to PERIMETER_MISSING."""
    with pytest.raises(FileNotFoundError):
        p.parse_perimeter(tmp_path / "no_such_file.md")


def test_parse_perimeter_no_matrix_raises_value_error(tmp_path):
    """A PERIMETER.md without the matrix table is malformed."""
    bad = tmp_path / "PERIMETER.md"
    bad.write_text("# Title\n\nSome prose, no table.\n", encoding="utf-8")
    with pytest.raises(ValueError, match="en-tête"):
        p.parse_perimeter(bad)


def test_parse_perimeter_no_data_rows_raises_value_error(tmp_path):
    """A PERIMETER.md with the header but no data rows is malformed."""
    bad = tmp_path / "PERIMETER.md"
    bad.write_text(
        "# Title\n\n"
        "| CSV | en | es | ar | fa | zh | ru | pt | Source |\n"
        "|---|---|---|---|---|---|---|---|---|\n"
        "\nNo data rows below.\n",
        encoding="utf-8",
    )
    with pytest.raises(ValueError, match="aucune ligne"):
        p.parse_perimeter(bad)


# ---------------------------------------------------------------------------
# scan_csv_langs — code cells skipped, only markdown counts
# ---------------------------------------------------------------------------

def test_scan_csv_langs_counts_only_markdown(tmp_path):
    """Code cells with non-empty text_en are NOT counted (T4 copies them
    byte-for-byte; their translations live in code comments, not the CSV)."""
    csv_path = tmp_path / "translations" / "genai" / "mixed.csv"
    _write_csv(csv_path, [
        _row("nb.ipynb", "c1", cell_type="markdown", text_en="English"),
        # Code cell with text_en filled — must NOT count.
        _row("nb.ipynb", "c2", cell_type="code", text_en="English code comment"),
        # Code cell with text_en empty — must NOT count (it's already 0).
        _row("nb.ipynb", "c3", cell_type="code"),
    ])
    counts = p.scan_csv_langs(csv_path)
    assert counts["en"] == 1  # only the markdown cell


def test_scan_csv_langs_returns_zero_for_empty_csv(tmp_path):
    csv_path = tmp_path / "translations" / "genai" / "empty.csv"
    _write_csv(csv_path, [])  # header only
    counts = p.scan_csv_langs(csv_path)
    assert all(v == 0 for v in counts.values())


# ---------------------------------------------------------------------------
# compute_anomalies — verdict logic
# ---------------------------------------------------------------------------

def test_compute_anomalies_no_violation_when_in_scope(tmp_path):
    """A CSV with text_en filled and ``en`` declared in-scope → 0 violations."""
    csv_path = tmp_path / "translations" / "genai" / "finetuning.csv"
    _write_csv(csv_path, [
        _row("nb.ipynb", "c1", text_en="English text"),
    ])
    perimeter = {"translations/genai/finetuning.csv": {"en"}}
    anomalies, fills = p.compute_anomalies([csv_path], perimeter, translations_root=tmp_path)
    violations = [a for a in anomalies if a.verdict == "PERIMETER_VIOLATION"]
    assert violations == []
    # ``fills`` is keyed by the repo-relative POSIX path including the
    # ``translations/`` prefix (matches PERIMETER.md keys).
    assert fills["translations/genai/finetuning.csv"]["en"] == 1


def test_compute_anomalies_violation_when_out_of_scope(tmp_path):
    """A CSV with text_ru filled but ``ru`` NOT declared in-scope → violation."""
    csv_path = tmp_path / "translations" / "genai" / "image.csv"
    _write_csv(csv_path, [
        _row("nb.ipynb", "c1", text_ru="Русский текст"),
    ])
    perimeter = {"translations/genai/image.csv": set()}  # ru not declared
    anomalies, _ = p.compute_anomalies([csv_path], perimeter, translations_root=tmp_path)
    violations = [a for a in anomalies if a.verdict == "PERIMETER_VIOLATION"]
    assert len(violations) == 1
    assert violations[0].detail["lang"] == "ru"
    assert violations[0].detail["n_cells"] == 1


def test_compute_anomalies_advisory_when_declared_but_unused(tmp_path):
    """A CSV with ``en`` declared in-scope but 0 cells filled → IN_SCOPE_UNUSED.
    When multiple langs are declared but unfilled, the script emits one
    advisory per (csv, lang) pair so the operator can track declared-but-unused
    work granularly."""
    csv_path = tmp_path / "translations" / "genai" / "image.csv"
    _write_csv(csv_path, [
        _row("nb.ipynb", "c1"),  # no text_en / text_ru filled
    ])
    perimeter = {"translations/genai/image.csv": {"en", "ru"}}
    anomalies, _ = p.compute_anomalies([csv_path], perimeter, translations_root=tmp_path)
    advisories = [a for a in anomalies if a.verdict == "IN_SCOPE_UNUSED"]
    # 2 advisories : one for ``en`` (declared but unfilled), one for ``ru``.
    assert len(advisories) == 2
    advisory_langs = {a.detail["lang"] for a in advisories}
    assert advisory_langs == {"en", "ru"}


def test_compute_anomalies_unlisted_csv_defaults_to_out_of_scope(tmp_path):
    """A CSV present in the filesystem but absent from PERIMETER.md is treated
    as all-langs out-of-scope (forces explicit declaration before any work)."""
    csv_path = tmp_path / "translations" / "genai" / "surprise.csv"
    _write_csv(csv_path, [
        _row("nb.ipynb", "c1", text_en="English"),
    ])
    perimeter = {}  # surprise.csv not declared
    anomalies, _ = p.compute_anomalies([csv_path], perimeter, translations_root=tmp_path)
    violations = [a for a in anomalies if a.verdict == "PERIMETER_VIOLATION"]
    assert len(violations) == 1
    assert violations[0].csv.endswith("surprise.csv")
    assert violations[0].detail["lang"] == "en"


# ---------------------------------------------------------------------------
# CLI — exit codes + verdict labels
# ---------------------------------------------------------------------------

def test_cli_returns_2_when_perimeter_missing(tmp_path, capsys, monkeypatch):
    """No PERIMETER.md → exit 2, verdict PERIMETER_MISSING."""
    monkeypatch.setattr(sys, "argv", [
        "check_perimeter.py",
        "--translations-root", str(tmp_path),
        "--perimeter", str(tmp_path / "no_perimeter.md"),
        "--json-only",
    ])
    rc = p.main()
    captured = capsys.readouterr()
    assert rc == 2
    report = json.loads(captured.out)
    assert report["verdict"] == "PERIMETER_MISSING"


def test_cli_returns_2_when_perimeter_malformed(tmp_path, capsys, monkeypatch):
    """A PERIMETER.md without a matrix table → exit 2, verdict PERIMETER_MALFORMED."""
    bad = tmp_path / "PERIMETER.md"
    bad.write_text("No matrix here.\n", encoding="utf-8")
    monkeypatch.setattr(sys, "argv", [
        "check_perimeter.py",
        "--translations-root", str(tmp_path),
        "--perimeter", str(bad),
        "--json-only",
    ])
    rc = p.main()
    captured = capsys.readouterr()
    assert rc == 2
    report = json.loads(captured.out)
    assert report["verdict"] == "PERIMETER_MALFORMED"


def test_cli_returns_0_when_perimeter_satisfied(tmp_path, capsys, monkeypatch):
    """PERIMETER.md matches CSV fill state → exit 0, verdict OK."""
    csv_path = tmp_path / "translations" / "genai" / "finetuning.csv"
    _write_csv(csv_path, [
        _row("nb.ipynb", "c1", text_en="English"),
    ])
    perimeter_path = tmp_path / "PERIMETER.md"
    perimeter_path.write_text(_perimeter_md([
        "| `translations/genai/finetuning.csv` | **en** | - | - | - | - | - | - | test |",
    ]), encoding="utf-8")
    monkeypatch.setattr(sys, "argv", [
        "check_perimeter.py",
        "--translations-root", str(tmp_path / "translations"),
        "--perimeter", str(perimeter_path),
        "--json-only",
    ])
    rc = p.main()
    captured = capsys.readouterr()
    assert rc == 0
    report = json.loads(captured.out)
    assert report["verdict"] == "OK"
    assert report["violation_count"] == 0


def test_cli_returns_1_on_violation(tmp_path, capsys, monkeypatch):
    """A CSV with text_ru filled but ``ru`` NOT declared → exit 1, violation reported."""
    csv_path = tmp_path / "translations" / "genai" / "image.csv"
    _write_csv(csv_path, [
        _row("nb.ipynb", "c1", text_ru="Русский"),
    ])
    perimeter_path = tmp_path / "PERIMETER.md"
    perimeter_path.write_text(_perimeter_md([
        "| `translations/genai/image.csv` | **en** | - | - | - | - | - | - | test |",
    ]), encoding="utf-8")
    monkeypatch.setattr(sys, "argv", [
        "check_perimeter.py",
        "--translations-root", str(tmp_path / "translations"),
        "--perimeter", str(perimeter_path),
        "--json-only",
    ])
    rc = p.main()
    captured = capsys.readouterr()
    assert rc == 1
    report = json.loads(captured.out)
    assert report["verdict"] == "PERIMETER_VIOLATION"
    assert report["violation_count"] == 1


# ---------------------------------------------------------------------------
# End-to-end — full repo state matches the gate (manual reference)
# ---------------------------------------------------------------------------

def test_full_repo_state_passes_perimeter():
    """Reference test against the live ``translations/`` tree on main.

    This is NOT a hermetic test — it asserts the actual state of the repo
    passes its own perimeter gate. If this fails, either (a) someone filled
    a cell out-of-scope (must update PERIMETER.md), or (b) the perimeter
    declaration is stale (must resync). Both are real defects that need
    handling, not a test bug to silence.
    """
    repo_root = HERE.parent.parent.parent  # scripts/translation/tests/ → repo root
    perimeter_path = repo_root / "translations" / "PERIMETER.md"
    if not perimeter_path.exists():
        pytest.skip("PERIMETER.md not present at repo root (pre-grain E state)")
    translations_root = repo_root / "translations"
    rc = p.main([
        "--perimeter", str(perimeter_path),
        "--translations-root", str(translations_root),
        "--json-only",
    ])
    # Exit 0 = perimeter satisfied. Exit 1 = violation (the gate caught a defect).
    # We assert exit 0 here because the grain E PR has just declared the
    # perimeter to match the actual CSV state.
    assert rc == 0, (
        f"Perimeter gate FAILED on repo state. Either update PERIMETER.md "
        f"to declare newly-filled langs, or revert the offending CSV fills."
    )


# ---------------------------------------------------------------------------
# Internal — fixture writer
# ---------------------------------------------------------------------------

def _write_perimeter(content: str) -> Path:
    """Write ``content`` to a tmp file and return its path. Used by parse tests
    that don't want to manage tmp_path themselves."""
    import tempfile
    fd, name = tempfile.mkstemp(suffix=".md")
    p = Path(name)
    p.write_text(content, encoding="utf-8")
    return p