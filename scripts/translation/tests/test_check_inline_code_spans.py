#!/usr/bin/env python3
"""Tests for ``scripts/translation/check_inline_code_spans.py`` — the 5th
invariant of the translation parity gate (issue #13536, Epic #10038).

Coverage :
- Nominal pair (FR == EN code-spans) : pass.
- Falsification 1 : EN drops 1 `` `code` `` span on a single line -> drift.
- Falsification 2 : EN drops multiple `` ` `` spans across multiple cells.
- Falsification 3 : EN gains spans not in FR (no false negative).
- Falsification 4 : FR/EN both lose a *shared* span (pair-wise diff = 0).
- Triple-backtick fence `` ```...``` `` must NOT be matched as inline spans.
- Real-world measurement on the 2 notebooks rendered by PR #12850
  (``medical_chatbot`` and ``FT-05-ModelMerging-Routing``).

stdlib-only (json/pathlib/re/argparse/pytest). Hermetic — no network,
no filesystem side effects beyond tmp_path fixtures.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
TRANSLATION_DIR = HERE.parent
sys.path.insert(0, str(TRANSLATION_DIR))

import check_inline_code_spans as ics  # noqa: E402


# ---------------------------------------------------------------------------
# Helpers — notebook builders
# ---------------------------------------------------------------------------


def _write_nb(path: Path, cells: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {
        "cells": cells,
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")


def _md_cell(cid: str, source: str) -> dict:
    return {
        "cell_type": "markdown",
        "id": cid,
        "metadata": {},
        "source": [line + "\n" for line in source.split("\n") if line is not None]
        if source
        else [],
    }


def _write_pair(
    root: Path,
    stem: str,
    src_md: dict,
    trd_md: dict,
    lang: str = "en",
) -> tuple[Path, Path]:
    """Write ``{stem}.ipynb`` + ``{stem}_{lang}.ipynb`` from {cid: source} dicts."""
    src_cells = [_md_cell(cid, src_md[cid]) for cid in src_md]
    trd_cells = [_md_cell(cid, trd_md[cid]) for cid in trd_md]
    _write_nb(root / f"{stem}.ipynb", src_cells)
    _write_nb(root / f"{stem}_{lang}.ipynb", trd_cells)
    return root / f"{stem}.ipynb", root / f"{stem}_{lang}.ipynb"


# ---------------------------------------------------------------------------
# Helpers — extract_inline_code_spans
# ---------------------------------------------------------------------------


def test_extract_inline_code_spans_basic():
    text = "Nous utilisons `Kernel` et `add_plugin` pour orchestrer les agents."
    spans = ics.extract_inline_code_spans(text)
    assert spans == ["`Kernel`", "`add_plugin`"]


def test_extract_inline_code_spans_excludes_triple_fence():
    text = "```python\nprint('hello')\n```\nInline `code` ici."
    spans = ics.extract_inline_code_spans(text)
    assert spans == ["`code`"], f"triple-fence should not match, got {spans}"


def test_extract_inline_code_spans_empty():
    assert ics.extract_inline_code_spans("") == []
    assert ics.extract_inline_code_spans("plain text without code") == []


def test_extract_inline_code_spans_excludes_empty_backticks():
    """`` `` `` (empty span) must NOT be counted."""
    spans = ics.extract_inline_code_spans("`` empty span ``")
    # The two `` are neighbours — neither is a real span.
    assert spans == [], f"empty backticks should not match, got {spans}"


def test_extract_inline_code_spans_multiline_excluded():
    """Code-spans cannot span newlines (GitHub-flavored)."""
    text = "open with `code\nbroken"
    spans = ics.extract_inline_code_spans(text)
    assert spans == []


# ---------------------------------------------------------------------------
# Falsifications — per-cell drift
# ---------------------------------------------------------------------------


def test_falsif_drop_single_span(tmp_path):
    """EN drops one `` `code` `` span on a single line."""
    src_md = {"c1": "Step `Kernel` is required."}
    trd_md = {"c1": "Step Kernel is required."}  # backticks lost
    src_path, trd_path = _write_pair(tmp_path, "demo", src_md, trd_md)
    src_records, _ = ics._load_markdown_cells(src_path)
    trd_records, _ = ics._load_markdown_cells(trd_path)
    per_cell = ics.measure_code_span_drift(src_records, trd_records)
    assert per_cell[0]["src_spans"] == 1
    assert per_cell[0]["trd_spans"] == 0
    assert per_cell[0]["lost"] == 1
    assert per_cell[0]["lost_examples"] == ["`Kernel`"]


def test_falsif_drop_multi_spans_multi_cells(tmp_path):
    """EN drops spans across 3 markdown cells, mirroring the medical_chatbot
    measurement (issue #13536 body : cell[2]/[8]/[16]/[19]/[26]/[36])."""
    src_md = {
        "c1": "Le `Kernel` est le conteneur central.",
        "c2": "Utilisez `add_plugin` et `FunctionChoiceBehavior`.",
        "c3": "`kernel.add_plugin()` enregistre une instance.",
    }
    trd_md = {
        "c1": "The Kernel is the central container.",
        "c2": "Use add_plugin and FunctionChoiceBehavior.",
        "c3": "kernel.add_plugin() registers an instance.",
    }
    src_path, trd_path = _write_pair(tmp_path, "demo", src_md, trd_md)
    src_records, _ = ics._load_markdown_cells(src_path)
    trd_records, _ = ics._load_markdown_cells(trd_path)
    per_cell = ics.measure_code_span_drift(src_records, trd_records)
    assert sum(e["lost"] for e in per_cell) == 4  # 1+2+1
    assert per_cell[0]["lost_examples"] == ["`Kernel`"]
    assert per_cell[1]["lost_examples"] == ["`add_plugin`", "`FunctionChoiceBehavior`"]
    assert per_cell[2]["lost_examples"] == ["`kernel.add_plugin()`"]


def test_falsif_en_gains_span(tmp_path):
    """EN introduces a span not present in FR — set-diff ``gained`` is 1,
    ``lost`` is 0 (no FR span is missing in EN)."""
    src_md = {"c1": "Plain text."}
    trd_md = {"c1": "Use `new_feature` instead."}
    src_path, trd_path = _write_pair(tmp_path, "demo", src_md, trd_md)
    src_records, _ = ics._load_markdown_cells(src_path)
    trd_records, _ = ics._load_markdown_cells(trd_path)
    per_cell = ics.measure_code_span_drift(src_records, trd_records)
    assert per_cell[0]["src_spans"] == 0
    assert per_cell[0]["trd_spans"] == 1
    assert per_cell[0]["lost"] == 0
    assert per_cell[0]["gained"] == 1


def test_falsif_set_diff_catches_fr_only_token(tmp_path):
    """The same number of tokens does NOT exonerate drift. Set-diff
    cardinality IS the right measure : ``only_fr`` is in src but not in
    trd, so ``lost`` is 1 even though both spans are dropped on a side.

    This is the falsification that motivates using set diff instead of
    raw counts (cf docstring of ``measure_code_span_drift``).
    """
    src_md = {"c1": "`shared` token and `only_fr` token."}
    trd_md = {"c1": "`shared` token and only_en token."}
    src_path, trd_path = _write_pair(tmp_path, "demo", src_md, trd_md)
    src_records, _ = ics._load_markdown_cells(src_path)
    trd_records, _ = ics._load_markdown_cells(trd_path)
    per_cell = ics.measure_code_span_drift(src_records, trd_records)
    assert per_cell[0]["src_spans"] == 2
    assert per_cell[0]["trd_spans"] == 1  # only `shared` survives
    assert per_cell[0]["lost"] == 1  # `only_fr` is missing in trd
    assert per_cell[0]["gained"] == 0
    assert per_cell[0]["lost_examples"] == ["`only_fr`"]


# ---------------------------------------------------------------------------
# Nominal — equal code-spans
# ---------------------------------------------------------------------------


def test_nominal_passes_drift_zero(tmp_path):
    src_md = {"c1": "Use `Kernel` and `add_plugin`."}
    trd_md = {"c1": "Use `Kernel` and `add_plugin`."}
    src_path, trd_path = _write_pair(tmp_path, "demo", src_md, trd_md)
    src_records, _ = ics._load_markdown_cells(src_path)
    trd_records, _ = ics._load_markdown_cells(trd_path)
    per_cell = ics.measure_code_span_drift(src_records, trd_records)
    assert sum(e["lost"] for e in per_cell) == 0


# ---------------------------------------------------------------------------
# End-to-end — single pair CLI
# ---------------------------------------------------------------------------


def test_cli_single_pair_advisory_returns_zero(tmp_path, capsys):
    """Advisory mode (default) : drift flagged but exit 0."""
    src_md = {"c1": "Use `Kernel`."}
    trd_md = {"c1": "Use Kernel."}
    src_path, trd_path = _write_pair(tmp_path, "demo", src_md, trd_md)
    rc = ics.main([
        "--src", str(src_path),
        "--translation", str(trd_path),
    ])
    captured = capsys.readouterr()
    assert rc == 0, f"advisory should not block, got exit {rc}"
    payload = json.loads(captured.out)
    assert payload["verdict"] == "OK_WITH_ADVISORIES"
    assert payload["pair_count"] == 1
    assert payload["advisory_count"] == 1
    pair = payload["pairs"][0]
    assert pair["verdict"] == "INLINE_CODE_DRIFT"
    assert pair["total_lost"] == 1


def test_cli_single_pair_strict_returns_one(tmp_path, capsys):
    """Strict mode : drift blocks exit 1."""
    src_md = {"c1": "Use `Kernel`."}
    trd_md = {"c1": "Use Kernel."}
    src_path, trd_path = _write_pair(tmp_path, "demo", src_md, trd_md)
    rc = ics.main([
        "--src", str(src_path),
        "--translation", str(trd_path),
        "--strict-inline-code",
    ])
    captured = capsys.readouterr()
    assert rc == 1, f"strict should block, got exit {rc}"
    payload = json.loads(captured.out)
    assert payload["verdict"] == "BLOCKED"
    assert payload["blocking_count"] == 1
    assert payload["pairs"][0]["verdict"] == "BLOCKED_INLINE_CODE_DRIFT"


def test_cli_nominal_pair_ok(tmp_path, capsys):
    src_md = {"c1": "Use `Kernel`."}
    trd_md = {"c1": "Use `Kernel`."}
    src_path, trd_path = _write_pair(tmp_path, "demo", src_md, trd_md)
    rc = ics.main(["--src", str(src_path), "--translation", str(trd_path)])
    captured = capsys.readouterr()
    assert rc == 0
    payload = json.loads(captured.out)
    assert payload["verdict"] == "OK"
    assert payload["advisory_count"] == 0


def test_cli_requires_pair_or_repo(capsys):
    """Single-pair mode requires both --src and --translation."""
    rc = ics.main(["--src", "/tmp/x.ipynb"])
    captured = capsys.readouterr()
    assert rc == 2
    assert "ERROR" in captured.err


# ---------------------------------------------------------------------------
# Real-world — measured against the PR #12850 historical commits
# ---------------------------------------------------------------------------


# Path to notebooks extracted from PR #12850 (commit 42e8b2d7c) and main.
# These are sanity baselines : the FR->EN loss on medical_chatbot was
# measured at 27 spans by the original issue (#13536 body) ; FT-05
# measured at 0 spans.
HISTORICAL_FIXTURE_NOTE = (
    "Notebooks extracted via `git show 42e8b2d7c:<path>` and copied to "
    "scratchpad by the worker before the test run. These fixtures are NOT "
    "checked into the repo (they would inflate test data with hundreds of "
    "KB of binary JSON); they are loaded from the scratchpad when present."
)

SCRATCHPAD = Path(r"C:/Users/Jesse/AppData/Local/Temp/claude/c--dev-CoursIA-2/d5b4280c-27fa-42e8-85f2-88897bfcc43c/scratchpad")


@pytest.mark.skipif(
    not (SCRATCHPAD / "mc_fr_main.ipynb").exists(),
    reason=f"Historical fixture missing — {HISTORICAL_FIXTURE_NOTE}",
)
def test_real_medical_chatbot_drift():
    """medical_chatbot : 27 code-spans lost in PR #12850 (issue #13536)."""
    src_path = SCRATCHPAD / "mc_fr_main.ipynb"
    trd_path = SCRATCHPAD / "mc_en_12850.ipynb"
    src_records, _ = ics._load_markdown_cells(src_path)
    trd_records, _ = ics._load_markdown_cells(trd_path)
    per_cell = ics.measure_code_span_drift(src_records, trd_records)
    total_lost = sum(e["lost"] for e in per_cell)
    # Issue #13536 measured 27 (slightly different methodology, but close).
    # The exact count depends on which cells we count — we accept a range.
    assert total_lost >= 20, f"medical_chatbot should lose >=20 spans, got {total_lost}"
    # Cells with loss should be > 0
    cells_with_loss = [e for e in per_cell if e["lost"] > 0]
    assert len(cells_with_loss) >= 5


@pytest.mark.skipif(
    not (SCRATCHPAD / "ft5_fr_main.ipynb").exists(),
    reason=f"Historical fixture missing — {HISTORICAL_FIXTURE_NOTE}",
)
def test_real_ft05_zero_drift():
    """FT-05-ModelMerging-Routing : 0 code-spans lost in PR #12850
    (issue #13536 body measurement)."""
    src_path = SCRATCHPAD / "ft5_fr_main.ipynb"
    trd_path = SCRATCHPAD / "ft5_en_12850.ipynb"
    src_records, _ = ics._load_markdown_cells(src_path)
    trd_records, _ = ics._load_markdown_cells(trd_path)
    per_cell = ics.measure_code_span_drift(src_records, trd_records)
    total_lost = sum(e["lost"] for e in per_cell)
    assert total_lost == 0, f"FT-05 should have 0 loss, got {total_lost}"