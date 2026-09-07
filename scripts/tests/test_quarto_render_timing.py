#!/usr/bin/env python
"""Tests for scripts/quarto_render_timing.py.

The script is a measurement, not a gate (it always exits 0 -- a Quarto
log-format change must degrade the report, never break a build). What must
NOT drift is the parsing contract, pinned against the REAL CI log format
observed on run 34074565982 (2026-09-07):

- document progress counters are SPACE-PADDED (``[   1/1265]``, width of M);
- progress segments ride \\r-separated inside one \\n-terminated line, after
  an ANSI color prefix (``\\x1b[1m\\x1b[34m\\r[ 586/1261] file\\x1b[39m``),
  so the first CI render of the tool reported ``documents: not found`` --
  text-mode ``readlines()`` split on those ``\\r`` and divorced every
  progress segment from the line's timestamp prefix;
- the doc phase ends at the LAST ``[N/M]`` segment, the post-render gap ends
  at the FIRST ``Output created`` line;
- a render crossing midnight must not produce a negative duration.
"""
from __future__ import annotations

import sys
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))

import quarto_render_timing as qrt  # noqa: E402


LOG = (
    "03:10:01 Preparing to render\n"
    "03:11:00 [1/1252] MyIA.AI.Notebooks/a.ipynb\n"
    "03:25:30 [1252/1252] README.md\n"
    "03:38:17 Output created: _site/index.html\n"
)

# Format as observed on CI run 34074565982: ANSI prefix, \r, padded counters.
CI_LOG = (
    "02:01:10 \x1b[1m\x1b[34m\r[   1/1265] MyIA.AI.Notebooks/GameTheory/index.qmd\x1b[39m\x1b[22m\n"
    "02:22:20 \x1b[1m\x1b[34m\r[1000/1265] Search/CSP-7.ipynb\x1b[39m\x1b[22m\n"
    "02:28:37 \x1b[1m\x1b[34m\r[1265/1265] Tweety-7a.ipynb\x1b[39m\x1b[22m\n"
    "02:32:54 Output created: _site/index.html\n"
)


def test_phases_split_at_last_doc_and_first_output():
    r = qrt.analyse(LOG)
    assert r["doc_count"] == 1252
    assert r["site_path"] == "_site/index.html"
    assert qrt._fmt((r["last_doc"][0] - r["first"]).total_seconds()) == "15:29"
    assert qrt._fmt((r["output_created"][0] - r["last_doc"][0]).total_seconds()) == "12:47"
    assert qrt._fmt((r["output_created"][0] - r["first"]).total_seconds()) == "28:16"


def test_ci_format_padded_counters_and_cr_segments():
    r = qrt.analyse(CI_LOG)
    assert r["doc_count"] == 1265
    assert "1265/1265" in r["last_doc"][1]
    # 02:01:10 -> 02:28:37 docs, -> 02:32:54 output created
    assert qrt._fmt((r["last_doc"][0] - r["first"]).total_seconds()) == "27:27"
    assert qrt._fmt((r["output_created"][0] - r["last_doc"][0]).total_seconds()) == "4:17"
    assert qrt._fmt((r["output_created"][0] - r["first"]).total_seconds()) == "31:44"


def test_report_renders_table_and_not_found():
    report = qrt.render_report(qrt.analyse(LOG))
    assert "| documents (1252) | 15:29 |" in report
    assert "| post-render (silent) | 12:47 |" in report
    empty = qrt.render_report(qrt.analyse("03:10:01 only one line\n"))
    assert "not found" in empty
    assert "[1252/1252]" not in empty


def test_midnight_rollover_is_positive():
    r = qrt.analyse(
        "23:58:00 [1/10] a.ipynb\n"
        "00:04:30 Output created: _site/index.html\n"
    )
    assert qrt._fmt((r["output_created"][0] - r["first"]).total_seconds()) == "6:30"


def test_untimestamped_lines_are_ignored():
    r = qrt.analyse(
        "no ts here\n"
        "03:00:00 [1/1] a.ipynb\n"
        "03:01:00 Output created: _site/index.html\n"
    )
    assert r["n_lines"] == 2
    assert r["doc_count"] == 1


def test_cr_segment_without_timestamp_is_not_its_own_event():
    # A \r-segment carrying content but no timestamp anywhere in its physical
    # line must not create an event (the v1 bug: text mode made these lines
    # timestamp-less events, losing every progress marker).
    r = qrt.analyse("03:00:00 \x1b[1m\x1b[34m\r[  1/900] a.ipynb\x1b[39m\n03:09:00 Output created: _site/index.html\n")
    assert r["doc_count"] == 900
    assert qrt._fmt((r["output_created"][0] - r["last_doc"][0]).total_seconds()) == "9:00"
