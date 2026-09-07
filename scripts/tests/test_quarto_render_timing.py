#!/usr/bin/env python
"""Tests for scripts/quarto_render_timing.py.

The script is a measurement, not a gate (it always exits 0 -- a Quarto
log-format change must degrade the report, never break a build). What must
NOT drift is the parsing contract: the doc phase ends at the LAST ``[N/M]``
line, the post-render gap ends at the FIRST ``Output created`` line, and a
render crossing midnight must not produce a negative duration.
"""
from __future__ import annotations

import sys
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))

import quarto_render_timing as qrt  # noqa: E402


LOG = [
    "03:10:01 Preparing to render\n",
    "03:11:00 [1/1252] MyIA.AI.Notebooks/a.ipynb\n",
    "03:25:30 [1252/1252] README.md\n",
    "03:38:17 Output created: _site/index.html\n",
]


def test_phases_split_at_last_doc_and_first_output():
    r = qrt.analyse(LOG)
    assert r["doc_count"] == 1252
    assert r["site_path"] == "_site/index.html"
    assert qrt._fmt((r["last_doc"][0] - r["first"]).total_seconds()) == "15:29"
    assert qrt._fmt((r["output_created"][0] - r["last_doc"][0]).total_seconds()) == "12:47"
    assert qrt._fmt((r["output_created"][0] - r["first"]).total_seconds()) == "28:16"


def test_report_renders_table_and_not_found():
    report = qrt.render_report(qrt.analyse(LOG))
    assert "| documents (1252) | 15:29 |" in report
    assert "| post-render (silent) | 12:47 |" in report
    empty = qrt.render_report(qrt.analyse(["03:10:01 only one line\n"]))
    assert "not found" in empty
    assert "[1252/1252]" not in empty


def test_midnight_rollover_is_positive():
    r = qrt.analyse([
        "23:58:00 [1/10] a.ipynb\n",
        "00:04:30 Output created: _site/index.html\n",
    ])
    assert qrt._fmt((r["output_created"][0] - r["first"]).total_seconds()) == "6:30"


def test_untimestamped_lines_are_ignored():
    r = qrt.analyse(["no ts here\n", "03:00:00 [1/1] a.ipynb\n",
                     "03:01:00 Output created: _site/index.html\n"])
    assert r["n_lines"] == 2
    assert r["doc_count"] == 1
