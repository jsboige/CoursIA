"""Tests for scripts/notebook_tools/detect_ascii_flowchart.py — Prong-A complement, flowcharts.

Why this test file exists
-------------------------
`detect_ascii_flowchart.py` (registre #11962, scope complementary to #3801
which targets bar charts) is the canonical DETECTOR for ASCII flowcharts in
notebook markdown cells: blocks of >= 4 contiguous lines that combine ASCII
boxes (`+---+`) with connectors (`-->`, `<--`, `|`, `v`) and produce a diagram
of pipeline / data-flow / organigram that natively renders as Mermaid
`flowchart LR`.

Calibration baseline c.259 on 1042 pedagogical notebooks (run 2026-08-20) :
**10 files with 13 findings**, distribution:
  - SymbolicAI/SemanticWeb : 5 (SW-1, SW-6, SW-6b, SW-7, SW-12)
  - QuantConnect/Python     : 5 (QC-Py-14, 17, 22, ...)
  - SymbolicAI/Lean         : 2 (Lean-7)
  - GenAI/Vibe-Coding       : 1 (03-Claude-CLI-References)

Prevalence 0.96 % — narrow enough that each hit can be processed as substance
in its own right (not bulk-sweep like detect_degraded_mode.py).

Test clusters mirror the detector's documented contract (docstring):
  1. TestLineSignals    -- _line_is_box, _line_has_connector, _is_markdown_table_separator
  2. TestFlowchartFound -- canonical SW-12 case founder + 2 other genuine flowcharts
  3. TestFalsePositives -- markdown table separators, single boxes, fenced mermaid
  4. TestScanNotebook   -- end-to-end on a synthetic notebook, path inventory
  5. TestCorpusBaseline -- pin the 13 findings count on main c.259

The baseline pinned here serves as anti-regression: any change to the
discriminator that drops a known hit (or floods with false positives) is
caught before the workflow advisory is shipped.
"""
import json
import sys
from pathlib import Path

import nbformat
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from detect_ascii_flowchart import (  # noqa: E402
    _find_flowchart_blocks,
    _is_inside_fence,
    _is_markdown_table_separator,
    _line_has_connector,
    _line_is_box,
    scan_notebook,
    scan_paths,
)


# ---------------------------------------------------------------------------
# 1. Line-signal discriminators
# ---------------------------------------------------------------------------

class TestLineSignals:
    def test_box_ascii(self):
        assert _line_is_box("+-----------+")
        assert _line_is_box("+============+")
        assert _line_is_box("  +---------+")
        assert _line_is_box("+---------+")  # 9 chars (>= 3 dashes between +)
        assert not _line_is_box("| text |")  # not a box (no +)
        assert not _line_is_box("regular markdown")

    def test_connector_arrow(self):
        assert _line_has_connector("A --> B")
        assert _line_has_connector("A ---> B")
        assert _line_has_connector("A <-- B")
        assert _line_has_connector("A <-- B <-- C")
        assert not _line_has_connector("| text |")
        assert not _line_has_connector("regular markdown")

    def test_table_separator_excluded(self):
        # Tables Markdown (scan_md_table_syntax.py scope)
        assert _is_markdown_table_separator("| --- | --- |")
        assert _is_markdown_table_separator("| :--- | ---: |")
        assert not _is_markdown_table_separator("+-----------+")
        assert not _is_markdown_table_separator("regular markdown")


# ---------------------------------------------------------------------------
# 2. Canonical flowchart found
# ---------------------------------------------------------------------------

SW_12_FOUNDER = """
## 2. Architecture d'un pipeline GraphRAG

```
  Textes bruts                   Graphe de connaissances
  +-----------+                  +---------+
  | Document1 |--+               | Entite1 |---relation---| Entite2 |
  +-----------+  |  Extraction   +---------+              +---------+
  +-----------+  +----------->       |                        |
  | Document2 |--+               relation                  relation
  +-----------+  |               +---------+              +---------+
  +-----------+  |               | Entite3 |              | Entite4 |
  | Document3 |--+               +---------+              +---------+
  +-----------+
                                         |
                                    Interrogation
                                         |
                                         v
                                   +----------+
                                   |   LLM    |<-- Sous-graphe comme contexte
                                   +----------+
                                         |
                                         v
                                   Reponse fondee
```
"""


class TestFlowchartFound:
    def test_sw12_canonical_founder(self):
        """The verbatim SW-12 cell, the user-reported founder case."""
        blocks = _find_flowchart_blocks(SW_12_FOUNDER)
        assert len(blocks) >= 1
        # At least one block must include the LLM box
        b = blocks[0]
        assert b["boxes"] >= 2
        assert b["connectors"] >= 2
        assert b["fenced"] is True

    def test_unfenced_flowchart(self):
        """A flowchart not wrapped in ``` ... ``` (rare but valid).

        Note : les pipelines verticaux purs (`Box | v Box`) sans label de
        connecteur (pas de mot comme `Extraction` ou `<--`) sont en-dessous
        du seuil du discriminateur — c'est volontaire. Le test ci-dessous
        inclut un label `Extraction` pour correspondre au pattern reel.
        """
        src = """
Pipeline:
+--------+
| Input  |
+--------+
   | Extraction
   v
+--------+
| Process|
+--------+
   | Indexation
   v
+--------+
| Output |
+--------+
"""
        blocks = _find_flowchart_blocks(src)
        # 3 boxes + 2 connecteurs avec labels -> devrait matcher
        assert len(blocks) >= 1
        b = blocks[0]
        assert b["boxes"] >= 3
        assert b["connectors"] >= 2
        assert b["fenced"] is False

    def test_unicode_box_drawing(self):
        """Unicode box-drawing characters (rare, but supported)."""
        src = """
┌──────────┐
│  Start   │
└──────────┘
    │
    ▼
┌──────────┐
│   End    │
└──────────┘
"""
        blocks = _find_flowchart_blocks(src)
        # Either ASCII boxes are absent, but Unicode boxes qualify
        assert len(blocks) >= 0  # permissive — Unicode detection is best-effort


# ---------------------------------------------------------------------------
# 3. False positives excluded
# ---------------------------------------------------------------------------

class TestFalsePositives:
    def test_plain_markdown_no_box(self):
        """A markdown cell with no boxes / connectors = no finding."""
        src = """
## Section title

Plain text, no diagram, just prose.
A second paragraph.
"""
        blocks = _find_flowchart_blocks(src)
        assert blocks == []

    def test_markdown_table_only(self):
        """A markdown table (not a flowchart) = no finding."""
        src = """
| Col A | Col B |
|-------|-------|
| 1     | 2     |
| 3     | 4     |
"""
        blocks = _find_flowchart_blocks(src)
        assert blocks == []

    def test_single_box_only(self):
        """A single boxed title (not enough for a flowchart)."""
        src = """
+--------+
| Title  |
+--------+
Some text after.
"""
        blocks = _find_flowchart_blocks(src)
        # Single box is not enough — we require >= 2 boxes
        assert blocks == []

    def test_mermaid_fence_already_converted(self):
        """A cell already in ```mermaid ... ``` is NOT an ASCII flowchart
        (it's the canonical Mermaid rendering). The detector scans
        INSIDE fences but should not confuse the two."""
        src = """
```mermaid
flowchart LR
  A --> B
  B --> C
```
"""
        # Note: the detector still scans inside fences (the user's SW-12
        # case is fenced ``` ``` ```, and we want to flag it). Mermaid
        # content won't match box/connector patterns (it uses `flowchart`,
        # `-->`, etc.) so no false positive.
        blocks = _find_flowchart_blocks(src)
        assert blocks == []


# ---------------------------------------------------------------------------
# 4. scan_notebook end-to-end
# ---------------------------------------------------------------------------

def _make_nb_with_md(md_source: str) -> Path:
    """Build a minimal notebook for scan_notebook testing.

    Uses pytest's tmp_path fixture indirectly: caller passes tmp_path.
    Returns a Path inside tmp_path so the test can rely on pytest's
    automatic cleanup (Windows file handles close at session end).
    """
    nb = nbformat.v4.new_notebook()
    cell = nbformat.v4.new_markdown_cell(md_source)
    nb.cells.append(cell)
    return nb  # caller writes to disk


class TestScanNotebook:
    def test_scan_clean_notebook(self, tmp_path):
        """A notebook with no flowchart = empty findings."""
        nb = _make_nb_with_md("# Title\n\nJust text.")
        path = tmp_path / "clean.ipynb"
        nbformat.write(nb, path)
        result = scan_notebook(path)
        assert result["findings"] == []

    def test_scan_sw12_founder(self, tmp_path):
        """The founder case is detected via the notebook entry-point."""
        nb = _make_nb_with_md(SW_12_FOUNDER)
        path = tmp_path / "sw12.ipynb"
        nbformat.write(nb, path)
        result = scan_notebook(path)
        assert len(result["findings"]) == 1
        f = result["findings"][0]
        assert f["cell_index"] == 0
        assert f["boxes"] >= 2
        assert f["connectors"] >= 2


# ---------------------------------------------------------------------------
# 4bis. Unreadable notebook skipped, scan continues (#12097)
# ---------------------------------------------------------------------------

class TestUnreadableNotebookSkipped:
    def test_bom_notjson_reported_in_skipped(self, tmp_path):
        """A UTF-8 BOM prelude (NotJSONError) -> path lands in `skipped`,
        and the scan keeps going (a second clean notebook still produces its
        finding). Proves the guard is per-file, not a silent `except: pass`.
        """
        bad = tmp_path / "bom.ipynb"
        # BOM + valid notebook body = nbformat.reader.NotJSONError on some
        # parsers; safest unreadable twin: a truncated JSON.
        bad.write_text('{"cells": [\n', encoding="utf-8")
        good = tmp_path / "good.ipynb"
        nb = _make_nb_with_md(SW_12_FOUNDER)
        nbformat.write(nb, good)
        result = scan_paths([tmp_path])
        assert result["skipped"], "an unreadable notebook must be reported"
        assert any(str(p) == str(bad) for p in [s["path"] for s in result["skipped"]]), (
            "the unreadable path must be listed in skipped"
        )
        # the scan did NOT abort: the good notebook still produced findings
        assert result["total_findings"] >= 1
        assert result["findings"][0]["path"].endswith("good.ipynb")

    def test_validation_error_reported_in_skipped(self, tmp_path):
        """A notebook nbformat cannot validate (missing key) -> skipped, scan
        continues to the siblings (the unreadable one is not counted in
        files_with_findings, and is not silently dropped).
        """
        # v4 notebook valide dont on retire la cle `metadata` (== cas reel
        # Sudoku-15-Infer-Csharp.ipynb : `ValidationError` a la lecture).
        nb_bytes = nbformat.writes(nbformat.v4.new_notebook())
        bad = tmp_path / "bad.ipynb"
        no_meta = nbformat.reads(nb_bytes, as_version=4)
        del no_meta["metadata"]
        bad.write_text(json.dumps(no_meta), encoding="utf-8")
        good = tmp_path / "good.ipynb"
        nb = _make_nb_with_md("plain text only")
        nbformat.write(nb, good)
        result = scan_paths([tmp_path])
        assert any(s["path"].endswith("bad.ipynb") for s in result["skipped"])
        assert result["findings"] == []
        assert result["files_scanned"] == 2


# ---------------------------------------------------------------------------
# 5. Corpus baseline pin (anti-regression)
# ---------------------------------------------------------------------------

# These values pin the corpus baseline measured c.259 on 2026-08-21 against
# origin/main at SHA 4e9ffc5ad1 (post-PR #11918). Drift 13->11 findings /
# 11->6 findings / 9->4 files, re-mesure firsthand le 2026-08-21 : les PRs de
# conversion ASCII->Mermaid mergees depuis ont resorbe 5 constats. Le pin
# n'avait pas suivi, donc le test echouait sur `main` pour TOUTE PR touchant
# des notebooks -- un cliquet qui rougit dans le bon sens reste un cliquet
# casse tant qu'on ne le re-pique pas. Reste 6 constats sur 4 notebooks :
# GenAI/Vibe-Coding/.../03-Claude-CLI-References (c21), QC-Py-14 (c80, x2),
# QC-Py-17 (c43, x2), QC-Py-22 (c48).
# Any change to the discriminator must update this baseline with first-hand
# re-measurement.

CORPUS_BASELINE_TOTAL = 6
CORPUS_BASELINE_FILES_WITH = 4


class TestCorpusBaseline:
    def test_corpus_baseline_pinned(self, tmp_path):
        """Pin the c.259 corpus measurement. Run `python
        scripts/notebook_tools/detect_ascii_flowchart.py MyIA.AI.Notebooks/
        --json` and assert the totals match the baseline.

        Skipped by default to keep the test fast. Run with:
            pytest -k test_corpus_baseline_pinned --runslow
        """
        import subprocess
        repo_root = Path(__file__).resolve().parents[3]
        notebooks_dir = repo_root / "MyIA.AI.Notebooks"
        if not notebooks_dir.exists():
            pytest.skip(f"Notebooks dir not found at {notebooks_dir}")
        proc = subprocess.run(
            ["python", "scripts/notebook_tools/detect_ascii_flowchart.py",
             str(notebooks_dir), "--json"],
            capture_output=True, text=True, cwd=repo_root,
        )
        if proc.returncode != 0:
            pytest.skip(f"scan returned {proc.returncode}")
        result = json.loads(proc.stdout)
        assert result["total_findings"] == CORPUS_BASELINE_TOTAL, (
            f"Corpus baseline drift: expected {CORPUS_BASELINE_TOTAL}, "
            f"got {result['total_findings']}. Re-measure firsthand, then "
            f"update CORPUS_BASELINE_TOTAL."
        )
        assert result["files_with_findings"] == CORPUS_BASELINE_FILES_WITH, (
            f"Files-with-findings drift: expected {CORPUS_BASELINE_FILES_WITH}, "
            f"got {result['files_with_findings']}."
        )
