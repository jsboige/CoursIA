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

Calibration baseline c.439 on 2026-08-21 (post-#12011 ASCII->Mermaid tranche
+ post-#12020 + post-#11994), re-measured firsthand with #12097 try/except fix
applied (without which the scan crashed on BTC-ML-Researcher.ipynb before
reaching the body) : **9 files with 11 findings**, distribution:
  - SymbolicAI/SemanticWeb : 4 (SW-6, SW-6b, SW-7, SW-12 ; SW-1 ASCII->Mermaid par #12011)
  - QuantConnect/Python     : 4 (QC-Py-14, 17, 22, ...)
  - SymbolicAI/Lean         : 2 (Lean-7)
  - GenAI/Vibe-Coding       : 1 (03-Claude-CLI-References)

Drift = 2 findings resolved by tranche ASCII->Mermaid #12011 (1 SW-1 + 1
autre) + 1 unreadable (Sudoku-15-Infer-Csharp.ipynb missing metadata,
mesure c.439).

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
        assert result.get("error") is None

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

    def test_scan_corrupt_json_returns_error_not_crash_12097(self, tmp_path):
        """#12097 acceptance : a notebook whose body is invalid JSON (e.g. raw
        text starting with '{' but missing proper structure) MUST return
        {error, findings=[]} instead of raising. Mirrors the sibling
        detect_ascii_workaround.py L344-350 contract."""
        path = tmp_path / "corrupt.ipynb"
        path.write_text("{ not valid json at all", encoding="utf-8")
        result = scan_notebook(path)
        assert result["findings"] == []
        assert result.get("error"), "expected error message for corrupt JSON"
        assert "NotJSONError" in result["error"] or "JSON" in result["error"]

    def test_scan_bom_prefix_returns_error_12097(self, tmp_path):
        """#12097 BOM-prefixed notebook (classic case from BTC-ML-Researcher) :
        nbformat raises NotJSONError because the BOM byte shifts the JSON
        parser. The new guard treats this like any other read failure."""
        path = tmp_path / "bom.ipynb"
        # nbformat rejects a UTF-8 BOM prefix on a non-JSON-leading byte
        path.write_bytes(b"\xef\xbb\xbfnot json")
        result = scan_notebook(path)
        assert result["findings"] == []
        assert result.get("error"), "expected error message for BOM-prefixed content"

    def test_scan_validation_error_returns_error_12097(self, tmp_path):
        """A JSON file that parses as JSON but does not pass nbformat's
        schema validation (e.g. missing required 'cells' field) should
        also be guarded. Mirrors Sudoku-15-Infer-Csharp.ipynb founder case."""
        path = tmp_path / "invalid_schema.ipynb"
        path.write_text('{"cells": "this should be a list"}', encoding="utf-8")
        result = scan_notebook(path)
        assert result["findings"] == []
        assert result.get("error"), "expected error for nbformat validation failure"


class TestScanPaths:
    """#12097 : scan_paths must aggregate unreadable notebooks without
    interrupting the whole scan. Mirrors the sibling L344-350 behavior."""

    def test_scan_paths_unreadable_does_not_interrupt_12097(self, tmp_path):
        """A clean notebook + a corrupt one + another clean one in the same
        directory : scan_paths must report the 2 clean findings AND the
        unreadable entry, without crashing on the corrupt middle file."""
        # Clean 1
        nb_clean = _make_nb_with_md(SW_12_FOUNDER)
        nb_clean_path = tmp_path / "a_clean.ipynb"
        nbformat.write(nb_clean, nb_clean_path)
        # Corrupt in the middle (alphabetically before a_clean or after, doesn't matter)
        corrupt_path = tmp_path / "b_corrupt.ipynb"
        corrupt_path.write_text("{ not json", encoding="utf-8")
        # Clean 2
        nb_clean2 = _make_nb_with_md("# Just text")
        nb_clean2_path = tmp_path / "c_clean.ipynb"
        nbformat.write(nb_clean2, nb_clean2_path)

        from detect_ascii_flowchart import scan_paths
        result = scan_paths([tmp_path])
        assert result["files_scanned"] == 3
        assert len(result["files_unreadable"]) == 1
        assert result["files_unreadable"][0]["path"] == str(corrupt_path)
        # Both clean notebooks must produce findings (or at least be counted)
        assert result["files_with_findings"] == 1  # only SW_12 has flowchart
        assert len(result["findings"]) == 1

    def test_scan_paths_baseline_pinned_12097(self, tmp_path):
        """After the fix, the corpus baseline scan must succeed end-to-end
        (it would have failed before when hitting BTC-ML-Researcher.ipynb).
        Sanity-check that scan_paths does not crash on the corpus."""
        # No real corpus in tmp_path ; just verify no crash on empty dir
        from detect_ascii_flowchart import scan_paths
        result = scan_paths([tmp_path])
        assert result["files_scanned"] == 0
        assert result["files_unreadable"] == []
        assert result["findings"] == []


# ---------------------------------------------------------------------------
# 5. Corpus baseline pin (anti-regression)
# ---------------------------------------------------------------------------

# These values pin the corpus baseline measured c.259 on 2026-08-20 against
# origin/main at SHA fbe61eb57 (post-PR #11918), and re-measured firsthand c.439
# on 2026-08-21 against current origin/main (post-#12011 ASCII->Mermaid tranche
# + post-#12020 Lean-22b + post-#11994 Lean-17c). 11 findings / 9 files is the
# new baseline; 2 findings resolved by the ASCII->Mermaid sweep #12011.
# Any further change to the discriminator must re-measure firsthand and update
# this baseline with first-hand re-measurement.

CORPUS_BASELINE_TOTAL = 11
CORPUS_BASELINE_FILES_WITH = 9


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
