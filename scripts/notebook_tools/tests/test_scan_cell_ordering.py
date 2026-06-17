"""Tests for scripts/notebook_tools/scan_cell_ordering.py.

Lock in the FP-hardening of the cell-ordering / enchainement scanner (#3240):
legitimate numbering (increment, sub-section open/close, reset-to-1, level-mixed
titles, fenced-code comments, TOC cells) must stay SILENT, while genuine
backwards jumps must be flagged HIGH.
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from scan_cell_ordering import (  # noqa: E402
    head_tail,
    _lines,
    scan_section_order,
    scan_exercise_order,
    scan_enchainement,
    scan_consecutive_code,
    scan_notebook,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _code(source: str) -> dict:
    return {"cell_type": "code", "source": [source], "execution_count": 1, "outputs": []}


def _md(source: str) -> dict:
    return {"cell_type": "markdown", "source": [source]}


def _cats(findings: list[dict]) -> set[str]:
    return {f["category"] for f in findings}


# ---------------------------------------------------------------------------
# _lines / head_tail
# ---------------------------------------------------------------------------

class TestLines:
    def test_drops_fenced_code_block(self):
        src = "## 2. Titre\n```bash\n# 1. step\n# 2. step\n```\nprose"
        lines = _lines(src)
        assert "## 2. Titre" in lines
        assert "# 1. step" not in lines  # inside fence -> dropped
        assert "prose" in lines

    def test_tilde_fence_also_dropped(self):
        src = "intro\n~~~\n# 1. not a header\n~~~\nafter"
        assert "# 1. not a header" not in _lines(src)


class TestHeadTail:
    def test_head_tail_basic(self):
        head, tail = head_tail("line1\nline2\nline3\nline4", n=2)
        assert head == ["line1", "line2"]
        assert tail == ["line3", "line4"]

    def test_skips_blank_lines(self):
        head, tail = head_tail("\n\nfirst\n\nlast\n\n", n=1)
        assert head == ["first"]
        assert tail == ["last"]

    def test_empty_cell_returns_empty(self):
        head, tail = head_tail("   \n\n  ", n=2)
        assert head == []
        assert tail == []


# ---------------------------------------------------------------------------
# scan_section_order
# ---------------------------------------------------------------------------

class TestSectionOrder:
    def test_clean_ascending(self):
        cells = [_md("## 1. A"), _md("## 2. B"), _md("## 3. C")]
        assert scan_section_order(cells) == []

    def test_backwards_jump_flagged_high(self):
        cells = [_md("## 2. B"), _md("## 3. C"), _md("## 2. oops")]
        findings = scan_section_order(cells)
        assert len(findings) == 1
        assert findings[0]["category"] == "SECTION_ORDER"
        assert findings[0]["severity"] == "HIGH"

    def test_subsection_open_and_close_silent(self):
        cells = [_md("## 3. A"), _md("### 3.1 a"), _md("### 3.2 b"), _md("## 4. B")]
        assert scan_section_order(cells) == []

    def test_reset_to_one_is_new_group(self):
        cells = [_md("## 1. A"), _md("## 2. B"), _md("## 1. new part"), _md("## 2. more")]
        assert scan_section_order(cells) == []

    def test_gap_is_low_not_high(self):
        cells = [_md("## 1. A"), _md("## 3. C")]
        findings = scan_section_order(cells)
        assert len(findings) == 1
        assert findings[0]["category"] == "SECTION_GAP"
        assert findings[0]["severity"] == "LOW"

    def test_level_mixed_title_not_a_regression(self):
        # "# 13." is the notebook H1 series title; "## 0.", "## 1." are H2 sections.
        cells = [_md("# 13. Series Title"), _md("## 0. Setup"), _md("## 1. First")]
        assert scan_section_order(cells) == []

    def test_fenced_bash_comments_not_headers(self):
        cells = [
            _md("## 2. Install\n```bash\n# 1. apt update\n# 4. done\n```"),
            _md("## 3. Next"),
        ]
        assert scan_section_order(cells) == []


# ---------------------------------------------------------------------------
# scan_exercise_order
# ---------------------------------------------------------------------------

class TestExerciseOrder:
    def test_clean_ascending(self):
        cells = [_md("### Exercice 1 : a"), _md("### Exercice 2 : b"), _md("### Exercice 3 : c")]
        assert scan_exercise_order(cells) == []

    def test_backwards_flagged_high(self):
        cells = [_md("### Exercice 1 : a"), _md("### Exercice 3 : c"), _md("### Exercice 2 : b")]
        findings = scan_exercise_order(cells)
        assert len(findings) == 1
        assert findings[0]["category"] == "EXERCISE_ORDER"
        assert findings[0]["severity"] == "HIGH"

    def test_toc_cell_skipped(self):
        # A single cell listing >=2 labels = overview/TOC -> not a sequence point.
        cells = [
            _md("## Sommaire\n- Exercice 2 : a\n- Exercice 3 : b\n- Exercice 4 : c"),
            _md("### Exercice 2 : a"),
            _md("### Exercice 3 : b"),
            _md("### Exercice 4 : c"),
        ]
        assert scan_exercise_order(cells) == []

    def test_prose_mention_not_counted(self):
        # "exercice 3" buried in an Indice line must NOT be taken for a label.
        cells = [
            _md("### Exercice 1 : a"),
            _md("### Exercice 2 : b\n**Indice** : revoyez l'exercice 3 plus loin."),
            _md("### Exercice 3 : c"),
        ]
        assert scan_exercise_order(cells) == []

    def test_exercices_and_exemples_separate_sequences(self):
        cells = [
            _md("### Exemple 1 : guided"),
            _md("### Exercice 1 : todo"),
            _md("### Exemple 2 : guided"),
            _md("### Exercice 2 : todo"),
        ]
        assert scan_exercise_order(cells) == []


# ---------------------------------------------------------------------------
# scan_enchainement
# ---------------------------------------------------------------------------

class TestEnchainement:
    def test_dangling_intro_flagged(self):
        cells = [_md("Voici le code ci-dessous :"), _md("not code")]
        findings = scan_enchainement(cells)
        assert "DANGLING_INTRO" in _cats(findings)

    def test_announce_then_code_is_fine(self):
        cells = [_md("Voici le code ci-dessous :"), _code("x = 1")]
        assert "DANGLING_INTRO" not in _cats(scan_enchainement(cells))

    def test_imperative_without_colon_no_codenoun_silent(self):
        # General prose with an imperative verb but no colon and no code-noun.
        cells = [_md("Nous implementons les concepts a la main."), _md("more prose")]
        assert "DANGLING_INTRO" not in _cats(scan_enchainement(cells))

    def test_interp_before_code_flagged(self):
        cells = [_md("On observe que la perte diminue."), _code("plot(loss)")]
        findings = scan_enchainement(cells)
        assert "INTERP_BEFORE_CODE" in _cats(findings)

    def test_interp_after_code_is_fine(self):
        cells = [_code("plot(loss)"), _md("On observe que la perte diminue.")]
        assert "INTERP_BEFORE_CODE" not in _cats(scan_enchainement(cells))


# ---------------------------------------------------------------------------
# scan_consecutive_code
# ---------------------------------------------------------------------------

class TestConsecutiveCode:
    def test_three_or_fewer_ok(self):
        cells = [_code("a"), _code("b"), _code("c")]
        assert scan_consecutive_code(cells) == []

    def test_more_than_threshold_flagged_low(self):
        cells = [_code("a"), _code("b"), _code("c"), _code("d")]
        findings = scan_consecutive_code(cells)
        assert len(findings) == 1
        assert findings[0]["category"] == "CONSECUTIVE_CODE"
        assert findings[0]["severity"] == "LOW"

    def test_markdown_resets_streak(self):
        cells = [_code("a"), _code("b"), _md("break"), _code("c"), _code("d")]
        assert scan_consecutive_code(cells) == []


# ---------------------------------------------------------------------------
# scan_notebook (file level)
# ---------------------------------------------------------------------------

class TestScanNotebook:
    def test_clean_notebook(self, tmp_path):
        p = tmp_path / "clean.ipynb"
        nb = {"cells": [_md("## 1. A"), _code("x = 1"), _md("## 2. B")],
              "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
        p.write_text(json.dumps(nb), encoding="utf-8")
        assert scan_notebook(p)["findings"] == []

    def test_backwards_notebook_flagged(self, tmp_path):
        p = tmp_path / "bad.ipynb"
        nb = {"cells": [_md("## 2. A"), _md("## 3. B"), _md("## 2. oops")],
              "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
        p.write_text(json.dumps(nb), encoding="utf-8")
        findings = scan_notebook(p)["findings"]
        assert any(f["category"] == "SECTION_ORDER" for f in findings)

    def test_invalid_json_returns_error(self, tmp_path):
        p = tmp_path / "broken.ipynb"
        p.write_text("{not valid json", encoding="utf-8")
        result = scan_notebook(p)
        assert "error" in result
        assert result["findings"] == []
