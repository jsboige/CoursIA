"""Tests for scripts/notebook_tools/detect_cjk_residue.py — CJK residue regression guard.

Why this test file exists
---------------------------------
`detect_cjk_residue.py` is the regression-guard that closes defect fleet-wide #8428
(LLM-translation residue: Chinese words inserted mid French/English prose during
notebook generation/enrichment). After the manual sweep (8 PRs on 2026-07-25:
#8430/#8433/#8434/#8437/#8455/#8461/#8465/#8523 eliminated every residual), this
detector watches that the reservoir does not silently refill.

The detection half is formally tested here. Four clusters, mirroring the
detector's documented contract (docstring):

  1. TestDetectCell      -- CJK glyph detection in markdown + code sources
  2. TestAllowlist        -- legitimate multilingual demo + known gated residual skipped
  3. TestScanNotebook     -- end-to-end nb read + allowed short-circuit + hit report
  4. TestMainExitCodes    -- --check exit contract (0 clean / 1 residue / 2 error)

Test data design: positives use the exact residue phrases from #8428
(`风险管理`, `胜利=1`, `分布式约束优化`, `dataset支撑`); negatives exercise the
documented allowlist (Audio TTS JP demo) and clean French/English prose.

The baseline validated c.884 on 937 pedagogical notebooks is **0 unexpected hits**
(fleet clean post-sweep). These tests pin the contract so a future regression
(CJK residue re-introduced by an enrichment pass) is caught before commit.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

# Make the sibling detector importable regardless of invocation cwd.
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import detect_cjk_residue as mod  # noqa: E402


# ---------- helpers ----------
def _nb(cells):
    """Build a minimal nbformat 4 notebook from a list of (cell_type, source_str)."""
    return {
        "cells": [
            {"cell_type": ct, "source": [src] if isinstance(src, str) else src,
             "metadata": {}, "outputs": [] if ct == "code" else None}
            for ct, src in cells
        ],
        "metadata": {},
        "nbformat": 4, "nbformat_minor": 5,
    }


def _write_nb(tmp_path: Path, name: str, cells) -> Path:
    p = tmp_path / name
    p.write_text(json.dumps(_nb(cells)), encoding="utf-8")
    return p


# ---------- 1. TestDetectCell ----------
class TestDetectCell:
    def test_markdown_chinese_phrase_detected(self):
        finding = mod.detect_cell("La 风险管理 est un concept cle (risk management).")
        assert finding is not None
        assert finding["count"] >= 4  # 风险管理 = 4 glyphs
        assert "风" in finding["glyphs"]

    def test_code_comment_victory_residue(self):
        # App-12 #8523 canonical residue: 胜利=1
        finding = mod.detect_cell("int utility() { return 胜利=1; } //胜利")
        assert finding is not None
        assert "胜" in finding["glyphs"]
        # return 胜利=1 (2) + //胜利 comment (2) = 4 glyph occurrences; 2 distinct.
        assert finding["count"] == 4
        # sorted by codepoint: 利 (U+5229) < 胜 (U+80DC)
        assert finding["glyphs"] == ["利", "胜"]

    def test_fullwidth_form_detected(self):
        finding = mod.detect_cell("largeur：50")  # fullwidth colon ＀-￯ range
        assert finding is not None

    def test_clean_french_prose_no_hit(self):
        assert mod.detect_cell("L'optimisation de contraintes distribuées.") is None

    def test_clean_english_prose_no_hit(self):
        assert mod.detect_cell("Distributed constraint optimization.") is None

    def test_context_window_returned(self):
        finding = mod.detect_cell("prefix texte 分布式约束优化 suffix")
        assert finding is not None
        assert "prefix" in finding["context"]
        assert "suffix" in finding["context"]

    def test_empty_source_no_hit(self):
        assert mod.detect_cell("") is None
        assert mod.detect_cell("   \n  ") is None


# ---------- 2. TestAllowlist ----------
class TestAllowlist:
    def test_audio_tts_demo_allowed(self):
        reason = mod._is_allowed("MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-8-Expressive-TTS.ipynb")
        assert reason is not None
        assert "TTS" in reason or "multilingue" in reason

    def test_texte_multilingual_allowed(self):
        reason = mod._is_allowed("MyIA.AI.Notebooks/GenAI/Texte/9_Production_Patterns.ipynb")
        assert reason is not None
        assert "multilingue" in reason.lower() or "mandarin" in reason.lower()

    def test_qcpy03_no_longer_allowed(self):
        # QC-Py-Cloud-03 was FALSELY allowlisted as "needs QC-Cloud re-exec" (it is local
        # Python, no QuantBook). The 简化 residue was fixed by local re-exec in #8553, so the
        # gated-residual allowlist entry is removed — the notebook must NOT be skipped now.
        reason = mod._is_allowed("MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-03-Risk-Parity.ipynb")
        assert reason is None

    def test_random_notebook_not_allowed(self):
        assert mod._is_allowed("MyIA.AI.Notebooks/ML/Some-Notebook.ipynb") is None


# ---------- 3. TestScanNotebook ----------
class TestScanNotebook:
    def test_scan_finds_cjk_in_markdown_cell(self, tmp_path):
        p = _write_nb(tmp_path, "NB.ipynb", [
            ("markdown", "# Titre\n\nProse avec 分布式约束优化 residu."),
            ("code", "x = 1"),
        ])
        r = mod.scan_notebook(p, tmp_path)
        assert r["allowed"] is None
        assert len(r["hits"]) == 1
        assert r["hits"][0]["cell_index"] == 0
        assert r["hits"][0]["cell_type"] == "markdown"

    def test_scan_finds_cjk_in_code_cell(self, tmp_path):
        p = _write_nb(tmp_path, "NB.ipynb", [
            ("markdown", "# Clean"),
            ("code", "def f(): return 胜利  # dataset支撑"),
        ])
        r = mod.scan_notebook(p, tmp_path)
        assert len(r["hits"]) == 1
        assert r["hits"][0]["cell_type"] == "code"

    def test_scan_allowed_notebook_skipped_zero_hits(self, tmp_path):
        # Notebook whose path matches the Audio TTS allowlist entry carries CJK
        # but is skipped (legitimate multilingual demo).
        tts_dir = tmp_path / "GenAI" / "Audio" / "02-Advanced"
        tts_dir.mkdir(parents=True)
        p = tts_dir / "02-8-Expressive-TTS.ipynb"
        p.write_text(json.dumps(_nb([("code", "print('こんにちは！多言語音声合成')")])), encoding="utf-8")
        r = mod.scan_notebook(p, tmp_path)
        assert r["allowed"] is not None
        assert r["hits"] == []

    def test_scan_clean_notebook_zero_hits(self, tmp_path):
        p = _write_nb(tmp_path, "NB.ipynb", [("markdown", "# Propre"), ("code", "x = 1")])
        r = mod.scan_notebook(p, tmp_path)
        assert r["hits"] == []
        assert r["allowed"] is None


# ---------- 4. TestMainExitCodes ----------
class TestMainExitCodes:
    def test_check_clean_notebook_exits_0(self, tmp_path, capsys):
        p = _write_nb(tmp_path, "Clean.ipynb", [("markdown", "# Sans CJK")])
        rc = mod.main(["--root", str(tmp_path), str(p), "--check"])
        assert rc == 0

    def test_check_residue_notebook_exits_1(self, tmp_path, capsys):
        p = _write_nb(tmp_path, "Dirty.ipynb", [("markdown", "# Avec 风险管理 residu")])
        rc = mod.main(["--root", str(tmp_path), str(p), "--check"])
        assert rc == 1

    def test_missing_notebook_exits_2(self, tmp_path):
        rc = mod.main(["--root", str(tmp_path), str(tmp_path / "nope.ipynb")])
        assert rc == 2

    def test_json_output_structure(self, tmp_path, capsys):
        p = _write_nb(tmp_path, "Dirty.ipynb", [("code", "x = 胜利")])
        rc = mod.main(["--root", str(tmp_path), str(p), "--json"])
        out = json.loads(capsys.readouterr().out)
        assert out["total_hits"] == 1
        assert out["notebooks_scanned"] == 1
        assert rc == 0  # --json without --check does not fail
