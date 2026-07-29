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

import io
import json
import sys
from pathlib import Path

import pytest

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

    def test_fullwidth_form_not_in_leak_class(self):
        # #8826: Halfwidth/Fullwidth forms (＀-￯) are EXCLUDED from the leak
        # detector -- typographic ASCII variants (fullwidth colon ：U+FF1A,
        # logical-not ￢ U+FFE2), not Chinese WORDS. The #8428 residue class is
        # unified ideographs + kana. `largeur：50` (fullwidth colon) is therefore
        # NOT flagged: including ＀-￯ inverted signal/noise (logic slides ￢,
        # regex ：) -- none of the 7 measured leaks uses fullwidth.
        assert mod.detect_cell("largeur：50") is None
        # Sanity: a fullwidth char adjacent to a REAL ideograph leak still flags
        # (the ideograph is the residue, the fullwidth is incidental).
        assert mod.detect_cell("largeur 风：50") is not None

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
        assert out["scanned"] == 1
        assert rc == 0  # --json without --check does not fail


# ===========================================================================
# #8829 review -- --stdin: decide the leak verdict on the PR's changed files
# only (``git diff --name-only`` input), so the label attributes to the PR that
# introduced the leak -- not to every PR while main carries pre-existing residue
# in files the PR never touched.
# ===========================================================================


class TestStdinMode:
    """--stdin reads paths from stdin and scans only those (the PR diff), not
    the whole fleet. Non-scannable extensions (.yml/.json) are skipped."""

    def test_stdin_scans_only_listed_files(self, tmp_path, monkeypatch, capsys):
        dirty = tmp_path / "leak.md"
        dirty.write_text("# volume plus均匀ément distribue\n", encoding="utf-8")
        clean = tmp_path / "ok.py"
        clean.write_text("x = 1\n", encoding="utf-8")
        monkeypatch.setattr(sys, "stdin", io.StringIO(f"{dirty}\n{clean}\n"))
        rc = mod.main(["--root", str(tmp_path), "--stdin", "--json"])
        out = json.loads(capsys.readouterr().out)
        assert rc == 0  # --json without --check never fails
        assert out["total_hits"] == 1  # only the dirty .md leaks
        assert out["scanned"] == 2  # both files scanned (dirty + clean)

    def test_stdin_skips_non_scannable_extensions(self, tmp_path, monkeypatch, capsys):
        # A .yml in the diff (e.g. this workflow editing itself) is NOT Latin
        # prose -- scanning it could false-positive on a legit CJK entry. It is
        # filtered out before scanning, so its CJK never reaches the results.
        yml = tmp_path / "workflow.yml"
        yml.write_text("name: 风险管理 demo\n", encoding="utf-8")
        dirty = tmp_path / "leak.md"
        dirty.write_text("# est拥挤 ici\n", encoding="utf-8")
        monkeypatch.setattr(sys, "stdin", io.StringIO(f"{yml}\n{dirty}\n"))
        rc = mod.main(["--root", str(tmp_path), "--stdin", "--json"])
        out = json.loads(capsys.readouterr().out)
        assert rc == 0
        assert out["total_hits"] == 1  # the .md only; .yml skipped entirely
        assert out["scanned"] == 1

    def test_stdin_check_exits_1_when_diff_carries_leak(self, tmp_path, monkeypatch):
        dirty = tmp_path / "leak.md"
        dirty.write_text("# de重建 needed\n", encoding="utf-8")
        monkeypatch.setattr(sys, "stdin", io.StringIO(f"{dirty}\n"))
        rc = mod.main(["--root", str(tmp_path), "--stdin", "--check"])
        assert rc == 1

    def test_stdin_check_exits_0_on_clean_diff(self, tmp_path, monkeypatch):
        clean = tmp_path / "ok.py"
        clean.write_text("print('bonjour')\n", encoding="utf-8")
        monkeypatch.setattr(sys, "stdin", io.StringIO(f"{clean}\n"))
        rc = mod.main(["--root", str(tmp_path), "--stdin", "--check"])
        assert rc == 0

    # #8846 -- --stdin must apply SKIP_DIRS (parity with the fleet mode that
    # already skips them at L374/L140), else a PR that merely touches
    # docs/archive/** inherits a cjk-residue label for pre-existing residue the
    # PR never introduced. Acceptance criterion of #8846: a SKIP_DIRS path
    # passed to --stdin must yield 0 hit. This test is RED on the unfixed code
    # (the detector scanned it -- 1 hit), GREEN after the parity fix.
    def test_stdin_skips_archive_paths(self, tmp_path, monkeypatch, capsys):
        # `archive` is a canonical SKIP_DIRS member (#8650): pedagogical archives
        # are not ours to fix, so a leak there is never attributed to a PR diff.
        # git diff --name-only emits repo-relative forward-slash paths.
        archived = tmp_path / "archive" / "leak.md"
        archived.parent.mkdir(parents=True)
        archived.write_text("# pre-existing均匀ément residue\n", encoding="utf-8")
        monkeypatch.setattr(
            sys, "stdin",
            io.StringIO(f"{archived.relative_to(tmp_path).as_posix()}\n"),
        )
        rc = mod.main(["--root", str(tmp_path), "--stdin", "--json"])
        out = json.loads(capsys.readouterr().out)
        assert rc == 0
        assert out["total_hits"] == 0   # the archive leak is NOT attributed
        assert out["scanned"] == 0      # ...and not even counted as scanned

    def test_stdin_skips_other_skip_dirs_members(self, tmp_path, monkeypatch, capsys):
        # Parity must hold for every SKIP_DIRS member, not just `archive`.
        # `_archives` (plural) is a distinct canonical member (#8650).
        archived = tmp_path / "_archives" / "leak.py"
        archived.parent.mkdir(parents=True)
        archived.write_text("# de重建 residue\n", encoding="utf-8")
        monkeypatch.setattr(
            sys, "stdin",
            io.StringIO(f"{archived.relative_to(tmp_path).as_posix()}\n"),
        )
        rc = mod.main(["--root", str(tmp_path), "--stdin", "--json"])
        out = json.loads(capsys.readouterr().out)
        assert rc == 0
        assert out["total_hits"] == 0
        assert out["scanned"] == 0

    # #8858 -- the SKIP_DIRS check must operate on the path RELATIVE to the repo
    # root, not on the absolute parts. `p` is absolutised (`p = root / p`), so if
    # the repo itself is cloned UNDER a SKIP_DIRS member (`archive`, `worktrees`,
    # ...), the absolute parts matched and the --stdin scan returned 0 hit on the
    # ENTIRE diff -- a total silence worse than #8846's false accusation. Here the
    # repo root sits under an `archive/` parent; a leaking .md INSIDE the repo
    # (not under an archive subdir) must still be detected. RED on the unfixed
    # code (0 hit), GREEN after the fix.
    def test_stdin_detects_leak_when_repo_under_skipdir_parent(self, tmp_path, monkeypatch, capsys):
        # The repo root lives UNDER a directory named `archive` (a canonical
        # SKIP_DIRS member): the parent's name must NOT silence leaks inside.
        repo = tmp_path / "archive" / "repo"
        dirty = repo / "leak.md"
        dirty.parent.mkdir(parents=True)
        dirty.write_text("# volume plus均匀ément distribue\n", encoding="utf-8")
        # git diff --name-only emits repo-relative forward-slash paths.
        monkeypatch.setattr(
            sys, "stdin",
            io.StringIO(f"{dirty.relative_to(repo).as_posix()}\n"),
        )
        rc = mod.main(["--root", str(repo), "--stdin", "--json"])
        out = json.loads(capsys.readouterr().out)
        assert rc == 0
        assert out["total_hits"] == 1   # the leak INSIDE the repo IS detected
        assert out["scanned"] == 1


# ===========================================================================
# #8826 -- discriminating guard: CJK soldered into/dropped into Latin = leak;
# pure-CJK (backticked term, quoted fixture, CJK-only line) = legit. The guard
# must invert the signal/noise ratio: the 7 measured leaks are the POSITIVE
# control; the legit multilingual/functional CJK is the NEGATIVE control.
# ===========================================================================


class TestDiscriminator:
    """Unit tests for classify_cjk_leaks -- the #8826 scope-mixed rule."""

    def test_soldered_cjk_latin_is_leak(self):
        # CJK directly adjacent to a Latin letter, no separator (均匀ément).
        leaks = mod.classify_cjk_leaks("volume plus均匀ément distribue")
        assert leaks, "soldered CJK+Latin must be a leak"
        assert "均" in leaks[0]["glyphs"]

    def test_latin_cjk_soldered_other_direction(self):
        # Latin immediately before CJK (de重建).
        leaks = mod.classify_cjk_leaks("Necessite de重建 l'environnement")
        assert leaks
        assert "重" in leaks[0]["glyphs"]

    def test_mid_latin_phrase_is_leak(self):
        # A CJK run dropped into an otherwise-Latin line, spaces around it
        # (可能性が高い = "fort probablement" in JP, in a French sentence).
        leaks = mod.classify_cjk_leaks("G.1 n'a pas detecte —可能性が高い c'est (1)")
        assert leaks
        assert any("可" in lk["glyphs"] for lk in leaks)

    def test_pure_cjk_backtick_span_is_legit(self):
        # A backticked CJK term in a Latin line is NOT a leak (`` `风险管理` ``).
        leaks = mod.classify_cjk_leaks("See `风险管理` (risk management) for details.")
        assert leaks == [], "pure-CJK backtick span in a Latin line is legit"

    def test_mixed_backtick_span_is_leak(self):
        # A backtick span that MIXES CJK+Latin (`` `dataset支撑` ``) is a leak:
        # the CJK is a corrupted Latin word, even though backticked. This is why
        # files that DOCUMENT leak examples (detector, README, tests) need ALLOWED.
        leaks = mod.classify_cjk_leaks("exemple typique: `dataset支撑` et `arbre de分支`")
        assert leaks, "mixed CJK+Latin span is a leak even inside backticks"


class TestLegitPureCjk:
    def test_pure_cjk_string_value_no_leak(self):
        leaks = mod.classify_cjk_leaks('prompt = "负面提示词"  # the negative prompt')
        assert leaks == [], "a pure-CJK quoted value (no Latin inside) is legit"

    def test_cjk_only_line_no_leak(self):
        # An integrally-CJK line (multilingual demo) -- no Latin letters at all.
        leaks = mod.classify_cjk_leaks("こんにちは！多言語音声合成のデモンストレーションです。")
        assert leaks == [], "a CJK-only line is legit (no Latin to intrude into)"

    def test_fenced_code_block_cjk_skipped(self):
        # CJK inside a ``` fence is config/output, not prose -- skipped.
        text = (
            "Intro line in French.\n"
            "```yaml\n"
            "prompt: 风险管理 is not residue here\n"
            "```\n"
            "Outro in French.\n"
        )
        leaks = mod.classify_cjk_leaks(text)
        assert leaks == [], "CJK inside a fenced code block is skipped"

    def test_fullwidth_logic_not_not_flagged(self):
        # ￢ (U+FFE2 fullwidth not) in a logic formula is NOT in the leak class.
        leaks = mod.classify_cjk_leaks("Ex: ￢B1,1 ∨ P1,2 (propositional logic)")
        assert leaks == [], "fullwidth logical-not is not CJK-word residue (#8826 narrowing)"


class TestLeakPatterns:
    """POSITIVE CONTROL (#8826 acceptance 4): the 7 measured leak patterns MUST
    be detected. These are the exact residues from the #8826 census (5 non-archive;
    the 2 docs/archive ones are the same class). A guard never seen to fire is not
    a guard (#8681)."""

    @pytest.mark.parametrize("phrase,glyph", [
        ("volume plus均匀ément distribue", "均"),      # ML-XGBoost README:70
        ("volume均等ément distribue", "均"),           # ML-XGBoost MANIFEST:139
        ("la zone supérieure est拥挤", "拥"),          # ML.Net MANIFEST:59
        ("Le rédacteur原始 ne pouvait pas", "原"),     # EMA-Cross MANIFEST:87
        ("Le rédacteur原始 ne pouvait pas", "原"),     # LongShortHarvest MANIFEST:119
        ("Necessite de重建 l'environnement", "重"),    # docs/archive RAPPORT (same class)
        ("—可能性が高い c'est (1)", "可"),              # docs/archive ledger (same class)
    ])
    def test_measured_leak_detected(self, phrase, glyph):
        leaks = mod.classify_cjk_leaks(phrase)
        assert leaks, f"expected leak in {phrase!r}"
        assert any(glyph in lk["glyphs"] for lk in leaks), (
            f"{glyph!r} not in leak glyphs for {phrase!r}")


class TestSourceFileScan:
    """#8826: the guard now covers .py/.md/.cs, not just .ipynb -- that is where
    #8823's `«经验 manquante»` lived (a .py), invisible to the ipynb-only scope."""

    def test_md_file_leak_detected(self, tmp_path):
        p = tmp_path / "README.md"
        p.write_text("# Titre\n\nLe volume plus均匀ément distribue.\n", encoding="utf-8")
        r = mod.scan_source_file(p, tmp_path)
        assert r["allowed"] is None
        assert len(r["hits"]) == 1
        assert r["hits"][0]["lineno"] == 3

    def test_py_file_pure_cjk_string_no_hit(self, tmp_path):
        # A pure-CJK string literal in a .py is legit (no Latin in the span).
        p = tmp_path / "x.py"
        p.write_text('prompt = "负面提示词"\n', encoding="utf-8")
        r = mod.scan_source_file(p, tmp_path)
        assert r["hits"] == []

    def test_py_file_soldered_leak_detected(self, tmp_path):
        # #8823 class: a corrupted French word in a .py comment/string.
        p = tmp_path / "learned_valence.py"
        p.write_text("# 经验 manquante -- should be 'expérience'\n", encoding="utf-8")
        r = mod.scan_source_file(p, tmp_path)
        assert len(r["hits"]) == 1
        assert r["hits"][0]["lineno"] == 1

    def test_allowed_source_file_skipped(self, tmp_path):
        # The detector's own ALLOWED path is skipped (irreducible legit).
        nbtools = tmp_path / "scripts" / "notebook_tools"
        nbtools.mkdir(parents=True)
        p = nbtools / "detect_cjk_residue.py"
        p.write_text("# docstring cites `dataset支撑` as the leak example\n", encoding="utf-8")
        r = mod.scan_source_file(p, tmp_path)
        assert r["allowed"] is not None
        assert r["hits"] == []

    def test_main_check_source_file_exits_1(self, tmp_path, capsys):
        p = tmp_path / "dirty.md"
        p.write_text("prose with 原始 leak\n", encoding="utf-8")
        rc = mod.main(["--root", str(tmp_path), str(p), "--check"])
        assert rc == 1
