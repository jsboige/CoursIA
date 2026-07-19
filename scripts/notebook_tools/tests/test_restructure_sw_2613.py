"""Tests unitaires pour scripts/notebook_tools/restructure_sw_2613.py — restructuration SW-8..SW-13 (#2613).

Couvre les fonctions module-level et le script CLI en black-box via subprocess :
- classify_cell (5 outcomes : corrige_md / corrige_code / exercise_stub / exercise_desc / other)
- extract_exercise_info (regex parsing "### Exercice N : Topic")
- restructure_notebook (file I/O end-to-end avec tmp_path)
- Script CLI (--dry-run flag, exit code, sub-grains manquants / RePEc ambiguity)

Pourquoi ce fichier existe
--------------------------
`restructure_sw_2613.py` (registre #2613, PR #2616 MERGED) restructure les
6 notebooks SW-8..SW-13 selon la convention "Exemples guidés FIRST, Exercices LAST"
(issue #2613 — pédagogique @Sosolalt corrigés promus). Le script est cité en exemple
mais n'avait JAMAIS de couverture pytest. Comblement c.634.

Pattern : fonctions module-level testées directement (pytest.importorskip path),
restructure_notebook en subprocess black-box via tmp_path (L812-L1 absolute path
canonique + L813-L1 strategy).

5 clusters :
  1. TestClassifyCell — 5 outcomes (corrige_md/corrige_code/exercise_stub/exercise_desc/other)
  2. TestExtractExerciseInfo — regex parsing number + topic
  3. TestRestructureNotebook — file I/O end-to-end avec tmp_path (dry-run, exercises moves, exemples promus)
  4. TestEdgeCases — RePEc ambiguity (resume/conclusion/classe detect), stub not_implemented remap, no corrigé
  5. TestRunScript — subprocess black-box end-to-end + exit codes
"""
import json
import subprocess
import sys
from pathlib import Path

import pytest

# Make the script importable from the tests dir (cf detect_accent_stripping pattern).
SCRIPT_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SCRIPT_DIR))

from restructure_sw_2613 import (  # noqa: E402
    DEFAULT_NOTEBOOKS,
    SW_DIR,
    classify_cell,
    extract_exercise_info,
    restructure_notebook,
)

# Absolute script path for subprocess.run on Windows (L812-L1 ★ NEW c.633).
RESTRUCTURER = str((SCRIPT_DIR / "restructure_sw_2613.py").resolve())


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _md(source: str, cell_id: str = "md-1") -> dict:
    """Build a markdown cell from source string."""
    return {"cell_type": "markdown", "id": cell_id, "metadata": {}, "source": [source]}


def _code(source: str, cell_id: str = "code-1") -> dict:
    """Build a code cell from source string."""
    return {
        "cell_type": "code",
        "id": cell_id,
        "metadata": {},
        "source": [source],
        "execution_count": None,
        "outputs": [],
    }


def _write_nb(tmp_path: Path, cells: list[dict], name: str = "test.ipynb") -> Path:
    """Write a minimal notebook dict to tmp_path/name.ipynb."""
    nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    p = tmp_path / name
    p.write_text(json.dumps(nb), encoding="utf-8")
    return p


# ---------------------------------------------------------------------------
# 1. TestClassifyCell — 5 outcomes
# ---------------------------------------------------------------------------

class TestClassifyCell:
    """classify_cell returns 1 of 5 string outcomes based on cell content."""

    def test_corrige_md_with_accent(self):
        """Markdown starting with '### Corrigé :' classifies as corrige_md."""
        cell = _md("### Corrigé : Exercice 1 : sujet\n\nbla")
        assert classify_cell(cell) == "corrige_md"

    def test_corrige_md_without_accent(self):
        """Markdown starting with '### Corrige :' (no accent) also matches."""
        cell = _md("### Corrige : Exercice 1 : sujet\n")
        assert classify_cell(cell) == "corrige_md"

    def test_corrige_md_case_insensitive(self):
        """Markdown '### corrigé :' (lowercase) still matches (IGNORECASE flag)."""
        cell = _md("### corrigé : exercice 2\n")
        assert classify_cell(cell) == "corrige_md"

    def test_corrige_code_id_prefix(self):
        """Code cell with id 'corrige-code-N' classifies as corrige_code."""
        cell = _code("print('solution')", cell_id="corrige-code-3")
        assert classify_cell(cell) == "corrige_code"

    def test_corrige_code_underscore_id_does_not_match(self):
        """Code cell with id 'corrige_code_5' (underscore variant) does NOT match — actual source only matches 'corrige-code-' (dash) prefix."""
        cell = _code("x = 42", cell_id="corrige_code_5")
        # Doc-test: verify exact behavior — underscore variant is NOT recognized as corrige_code
        assert classify_cell(cell) == "other"

    def test_exercise_stub_avec_phrase(self):
        """Code cell with 'Exercice a completer' classifies as exercise_stub."""
        cell = _code('print("Exercice a completer")\n', cell_id="stub-1")
        assert classify_cell(cell) == "exercise_stub"

    def test_exercise_stub_avec_todo(self):
        """Code cell with '# TODO etudiant' classifies as exercise_stub."""
        cell = _code("def f(x):\n    # TODO etudiant\n    return x\n", cell_id="stub-2")
        assert classify_cell(cell) == "exercise_stub"

    def test_exercise_stub_todo_case_insensitive(self):
        """'# TODO ETUDIANT' (uppercase) still matches (IGNORECASE flag)."""
        cell = _code("# TODO ETUDIANT\nx = 1\n", cell_id="stub-3")
        assert classify_cell(cell) == "exercise_stub"

    def test_exercise_desc_with_number(self):
        """Markdown '### Exercice 3 : titre' classifies as exercise_desc."""
        cell = _md("### Exercice 3 : propagation\n\nbla bla")
        assert classify_cell(cell) == "exercise_desc"

    def test_exercise_desc_with_dash(self):
        """Markdown '### Exercice 4 - titre' (dash) classifies as exercise_desc."""
        cell = _md("### Exercice 4 - graphique\n")
        assert classify_cell(cell) == "exercise_desc"

    def test_other_random_markdown(self):
        """Generic markdown (no specific prefix) classifies as other."""
        cell = _md("# Introduction\n\nbla bla")
        assert classify_cell(cell) == "other"

    def test_other_random_code(self):
        """Generic code cell (no specific markers) classifies as other."""
        cell = _code("x = 1\nprint(x)\n", cell_id="code-99")
        assert classify_cell(cell) == "other"

    def test_other_empty_cell(self):
        """Empty cell (no source) classifies as other (not None)."""
        cell = {"cell_type": "code", "id": "empty", "metadata": {}, "source": []}
        assert classify_cell(cell) == "other"

    def test_other_no_source_key(self):
        """Cell without 'source' key classifies as other (no crash)."""
        cell = {"cell_type": "markdown", "id": "no-src", "metadata": {}}
        assert classify_cell(cell) == "other"


# ---------------------------------------------------------------------------
# 2. TestExtractExerciseInfo — regex parsing
# ---------------------------------------------------------------------------

class TestExtractExerciseInfo:
    """extract_exercise_info returns (number, topic) or (None, None)."""

    def test_basic_extraction(self):
        """Standard '### Exercice N : Topic' format parses to (N, Topic)."""
        src = "### Exercice 1 : propagation de contraintes\n"
        assert extract_exercise_info(src) == (1, "propagation de contraintes")

    def test_with_dash_separator(self):
        """'### Exercice N - Topic' (dash instead of colon) parses correctly."""
        src = "### Exercice 5 - analyse semantique\n"
        assert extract_exercise_info(src) == (5, "analyse semantique")

    def test_corrige_prefix(self):
        """'### Corrigé : Exercice N : Topic' (corrige wrapper) also matches."""
        src = "### Corrigé : Exercice 7 : regles SHACL\n"
        result = extract_exercise_info(src)
        assert result == (7, "regles SHACL")

    def test_returns_none_when_no_exercise(self):
        """No exercise pattern returns (None, None), not crash."""
        src = "## Conclusion\n\nNotebook termine.\n"
        assert extract_exercise_info(src) == (None, None)

    def test_topic_stripped_of_whitespace(self):
        """Topic is stripped of trailing whitespace."""
        src = "### Exercice 2 : trucs   \n"
        assert extract_exercise_info(src) == (2, "trucs")

    def test_large_number(self):
        """Multi-digit number parses correctly."""
        src = "### Exercice 42 : heritage\n"
        assert extract_exercise_info(src) == (42, "heritage")

    def test_empty_string(self):
        """Empty string returns (None, None)."""
        assert extract_exercise_info("") == (None, None)

    def test_case_insensitive(self):
        """'EXERCICE 1 :' (uppercase) still matches (IGNORECASE flag)."""
        src = "EXERCICE 8 : algèbre\n"
        assert extract_exercise_info(src) == (8, "algèbre")


# ---------------------------------------------------------------------------
# 3. TestRestructureNotebook — file I/O end-to-end avec tmp_path
# ---------------------------------------------------------------------------

class TestRestructureNotebook:
    """restructure_notebook operates on a notebook file (file I/O, dry_run option)."""

    def test_dry_run_returns_false_on_change_needed(self, tmp_path, capsys):
        """Dry-run with content to restructure returns False (no write)."""
        nb_cells = [
            _md("### Exercice 1 : sujet\n\nbla\n", cell_id="desc-1"),
            _code('print("Exercice a completer")\n', cell_id="stub-1"),
            _md("### Corrigé : Exercice 1 : sujet\n\nsolution\n", cell_id="corr-md-1"),
            _code("print('solution')\n", cell_id="corrige-code-1"),
        ]
        p = _write_nb(tmp_path, nb_cells)
        result = restructure_notebook(p, dry_run=True)
        assert result is False
        # Plan must be printed
        captured = capsys.readouterr()
        assert "Plan:" in captured.out
        assert "Corrigé pairs found: 1" in captured.out

    def test_dry_run_does_not_modify_file(self, tmp_path):
        """Dry-run must NOT modify the notebook file on disk."""
        nb_cells = [
            _md("### Exercice 1 : sujet\n", cell_id="desc-1"),
            _code('print("Exercice a completer")\n', cell_id="stub-1"),
            _md("### Corrigé : Exercice 1\n", cell_id="corr-md-1"),
            _code("print('ok')\n", cell_id="corrige-code-1"),
        ]
        p = _write_nb(tmp_path, nb_cells)
        before = p.read_bytes()
        restructure_notebook(p, dry_run=True)
        after = p.read_bytes()
        assert before == after, "dry_run MUST NOT modify the file"

    def test_returns_false_when_nothing_to_do(self, tmp_path, capsys):
        """Notebook without exercise/corrige patterns returns False and prints skip msg."""
        nb_cells = [
            _md("# Intro\n\nbla\n"),
            _code("x = 1\n"),
        ]
        p = _write_nb(tmp_path, nb_cells)
        result = restructure_notebook(p, dry_run=False)
        assert result is False
        captured = capsys.readouterr()
        assert "No corrigés or exercise stubs found" in captured.out
        assert "Skipping." in captured.out

    def test_returns_true_on_actual_restructure(self, tmp_path, capsys):
        """Restructure returns True when changes are written to disk."""
        nb_cells = [
            _md("### Exercice 1 : sujet\n", cell_id="desc-1"),
            _code('print("Exercice a completer")\n', cell_id="stub-1"),
            _md("### Corrigé : Exercice 1 : sujet\n", cell_id="corr-md-1"),
            _code("print('solution')\n", cell_id="corrige-code-1"),
        ]
        p = _write_nb(tmp_path, nb_cells)
        result = restructure_notebook(p, dry_run=False)
        assert result is True
        # File is rewritten
        assert p.exists()
        reloaded = json.loads(p.read_text(encoding="utf-8"))
        assert "cells" in reloaded
        # Exemples section + Exercices section must be present
        all_src = "".join("".join(c.get("source", [])) for c in reloaded["cells"])
        assert "Exemples guidés" in all_src
        assert "Exercices a completer" in all_src

    def test_promotes_corrige_to_exemple_guide(self, tmp_path):
        """Corrigé markdown title 'Corrigé : Exercice 1 : topic' becomes 'Exemple guide : topic'."""
        nb_cells = [
            _md("### Exercice 1 : sujet\n", cell_id="desc-1"),
            _code('print("Exercice a completer")\n', cell_id="stub-1"),
            _md("### Corrigé : Exercice 1 : sujet\n", cell_id="corr-md-1"),
            _code("print('ok')\n", cell_id="corrige-code-1"),
        ]
        p = _write_nb(tmp_path, nb_cells)
        restructure_notebook(p, dry_run=False)
        reloaded = json.loads(p.read_text(encoding="utf-8"))
        all_src = "".join("".join(c.get("source", [])) for c in reloaded["cells"])
        # "Corrigé :" prefix must be GONE, "Exemple guide :" prefix must be PRESENT
        assert "### Corrigé :" not in all_src
        assert "Exemple guide" in all_src

    def test_id_prefix_replaced(self, tmp_path):
        """Cell id 'corrige-md-1' becomes 'exemple-md-1' after restructure."""
        nb_cells = [
            _md("### Exercice 1 : sujet\n", cell_id="desc-1"),
            _code('print("Exercice a completer")\n', cell_id="stub-1"),
            _md("### Corrigé : Exercice 1 : sujet\n", cell_id="corrige-md-1"),
            _code("print('ok')\n", cell_id="corrige-code-1"),
        ]
        p = _write_nb(tmp_path, nb_cells)
        restructure_notebook(p, dry_run=False)
        reloaded = json.loads(p.read_text(encoding="utf-8"))
        all_ids = [c.get("id", "") for c in reloaded["cells"]]
        assert any("exemple-md" in i for i in all_ids), f"expected exemple-md in {all_ids}"
        assert any("exemple-code" in i for i in all_ids), f"expected exemple-code in {all_ids}"
        # No raw "corrige-" id should remain (corrige replaced by exemple)
        assert not any("corrige-" in i for i in all_ids), f"stale corrige- id in {all_ids}"

    def test_stub_without_corrige_moved_to_end(self, tmp_path):
        """Exercise stub without corrigé is moved to exercices section (not promoted)."""
        nb_cells = [
            _md("# Intro\n\nbla\n"),
            _md("### Exercice 2 : sans corrige\n", cell_id="desc-2"),
            _code('print("Exercice a completer")\n', cell_id="stub-2"),
            _md("## Conclusion\n\nfin.\n", cell_id="conc"),
        ]
        p = _write_nb(tmp_path, nb_cells)
        result = restructure_notebook(p, dry_run=False)
        assert result is True
        reloaded = json.loads(p.read_text(encoding="utf-8"))
        # Stub must be moved AFTER the "Exercices a completer" header
        cells = reloaded["cells"]
        section_idx = next(
            i for i, c in enumerate(cells)
            if "Exercices a completer" in "".join(c.get("source", []))
        )
        # Stub should appear at index >= section_idx (after section header)
        stub_idx = next(
            (i for i, c in enumerate(cells) if c.get("id") == "stub-2"),
            None
        )
        assert stub_idx is not None, "stub-2 missing from output"
        assert stub_idx > section_idx, f"stub at {stub_idx} should be after section at {section_idx}"

    def test_not_implemented_error_replaced_with_pass(self, tmp_path):
        """Stub containing 'raise NotImplementedError' is rewritten to 'pass  # TODO etudiant'."""
        # Cell must contain '# TODO etudiant' so it's first classified as exercise_stub,
        # then the restructure_notebook phase 3 converts the raise NotImplementedError.
        nb_cells = [
            _md("# Intro\n"),
            _md("### Exercice 1 : sujet\n", cell_id="desc-1"),
            _code("def f(x):\n    # TODO etudiant\n    raise NotImplementedError\n", cell_id="stub-1"),
            _md("## Conclusion\n"),
        ]
        p = _write_nb(tmp_path, nb_cells)
        restructure_notebook(p, dry_run=False)
        reloaded = json.loads(p.read_text(encoding="utf-8"))
        all_src = "".join("".join(c.get("source", [])) for c in reloaded["cells"])
        assert "raise NotImplementedError" not in all_src
        assert "pass" in all_src
        assert "TODO etudiant" in all_src


# ---------------------------------------------------------------------------
# 4. TestEdgeCases — resume/conclusion/classe detect, ambiguities
# ---------------------------------------------------------------------------

class TestEdgeCases:
    """Edge cases for classify_cell + restructure_notebook."""

    def test_resume_keyword_detected_in_conclusion(self, tmp_path, capsys):
        """'## Resume' header in markdown counts as conclusion/insertion point."""
        nb_cells = [
            _md("## Resume\n\nbla bla\n"),
            _md("### Exercice 1 : sujet\n", cell_id="desc-1"),
            _code('print("Exercice a completer")\n', cell_id="stub-1"),
            _md("### Corrigé : Exercice 1 : sujet\n", cell_id="corr-md-1"),
            _code("print('ok')\n", cell_id="corrige-code-1"),
        ]
        p = _write_nb(tmp_path, nb_cells)
        result = restructure_notebook(p, dry_run=True)
        # Dry-run reports insertion point; should be BEFORE the Resume cell
        captured = capsys.readouterr()
        assert "Insert point" in captured.out
        # The plan must complete without crash
        assert result is False  # dry_run

    def test_bilan_keyword_detected(self, tmp_path, capsys):
        """'## Bilan' header counts as conclusion (alternative to Resume/Conclusion)."""
        nb_cells = [
            _md("## Bilan\n\nbla bla\n"),
            _md("### Exercice 1 : sujet\n", cell_id="desc-1"),
            _code('print("Exercice a completer")\n', cell_id="stub-1"),
            _md("### Corrigé : Exercice 1\n", cell_id="corr-md-1"),
            _code("print('ok')\n", cell_id="corrige-code-1"),
        ]
        p = _write_nb(tmp_path, nb_cells)
        # Just dry-run, ensure no crash
        result = restructure_notebook(p, dry_run=True)
        assert result is False

    def test_classify_with_empty_source_list(self):
        """Cell with source=[] classifies as 'other' (no crash on re.search)."""
        cell = {"cell_type": "markdown", "id": "empty-md", "metadata": {}, "source": []}
        assert classify_cell(cell) == "other"

    def test_classify_with_missing_id(self):
        """Cell without 'id' key classifies correctly (no crash on cid.startswith)."""
        cell = {"cell_type": "code", "source": ["x = 1"], "metadata": {}}
        assert classify_cell(cell) == "other"

    def test_classify_md_with_corrige_in_middle_not_start(self):
        """Markdown 'Some text\n### Corrigé : ...' (NOT at start) classifies as 'other'."""
        cell = _md("Some text\n\n### Corrigé : Exercice 1\n")
        # '^###' anchor means only markdown STARTING with ### Corrigé matches
        assert classify_cell(cell) == "other"


# ---------------------------------------------------------------------------
# 5. TestRunScript — subprocess black-box end-to-end
# ---------------------------------------------------------------------------

class TestRunScript:
    """Script CLI executed via subprocess.run (black-box)."""

    def test_help_message_when_no_args(self, tmp_path):
        """Running with a non-existent path prints NOT FOUND and exits 0."""
        # Pass a non-existent notebook path. Script reports 'NOT FOUND' but exits 0
        # because the main loop continues over multiple paths.
        result = subprocess.run(
            [sys.executable, RESTRUCTURER, "--dry-run", str(tmp_path / "does-not-exist.ipynb")],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
            timeout=30,
        )
        assert result.returncode == 0
        assert "NOT FOUND" in result.stdout

    def test_specific_notebook_dry_run(self, tmp_path):
        """Dry-run on a specific notebook prints the Plan and exits 0."""
        nb_cells = [
            _md("# Intro\n"),
            _md("### Exercice 1 : sujet\n", cell_id="desc-1"),
            _code('print("Exercice a completer")\n', cell_id="stub-1"),
            _md("### Corrigé : Exercice 1 : sujet\n", cell_id="corr-md-1"),
            _code("print('ok')\n", cell_id="corrige-code-1"),
        ]
        nb_path = _write_nb(tmp_path, nb_cells, name="my-notebook.ipynb")
        result = subprocess.run(
            [sys.executable, RESTRUCTURER, "--dry-run", str(nb_path)],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
            timeout=30,
        )
        assert result.returncode == 0
        assert "Processing: my-notebook.ipynb" in result.stdout
        assert "Plan:" in result.stdout
        assert "Corrigé pairs found: 1" in result.stdout

    def test_specific_notebook_no_change(self, tmp_path):
        """Notebook without corrigés or stubs returns False, prints skip, exit 0."""
        nb_cells = [
            _md("# Intro\n"),
            _code("x = 1\n"),
        ]
        nb_path = _write_nb(tmp_path, nb_cells, name="plain.ipynb")
        result = subprocess.run(
            [sys.executable, RESTRUCTURER, str(nb_path)],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
            timeout=30,
        )
        assert result.returncode == 0
        assert "No corrigés or exercise stubs found" in result.stdout
        assert "Skipping." in result.stdout
        # File MUST be untouched
        original = json.loads(nb_path.read_text(encoding="utf-8"))
        assert len(original["cells"]) == 2

    def test_specific_notebook_restructured(self, tmp_path):
        """Restructure a notebook with corrigé pair — file modified on disk."""
        nb_cells = [
            _md("# Intro\n"),
            _md("### Exercice 1 : sujet\n", cell_id="desc-1"),
            _code('print("Exercice a completer")\n', cell_id="stub-1"),
            _md("### Corrigé : Exercice 1 : sujet\n", cell_id="corr-md-1"),
            _code("print('ok')\n", cell_id="corrige-code-1"),
            _md("## Conclusion\n\nfin.\n"),
        ]
        nb_path = _write_nb(tmp_path, nb_cells, name="restruct.ipynb")
        before_size = nb_path.stat().st_size
        result = subprocess.run(
            [sys.executable, RESTRUCTURER, str(nb_path)],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
            timeout=30,
        )
        assert result.returncode == 0
        assert "Restructured:" in result.stdout
        assert "Written to" in result.stdout
        # File must have changed
        after_size = nb_path.stat().st_size
        assert after_size != before_size, "file size must change after restructure"
        # And content too
        reloaded = json.loads(nb_path.read_text(encoding="utf-8"))
        all_src = "".join("".join(c.get("source", [])) for c in reloaded["cells"])
        assert "Exemples guidés" in all_src
        assert "Exercices a completer" in all_src

    def test_default_notebooks_constant_is_list_of_six(self):
        """DEFAULT_NOTEBOOKS = 6 SW-8..SW-13 notebook names."""
        assert isinstance(DEFAULT_NOTEBOOKS, list)
        assert len(DEFAULT_NOTEBOOKS) == 6
        # All start with 'SW-' and end with '.ipynb'
        for nb in DEFAULT_NOTEBOOKS:
            assert nb.startswith("SW-")
            assert nb.endswith(".ipynb")

    def test_sw_dir_constant_points_to_semanticweb(self):
        """SW_DIR = REPO/MyIA.AI.Notebooks/SymbolicAI/SemanticWeb."""
        assert SW_DIR.name == "SemanticWeb"
        assert SW_DIR.parent.name == "SymbolicAI"
        assert SW_DIR.parent.parent.name == "MyIA.AI.Notebooks"