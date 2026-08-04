"""Tests for scripts/audit_genai_corruption.py — GenAI notebook corruption audit.

Hermetic: targets the pure detection functions (no filesystem, no glob). The
module's side-effects live under `if __name__ == "__main__"`, so importing it
via importlib is safe (the glob never runs).

Covers the two detection classes the audit reports on:
  - corruption   : a code cell collapsed onto a single >500-char line carrying
                   import / def / dotenv (the minified-cell signature).
  - env-pattern  : which .env-loading idiom the first env-marked code cell uses,
                   with the original priority chain preserved.
"""
import importlib.util
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCRIPT_PATH = HERE.parent.parent / "audit_genai_corruption.py"


def _load():
    spec = importlib.util.spec_from_file_location("audit_genai_corruption", SCRIPT_PATH)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _code(src_lines):
    """Build a code cell from a list of source lines."""
    return {"cell_type": "code", "source": list(src_lines), "execution_count": 1}


def _md(text):
    return {"cell_type": "markdown", "source": [text]}


def _nb(*cells):
    return {"cells": list(cells), "metadata": {}, "nbformat": 4}


# ---------------------------------------------------------------------------
# is_corrupted_line
# ---------------------------------------------------------------------------

def test_is_corrupted_line_long_import():
    m = _load()
    assert m.is_corrupted_line("import " + "x" * 600) is True


def test_is_corrupted_line_long_def():
    m = _load()
    assert m.is_corrupted_line("def " + "f" * 600 + "():") is True


def test_is_corrupted_line_long_dotenv():
    m = _load()
    assert m.is_corrupted_line("dotenv" + " " * 600) is True


def test_is_corrupted_line_short_is_clean():
    m = _load()
    assert m.is_corrupted_line("import os") is False


def test_is_corrupted_line_long_without_markers_is_clean():
    m = _load()
    # long line but no import/def/dotenv -> not the corruption signature
    assert m.is_corrupted_line("x" * 600) is False


def test_is_corrupted_line_boundary_500_is_clean():
    m = _load()
    # exactly 500 chars -> not > 500 -> clean (boundary is strict)
    assert m.is_corrupted_line("import " + "x" * 493) is False  # len == 500


# ---------------------------------------------------------------------------
# count_corrupted_cells
# ---------------------------------------------------------------------------

def test_count_zero_for_clean_notebook():
    m = _load()
    nb = _nb(_code(["import os", "print(1)"]), _md("text"), _code(["x = 1"]))
    assert m.count_corrupted_cells(nb) == 0


def test_count_one_per_offending_cell_not_per_line():
    m = _load()
    long1 = "import " + "a" * 600
    long2 = "def " + "b" * 600
    # one code cell with TWO corrupted lines still counts as ONE cell
    nb = _nb(_code([long1, long2]))
    assert m.count_corrupted_cells(nb) == 1


def test_count_multiple_corrupted_cells():
    m = _load()
    long = "import " + "a" * 600
    nb = _nb(_code([long]), _md("ignore"), _code([long]), _code(["clean"]))
    assert m.count_corrupted_cells(nb) == 2


def test_count_ignores_markdown_cells():
    m = _load()
    long = "import " + "a" * 600
    # markdown cell carrying the signature must NOT count
    nb = _nb(_md(long))
    assert m.count_corrupted_cells(nb) == 0


def test_count_handles_empty_and_no_cells():
    m = _load()
    assert m.count_corrupted_cells({"cells": []}) == 0
    assert m.count_corrupted_cells({}) == 0


# ---------------------------------------------------------------------------
# classify_env_pattern (priority chain)
# ---------------------------------------------------------------------------

def test_env_pattern_none_when_no_env_marker():
    m = _load()
    assert m.classify_env_pattern(_nb(_code(["print(1)"]))) is None


def test_env_pattern_env_loaded_highest_priority():
    m = _load()
    # src carries every marker -> env_loaded wins (first in the chain)
    src = "load_dotenv() GENAI_ROOT find_dotenv env_loaded while current_path.name .env"
    assert m.classify_env_pattern(_nb(_code([src]))) == "env_loaded flag"


def test_env_pattern_priority_order():
    m = _load()
    cases = [
        ("env_loaded flag", "import dotenv; env_loaded=True"),
        ("while loop", "while current_path.name: pass  # .env"),
        ("GENAI_ROOT", "GENAI_ROOT = '/x'"),
        ("find_dotenv", "from dotenv import find_dotenv"),
        ("simple load_dotenv", "load_dotenv()"),
        ("other", "x = '.env'"),
    ]
    for expected, src in cases:
        assert m.classify_env_pattern(_nb(_code([src]))) == expected, src


def test_env_pattern_first_matching_cell_wins():
    m = _load()
    # cell 0 (load_dotenv) comes before cell 1 (env_loaded) -> load_dotenv wins
    nb = _nb(_code(["load_dotenv()"]), _code(["env_loaded = True"]))
    assert m.classify_env_pattern(nb) == "simple load_dotenv"


def test_env_pattern_skips_non_code_cells():
    m = _load()
    # markdown carrying the marker is ignored; the code cell after classifies
    nb = _nb(_md("load_dotenv here"), _code(["GENAI_ROOT = '/x'"]))
    assert m.classify_env_pattern(nb) == "GENAI_ROOT"


# ---------------------------------------------------------------------------
# classify_series
# ---------------------------------------------------------------------------

def test_classify_series_known_roots():
    m = _load()
    for series in ["Audio", "Image", "Video", "Texte",
                   "00-GenAI-Environment", "SemanticKernel"]:
        assert m.classify_series(f"{series}/sub/nb.ipynb") == series


def test_classify_series_unknown_is_other():
    m = _load()
    assert m.classify_series("FineTuning/FT-01.ipynb") == "Other"
    assert m.classify_series("Whatever/x.ipynb") == "Other"


def test_classify_series_backslash_normalized():
    m = _load()
    assert m.classify_series("Audio\\04-Applications\\nb.ipynb") == "Audio"


# ---------------------------------------------------------------------------
# status_label
# ---------------------------------------------------------------------------

def test_status_label_boundaries():
    m = _load()
    assert m.status_label(0) == "OK"
    assert m.status_label(20) == "OK"      # 20 is NOT > 20
    assert m.status_label(21) == "MOYEN"
    assert m.status_label(50) == "MOYEN"   # 50 is NOT > 50
    assert m.status_label(51) == "CRITIQUE"
    assert m.status_label(100) == "CRITIQUE"


# ---------------------------------------------------------------------------
# audit_notebook (integration)
# ---------------------------------------------------------------------------

def test_audit_notebook_clean_no_env():
    m = _load()
    nb = _nb(_code(["import os", "print(1)"]))
    assert m.audit_notebook(nb) == (0, None)


def test_audit_notebook_corrupted_with_env():
    m = _load()
    long = "import " + "a" * 600
    nb = _nb(_code([long, "load_dotenv()"]))
    count, pattern = m.audit_notebook(nb)
    assert count == 1
    assert pattern == "simple load_dotenv"


# ---------------------------------------------------------------------------
# shorten_path
# ---------------------------------------------------------------------------

def test_shorten_path_strips_prefix_and_normalizes():
    m = _load()
    assert m.shorten_path("MyIA.AI.Notebooks/GenAI/Audio/04-Applications/nb.ipynb") \
        == "Audio/04-Applications/nb.ipynb"
    # backslash variant
    assert "Audio" in m.shorten_path("MyIA.AI.Notebooks/GenAI\\Audio\\nb.ipynb")
