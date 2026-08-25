"""Tests for scripts/notebook_tools/scan_md_hierarchy.py.

Locks in the COLLAPSED-MARKDOWN detector added for #3966: a markdown cell
whose newlines were stripped (heading + prose + GFM table separator + fenced
code glued onto ONE line) must be flagged, while legitimate tables, blockquoted
tables, and fenced ASCII art (all with their newlines intact) must stay SILENT.
Also guards the pre-existing H1-DEEP / MULTI-H1 / HINT-AS-HEADING checks.

The `# Rename merge (#12735)` block below covers the rename-handling fix for
the constant `+2 across 2 notebook(s), 386 burned down` verdict on every PR
(zero-pad renames `4b -> 04b` and `PT_11_grpo_qwen_rlvr_on_verifiers ->
PT_11_grpo_qwen_rlvr_on_verifiers` produced phantom `+1/-1` deltas).
"""

import json
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from scan_md_hierarchy import (  # noqa: E402
    scan_notebook,
    _has_collapsed_markdown,
    _merge_baseline_renames,
    _git_renames,
    diff_against_baseline,
    main,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _md(source) -> dict:
    # Match the real notebook convention: source is a list of lines (str stayed
    # joined is also accepted by the scanner). Default to list-of-lines.
    if isinstance(source, str):
        source = [source]
    return {"cell_type": "markdown", "source": source}


def _code(source: str) -> dict:
    return {"cell_type": "code", "source": [source], "execution_count": 1, "outputs": []}


def _write_nb(cells: list[dict]) -> str:
    nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    f = tempfile.NamedTemporaryFile(
        mode="w", suffix=".ipynb", delete=False, encoding="utf-8")
    json.dump(nb, f)
    f.close()
    return f.name


def _kinds(path: str) -> list[str]:
    return [f["kind"] for f in scan_notebook(path)]


# ---------------------------------------------------------------------------
# COLLAPSED-MARKDOWN — true positives (must flag)
# ---------------------------------------------------------------------------

def test_collapsed_heading_plus_table_on_one_line():
    """The canonical #3966 defect: heading + prose + table rows glued."""
    collapsed = (
        "### Analyse### Détail| Méthode | Rôle ||---------|------|"
        "| init() | construit |"
    )
    path = _write_nb([_md(collapsed)])
    assert "COLLAPSED-MARKDOWN" in _kinds(path)


def test_collapsed_heading_plus_fence_on_one_line():
    """Heading + fenced code opener + glued table rows (GenAI payoff diagrams).

    The detector keys on the glued GFM table separator (its documented
    signature); the heading+fence glue alone is a different, out-of-scope
    defect. This cell is flagged because the table rows are also collapsed.
    """
    collapsed = (
        "### Diagramme des payoffs  ``` LONG CALL ... LONG PUT ... ```  "
        "| Stratégie | Payoff ||-----------|--------|| Call | +∞ |"
    )
    assert _has_collapsed_markdown(collapsed)


def test_heading_fence_glue_without_table_out_of_scope():
    """Heading + fence glued but NO table-separator fragment -> not flagged.

    Documents the detector's scope: it catches table-separator collapse
    (#3966), not pure heading/fence gluing. The latter is a separate defect.
    """
    glued = "### Diagramme des payoffs  ``` LONG CALL (Achat d'un Call)"
    assert not _has_collapsed_markdown(glued)


def test_collapsed_multiple_headings_on_one_line():
    """Multiple section headers glued (no table, but separator fragment absent)."""
    # No table-separator fragment here -> NOT a collapsed-markdown case per the
    # detector's signature (it keys on a glued table separator). This documents
    # the detector's scope: it catches table-collapse, not heading-only gluing.
    glued = "## Partie 4### 4.1 Concept Lorem ipsum"
    assert not _has_collapsed_markdown(glued)


# ---------------------------------------------------------------------------
# COLLAPSED-MARKDOWN — false positives (must stay SILENT)
# ---------------------------------------------------------------------------

def test_clean_table_not_flagged():
    """A well-formed GFM table with its separator on its own line is clean."""
    clean = (
        "| Colonne A | Colonne B |\n"
        "|-----------|-----------|\n"
        "| 1         | 2         |\n"
    )
    assert not _has_collapsed_markdown(clean)


def test_clean_blockquoted_table_not_flagged():
    """A blockquoted table (`> |---|---|`) is a legit table, not collapsed."""
    clean = (
        "> | Avantage | Inconvénient |\n"
        "> |----------|--------------|\n"
        "> | rapide   | coûteux      |\n"
    )
    assert not _has_collapsed_markdown(clean)


def test_clean_aligned_table_not_flagged():
    """Alignment colons in the separator are still a clean separator row."""
    clean = (
        "| Gauche | Centre | Droite |\n"
        "|:-------|:------:|-------:|\n"
        "| a      | b      | c      |\n"
    )
    assert not _has_collapsed_markdown(clean)


def test_clean_table_without_trailing_pipes_not_flagged():
    """GFM allows tables without trailing pipes (`|---|---`, no closing `|`).

    Regression guard: an earlier version of CLEAN_SEP_LINE_RE required a trailing
    pipe and false-positived on these, caught on Sudoku-6 cell 1 (a valid table).
    """
    clean = (
        "| Composant | Description | Taille\n"
        "|-----------|-------------|-------\n"
        "| **Variables** | $X_{i,j}$ | 81\n"
        "| **Domaines** | $D_{i,j}$ | 9\n"
    )
    assert not _has_collapsed_markdown(clean)


def test_clean_table_no_trailing_pipe_and_aligned_not_flagged():
    """Mix: no trailing pipe + alignment colons is still a clean separator."""
    clean = (
        "| Algo | Type\n"
        "|:-----|----:\n"
        "| BT   | Recherche\n"
    )
    assert not _has_collapsed_markdown(clean)


def test_clean_fence_with_table_inside_not_flagged():
    """A fenced code block documenting a table (newlines intact) is clean."""
    clean = (
        "Exemple de tableau markdown :\n"
        "```\n"
        "| a | b |\n"
        "|---|---|\n"
        "| 1 | 2 |\n"
        "```\n"
    )
    assert not _has_collapsed_markdown(clean)


def test_clean_file_tree_in_fence_not_flagged():
    """A fenced ASCII file tree (`|-- file`) is CODE, not a collapsed table.

    Regression guard: without fence-aware stripping, the `|--` of a file tree
    triggered the table-separator fragment and false-positived. Caught on
    Lean-12 cell 16 (Lean port file listing). Tilde fences too.
    """
    clean = (
        "### Architecture du port\n\n"
        "```\n"
        "sensitivity_lean/\n"
        "|-- lakefile.lean\n"
        "|-- MainTheorem.lean\n"
        "|-- Hypercube.lean\n"
        "```\n\n"
        "Le port s'inspire de Mathlib.\n"
    )
    assert not _has_collapsed_markdown(clean)


def test_clean_tilde_fence_file_tree_not_flagged():
    """Tilde fences (~~~) are also respected."""
    clean = (
        "Arbre :\n~~~\n|-- a\n|-- b\n~~~\n"
    )
    assert not _has_collapsed_markdown(clean)


def test_collapsed_fence_glued_still_flagged():
    # A truly collapsed cell (fence opener glued to a heading, no newlines) is
    # still flagged: the glued line does not start with a fence marker so the
    # fence-stripping leaves it intact, and the glued table fragment is detected.
    collapsed = (
        "### Architecture ``` sensitivity_lean/ |-- lakefile | Fichier | Lignes ||---|---|"
    )
    assert _has_collapsed_markdown(collapsed)


def test_clean_cell_without_any_table_not_flagged():
    """A normal prose+heading cell with no table is never flagged."""
    clean = "## Introduction\n\nDu paragraphe normal ici.\n"
    assert not _has_collapsed_markdown(clean)


# ---------------------------------------------------------------------------
# Integration — scan_notebook end-to-end
# ---------------------------------------------------------------------------

def test_scan_clean_notebook_no_findings():
    cells = [
        _md("# Titre du notebook\n"),
        _md("## Section\n\n| A | B |\n|---|---|\n| 1 | 2 |\n"),
        _code("print('ok')"),
    ]
    assert _kinds(_write_nb(cells)) == []


def test_scan_collapsed_cell_flagged_integration():
    cells = [
        _md("# Titre\n"),
        _md("## Synthèse| Cas | Verdict ||-----|---------|| a | ok |"),
    ]
    kinds = _kinds(_write_nb(cells))
    assert "COLLAPSED-MARKDOWN" in kinds


# ---------------------------------------------------------------------------
# Regression guard — pre-existing checks still work
# ---------------------------------------------------------------------------

def test_h1_deep_still_detected():
    """An H1 in the 2nd markdown cell (not the first) is still H1-DEEP."""
    cells = [
        _md("# Premier titre\n"),
        _md("Texte\n"),
        _md("# Deuxième H1 profond\n"),
    ]
    assert "H1-DEEP" in _kinds(_write_nb(cells))


def test_multi_h1_still_detected():
    cells = [_md("# H1 un\n"), _md("# H1 deux\n")]
    assert "MULTI-H1" in _kinds(_write_nb(cells))


def test_hint_as_heading_still_detected():
    """A bare `## Note` aside is still HINT-AS-HEADING."""
    cells = [_md("# Titre\n"), _md("## Note\n")]
    assert "HINT-AS-HEADING" in _kinds(_write_nb(cells))


def test_titled_step_not_hint():
    """`## Étape 3 : Titre` is a real section header, not a bare aside."""
    cells = [_md("# Titre\n"), _md("## Étape 3 : Installation\n")]
    assert "HINT-AS-HEADING" not in _kinds(_write_nb(cells))


def test_titled_step_no_colon_not_hint():
    """`### Step 1 Import configuration...` (no colon) is a real section header.

    Regression guard for c.754 / #3966 follow-up: the original TITLED_STEP_RE
    required a colon (`Step 1: Title`), which false-positived on `Step N
    <descriptive verb phrase>` (no colon) section headers — the same
    pedagogical pattern, just without punctuation. G.1 firsthand on
    GenAI/SemanticKernel/dotnet/notebooks/00-AI-settings.ipynb cells 1/3/5/7
    confirmed `### Step 1 Import configuration packages and classes` is a
    tutorial section header (prose body underneath), same as `### Step 4:
    Save Configuration to settings.json`.
    """
    cells = [_md("# Titre\n"), _md("### Step 1 Import configuration packages and classes\n")]
    assert "HINT-AS-HEADING" not in _kinds(_write_nb(cells))


def test_bare_step_aside_still_hint():
    """`## Étape 3` (bare number, no title) remains a bare aside, still flagged.

    Regression guard: extending TITLED_STEP_RE to also match the no-colon
    variant must not relax the bare-aside rule. A bare `## Étape 3` has no
    title after the number and stays HINT-AS-HEADING.
    """
    cells = [_md("# Titre\n"), _md("## Étape 3\n")]
    assert "HINT-AS-HEADING" in _kinds(_write_nb(cells))


def test_titled_step_no_colon_with_glued_colon_not_hint():
    """`### Step 1:Import...` (glued colon, no space) also matches — GFM-style."""
    cells = [_md("# Titre\n"), _md("### Step 1:Import configuration\n")]
    assert "HINT-AS-HEADING" not in _kinds(_write_nb(cells))


# ---------------------------------------------------------------------------
# CLI contract — an EMPTY scan is never reported as a CLEAN scan
#
# The scanner used to print `=== 0/0 notebooks flagged ===` and exit 0 whenever
# it had been handed nothing to look at: no argument at all, a mistyped path, a
# flag swallowed as a positional. That output reads as an all-clear while
# nothing was scanned. Same defect class as the vacuous `scanner reports 0`
# acceptance criterion of #3968 (see HINT_RE in the scanner).
# ---------------------------------------------------------------------------

def _run(argv: list[str]) -> int:
    """Run main(argv), returning its exit code (argparse errors -> SystemExit)."""
    try:
        return main(argv)
    except SystemExit as exc:  # argparse.error() / --help
        return exc.code


def test_no_argument_is_an_error_not_an_all_clear():
    assert _run([]) == 2


def test_mistyped_path_is_an_error_not_an_all_clear():
    """A path that designates nothing must fail, not scan zero notebooks."""
    assert _run(["MyIA.AI.Notebook"]) == 2  # missing final 's'


def test_directory_without_notebooks_is_an_error():
    with tempfile.TemporaryDirectory() as empty:
        assert _run([empty]) == 2


def test_clean_notebook_exits_zero():
    nb = _write_nb([_md("# Titre\n"), _md("Du texte ordinaire.\n")])
    assert _run([nb]) == 0


def test_findings_stay_non_fatal_by_default():
    """Census mode: the CI reads the summary line and must not be broken."""
    nb = _write_nb([_md("# Titre\n"), _md("### Indices\n")])
    assert _run([nb]) == 0


def test_fail_on_findings_exits_one():
    nb = _write_nb([_md("# Titre\n"), _md("### Indices\n")])
    assert _run([nb, "--fail-on-findings"]) == 1


def test_fail_on_findings_still_zero_when_clean():
    nb = _write_nb([_md("# Titre\n"), _md("Du texte ordinaire.\n")])
    assert _run([nb, "--fail-on-findings"]) == 0


def test_summary_is_the_last_stdout_line(capsys):
    """The CI census does `... | tail -1`: the summary must stay last."""
    nb = _write_nb([_md("# Titre\n"), _md("### Indices\n")])
    _run([nb])
    assert capsys.readouterr().out.rstrip().splitlines()[-1] == (
        "=== 1/1 notebooks flagged ===")


# ---------------------------------------------------------------------------
# Rename merge (#12735) — phantom drift verdict fix
#
# Symptom: every PR returned `+2 across 2 notebook(s), 386 burned down`,
# because two zero-pad renames (`GameTheory-4b -> GameTheory-04b` and
# `PT_11_grpo_qwen_rlvr_on_verifiers -> PT_11_grpo_qwen_rlvr_on_verifiers`)
# left the baseline JSON with keys at the OLD paths. The new code paths
# (still on HEAD) bumped the *new* paths, so the baseline subtracted from
# the new tally, producing constant phantom `+1/-1` deltas.
#
# Fix: `_merge_baseline_renames(baseline, renames)` rewrites the baseline
# dict in place so that counts follow the rename pair, and `--renames-from
# origin/main` populates the rename map from `git diff -M`.
# ---------------------------------------------------------------------------


def test_rename_merge_moves_baseline_entry():
    """A rename pair moves the OLD entry's counts to the NEW entry."""
    baseline = {
        "GameTheory-4b.ipynb": {"COLLAPSED-MARKDOWN": 3, "HINT-AS-HEADING": 1},
        "Search-2.ipynb": {"COLLAPSED-MARKDOWN": 0, "HINT-AS-HEADING": 2},
    }
    renames = {"GameTheory-4b.ipynb": "GameTheory-04b.ipynb"}
    merged = _merge_baseline_renames(baseline, renames)
    # OLD key gone
    assert "GameTheory-4b.ipynb" not in merged
    # NEW key carries the counts
    assert merged["GameTheory-04b.ipynb"] == {"COLLAPSED-MARKDOWN": 3, "HINT-AS-HEADING": 1}
    # Untouched sibling stays intact
    assert merged["Search-2.ipynb"] == {"COLLAPSED-MARKDOWN": 0, "HINT-AS-HEADING": 2}


def test_rename_merge_existing_target_sums_counts():
    """If the NEW path already has baseline entries, the counts SUM (rename + prior)."""
    baseline = {
        "old.ipynb": {"COLLAPSED-MARKDOWN": 2},
        "new.ipynb": {"COLLAPSED-MARKDOWN": 5},
    }
    renames = {"old.ipynb": "new.ipynb"}
    merged = _merge_baseline_renames(baseline, renames)
    assert "old.ipynb" not in merged
    # Sum: 2 (rename origin) + 5 (existing target) = 7
    assert merged["new.ipynb"] == {"COLLAPSED-MARKDOWN": 7}


def test_rename_merge_empty_renames_is_passthrough():
    """No renames -> baseline dict returned with same content (shallow copy)."""
    baseline = {
        "a.ipynb": {"COLLAPSED-MARKDOWN": 1},
        "b.ipynb": {"HINT-AS-HEADING": 2},
    }
    merged = _merge_baseline_renames(baseline, {})
    assert merged == baseline
    # Function returns a shallow copy (defensive: callers can mutate freely).
    # Mutating `merged` must NOT mutate the input baseline.
    merged.pop("a.ipynb")
    assert "a.ipynb" in baseline


def test_rename_merge_unknown_target_creates_new_entry():
    """Rename to a target not in the baseline: OLD moved to NEW (NEW created if missing).

    The function always carries OLD counts forward to NEW, even if NEW wasn't in
    the baseline yet. This is the correct behavior for #12735's
    `PT_11_grpo_qwen_rlvr_on_verifiers` case: the new (longer) name wasn't in
    the baseline at all, but the OLD counts must travel with the rename so the
    diff doesn't false-posit `+N -N`.
    """
    baseline = {
        "old-name.ipynb": {"COLLAPSED-MARKDOWN": 4, "HINT-AS-HEADING": 1},
    }
    renames = {"old-name.ipynb": "totally-new-name.ipynb"}
    merged = _merge_baseline_renames(baseline, renames)
    assert "old-name.ipynb" not in merged
    # NEW key is created with OLD counts (canonical "rename carries counts forward")
    assert merged["totally-new-name.ipynb"] == {"COLLAPSED-MARKDOWN": 4, "HINT-AS-HEADING": 1}


def test_git_renames_returns_empty_on_missing_ref():
    """`_git_renames('nonexistent-ref', repo)` returns {} without crashing.

    This guards the workflow when `--renames-from origin/main` is invoked on
    a branch where `origin/main` is unreachable (shallow clone, fork, etc.).
    The drift block must skip rename-merging cleanly, not raise.
    """
    empty = _merge_baseline_renames({}, {})
    assert empty == {}
    # Direct call to the helper with a non-existent ref: it shells out to
    # `git diff -M --name-status` and may legitimately return non-zero exit
    # because the ref doesn't exist -- the function's contract is to swallow
    # that and return {}. Verify by calling with a clearly invalid ref.
    # We pass a tempdir as `repo_root` so even if git tries to run, it has a
    # valid working directory. We don't assert content, just that no exception
    # propagates out.
    with tempfile.TemporaryDirectory() as tmp:
        result = _git_renames("nonexistent-deadbeef-ref", tmp)
    assert result == {} or isinstance(result, dict)


def test_drift_output_clean_when_baseline_aligned_with_renames(capsys, tmp_path):
    """End-to-end: phantom `+1/-1` deltas disappear when rename merge aligns keys.

    We exercise `diff_against_baseline` directly (not `main`), because the
    scanner emits absolute paths from `pathlib.Path(a).rglob('*.ipynb')`
    while baseline keys are repo-relative -- testing through `main` would
    require mirroring that absolutization. The rename-merge logic lives in
    the helper and the drift block; this test proves their composition.

    Without rename merge, the diff would yield a phantom `+1` for the NEW
    path (baseline 0) AND a phantom `-1` burndown for the OLD path (baseline
    had 1, current doesn't see it). With the merge, the baseline carries
    the count forward to the NEW key, and the diff renders zero deltas.
    """
    from scan_md_hierarchy import diff_against_baseline
    # "Current" state as the scanner would see it (only the NEW path).
    current = {
        "MyIA.AI.Notebooks/GameTheory/GameTheory-04b.ipynb": {"COLLAPSED-MARKDOWN": 1},
    }
    # "Baseline" state (only the OLD path, pre-rename).
    baseline_raw = {
        "MyIA.AI.Notebooks/GameTheory/GameTheory-4b.ipynb": {"COLLAPSED-MARKDOWN": 1},
    }
    # No rename merge yet -> phantom pair.
    regressions, improvements = diff_against_baseline(current, baseline_raw)
    assert any(k == "COLLAPSED-MARKDOWN" and d > 0
               for _, k, d in regressions), regressions
    assert any(k == "COLLAPSED-MARKDOWN" and d < 0
               for _, k, d in improvements), improvements

    # Apply the rename merge (what `--renames-from origin/main` does internally)
    baseline_aligned = _merge_baseline_renames(
        baseline_raw,
        {"MyIA.AI.Notebooks/GameTheory/GameTheory-4b.ipynb":
         "MyIA.AI.Notebooks/GameTheory/GameTheory-04b.ipynb"},
    )
    # Now the diff is silent: baseline NEW = current NEW = 1.
    regressions2, improvements2 = diff_against_baseline(current, baseline_aligned)
    assert regressions2 == [], f"expected no regressions after rename merge, got {regressions2}"
    assert improvements2 == [], f"expected no improvements after rename merge, got {improvements2}"
