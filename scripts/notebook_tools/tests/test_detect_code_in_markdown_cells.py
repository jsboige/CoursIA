#!/usr/bin/env python3
"""Tests for ``scripts/notebook_tools/detect_code_in_markdown_cells.py`` (#12064).

Why this file exists
--------------------
PR #12064 ships a guard that flags ``code`` patterns embedded in markdown
cells — the trap is that **what reads as a citation in prose and what
reads as a stub in code look identical at the line level**. The unit tests
pin the discriminators so a bad regex rewrite can't silently regress.

Discriminators pinned
---------------------
1. **Top-level Python assignment**: ``NAME = VALUE`` at column 0.
2. **≥ 2 consecutive non-blank assignments** on the same cell (a single
   prose mention is a citation, two in a row is a code block).
3. **Python signature**: ``def NAME`` or ``class NAME`` at column 0.
4. **Papermill tag**: a ``parameters``-tagged markdown cell with any
   assignment is *always* a dead parameter block — single occurrence is
   enough.
5. **Assignment interrupted by prose or blank lines is NOT a code block**
   (the prose-discriminator: a list bullet ``- x = y`` next to ``y = 2``
   is still a list, not code).

The acceptance for #12064 is ``PT_11b_grpo_qwen_rlvr_on_verifiers.ipynb``
cell 5 — a markdown cell tagged ``parameters`` carrying two assignments
(``LOAD_MODEL_AND_TRAIN`` and ``RUN_SEED``). Both rules must trigger.

Run::

    python -m pytest scripts/notebook_tools/tests/test_detect_code_in_markdown_cells.py -v
"""
from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[3]
TOOL = REPO_ROOT / "scripts" / "notebook_tools" / "detect_code_in_markdown_cells.py"
sys.path.insert(0, str(TOOL.parent))

import detect_code_in_markdown_cells as dcm  # noqa: E402


def _mk_md(source, tags=None):
    return {
        "cell_type": "markdown",
        "source": source,
        "metadata": {"tags": tags} if tags else {},
        "execution_count": None,
        "outputs": [],
    }


def test_prose_alone_no_finding():
    """Real markdown prose, no code, must not flag."""
    cell = _mk_md(["## Title\n", "Some prose.\n", "Another sentence.\n"])
    findings = dcm.scan_cell(cell, 0)
    assert findings == [], f"expected no findings, got {findings}"


def test_single_assignment_in_prose_no_finding():
    """A single `x = 1` in prose is a citation, not a stub."""
    cell = _mk_md(["Voir `x = 1` ci-dessous pour le cas simple.\n"])
    findings = dcm.scan_cell(cell, 0)
    assert findings == [], f"expected no findings, got {findings}"


def test_assignments_interrupted_by_prose_no_finding():
    """Two assignments separated by prose are not a code block."""
    cell = _mk_md([
        "x = 1\n",
        "Some prose in between.\n",
        "y = 2\n",
    ])
    findings = dcm.scan_cell(cell, 0)
    assert findings == [], f"expected no findings, got {findings}"


def test_two_consecutive_assignments_flag_assignment():
    """Two consecutive assignments at column 0 are structural code."""
    cell = _mk_md([
        "x = 1\n",
        "y = 2\n",
    ])
    findings = dcm.scan_cell(cell, 7)
    rules = {f["rule"] for f in findings}
    assert "markdown_cell_with_python_assignment" in rules, \
        f"expected assignment rule, got {rules}"


def test_python_signature_flagged():
    """A `def NAME(` or `class NAME(` at column 0 is structural."""
    cell = _mk_md([
        "## Skeleton\n",
        "def fibonacci(n):\n",
        "    return fibonacci(n - 1) + fibonacci(n - 2)\n",
    ])
    findings = dcm.scan_cell(cell, 0)
    rules = {f["rule"] for f in findings}
    assert "markdown_cell_with_python_signature" in rules, \
        f"expected signature rule, got {rules}"


def test_papermill_param_single_assignment_flagged():
    """A `parameters`-tagged cell with one assignment is dead — the
    discriminator is the tag, not the count of assignments."""
    cell = _mk_md(
        [
            "# Papermill injects LOAD_MODEL_AND_TRAIN\n",
            "LOAD_MODEL_AND_TRAIN = False\n",
            'print(f"LOAD_MODEL_AND_TRAIN = {LOAD_MODEL_AND_TRAIN}")\n',
        ],
        tags=["parameters"],
    )
    findings = dcm.scan_cell(cell, 5)
    rules = {f["rule"] for f in findings}
    assert "markdown_cell_with_papermill_param" in rules, \
        f"expected papermill rule, got {rules}"


def test_papermill_param_with_multiple_assignments_both_rules():
    """PT_11 c5 acceptance — both rules trigger when count ≥ 2."""
    cell = _mk_md(
        [
            "# Papermill injects LOAD_MODEL_AND_TRAIN\n",
            "LOAD_MODEL_AND_TRAIN = False\n",
            "RUN_SEED = 42\n",
            'print(f"LOAD_MODEL_AND_TRAIN = {LOAD_MODEL_AND_TRAIN}")\n',
            "if not LOAD_MODEL_AND_TRAIN:\n",
            '    print("(Mode CPU-safe)")\n',
        ],
        tags=["parameters"],
    )
    findings = dcm.scan_cell(cell, 5)
    rules = {f["rule"] for f in findings}
    assert "markdown_cell_with_papermill_param" in rules, \
        f"expected papermill rule, got {rules}"
    assert "markdown_cell_with_python_assignment" in rules, \
        f"expected assignment rule, got {rules}"


def test_code_cell_not_visited():
    """The scanner visits only markdown cells. A code cell with two
    assignments must produce zero findings."""
    cell = {
        "cell_type": "code",
        "source": ["x = 1\n", "y = 2\n"],
        "metadata": {},
        "execution_count": 3,
        "outputs": [],
    }
    findings = dcm.scan_cell(cell, 0)
    assert findings == [], f"code cell must not be visited, got {findings}"


def test_selfcheck_passes():
    """The embedded selfcheck of the detector must pass — if it doesn't,
    the regex is broken enough to fail its own controls."""
    import subprocess
    rc = subprocess.call(
        [sys.executable, str(TOOL), "--selfcheck"],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    assert rc == 0, f"detector --selfcheck exited {rc}, expected 0"


def test_baseline_check_exits_zero_on_main():
    """With the shipped baseline, --check on the full corpus must exit 0
    (no NEW violations). This is the guard that lets the detector ship
    without forcing every pre-existing violation to be fixed at once."""
    import subprocess
    baseline = REPO_ROOT / "scripts" / "notebook_tools" / "code_in_markdown_cells_baseline.json"
    proc = subprocess.run(
        [
            sys.executable, str(TOOL),
            "MyIA.AI.Notebooks",
            "--check",
            "--baseline", str(baseline),
        ],
        capture_output=True,
        text=True,
        encoding="utf-8", errors="replace",
        cwd=REPO_ROOT,
    )
    assert proc.returncode == 0, (
        f"--check exited {proc.returncode}\n"
        f"stdout: {proc.stdout[:500]}\nstderr: {proc.stderr[:500]}"
    )


def test_check_without_baseline_defaults_to_canonical_rc0():
    """#12585 : ``--check`` SANS ``--baseline`` doit comparer au baseline
    canonique du depot (celui que la CI passe), pas a un ensemble vide.
    Avant le fix, l'invocation desarmee rendait un FAIL fantome sur un main
    vert -- toutes les violations acceptees ressortaient « new ». Le test
    existant passait le chemin explicitement, donc ne pouvait pas voir ce
    defaut. Exige en outre la ligne d'identite qui nomme la reference."""
    import subprocess
    proc = subprocess.run(
        [
            sys.executable, str(TOOL),
            "MyIA.AI.Notebooks",
            "--check",
        ],
        capture_output=True,
        text=True,
        encoding="utf-8", errors="replace",
        cwd=REPO_ROOT,
    )
    assert proc.returncode == 0, (
        f"bare --check exited {proc.returncode}\n"
        f"stdout: {proc.stdout[:500]}\nstderr: {proc.stderr[:500]}"
    )
    assert "baseline:" in proc.stdout and "entries)" in proc.stdout, (
        "l'identite de la reference doit etre affichee "
        f"(baseline: <path> (<n> entries)); stdout: {proc.stdout[:300]}"
    )


def test_json_stdout_is_pure_and_identity_on_stderr():
    """#12858 : ``--json`` doit rendre du JSON **pur** sur stdout (le premier
    ``jq``/``json.load`` branche dessus ne doit pas casser), et la ligne
    d'identite qui nomme la reference ne se perd pas — elle migre sur stderr.
    Avant le fix, stdout commencait par ``baseline: ... (N entries)`` (prose),
    donc un ``json.load`` sur tout stdout levait JSONDecodeError (positif_1).
    """
    import json as _json
    import subprocess
    proc = subprocess.run(
        [sys.executable, str(TOOL), "MyIA.AI.Notebooks", "--json"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        cwd=REPO_ROOT,
    )
    assert proc.returncode == 0, f"stdout: {proc.stdout[:300]}\nstderr: {proc.stderr[:300]}"
    # Tout stdout est du JSON parsable (pas de ligne de prose en prefixe).
    data = _json.loads(proc.stdout)
    assert {"total", "new", "baseline_size", "findings"} <= set(data), \
        f"shape inattendue: {sorted(data)}"
    # L'identite n'est pas perdue : elle apparait sur stderr, pas sur stdout.
    assert "baseline:" in proc.stderr and "entries)" in proc.stderr, \
        f"identite absente de stderr: {proc.stderr[:300]}"
    assert not proc.stdout.lstrip().startswith("baseline:"), \
        "la ligne d'identite ne doit pas prefixer stdout en mode json"


if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))
