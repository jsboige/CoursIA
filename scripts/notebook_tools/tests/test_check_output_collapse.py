"""Tests for check_output_collapse.py — output-volume collapse axis (#15327).

Pins the discriminating design (ai-01 measurement on the issue: aggregate
contraction alone is ~100 % FP): the SIGNATURE signal fires on a
graceful-degradation motif over a substantial base, the MAGNITUDE signal on
a per-cell order-of-magnitude loss, and the two mechanically detectable
legitimate causes (content moved to a notebook created by the same diff,
diagnostic-text purge) exempt the magnitude signal only. Benign variance,
sub-floor bases, growth, deleted cells and added notebooks are silent.
The logic under test is the pure ``analyze`` / ``_apply_moved_content`` —
no git, no kernel.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_output_collapse import (
    BASE_FLOOR,
    CONCESSION_RE,
    DIAGNOSTIC_LINE_FRACTION,
    MAGNITUDE_FACTOR,
    MOVED_GAIN_FRACTION,
    SIGNATURE_FACTOR,
    _apply_moved_content,
    _diagnostic_fraction,
    _normalize,
    analyze,
    history,
)


def code_cell(cid, text):
    return {"cell_type": "code", "id": cid,
            "outputs": [{"output_type": "stream", "text": text}]}


def nb(code_cells):
    return {"cells": [code_cell(k, t) for k, t in code_cells],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def base(code_cells, added=False):
    """None when the notebook is ADDED by the branch (no baseline)."""
    return None if added else nb(code_cells)


LONG = "x" * 1000
SKIP_NOTICE = ("[INFO] API non configuree - execution sautee\n"
               "Configurez OPENAI_API_KEY pour executer les exemples\n")
WARNINGS = "".join(
    "warning CS8632: Une reference nullable est requise %d\n" % i
    for i in range(30))


def test_signature_fires_on_skip_notice():
    got = analyze(base([("a", LONG)]), nb([("a", SKIP_NOTICE)]))
    assert got["regressed"]
    assert got["cells"][0]["kind"] == "signature"
    assert got["cells"][0]["factor"] >= SIGNATURE_FACTOR


def test_signature_is_accent_blind():
    # "sautée" / "configurée" with accents must match the accent-stripped
    # motifs (both spellings exist in the wild).
    got = analyze(base([("a", LONG)]),
                  nb([("a", "Execution sautée (API non configurée)\n")]))
    assert got["cells"] and got["cells"][0]["kind"] == "signature"


def test_signature_needs_real_contraction():
    # A motif substring in a GROWN output is not degradation.
    got = analyze(base([("a", LONG)]),
                  nb([("a", "skipped 0 tests\n" + "x" * 1500)]))
    assert got["cells"] == []


def test_magnitude_fires_on_order_of_magnitude_loss():
    got = analyze(base([("a", LONG)]), nb([("a", "y" * 40)]))
    assert got["regressed"]
    assert got["cells"][0]["kind"] == "magnitude"
    assert got["cells"][0]["factor"] >= MAGNITUDE_FACTOR


def test_benign_variance_silent():
    got = analyze(base([("a", LONG)]), nb([("a", "x" * 700)]))
    assert got["cells"] == []
    assert not got["regressed"]


def test_subfloor_base_silent():
    # Below the noise floor a base is jitter, even at x400 contraction.
    assert len("x" * 400) < BASE_FLOOR
    got = analyze(base([("a", "x" * 400)]), nb([("a", "y")]))
    assert got["cells"] == []


def test_growth_silent():
    got = analyze(base([("a", LONG)]), nb([("a", "x" * 5000)]))
    assert got["cells"] == []


def test_diagnostic_purge_exempt():
    got = analyze(base([("a", WARNINGS)]), nb([("a", "Build succeeded.\n")]))
    assert got["cells"][0]["kind"] == "exempt-diagnostic"
    assert got["cells"][0]["diagnostic_fraction"] >= DIAGNOSTIC_LINE_FRACTION
    assert not got["regressed"]


def test_purge_swallowing_real_output_still_fires():
    # Char-weighted classification: a purge that also swallows a large real
    # output line must not ride along the short warning lines.
    got = analyze(base([("a", WARNINGS + "real: " + "z" * 900 + "\n")]),
                  nb([("a", "real: " + "z" * 50 + "\n")]))
    assert got["cells"][0]["kind"] == "magnitude"
    assert got["regressed"]


def test_deleted_cell_silent():
    # A PR that deletes code cells loses volume legitimately: the deleted
    # cell has no head counterpart, so no finding is produced.
    got = analyze(base([("a", LONG), ("b", LONG)]), nb([("a", LONG)]))
    assert got["cells"] == []
    assert not got["regressed"]


def test_added_notebook_never_regressed():
    got = analyze(base([], added=True), nb([("a", SKIP_NOTICE)]))
    assert not got["regressed"]
    assert got["added"]


def test_index_shift_not_misattributed():
    got = analyze(base([("a", LONG)]), nb([("zz", "y"), ("a", LONG)]))
    assert got["cells"] == []


def test_moved_content_exempts_at_diff_scale():
    # Split pattern (#14795): notebook A collapses a cell, notebook B is
    # CREATED by the same diff with comparable volume.
    rows = [analyze(base([("a", LONG * 3)]), nb([("a", "y" * 30)])),
            analyze(base([], added=True), nb([("b", "z" * 1500)]))]
    _apply_moved_content(rows)
    assert rows[0]["cells"][0]["kind"] == "exempt-moved"
    assert not rows[0]["regressed"]


def test_insufficient_moved_gain_does_not_exempt():
    rows = [analyze(base([("a", LONG * 3)]), nb([("a", "y" * 30)])),
            analyze(base([], added=True), nb([("b", "z" * 300)]))]
    _apply_moved_content(rows)
    assert rows[0]["cells"][0]["kind"] == "magnitude"
    assert rows[0]["regressed"]


def test_moved_content_never_exempts_signature():
    rows = [analyze(base([("a", LONG)]), nb([("a", SKIP_NOTICE)])),
            analyze(base([], added=True), nb([("b", "z" * 5000)]))]
    _apply_moved_content(rows)
    assert rows[0]["cells"][0]["kind"] == "signature"
    assert rows[0]["regressed"]


def test_normalize_strips_accents_and_lowercases():
    assert _normalize("Exécution Sautée (non configuré)") == \
        "execution sautee (non configure)"


def test_diagnostic_fraction_char_weighted():
    removed_real = "z" * 900
    got = _diagnostic_fraction(WARNINGS + removed_real + "\n",
                               removed_real + "\n")
    # All removed chars are warnings here: fraction 1.0.
    assert got == 1.0
    got = _diagnostic_fraction(WARNINGS + removed_real + "\n", "\n")
    # The real 900-char line dominates the removed volume: fraction < 0.8.
    assert got < DIAGNOSTIC_LINE_FRACTION


def test_constants_pinned():
    # Calibration provenance: reference case factors 14.9/67.6/49.4 (all
    # above 10), noise floor 500 chars, moved-gain fraction from ai-01's
    # "un volume comparable" on #14795's split.
    assert BASE_FLOOR == 500
    assert MAGNITUDE_FACTOR == 10
    assert SIGNATURE_FACTOR == 2
    assert MOVED_GAIN_FRACTION == 0.5
    assert DIAGNOSTIC_LINE_FRACTION == 0.8


# --- --history mode (Epic #21424, T1) -----------------------------------

import json
import os
import subprocess
import tempfile

# CONCESSION_RE is the regex that the --history mode uses to count added
# prose lines that admit a degraded state. The calibration dataset is built
# by hand from a few representative notebooks, but the regex itself is
# pinned here, against both positive controls (the prose twins of
# SIGNATURE cells) and a negative control (ordinary prose).
CONCESSION_POSITIVE = [
    "## Note honnete : la cellule 5 a ete executee partiellement",
    "**Mode simulation** -- la branche Anthropic n'est pas testee ici",
    "API non configuree, merci de renseigner OPENAI_API_KEY",
    "cle api absente sur la machine d'execution",
    "execution sautee (le modele n'est pas disponible)",
    "ce carnet a des limites : la jambe QC n'est pas executee",
    "placeholder pour les exemples reels",
    "indisponible en l'absence du fichier modele",
    "note d'illustration, ce resultat n'est pas un benchmark",
]


def test_concession_re_matches_known_shapes():
    for line in CONCESSION_POSITIVE:
        assert CONCESSION_RE.search(_normalize(line)), (
            "CONCESSION_RE missed positive control: " + line[:80])


def test_concession_re_does_not_over_fire_on_ordinary_prose():
    ordinary = [
        "Cette cellule calcule la moyenne du tableau ci-dessus.",
        "Le resultat depend de la graine aleatoire choisie.",
        "Voir la documentation officielle pour plus de details.",
        "L'API est appelee avec un timeout de 30 secondes.",
    ]
    for line in ordinary:
        assert not CONCESSION_RE.search(_normalize(line)), (
            "CONCESSION_RE over-fired on ordinary prose: " + line)


def test_history_writes_json_lines_resumable(tmp_path=None):
    # Synthesise a git history with one commit that carries a prose
    # concession line. The replay must:
    #   - produce exactly one JSON line (the commit's SHA + the matched
    #     concession snippet + a non-empty concessions list),
    #   - be re-runnable: a second call on the same output file is a
    #     no-op (deduped by short SHA), so the file still has one row.
    # The setup avoids touching the real repo: a throwaway git repo is
    # built in a temp dir with branch `main` and a `origin/main` ref so
    # the `git log origin/main` call inside ``history`` finds commits.
    tmp = tempfile.mkdtemp()
    subprocess.run(["git", "init", "-q", "-b", "main", tmp], check=True)
    subprocess.run(["git", "-C", tmp, "config", "user.email",
                    "test@example.com"], check=True)
    subprocess.run(["git", "-C", tmp, "config", "user.name",
                    "Test"], check=True)
    # Initial commit: a notebook with a healthy output.
    nb_path = "demo.ipynb"
    nb_v1 = {
        "cells": [
            {"cell_type": "code", "id": "c1",
             "outputs": [{"output_type": "stream",
                          "text": "x" * 1000}]}],
        "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
    }
    with open(os.path.join(tmp, nb_path), "w", encoding="utf-8") as f:
        json.dump(nb_v1, f)
    subprocess.run(["git", "-C", tmp, "add", "."], check=True)
    subprocess.run(["git", "-C", tmp, "commit", "-q", "-m",
                    "initial healthy notebook"], check=True)
    # Second commit: collapse the cell to a skip notice AND add a prose
    # concession line in a markdown cell. The regression must fire AND
    # the concession must be recorded.
    nb_v2 = {
        "cells": [
            {"cell_type": "code", "id": "c1",
             "outputs": [{"output_type": "stream",
                          "text": ("[INFO] API non configuree - "
                                   "execution sautee\n")}]},
            {"cell_type": "markdown", "id": "c2",
             "source": ("## Note honnete : la cellule 5 a ete "
                        "executee partiellement\n")}],
        "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
    }
    with open(os.path.join(tmp, nb_path), "w", encoding="utf-8") as f:
        json.dump(nb_v2, f)
    subprocess.run(["git", "-C", tmp, "add", "."], check=True)
    subprocess.run(["git", "-C", tmp, "commit", "-q", "-m",
                    "collapse to skip notice + concession prose"],
                   check=True)
    # The replay targets `origin/main`; we add a local remote-less ref
    # that points at HEAD, which ``git log origin/main`` resolves
    # without a network. Equivalent to ``git remote add`` followed by
    # ``git fetch`` in a real workflow, but pure local.
    head = subprocess.run(["git", "-C", tmp, "rev-parse", "HEAD"],
                          capture_output=True, text=True,
                          encoding="utf-8", errors="replace", check=True
                          ).stdout.strip()
    subprocess.run(["git", "-C", tmp, "update-ref",
                    "refs/remotes/origin/main", head], check=True)
    out = os.path.join(tmp, "calibration.jsonl")
    scanned, emitted = history("1970-01-01", "2099-01-01", out, cwd=tmp)
    assert scanned == 2, f"expected 2 commits scanned, got {scanned}"
    assert emitted == 1, f"expected 1 commit emitted, got {emitted}"
    with open(out, "r", encoding="utf-8") as f:
        rows = [json.loads(line) for line in f if line.strip()]
    assert len(rows) == 1
    row = rows[0]
    assert row["regressed"], "expected the collapse to be detected"
    assert row["n_concessions"] >= 1, "expected at least one concession"
    assert any("honnete" in c for c in row["concessions"]), (
        "expected the 'honnete' concession snippet to be captured")
    # Re-run: must be idempotent (no duplicate row). The first commit
    # is healthy (no row), the second is in the dedupe set -- both are
    # skipped on the re-run, so the file still has one row.
    scanned2, emitted2 = history("1970-01-01", "2099-01-01", out, cwd=tmp)
    assert emitted2 == 0
    with open(out, "r", encoding="utf-8") as f:
        rows2 = [json.loads(line) for line in f if line.strip()]
    assert len(rows2) == 1


def test_history_silent_commit_emits_no_row():
    # A commit that ONLY adds an unrelated source file (no notebook
    # touched, no concession prose) must produce no row. The replay
    # function must not invent findings.
    tmp = tempfile.mkdtemp()
    subprocess.run(["git", "init", "-q", "-b", "main", tmp], check=True)
    subprocess.run(["git", "-C", tmp, "config", "user.email",
                    "test@example.com"], check=True)
    subprocess.run(["git", "-C", tmp, "config", "user.name",
                    "Test"], check=True)
    open(os.path.join(tmp, "README.md"), "w", encoding="utf-8").write("# hi")
    subprocess.run(["git", "-C", tmp, "add", "."], check=True)
    subprocess.run(["git", "-C", tmp, "commit", "-q", "-m",
                    "add readme"], check=True)
    head = subprocess.run(["git", "-C", tmp, "rev-parse", "HEAD"],
                          capture_output=True, text=True,
                          encoding="utf-8", errors="replace", check=True
                          ).stdout.strip()
    subprocess.run(["git", "-C", tmp, "update-ref",
                    "refs/remotes/origin/main", head], check=True)
    out = os.path.join(tmp, "calibration.jsonl")
    scanned, emitted = history("1970-01-01", "2099-01-01", out, cwd=tmp)
    assert scanned == 1, f"expected 1 commit scanned, got {scanned}"
    assert emitted == 0
    assert os.path.getsize(out) == 0


def test_history_missing_origin_main_returns_zero():
    # A repo without origin/main (the throwaway case above) must
    # return (0, 0) without writing the file -- ``git log origin/main``
    # produces no output, and the function must not invent commits.
    tmp = tempfile.mkdtemp()
    subprocess.run(["git", "init", "-q", "-b", "main", tmp], check=True)
    out = os.path.join(tmp, "calibration.jsonl")
    scanned, emitted = history("1970-01-01", "2099-01-01", out, cwd=tmp)
    assert (scanned, emitted) == (0, 0)
    assert not os.path.exists(out)
