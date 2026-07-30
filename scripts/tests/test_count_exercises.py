"""Regression suite for ``scripts/notebook_tools/count_exercises.py`` (#2161).

Background. ``count_exercises.py`` is the daily-driver that gates the
``>= 3 exercises per pedagogical notebook`` convention (#2161): it is wired into
both the fleet scan and the PR gate (``check_pr_exercises.py``), and an advisory
CI job (``#8816``). It carries a documented history of **false negatives** that
under-counted real exercises -- the C# ``//`` blind-spot (#5760), the .NET
Interactive ``display()`` idiom (#6056), the Lean ``--`` comment blind-spot
(#5774), the ``# a completer`` line marker (#6091), the grouped-markdown-headers
undercount (#6051 Bug 1), the plural-section-steals-instance bug (#6051 Bug 2),
and the ``#8858`` clone-prefix corpus-empty trap -- yet the pure helper functions
had **zero unit tests**. One regex tweak could silently invert a verdict
cluster-wide and re-open every one of those undercounts.

This suite covers the pure helpers with assertions pinned to exact verdicts /
kinds / counts / numbers (G.9 non-vacuous), so each historically-fixed behaviour
is locked against regression:

  * ``_classify`` : corpus scope + per-kind threshold (standard/setup/lean/
    legacy/artifact/template/student/vendored/tooling) including the ``#8858``
    clone-prefix guard (a notebook under a ``.../archive/`` clone root must NOT
    be silently archived) and the path-form invariance (relative vs absolute).
  * ``_is_stub_code`` : C.1 stub patterns (``pass`` / ``return None`` /
    ``print("Exercice a completer")`` / ``# TODO`` / ``// TODO`` / ``-- TODO`` /
    ``result = None``) are STUBS; a complete multi-line solution is NOT.
  * ``_code_cell_mentions_exercise`` : ``#`` / ``//`` / ``--`` comment forms all
    detected (the three language blind-spots).
  * ``_markdown_instance_header_lines`` : grouped singular headers count per
    INSTANCE (#6051 Bug 1); plural section headers count ZERO (#6051 Bug 2); a
    line carrying both forms counts as an instance (singular dominates).
  * ``_exercise_number`` : ``Exercice 3`` -> ``'3'``, ``Exercice 3b`` -> ``'3b'``,
    numberless ``# Exercice :`` -> ``None`` (gates backward pairing).
  * ``count_exercises_in_notebook`` : end-to-end dedup -- header + adjacent stub
    counts ONCE (forward pairing), three grouped headers count THREE, a
    stub-then-header layout with matching number counts ONCE (backward pairing).

Run: ``python -m pytest scripts/tests/test_count_exercises.py -q``
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "notebook_tools"))

import count_exercises as C  # noqa: E402


# --- _classify (corpus scope + per-kind threshold) -----------------------

def _nb(root: Path, rel: str) -> Path:
    """A notebook path under ``root`` (created on demand so ``resolve`` works)."""
    p = root / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text("{}", encoding="utf-8")
    return p


def test_classify_standard_course_notebook():
    p = Path("ML/ML-1-Regression.ipynb")
    assert C._classify(p, standard_threshold=3, root=Path("/repo/MyIA.AI.Notebooks")) == ("standard", 3)


def test_classify_setup_stem_exempt():
    # `...-Setup...` -> setup, threshold 0 (rule exception table, 0-1 as ceiling).
    p = Path("Sudoku/Sudoku-0-Environment-Csharp.ipynb")
    kind, thr = C._classify(p, standard_threshold=3, root=Path("/repo/MyIA.AI.Notebooks"))
    assert kind == "setup" and thr == 0


def test_classify_setup_dir_scoped():
    # A directory named `environment` scopes the whole sub-series (GenAI/00-...).
    p = Path("GenAI/00-GenAI-Environment/00-3-Config.ipynb")
    kind, thr = C._classify(p, standard_threshold=3, root=Path("/repo/MyIA.AI.Notebooks"))
    assert kind == "setup" and thr == 0


def test_classify_lean_stem_exempt():
    p = Path("GameTheory/GameTheory-11b-Lean-BayesianGames.ipynb")
    kind, thr = C._classify(p, standard_threshold=3, root=Path("/repo/MyIA.AI.Notebooks"))
    assert kind == "lean" and thr == 0


def test_classify_legacy_directory():
    # Legacy matched on a DIRECTORY part, never the stem (a `-Legacy` notebook
    # subject must not be silently archived).
    p = Path("SemanticWeb/RDF.Net-Legacy/OldLesson.ipynb")
    kind, thr = C._classify(p, standard_threshold=3, root=Path("/repo/MyIA.AI.Notebooks"))
    assert kind == "legacy" and thr is None


def test_classify_legacy_stem_not_archived():
    # `04-4-Cross-Stitch-Pattern-Maker-Legacy.ipynb` names the SUBJECT, not the
    # status -> it is a maintained standard notebook (NOT legacy).
    p = Path("GenAI/Image/04-Applications/04-4-Cross-Stitch-Pattern-Maker-Legacy.ipynb")
    kind, thr = C._classify(p, standard_threshold=3, root=Path("/repo/MyIA.AI.Notebooks"))
    assert kind == "standard" and thr == 3


def test_classify_artifact_stem():
    for stem in ("research", "quantbook", "research_robustness", "m12_har_rv_j_research"):
        p = Path(f"QC/{stem}.ipynb")
        kind, thr = C._classify(p, standard_threshold=3, root=Path("/repo/MyIA.AI.Notebooks"))
        assert kind == "artifact" and thr is None, f"stem {stem} -> {kind}"


def test_classify_template_stem():
    p = Path("ML/ML-template.ipynb")
    kind, thr = C._classify(p, standard_threshold=3, root=Path("/repo/MyIA.AI.Notebooks"))
    assert kind == "template" and thr is None


def test_classify_non_pedagogical_dir():
    # ML-Training-Pipeline is QC model-training research, not a taught series.
    p = Path("GenAI/ML-Training-Pipeline/runner.ipynb")
    kind, thr = C._classify(p, standard_threshold=3, root=Path("/repo/MyIA.AI.Notebooks"))
    assert kind == "archive" and thr is None


def test_classify_underscore_dir():
    # Underscore-prefixed dirs are internal (_archives/, _probes/, _legacy/).
    p = Path("ML/_archives/old.ipynb")
    kind, thr = C._classify(p, standard_threshold=3, root=Path("/repo/MyIA.AI.Notebooks"))
    assert kind == "archive" and thr is None


def test_classify_student_group_dir():
    p = Path("Argument/groupe-I2-contre-arguments/submit.ipynb")
    kind, thr = C._classify(p, standard_threshold=3, root=Path("/repo/MyIA.AI.Notebooks"))
    assert kind == "student" and thr is None


def test_classify_root_gradebook_tooling():
    # A notebook sitting at the top of MyIA.AI.Notebooks/ belongs to no series.
    p = Path("GradeBook.ipynb")
    kind, thr = C._classify(p, standard_threshold=3, root=Path("/repo/MyIA.AI.Notebooks"))
    assert kind == "tooling" and thr is None


def test_classify_underscore_stem_tooling():
    p = Path("ML/_e2e_quant_validation.ipynb")
    kind, thr = C._classify(p, standard_threshold=3, root=Path("/repo/MyIA.AI.Notebooks"))
    assert kind == "tooling" and thr is None


def test_classify_clone_prefix_not_misarchived(tmp_path):
    # #8858 guard: a clone living under `.../legacy-box/...` must NOT classify
    # every notebook as legacy. Only the parts RELATIVE to the scan root carry
    # signal. The scan root is passed explicitly as ``root``.
    root = tmp_path / "legacy-box" / "clone" / "MyIA.AI.Notebooks"
    root.mkdir(parents=True)
    p = _nb(root, "ML/ML-1-Regression.ipynb")
    kind, thr = C._classify(p, standard_threshold=3, root=root)
    assert kind == "standard" and thr == 3, (
        "clone prefix 'legacy-box' must not archive a standard notebook (#8858)"
    )


def test_classify_path_form_invariant(tmp_path):
    # A relative path and its absolute form must yield the SAME verdict (#8835):
    # the PR gate receives relative paths from `git diff --name-only`.
    root = tmp_path / "MyIA.AI.Notebooks"
    root.mkdir()
    rel = Path("ML/ML-1-Regression.ipynb")
    abs_p = _nb(root, "ML/ML-1-Regression.ipynb")
    verdict_rel = C._classify(rel, standard_threshold=3, root=root)
    verdict_abs = C._classify(abs_p, standard_threshold=3, root=root)
    assert verdict_rel == verdict_abs == ("standard", 3)


# --- _is_stub_code (C.1 stub patterns) ------------------------------------

def test_stub_pass():
    assert C._is_stub_code("pass") is True


def test_stub_return_none():
    assert C._is_stub_code("    return None") is True


def test_stub_print_a_completer():
    assert C._is_stub_code('print("Exercice a completer")') is True


def test_stub_hash_todo():
    assert C._is_stub_code("# TODO etudiant\nx = 1") is True


def test_stub_csharp_double_slash_todo():
    # C# blind-spot (#5760): `// TODO` must register as a stub marker.
    assert C._is_stub_code("// TODO etudiant\nvar x = 1;") is True


def test_stub_lean_dash_dash_todo():
    # Lean blind-spot (#5774): `-- TODO` must register as a stub marker.
    assert C._is_stub_code("-- TODO etudiant\n-- Exercice 1") is True


def test_stub_result_none_todo():
    assert C._is_stub_code("result = None  # TODO etudiant") is True


def test_stub_csharp_display_a_completer():
    # .NET Interactive `display(...)` idiom (#6056).
    assert C._is_stub_code('display("Exercice 2 a completer ...")') is True


def test_stub_raise_notimplemented():
    assert C._is_stub_code("    raise NotImplementedError") is True


def test_stub_single_effective_line():
    # One effective code line -> stub (<=1 rule).
    assert C._is_stub_code("# Exercice 1\nx = 1") is True


def test_complete_solution_not_stub():
    # Multi-line real logic with NO stub marker -> NOT a stub (it is an example).
    src = "def solve(x):\n    a = x + 1\n    b = a * 2\n    return b\nprint(solve(3))"
    assert C._is_stub_code(src) is False


def test_empty_source_is_stub():
    assert C._is_stub_code("") is True


# --- _code_cell_mentions_exercise (comment forms) ------------------------

def test_mentions_hash_comment():
    assert C._code_cell_mentions_exercise("# Exercice 1 : calculer la moyenne") is True


def test_mentions_csharp_comment():
    # C# blind-spot: `// Exercice` (#5760).
    assert C._code_cell_mentions_exercise("// Exercice 1\nvar x = 1;") is True


def test_mentions_lean_comment():
    # Lean blind-spot: `-- Exercice` (#5774).
    assert C._code_cell_mentions_exercise("-- Exercice 1\ntheorem foo :=") is True


def test_mentions_inline_comment_not_counted():
    # An inline trailing comment after executable code is intentionally NOT a
    # mention (a stub marker is a FULL-LINE comment).
    assert C._code_cell_mentions_exercise('print(x) // Exercice reference') is False


def test_mentions_no_exercice_word():
    assert C._code_cell_mentions_exercise("# Calculez la somme\nx = 1") is False


def test_mentions_english_exercise():
    assert C._code_cell_mentions_exercise("# Exercise 2: compute the trace") is True


# --- _markdown_instance_header_lines (#6051 Bug 1 + Bug 2) ---------------

def test_grouped_singular_headers_count_per_instance():
    # Bug 1 fix: a single markdown cell grouping several statements yields N
    # instances, not 1.
    src = "### Exercice 1\nintro\n### Exercice 2\nintro\n### Exercice 3\nintro"
    assert len(C._markdown_instance_header_lines(src)) == 3


def test_plural_section_header_zero_instances():
    # Bug 2 fix: a PLURAL section header (`## 9. Exercices`) groups without
    # being one -> 0 instances, and does not steal the next code cell's pairing.
    assert C._markdown_instance_header_lines("## 9. Exercices\nrecap") == []


def test_singular_and_plural_dominates_singular():
    # A line with BOTH forms is an instance (singular dominates).
    assert len(C._markdown_instance_header_lines("## Exercices : Exercice 1 recapitulatif")) == 1


def test_english_singular_instance():
    assert len(C._markdown_instance_header_lines("### Exercise")) == 1


def test_no_header_no_instance():
    assert C._markdown_instance_header_lines("Some prose without a header.\nMore text.") == []


# --- _exercise_number (backward-pairing gate) ----------------------------

def test_number_plain():
    assert C._exercise_number("### Exercice 3") == "3"


def test_number_with_letter():
    # The trailing letter distinguishes 3 from 3b (two distinct exercises).
    assert C._exercise_number("### Exercice 3b") == "3b"


def test_number_english():
    assert C._exercise_number("# Exercise 2") == "2"


def test_number_numberless_is_none():
    # Numberless references return None -> treated as unpaired (conservative).
    assert C._exercise_number("# Exercice : exploration libre") is None


# --- count_exercises_in_notebook (end-to-end dedup) ----------------------

def _write_nb(path: Path, cells: list[dict]) -> None:
    nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb), encoding="utf-8")


def _md(src: str) -> dict:
    return {"cell_type": "markdown", "source": [src], "metadata": {}}


def _code(src: str) -> dict:
    return {"cell_type": "code", "source": [src], "metadata": {}, "outputs": [], "execution_count": None}


def test_header_plus_adjacent_stub_counts_once(tmp_path):
    # Forward pairing: a markdown header + the following code stub = 1 exercise.
    p = tmp_path / "nb.ipynb"
    _write_nb(p, [
        _md("### Exercice 1\nCalculer la moyenne."),
        _code("# Exercice 1\npass"),
    ])
    assert C.count_exercises_in_notebook(p).count == 1


def test_three_grouped_headers_count_three(tmp_path):
    # Integration of Bug 1 fix: three singular headers in one markdown cell
    # followed by a single shared stub = 3 exercises (the realistic grouped
    # layout -- one cell groups the statements, one stub cell answers them).
    p = tmp_path / "nb.ipynb"
    _write_nb(p, [
        _md("### Exercice 1\na\n### Exercice 2\nb\n### Exercice 3\nc"),
        _code("# Exercices\npass"),
    ])
    # 3 markdown instances (Bug 1 fix); the shared stub is forward-paired to the
    # header cell once (deduped) -> total 3, not 1 (old per-cell bug) nor 4.
    assert C.count_exercises_in_notebook(p).count == 3


def test_plural_section_does_not_steal_pairing(tmp_path):
    # Integration of Bug 2 fix: a plural section header above a real exercise
    # must NOT absorb the exercise stub below it.
    p = tmp_path / "nb.ipynb"
    _write_nb(p, [
        _md("## 9. Exercices\nThis section groups exercises."),
        _md("### Exercice 1\nDo this."),
        _code("# Exercice 1\npass"),
    ])
    # The plural section contributes 0; the singular header + stub = 1.
    assert C.count_exercises_in_notebook(p).count == 1


def test_unpaired_code_stub_counts(tmp_path):
    # A code stub that mentions an exercise but has NO preceding markdown
    # header is its own exercise.
    p = tmp_path / "nb.ipynb"
    _write_nb(p, [
        _code("# Exercice libre\npass"),
    ])
    assert C.count_exercises_in_notebook(p).count == 1


def test_complete_solution_not_counted_as_exercise(tmp_path):
    # A code cell that mentions "exercice" in prose but is a COMPLETE solution
    # is an example, not an exercise -> not counted.
    p = tmp_path / "nb.ipynb"
    _write_nb(p, [
        _code("# Exercice corrige : la solution ci-dessous\n"
              "def solve(x):\n"
              "    a = x + 1\n"
              "    b = a * 2\n"
              "    return b\n"
              "print(solve(3))"),
    ])
    assert C.count_exercises_in_notebook(p).count == 0


def test_backward_pairing_matching_number(tmp_path):
    # Stub-then-header layout: a stub at cell i preceding its own header at
    # cell i+1 is absorbed when BOTH reference the same number.
    p = tmp_path / "nb.ipynb"
    _write_nb(p, [
        _code("# Exercice 5\npass"),
        _md("### Exercice 5\nFill the box above."),
    ])
    assert C.count_exercises_in_notebook(p).count == 1


def test_csharp_double_slash_stub_detected(tmp_path):
    # Integration of the C# `//` blind-spot (#5760): a `// Exercice` stub with
    # no markdown header is counted.
    p = tmp_path / "nb.ipynb"
    _write_nb(p, [
        _code("// Exercice 1\n// TODO etudiant\nvar x = 1;"),
    ])
    assert C.count_exercises_in_notebook(p).count == 1


def test_lean_dash_dash_stub_detected(tmp_path):
    # Integration of the Lean `--` blind-spot (#5774).
    p = tmp_path / "nb.ipynb"
    _write_nb(p, [
        _code("-- Exercice 1\n-- TODO etudiant\ntheorem foo :="),
    ])
    assert C.count_exercises_in_notebook(p).count == 1


def test_parse_error_does_not_silently_conform(tmp_path):
    # A malformed notebook sets parse_error and is reported, never a silent 0.
    p = tmp_path / "broken.ipynb"
    p.write_text("{not valid json", encoding="utf-8")
    cnt = C.count_exercises_in_notebook(p)
    assert cnt.parse_error is not None
    assert cnt.conforming is False


# --- corpus_scope (integration of the #8858 filter) ----------------------

def test_corpus_scope_excludes_output_and_artifacts(tmp_path):
    # `_output.ipynb` (papermill artifact) and research stems are removed, while
    # a real course notebook (inside a family subdir) stays in the corpus.
    root = tmp_path / "MyIA.AI.Notebooks"
    (root / "ML").mkdir(parents=True)
    _write_nb(root / "ML" / "ML-1-Real.ipynb", [_md("### Exercice 1\nx"), _code("# Exercice 1\npass")])
    (root / "ML" / "ML-1-Real_output.ipynb").write_text("{}", encoding="utf-8")
    _write_nb(root / "research.ipynb", [_md("### Exercice 1\nx")])
    corpus, removed = C.corpus_scope(root)
    names = {p.name for p in corpus}
    assert "ML-1-Real.ipynb" in names
    assert "ML-1-Real_output.ipynb" not in names  # _output excluded
    assert "research.ipynb" not in names and removed.get("artifact") == 1
