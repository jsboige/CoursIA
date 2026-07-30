"""Regression suite for ``scripts/notebook_tools/audit_solution_leaks.py`` (#362).

Background. ``audit_solution_leaks.py`` is the CI-relevant solution-leak scanner
for pedagogical notebooks. Its detectors gate notebook PRs (issue #362): a cell
that carries a complete worked solution under ``# Exercice`` (instead of a stub)
is a leak that gives students the answer. The detectors have a documented history
of false positives (prose comments read as code, example-guide cells) and false
negatives (C# notebooks invisible to the Python ``#``-comment detectors, fixed
by the C# candidate path) -- yet the 6 pure detector functions had ZERO unit
tests. One regex tweak could silently invert a verdict cluster-wide.

This suite covers the 6 pure detectors with assertions pinned to exact verdict
types / severities / counts (G.9 non-vacuous):

  * ``_is_csharp_notebook`` : C#/F# detection from metadata/kernelspec.
  * ``get_cells_after_exercice_md`` : code-cell collection after a markdown
    exercice header, with header/marker break semantics.
  * ``detect_function_body_leak`` : >3-logic-line function under an exercice =
    leak (MEDIUM, HIGH if >5); stub bodies (``pass`` / ``return None`` / the C.1
    canonical stubs) are NOT flagged.
  * ``detect_commented_solution_leak`` : >3 consecutive code-like ``#`` comments
    = leak; pedagogical prose comments are NOT flagged (the documented FP class).
  * ``detect_preresolved_cells`` : ``# Solution`` cell with >3 code lines = LOW
    leak; a stub ``# Solution`` cell is NOT flagged.
  * ``detect_csharp_leak_candidates`` : ``// Exercice`` cell with >3 code lines
    and NO stub marker = FLAG candidate; a stubbed ``// Exercice`` cell is NOT
    flagged; ``// Solution`` cells FLAG as ``csharp_preresolved``.

Run: ``python -m pytest scripts/tests/test_audit_solution_leaks.py -q``
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "notebook_tools"))

import audit_solution_leaks as A  # noqa: E402


# --- _is_csharp_notebook -------------------------------------------------

def test_is_csharp_via_language_info_name():
    nb = {"metadata": {"language_info": {"name": "c#"}}}
    assert A._is_csharp_notebook(nb) is True


def test_is_csharp_via_csharp_alias():
    nb = {"metadata": {"language_info": {"name": "csharp"}}}
    assert A._is_csharp_notebook(nb) is True


def test_is_csharp_via_net_csharp_kernel():
    nb = {"metadata": {"kernelspec": {"name": ".net-csharp"}}}
    assert A._is_csharp_notebook(nb) is True


def test_is_csharp_via_net_polyglot_kernel():
    nb = {"metadata": {"kernelspec": {"name": ".net-polyglot"}}}
    assert A._is_csharp_notebook(nb) is True


def test_is_fsharp_detected():
    nb = {"metadata": {"language_info": {"name": "f#"}}}
    assert A._is_csharp_notebook(nb) is True


def test_python_notebook_not_csharp():
    nb = {"metadata": {"language_info": {"name": "python"},
                       "kernelspec": {"name": "python3"}}}
    assert A._is_csharp_notebook(nb) is False


# --- get_cells_after_exercice_md -----------------------------------------

def _md(src):
    return {"cell_type": "markdown", "source": [src]}


def _code(src):
    return {"cell_type": "code", "source": [src]}


def test_cells_after_exercice_collects_following_code():
    cells = [_md("### Exercice 1"), _code("a = 1"), _code("b = 2")]
    out = A.get_cells_after_exercice_md(cells, 0)
    assert len(out) == 2
    assert all(c["cell_type"] == "code" for _, c in out)


def test_cells_after_exercice_breaks_on_next_header():
    # A markdown header line (starts with #) stops the walk.
    cells = [_md("### Exercice 1"), _code("a = 1"), _md("# Section suivante"),
             _code("b = 2")]
    out = A.get_cells_after_exercice_md(cells, 0)
    assert len(out) == 1  # only "a = 1"; the header stops collection


def test_cells_after_exercice_breaks_on_next_exercice_marker():
    cells = [_md("### Exercice 1"), _code("a = 1"),
             _md("### Exercice 2"), _code("b = 2")]
    out = A.get_cells_after_exercice_md(cells, 0)
    assert len(out) == 1  # stops at the next Exercice markdown


def test_cells_after_exercice_caps_at_four_following():
    # The window is start_idx+1 .. start_idx+4 (min(start+5, len)).
    cells = [_md("### Exercice 1")] + [_code(f"x{i} = {i}") for i in range(7)]
    out = A.get_cells_after_exercice_md(cells, 0)
    assert len(out) == 4


# --- detect_function_body_leak -------------------------------------------

def test_function_body_leak_high_severity():
    # 6 logic lines under a function -> HIGH (>5).
    src = ["def exo():",
           "    a = 1", "    b = 2", "    c = 3",
           "    d = 4", "    e = 5", "    f = 6",
           'print("after")']
    leaks = A.detect_function_body_leak(src)
    assert len(leaks) == 1
    assert leaks[0]["type"] == "function_body_leak"
    assert leaks[0]["severity"] == "HIGH"
    assert leaks[0]["func_name"] == "exo"


def test_function_body_leak_medium_severity():
    # 4 logic lines (>3, not >5) -> MEDIUM.
    src = ["def exo():",
           "    a = 1", "    b = 2", "    c = 3", "    d = 4",
           'print("after")']
    leaks = A.detect_function_body_leak(src)
    assert len(leaks) == 1
    assert leaks[0]["severity"] == "MEDIUM"


def test_function_stub_pass_not_flagged():
    # C.1 canonical stub: `pass` resets the logic counter -> no leak.
    src = ["def exo():", "    pass", 'print("after")']
    assert A.detect_function_body_leak(src) == []


def test_function_stub_return_none_not_flagged():
    src = ["def exo():", "    return None", 'print("after")']
    assert A.detect_function_body_leak(src) == []


def test_function_stub_print_todo_not_flagged():
    src = ['def exo():', '    print("Exercice a completer")', 'print("after")']
    assert A.detect_function_body_leak(src) == []


def test_short_function_not_flagged():
    # 2 logic lines (<=3) -> no leak.
    src = ["def exo():", "    x = 1", "    y = 2", 'print("after")']
    assert A.detect_function_body_leak(src) == []


# --- detect_commented_solution_leak --------------------------------------

def test_commented_solution_block_flagged():
    # 5 consecutive code-like # comments (expected/result/solution/answer/correct=).
    src = ["# expected = [1, 2, 3]",
           "# result = compute(x)",
           "# solution = foo(bar)",
           "# answer = 42",
           "# correct = True",
           'print("x")']
    leaks = A.detect_commented_solution_leak(src)
    assert len(leaks) == 1
    assert leaks[0]["type"] == "commented_solution_leak"
    assert leaks[0]["lines"] == 5
    assert leaks[0]["severity"] == "MEDIUM"


def test_commented_code_pattern_flagged():
    # A commented assignment with a function call: `# x = compute(y)`.
    src = ["# x = compute(y)",
           "# a = transform(z)",
           "# b = combine(w)",
           "# c = finalize(v)",
           'print("x")']
    leaks = A.detect_commented_solution_leak(src)
    assert len(leaks) == 1
    assert leaks[0]["lines"] == 4


def test_pedagogical_prose_comments_not_flagged():
    # Prose comments (no code-like pattern) are the documented FP class -> no leak.
    src = ["# Ceci est un commentaire de prose pedagogique",
           "# qui explique le concept sans contenir de code",
           "# et ne doit pas etre flagge comme une fuite de solution",
           'print("x")']
    assert A.detect_commented_solution_leak(src) == []


def test_short_comment_block_not_flagged():
    # Only 2 code-like comments (<=3) -> no leak.
    src = ["# expected = 1", "# result = 2", 'print("x")']
    assert A.detect_commented_solution_leak(src) == []


# --- detect_preresolved_cells --------------------------------------------

def test_preresolved_solution_cell_flagged():
    # `# Solution` on the first line + >3 code lines -> LOW leak.
    cell = {"cell_type": "code",
            "source": ["# Solution\nx = 1\ny = 2\nz = 3\nw = 4"]}
    leaks = A.detect_preresolved_cells([cell])
    assert len(leaks) == 1
    assert leaks[0]["type"] == "preresolved_cell"
    assert leaks[0]["severity"] == "LOW"
    assert leaks[0]["code_lines"] == 4


def test_preresolved_exemple_resolu_flagged():
    cell = {"cell_type": "code",
            "source": ["# Exemple resolu\na = 1\nb = 2\nc = 3\nd = 4"]}
    leaks = A.detect_preresolved_cells([cell])
    assert len(leaks) == 1


def test_preresolved_stub_solution_not_flagged():
    # `# Solution` but only comment lines (a stub) -> no leak.
    cell = {"cell_type": "code",
            "source": ["# Solution\n# TODO etudiant"]}
    assert A.detect_preresolved_cells([cell]) == []


def test_preresolved_short_solution_not_flagged():
    # `# Solution` with <=3 code lines -> no leak.
    cell = {"cell_type": "code",
            "source": ["# Solution\nx = 1\ny = 2"]}
    assert A.detect_preresolved_cells([cell]) == []


def test_preresolved_skips_markdown_cells():
    cells = [{"cell_type": "markdown", "source": ["# Solution\nstuff"]}]
    assert A.detect_preresolved_cells(cells) == []


# --- detect_csharp_leak_candidates ---------------------------------------

def test_csharp_exercice_body_flagged():
    # `// Exercice` + >3 code lines + NO stub marker -> csharp_exercice_body FLAG.
    cell = {"cell_type": "code",
            "source": ["// Exercice 1\n"
                       "var x = Compute(data);\n"
                       "var y = Transform(x);\n"
                       "var z = Combine(y);\n"
                       "return z;"]}
    out = A.detect_csharp_leak_candidates([cell])
    assert len(out) == 1
    assert out[0]["type"] == "csharp_exercice_body"
    assert out[0]["severity"] == "FLAG"


def test_csharp_exercice_with_stub_not_flagged():
    # `// Exercice` + stub marker (// TODO) -> legit student stub, NOT flagged.
    cell = {"cell_type": "code",
            "source": ["// Exercice 1\n"
                       "// TODO etudiant\n"
                       "var a = 1;\n"
                       "var b = 2;\n"
                       "var c = 3;\n"
                       "return;"]}
    assert A.detect_csharp_leak_candidates([cell]) == []


def test_csharp_solution_flagged_as_preresolved():
    # `// Solution` cell -> csharp_preresolved FLAG (verdict left to reviewer).
    cell = {"cell_type": "code",
            "source": ["// Solution\n"
                       "var x = 1;\n"
                       "var y = 2;\n"
                       "var z = 3;\n"
                       "var w = 4;"]}
    out = A.detect_csharp_leak_candidates([cell])
    assert len(out) == 1
    assert out[0]["type"] == "csharp_preresolved"
    assert out[0]["severity"] == "FLAG"


def test_csharp_short_exercice_not_flagged():
    # `// Exercice` with <=3 code lines -> below threshold, not flagged.
    cell = {"cell_type": "code",
            "source": ["// Exercice 1\nvar x = 1;\nvar y = 2;"]}
    assert A.detect_csharp_leak_candidates([cell]) == []


def test_csharp_no_marker_not_flagged():
    # A cell with no C# exercice/solution marker is invisible to this detector.
    cell = {"cell_type": "code",
            "source": ["var x = Compute(data);\n"
                       "var y = Transform(x);\n"
                       "var z = Combine(y);\n"
                       "return z;"]}
    assert A.detect_csharp_leak_candidates([cell]) == []
