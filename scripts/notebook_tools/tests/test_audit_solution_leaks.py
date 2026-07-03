"""Tests for scripts/notebook_tools/audit_solution_leaks.py — solution leak detector.

Tests focus on pure functions: detect_function_body_leak, detect_commented_solution_leak,
detect_preresolved_cells, get_cells_after_exercice_md, and audit_notebook (via tmp_path).
No filesystem I/O on production files.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from audit_solution_leaks import (
    audit_notebook,
    detect_commented_solution_leak,
    detect_csharp_leak_candidates,
    detect_function_body_leak,
    detect_preresolved_cells,
    get_cells_after_exercice_md,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _code_cell(source, cell_index=0):
    """Build a code cell."""
    return {
        "cell_type": "code",
        "source": [source] if isinstance(source, str) else source,
        "execution_count": 1,
        "outputs": [],
        "metadata": {},
    }


def _md_cell(source):
    """Build a markdown cell."""
    return {
        "cell_type": "markdown",
        "source": [source] if isinstance(source, str) else source,
        "metadata": {},
    }


def _write_nb(tmp_path, nb_dict, name="test.ipynb"):
    """Write notebook dict to temp file and return path."""
    p = tmp_path / name
    p.write_text(json.dumps(nb_dict), encoding="utf-8")
    return str(p)


# ---------------------------------------------------------------------------
# detect_function_body_leak
# ---------------------------------------------------------------------------

class TestDetectFunctionBodyLeak:
    def test_no_function(self):
        lines = ["x = 1", "y = 2", "print(x + y)"]
        assert detect_function_body_leak(lines) == []

    def test_stub_pass_not_leak(self):
        """Function with 'pass' is not a leak."""
        lines = ["def exercise():", "    pass"]
        assert detect_function_body_leak(lines) == []

    def test_stub_return_none_not_leak(self):
        """Function with 'return None' is not a leak."""
        lines = ["def exercise():", "    return None"]
        assert detect_function_body_leak(lines) == []

    def test_stub_print_not_leak(self):
        """Function with print stub is not a leak."""
        lines = ["def exercise():", '    print("Exercice a completer")']
        assert detect_function_body_leak(lines) == []

    def test_stub_return_empty_not_leak(self):
        """Functions returning empty collections are stubs."""
        for ret in ["return []", "return {}", 'return ""', "return 0",
                     "return False", "return True"]:
            lines = ["def exercise():", f"    {ret}"]
            assert detect_function_body_leak(lines) == [], f"Failed for {ret}"

    def test_real_solution_detected(self):
        """Function with >3 logic lines is a leak."""
        lines = [
            "def exercise():",
            "    total = 0",
            "    for x in data:",
            "        total += x * 2",
            "        if total > threshold:",
            "            total = threshold",
            "    return total",
        ]
        leaks = detect_function_body_leak(lines)
        assert len(leaks) == 1
        assert leaks[0]["type"] == "function_body_leak"
        assert leaks[0]["func_name"] == "exercise"
        assert leaks[0]["severity"] == "HIGH"

    def test_exactly_4_logic_lines_medium(self):
        """Function with exactly 4 logic lines = MEDIUM severity."""
        lines = [
            "def exercise():",
            "    x = compute(a)",
            "    y = compute(b)",
            "    z = compute(c)",
            "    return x + y + z",
        ]
        leaks = detect_function_body_leak(lines)
        assert len(leaks) == 1
        assert leaks[0]["severity"] == "MEDIUM"
        assert leaks[0]["logic_lines"] == 4

    def test_exactly_3_logic_lines_not_leak(self):
        """Function with <=3 logic lines is not a leak."""
        lines = [
            "def exercise():",
            "    x = 1",
            "    y = 2",
            "    return x + y",
        ]
        assert detect_function_body_leak(lines) == []

    def test_two_functions_one_leak(self):
        """Only the function with >3 logic lines should be flagged."""
        lines = [
            "def helper():",
            "    pass",
            "",
            "def solution():",
            "    total = 0",
            "    for x in data:",
            "        total += process(x)",
            "        if total > max_val:",
            "            break",
            "    return total",
        ]
        leaks = detect_function_body_leak(lines)
        assert len(leaks) == 1
        assert leaks[0]["func_name"] == "solution"

    def test_comments_not_counted(self):
        """Comment lines don't count as logic."""
        lines = [
            "def exercise():",
            "    # This is a comment",
            '    """Docstring"""',
            "    x = 1",
            "    return x",
        ]
        assert detect_function_body_leak(lines) == []

    def test_return_with_todo_not_leak(self):
        """'return ... TODO' is not a leak."""
        lines = ["def exercise():", "    return None  # TODO: implement"]
        assert detect_function_body_leak(lines) == []

    def test_nested_function(self):
        """Nested function with >3 lines is detected."""
        lines = [
            "def outer():",
            "    def inner():",
            "        x = compute()",
            "        y = transform(x)",
            "        z = validate(y)",
            "        return z",
            "    return inner()",
        ]
        leaks = detect_function_body_leak(lines)
        assert len(leaks) >= 1

    def test_6_logic_lines_high(self):
        """Function with >5 logic lines is HIGH severity."""
        lines = [
            "def exercise():",
            "    x = step1()",
            "    y = step2(x)",
            "    z = step3(y)",
            "    w = step4(z)",
            "    v = step5(w)",
            "    return step6(v)",
        ]
        leaks = detect_function_body_leak(lines)
        assert len(leaks) == 1
        assert leaks[0]["severity"] == "HIGH"
        assert leaks[0]["logic_lines"] == 6


# ---------------------------------------------------------------------------
# detect_commented_solution_leak
# ---------------------------------------------------------------------------

class TestDetectCommentedSolutionLeak:
    def test_no_comments(self):
        lines = ["x = 1", "y = 2"]
        assert detect_commented_solution_leak(lines) == []

    def test_short_comment_block_not_leak(self):
        """Comment block <=3 lines is not a leak."""
        lines = [
            "# result = compute()",
            "# expected = [1, 2, 3]",
            "# answer = 42",
        ]
        assert detect_commented_solution_leak(lines) == []

    def test_long_commented_code_block_leak(self):
        """Comment block >3 lines with code patterns is a leak."""
        lines = [
            "# result = compute(input_data)",
            "# expected = [1, 2, 3, 4, 5]",
            "# for item in expected:",
            "#     if item > threshold:",
            "#         result.append(item)",
        ]
        leaks = detect_commented_solution_leak(lines)
        assert len(leaks) == 1
        assert leaks[0]["type"] == "commented_solution_leak"
        assert leaks[0]["severity"] == "MEDIUM"

    def test_normal_comments_not_leak(self):
        """Comments that don't look like code are not detected."""
        lines = [
            "# This section explains the algorithm",
            "# We use a greedy approach",
            "# The complexity is O(n log n)",
            "# See reference for details",
        ]
        assert detect_commented_solution_leak(lines) == []

    def test_shebang_not_counted(self):
        """Shebang lines are not counted."""
        lines = ["#!/usr/bin/env python3"]
        assert detect_commented_solution_leak(lines) == []

    def test_magic_comment_not_counted(self):
        """IPython magic comments (# @) are not counted."""
        lines = ["# @markdown Input parameter"]
        assert detect_commented_solution_leak(lines) == []

    def test_solution_keyword_in_comments(self):
        """Comments with 'solution' keyword are flagged even in short blocks if >3."""
        lines = [
            "# solution = algorithm(data)",
            "# solution = optimize(solution)",
            "# solution = validate(solution)",
            "# solution = final_answer(solution)",
        ]
        leaks = detect_commented_solution_leak(lines)
        assert len(leaks) == 1

    def test_two_separate_blocks(self):
        """Two separate comment blocks produce separate leaks."""
        lines = [
            "# prof_result = compute(a)",
            "# prof_expected = [1, 2]",
            "# prof_answer = 42",
            "# prof_check = validate()",
            "x = 1",  # separator
            "# result = process(b)",
            "# expected = [3, 4]",
            "# answer = 99",
            "# correct = True",
        ]
        leaks = detect_commented_solution_leak(lines)
        assert len(leaks) == 2


# ---------------------------------------------------------------------------
# detect_preresolved_cells
# ---------------------------------------------------------------------------

class TestDetectPreresolvedCells:
    def test_no_preresolved(self):
        cells = [_code_cell("x = 1"), _md_cell("# Title")]
        assert detect_preresolved_cells(cells) == []

    def test_solution_cell_with_code(self):
        """Code cell starting with # Solution and >3 code lines is preresolved."""
        source = (
            "# Solution\n"
            "x = compute(data)\n"
            "y = transform(x)\n"
            "z = validate(y)\n"
            "result = aggregate(x, y, z)\n"
        )
        cells = [_code_cell(source)]
        leaks = detect_preresolved_cells(cells)
        assert len(leaks) == 1
        assert leaks[0]["type"] == "preresolved_cell"
        assert leaks[0]["severity"] == "LOW"
        assert leaks[0]["cell_index"] == 0

    def test_exemple_resolu_detected(self):
        """# Exemple resolu header with >3 code lines is detected."""
        source = (
            "# Exemple resolu\n"
            "data = load()\n"
            "processed = clean(data)\n"
            "result = analyze(processed)\n"
            "output = format(result)\n"
        )
        cells = [_code_cell(source)]
        leaks = detect_preresolved_cells(cells)
        assert len(leaks) == 1

    def test_solution_short_not_detected(self):
        """# Solution cell with <=3 code lines is not flagged."""
        source = "# Solution\nx = 1\ny = 2\n"
        cells = [_code_cell(source)]
        assert detect_preresolved_cells(cells) == []

    def test_solution_only_comments_not_detected(self):
        """# Solution cell with only comment lines is not flagged."""
        source = "# Solution\n# Step 1\n# Step 2\n# Step 3\n# Step 4\n"
        cells = [_code_cell(source)]
        assert detect_preresolved_cells(cells) == []

    def test_markdown_cells_ignored(self):
        """Markdown cells are not checked for preresolved."""
        cells = [_md_cell("# Solution complete\n## Full answer")]
        assert detect_preresolved_cells(cells) == []

    def test_reponse_marker(self):
        """# Reponse: header is detected."""
        source = (
            "# Reponse: exercice 3\n"
            "def solve():\n"
            "    a = 1\n"
            "    b = 2\n"
            "    return a + b\n"
        )
        cells = [_code_cell(source)]
        leaks = detect_preresolved_cells(cells)
        assert len(leaks) == 1

    def test_solution_not_first_line(self):
        """Solution marker must be on the first line to be detected."""
        source = (
            "x = 1\n"
            "# Solution\n"
            "y = 2\n"
            "z = 3\n"
            "w = 4\n"
        )
        cells = [_code_cell(source)]
        # First line is 'x = 1', not '# Solution'
        assert detect_preresolved_cells(cells) == []


# ---------------------------------------------------------------------------
# get_cells_after_exercice_md
# ---------------------------------------------------------------------------

class TestGetCellsAfterExerciceMd:
    def test_code_cells_following_md(self):
        """Returns code cells after exercice markdown header.
        Note: plain markdown text (no heading) does NOT stop the scan —
        only markdown headings (lines starting with #) break the sequence."""
        cells = [
            _md_cell("## Exercice 1"),
            _code_cell("x = 1"),
            _md_cell("Some explanation"),  # NOT a heading, so doesn't stop
            _code_cell("y = 2"),
        ]
        result = get_cells_after_exercice_md(cells, 0)
        # Both code cells are within range (no heading to stop)
        assert len(result) == 2
        assert result[0][0] == 1
        assert result[1][0] == 3

    def test_stops_at_next_heading(self):
        """Stops when hitting another markdown heading."""
        cells = [
            _md_cell("## Exercice 1"),
            _code_cell("x = 1"),
            _md_cell("# New Section"),
            _code_cell("y = 2"),
        ]
        result = get_cells_after_exercice_md(cells, 0)
        assert len(result) == 1

    def test_stops_at_next_exercice(self):
        """Stops when hitting another exercice header."""
        cells = [
            _md_cell("## Exercice 1"),
            _code_cell("x = 1"),
            _md_cell("## Exercice 2"),
            _code_cell("y = 2"),
        ]
        result = get_cells_after_exercice_md(cells, 0)
        assert len(result) == 1

    def test_no_code_cells(self):
        """No code cells following = empty result."""
        cells = [
            _md_cell("## Exercice 1"),
            _md_cell("Explanation"),
            _md_cell("# Next section"),
        ]
        result = get_cells_after_exercice_md(cells, 0)
        assert result == []

    def test_max_range(self):
        """Only checks up to 5 cells after start."""
        cells = [
            _md_cell("## Exercice 1"),
            _code_cell("a = 1"),
            _code_cell("b = 2"),
            _code_cell("c = 3"),
            _code_cell("d = 4"),
            _code_cell("e = 5"),  # beyond range
        ]
        result = get_cells_after_exercice_md(cells, 0)
        assert len(result) == 4  # only indices 1-4

    def test_at_end_of_notebook(self):
        """Works when exercice is last cell."""
        cells = [
            _md_cell("## Exercice 1"),
        ]
        result = get_cells_after_exercice_md(cells, 0)
        assert result == []

    def test_middle_of_notebook(self):
        """Works when exercice is in the middle."""
        cells = [
            _md_cell("# Introduction"),
            _code_cell("setup = True"),
            _md_cell("## Exercice 1"),
            _code_cell("answer = 42"),
            _md_cell("## Conclusion"),
        ]
        result = get_cells_after_exercice_md(cells, 2)
        assert len(result) == 1
        assert result[0][0] == 3


# ---------------------------------------------------------------------------
# audit_notebook (integration via tmp_path)
# ---------------------------------------------------------------------------

class TestAuditNotebook:
    def test_clean_notebook(self, tmp_path):
        """Clean notebook with no leaks."""
        nb = {
            "cells": [
                _md_cell("# Introduction"),
                _code_cell("x = 1\nprint(x)"),
                _md_cell("# Conclusion"),
            ],
            "metadata": {},
        }
        path = _write_nb(tmp_path, nb)
        assert audit_notebook(path) == []

    def test_function_body_leak_under_exercice(self, tmp_path):
        """Function body leak detected under # Exercice marker."""
        nb = {
            "cells": [
                _code_cell("# Exercice 1\ndef solve():\n    x = compute(a)\n    y = transform(x)\n    z = validate(y)\n    return aggregate(x, y, z)"),
            ],
            "metadata": {},
        }
        path = _write_nb(tmp_path, nb)
        leaks = audit_notebook(path)
        function_leaks = [l for l in leaks if l["type"] == "function_body_leak"]
        assert len(function_leaks) >= 1

    def test_preresolved_cell(self, tmp_path):
        """Preresolved cell detected."""
        nb = {
            "cells": [
                _code_cell("# Solution\nx = compute()\ny = transform(x)\nz = validate(y)\nresult = aggregate(x, y, z)"),
            ],
            "metadata": {},
        }
        path = _write_nb(tmp_path, nb)
        leaks = audit_notebook(path)
        preresolved = [l for l in leaks if l["type"] == "preresolved_cell"]
        assert len(preresolved) == 1

    def test_stub_exercice_not_leak(self, tmp_path):
        """Exercise stubs are NOT leaks."""
        nb = {
            "cells": [
                _code_cell("# Exercice 1\ndef solve():\n    pass"),
            ],
            "metadata": {},
        }
        path = _write_nb(tmp_path, nb)
        leaks = audit_notebook(path)
        function_leaks = [l for l in leaks if l["type"] == "function_body_leak"]
        assert function_leaks == []

    def test_exercice_md_with_leak(self, tmp_path):
        """Leak detected in code cell after ## Exercice markdown."""
        nb = {
            "cells": [
                _md_cell("## Exercice 1"),
                _code_cell("def solve():\n    x = compute(a)\n    y = transform(x)\n    z = validate(y)\n    return aggregate(x, y, z)"),
            ],
            "metadata": {},
        }
        path = _write_nb(tmp_path, nb)
        leaks = audit_notebook(path)
        function_leaks = [l for l in leaks if l["type"] == "function_body_leak"]
        assert len(function_leaks) >= 1

    def test_example_resolu_not_leak(self, tmp_path):
        """# Exemple resolu cells are not flagged as function body leaks."""
        nb = {
            "cells": [
                _code_cell("# Exemple resolu\ndef demo():\n    x = compute(a)\n    y = transform(x)\n    z = validate(y)\n    return aggregate(x, y, z)"),
            ],
            "metadata": {},
        }
        path = _write_nb(tmp_path, nb)
        leaks = audit_notebook(path)
        # Should NOT have function_body_leak (Exemple resolu is legitimate)
        function_leaks = [l for l in leaks if l["type"] == "function_body_leak"]
        assert function_leaks == []

    def test_invalid_json(self, tmp_path):
        """Invalid JSON returns empty list (no crash)."""
        p = tmp_path / "bad.ipynb"
        p.write_text("not valid json {{{", encoding="utf-8")
        assert audit_notebook(str(p)) == []

    def test_empty_notebook(self, tmp_path):
        """Empty notebook has no leaks."""
        nb = {"cells": [], "metadata": {}}
        path = _write_nb(tmp_path, nb)
        assert audit_notebook(path) == []

    def test_commented_solution_leak_in_exercice(self, tmp_path):
        """Commented solution leak detected under # Exercice marker."""
        source = (
            "# Exercice 1\n"
            "# prof_result = compute(data)\n"
            "# prof_expected = [1, 2, 3]\n"
            "# prof_answer = validate(result)\n"
            "# prof_correct = check(answer)\n"
        )
        nb = {"cells": [_code_cell(source)], "metadata": {}}
        path = _write_nb(tmp_path, nb)
        leaks = audit_notebook(path)
        comment_leaks = [l for l in leaks if l["type"] == "commented_solution_leak"]
        assert len(comment_leaks) == 1

    def test_multiple_leaks_in_notebook(self, tmp_path):
        """Multiple leak types in one notebook are all detected."""
        nb = {
            "cells": [
                _code_cell("# Exercice 1\ndef solve():\n    x = compute(a)\n    y = transform(x)\n    z = validate(y)\n    return aggregate(x, y, z)"),
                _code_cell("# Solution\nx = compute(data)\ny = transform(x)\nz = validate(y)\nresult = aggregate(x, y, z)"),
            ],
            "metadata": {},
        }
        path = _write_nb(tmp_path, nb)
        leaks = audit_notebook(path)
        types = {l["type"] for l in leaks}
        assert "function_body_leak" in types
        assert "preresolved_cell" in types


# ---------------------------------------------------------------------------
# C# / .NET Interactive leak candidates (#2161 blind-spot, complement to #5179)
# ---------------------------------------------------------------------------
# A C# notebook metadata marker so detect_csharp_leak_candidates runs.
CSHARP_META = {
    "kernelspec": {"name": ".net-csharp", "display_name": ".NET (C#)"},
    "language_info": {"name": "C#"},
}


class TestCSharpLeakCandidates:
    """The Python detectors only match `#`; C# uses `//`. These tests verify the
    C# candidate layer flags cells for MANUAL review (never auto-verdicts -- the
    example-vs-leak judgment is content-based, exercise-example-labeling rule).
    """

    def test_csharp_exercice_with_full_body_is_flagged(self, tmp_path):
        """A `// Exercice` cell holding >3 code lines and NO stub marker is a
        leak candidate (C# analogue of a Python function_body_leak)."""
        src = (
            "// Exercice : implementez le melange a 3 composantes\n"
            "public class CyclisteBase3Composantes {\n"
            "    var a = data[0];\n"
            "    var b = data[1];\n"
            "    var c = data[2];\n"
            "    var model = Mix(a, b, c);\n"
            "    return model;\n"
            "}\n"
        )
        candidates = detect_csharp_leak_candidates([_code_cell(src)])
        assert len(candidates) == 1
        assert candidates[0]["type"] == "csharp_exercice_body"
        # FLAG severity = candidate, NOT an auto-verdicted leak.
        assert candidates[0]["severity"] == "FLAG"
        assert candidates[0]["code_lines"] > 3

    def test_csharp_exercice_with_todo_stub_is_not_flagged(self, tmp_path):
        """A `// Exercice` cell with a TODO stub marker is a legit student stub
        -- NOT a leak candidate. (Guards against over-flagging 302/350 real
        C# stubs that the #5179 lesson showed are the common case.)"""
        src = (
            "// Exercice 1 : Lancer de trois pieces\n"
            "// TODO etudiant : Creer trois variables booleennes\n"
            "// TODO etudiant : Calculer la probabilite\n"
            "bool p1 = true;\n"
            "bool p2 = false;\n"
        )
        candidates = detect_csharp_leak_candidates([_code_cell(src)])
        assert len(candidates) == 0, (
            "C# exercice cell WITH TODO stub must NOT be flagged"
        )

    def test_csharp_exercice_with_few_lines_is_not_flagged(self, tmp_path):
        """A `// Exercice` cell with <=3 code lines (even without TODO) is too
        small to be a solution leak -- a real solution needs >3 logic lines."""
        src = (
            "// Exercice : court stub sans TODO\n"
            "var x = 1;\n"
            "var y = 2;\n"
        )
        candidates = detect_csharp_leak_candidates([_code_cell(src)])
        assert len(candidates) == 0

    def test_csharp_solution_cell_is_flagged_as_preresolved(self, tmp_path):
        """A `// Solution` / `// Exemple resolu` cell with >3 code lines is a
        pre-resolved candidate. It MAY be a legit worked example -- hence FLAG
        for review, not an auto-leak verdict."""
        src = (
            "// Exemple resolu : factorielle recursive\n"
            "int Factorielle(int n) {\n"
            "    if (n <= 1) return 1;\n"
            "    return n * Factorielle(n - 1);\n"
            "}\n"
            "Console.WriteLine(Factorielle(5));\n"
        )
        candidates = detect_csharp_leak_candidates([_code_cell(src)])
        assert len(candidates) == 1
        assert candidates[0]["type"] == "csharp_preresolved"
        assert candidates[0]["severity"] == "FLAG"

    def test_python_cell_is_not_double_flagged_by_csharp_layer(self, tmp_path):
        """A Python `# Exercice` cell (not C#) must NOT be picked up by the C#
        candidate layer -- `#` comments are not `//`. (Guards scope boundary.)"""
        src = (
            "# Exercice 1 : solution complete en Python\n"
            "def solve(x):\n"
            "    a = compute(x)\n"
            "    b = transform(a)\n"
            "    c = validate(b)\n"
            "    return aggregate(a, b, c)\n"
        )
        candidates = detect_csharp_leak_candidates([_code_cell(src)])
        assert len(candidates) == 0, "Python # cell must not hit the // detector"

    def test_audit_notebook_only_runs_csharp_layer_on_csharp_notebooks(
        self, tmp_path
    ):
        """A Python-kernel notebook with a `// Exercice`-looking cell must NOT
        trigger the C# layer (false-positive guard: // in a Python notebook is
        not a C# comment)."""
        # Python kernel metadata
        py_meta = {"kernelspec": {"name": "python3"}, "language_info": {"name": "python"}}
        nb = {
            "cells": [_code_cell(
                "// Exercice : ceci n'est pas un commentaire C#\n"
                "x = compute(data)  # mais ceci l'est, en Python\n"
                "y = transform(x)\n"
                "z = validate(y)\n"
                "return aggregate(x, y, z)\n"
            )],
            "metadata": py_meta,
        }
        path = _write_nb(tmp_path, nb)
        leaks = audit_notebook(path)
        csharp_types = {l["type"] for l in leaks if l["type"].startswith("csharp_")}
        assert csharp_types == set(), (
            "C# layer must NOT run on a Python-kernel notebook"
        )
