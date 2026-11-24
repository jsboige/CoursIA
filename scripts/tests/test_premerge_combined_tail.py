"""Queue de sortie pytest sur un verdict non vert (#28147).

Contrat du grain :
- l'organe ``premerge_combined_check`` publie une **queue bornee** de la
  sortie pytest sur un verdict non vert ;
- ``merge_ready`` joint cette queue au motif qu'il journalise, **aplatie en
  une ligne** ;
- sans queue, le motif reste exactement celui d'avant (le skip d'une PR
  approuvee ne doit pas changer de forme).

Aucun reseau, aucun gh : le module sous test est charge par importlib et le
runner est un stub.
"""

import importlib.util
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
COMBINED_PATH = HERE.parent / "coordination" / "premerge_combined_check.py"
MERGE_READY_PATH = HERE.parent / "coordination" / "merge_ready.py"


def _load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


combined = _load("premerge_combined_check_under_test", COMBINED_PATH)
mr = _load("merge_ready_under_test", MERGE_READY_PATH)


class _Result:
    def __init__(self, returncode: int, stdout: str = "", stderr: str = ""):
        self.returncode = returncode
        self.stdout = stdout
        self.stderr = stderr


class _StubRunner:
    """Runner qui repond par un resultat unique (l'organe n'est pas joue)."""

    def __init__(self, returncode: int, stdout: str = "", stderr: str = ""):
        self._result = _Result(returncode, stdout, stderr)
        self.calls: list[list[str]] = []

    def run(self, cmd, cwd=None, env=None, timeout=None):
        self.calls.append(list(cmd))
        return self._result


# --- l'organe : la queue est bornee et garde la fin --------------------------


def test_tail_is_empty_on_empty_output():
    assert combined._tail("") == ""
    assert combined._tail("   \n  ") == ""


def test_tail_keeps_a_short_output_verbatim():
    out = "AssertionError: 1 != 2"
    assert combined._tail(out) == out


def test_tail_keeps_the_END_of_a_long_output():
    """La cause est en fin de sortie : on tronque par la fin, on prefixe."""
    out = "HEAD\n" + ("x" * 5000) + "\nAssertionError: boom"
    tail = combined._tail(out)
    assert tail.startswith("...")
    assert tail.endswith("AssertionError: boom")
    assert len(tail) <= combined.TAIL_MAX_CHARS + 3


def test_tail_is_bounded_by_the_limit():
    tail = combined._tail("y" * 10_000, limit=100)
    assert len(tail) == 103  # "..." + 100 caracteres


# --- merge_ready : la queue est aplatie en une ligne -------------------------


def test_one_line_flattens_newlines_and_blanks():
    flat = mr._one_line("a\n  b\tc\n\nd")
    assert flat == "a b c d"
    assert "\n" not in flat


def test_one_line_is_empty_on_empty_input():
    assert mr._one_line("") == ""
    assert mr._one_line("   \n ") == ""


def test_one_line_is_bounded():
    flat = mr._one_line("z" * 5000, limit=50)
    assert len(flat) == 50
    assert flat.endswith("...")


# --- le motif journalise -----------------------------------------------------


def _reason(payload: dict, returncode: int) -> str:
    runner = _StubRunner(returncode, stdout=json.dumps(payload))
    return mr.combined_tree_reason(runner, 123, "0" * 40, {})


def test_red_reason_without_tail_is_unchanged():
    reason = _reason({"verdict": "RED",
                       "failed": ["scripts/x/test_a.py::test_u"]}, 1)
    assert reason == "combined-tree-red:scripts/x/test_a.py::test_u"


def test_red_reason_carries_the_tail_flattened_on_one_line():
    reason = _reason({
        "verdict": "RED",
        "failed": ["scripts/x/test_a.py::test_u"],
        "output_tail": "E   AssertionError: 1 != 2\nE   at foo.py:12",
    }, 1)
    assert reason.startswith("combined-tree-red:scripts/x/test_a.py::test_u")
    assert "pytest-tail:" in reason
    assert "\n" not in reason
    assert "AssertionError: 1 != 2" in reason


def test_unreadable_reason_carries_the_tail():
    reason = _reason({"verdict": "UNREADABLE", "reason": "timeout",
                       "output_tail": "TIMEOUT after 600.0s"}, 2)
    assert reason.startswith("combined-tree-unreadable:timeout")
    assert "pytest-tail:" in reason
    assert "\n" not in reason


def test_green_reason_is_none():
    assert _reason({"verdict": "GREEN"}, 0) is None


def test_conflict_reason_is_unchanged():
    assert _reason({"verdict": "CONFLICT"}, 1) == "combined-tree-conflict"
