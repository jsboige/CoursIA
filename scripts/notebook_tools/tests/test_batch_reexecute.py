"""Tests for scripts/notebook_tools/batch_reexecute.py — batch notebook re-execution.

Tests focus on pure functions: needs_reexecution, get_kernel_name.
No filesystem I/O on production files.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from batch_reexecute import (
    get_kernel_name,
    needs_reexecution,
    read_kernelspec_name,
    _normalize_kernel_paths,
)


# ---------------------------------------------------------------------------
# needs_reexecution
# ---------------------------------------------------------------------------

class TestNeedsReexecution:
    def test_broken_notebook_skipped(self):
        """BROKEN notebooks are never re-executed."""
        entry = {"status": "BROKEN", "cells_without_outputs": 5}
        assert needs_reexecution(entry) is False

    def test_missing_outputs_needs_reexec(self):
        """Notebooks with cells_without_outputs > 0 need re-execution."""
        entry = {"status": "READY", "cells_without_outputs": 3}
        assert needs_reexecution(entry) is True

    def test_zero_outputs_ok(self):
        """Notebooks with 0 missing outputs don't need re-execution."""
        entry = {"status": "READY", "cells_without_outputs": 0}
        assert needs_reexecution(entry) is False

    def test_no_status_field(self):
        """Missing status field defaults to not BROKEN."""
        entry = {"cells_without_outputs": 2}
        assert needs_reexecution(entry) is True

    def test_no_outputs_field(self):
        """Missing cells_without_outputs defaults to 0."""
        entry = {"status": "READY"}
        assert needs_reexecution(entry) is False

    def test_empty_entry(self):
        """Empty dict needs no re-execution."""
        assert needs_reexecution({}) is False

    def test_status_draft_with_missing(self):
        """DRAFT status with missing outputs still needs re-execution."""
        entry = {"status": "DRAFT", "cells_without_outputs": 1}
        assert needs_reexecution(entry) is True


# ---------------------------------------------------------------------------
# get_kernel_name
# ---------------------------------------------------------------------------

class TestGetKernelName:
    def test_python3(self):
        assert get_kernel_name({"kernel": "Python 3"}) == "python3"

    def test_python3_case_insensitive(self):
        assert get_kernel_name({"kernel": "python 3"}) == "python3"

    def test_dotnet_csharp(self):
        assert get_kernel_name({"kernel": ".NET (C#)"}) == ".net-interactive"

    def test_dotnet_fsharp(self):
        assert get_kernel_name({"kernel": ".NET (F#)"}) == ".net-interactive"

    def test_csharp_direct(self):
        assert get_kernel_name({"kernel": "C# Interactive"}) == ".net-interactive"

    def test_unknown_kernel_passthrough(self):
        """Unknown kernel names are passed through as-is (lowercased)."""
        assert get_kernel_name({"kernel": "Lean4"}) == "lean4"

    def test_empty_kernel(self):
        assert get_kernel_name({"kernel": ""}) == ""

    def test_missing_kernel_key(self):
        assert get_kernel_name({}) == ""

    def test_python3_exact(self):
        """Exact 'Python 3' match."""
        assert get_kernel_name({"kernel": "Python 3 (ipykernel)"}) == "python3"

    def test_dotnet_in_name(self):
        """Any '.net' substring maps to .net-interactive."""
        assert get_kernel_name({"kernel": ".NET Interactive"}) == ".net-interactive"

    def test_kernelspec_shaped_passthrough_csharp(self):
        """A kernelspec name (no space) from --path passes through untouched
        instead of being remapped to an unrelated kernel (#11199)."""
        assert get_kernel_name({"kernel": ".net-csharp"}) == ".net-csharp"

    def test_kernelspec_shaped_passthrough_fsharp(self):
        assert get_kernel_name({"kernel": ".net-fsharp"}) == ".net-fsharp"

    def test_kernelspec_shaped_passthrough_python3(self):
        assert get_kernel_name({"kernel": "python3"}) == "python3"

    def test_kernelspec_shaped_passthrough_wsl(self):
        assert get_kernel_name({"kernel": "lean4-wsl"}) == "lean4-wsl"


# ---------------------------------------------------------------------------
# read_kernelspec_name — kernel truth source for --path (#11199)
# ---------------------------------------------------------------------------

class TestReadKernelspecName:
    def _write_nb(self, tmp_path: Path, metadata: dict) -> Path:
        nb = {"cells": [], "metadata": metadata, "nbformat": 4,
              "nbformat_minor": 5}
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        return p

    def test_reads_kernelspec_name(self, tmp_path):
        p = self._write_nb(
            tmp_path,
            {"kernelspec": {"name": ".net-csharp", "language": "C#"}},
        )
        assert read_kernelspec_name(p) == ".net-csharp"

    def test_missing_kernelspec_falls_back_to_python3(self, tmp_path):
        p = self._write_nb(tmp_path, {})
        assert read_kernelspec_name(p) == "python3"

    def test_empty_kernelspec_name_falls_back(self, tmp_path):
        p = self._write_nb(tmp_path, {"kernelspec": {"name": ""}})
        assert read_kernelspec_name(p) == "python3"

    def test_malformed_json_falls_back(self, tmp_path):
        p = tmp_path / "broken.ipynb"
        p.write_text("{not json", encoding="utf-8")
        assert read_kernelspec_name(p) == "python3"

    def test_missing_file_falls_back(self, tmp_path):
        assert read_kernelspec_name(tmp_path / "ghost.ipynb") == "python3"


# ---------------------------------------------------------------------------
# _normalize_kernel_paths — strip_machine_paths wired into the re-exec path (#10061)
# ---------------------------------------------------------------------------

def _nb_with_ipykernel_leak(pid: int):
    """Build a minimal nbformat-4 notebook whose single code cell carries a
    stream output with a username + ipykernel_<pid> kernel-injected path."""
    return {
        "cells": [
            {
                "cell_type": "code",
                "execution_count": 1,
                "source": ["print('hi')\n"],
                "outputs": [
                    {
                        "output_type": "stream",
                        "name": "stderr",
                        "text": [
                            f"C:\\Users\\jsboi\\AppData\\Local\\Temp\\ipykernel_{pid}"
                            f"\\1424116259.py:8: DeprecationWarning\n"
                        ],
                    }
                ],
                "metadata": {},
            }
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


class TestNormalizeKernelPaths:
    """#10061 — re-exec must auto-normalize username paths AND per-execution
    PIDs so two runs produce byte-identical output (no spurious diff)."""

    def test_normalizes_username_and_pid(self, tmp_path):
        import json

        nb_path = tmp_path / "nb.ipynb"
        nb_path.write_text(json.dumps(_nb_with_ipykernel_leak(30104)), encoding="utf-8")

        fixed = _normalize_kernel_paths(nb_path)
        # The leak line was detected and normalized.
        assert fixed >= 1
        out = json.loads(nb_path.read_text(encoding="utf-8"))
        text = out["cells"][0]["outputs"][0]["text"][0]
        # Username is redacted, PID is normalized to the stable placeholder.
        assert "jsboi" not in text
        assert "30104" not in text
        assert "ipykernel_<pid>" in text
        assert "<USER_PATH>" in text
        # The per-cell source hash (stable, pedagogy) survives.
        assert "1424116259.py" in text

    def test_two_reexecs_produce_identical_output(self, tmp_path):
        """Acceptance (a): two re-execs differing only in the PID redact to the
        same byte-identical output → empty git diff on the PID motif."""
        import json

        a = tmp_path / "a.ipynb"
        b = tmp_path / "b.ipynb"
        a.write_text(json.dumps(_nb_with_ipykernel_leak(30104)), encoding="utf-8")
        b.write_text(json.dumps(_nb_with_ipykernel_leak(55982)), encoding="utf-8")
        _normalize_kernel_paths(a)
        _normalize_kernel_paths(b)
        assert a.read_text(encoding="utf-8") == b.read_text(encoding="utf-8")

    def test_idempotent(self, tmp_path):
        """Re-normalizing an already-clean notebook is a no-op (no leak → 0)."""
        import json

        nb_path = tmp_path / "nb.ipynb"
        nb_path.write_text(json.dumps(_nb_with_ipykernel_leak(30104)), encoding="utf-8")
        first = _normalize_kernel_paths(nb_path)
        assert first >= 1
        second = _normalize_kernel_paths(nb_path)
        assert second == 0
