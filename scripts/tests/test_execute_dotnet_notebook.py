"""Tests for scripts/notebook_tools/execute_dotnet_notebook.py.

Covers the timeout + cell-success accounting regression that this module
shipped with:

1. **Timeout diagnostic** -- jupyter_client's ``get_iopub_msg`` raises
   ``queue.Empty`` when no message arrives within ``timeout``. The previous
   detection ``'timeout' in str(e).lower()`` never matched:
   ``str(queue.Empty())`` is the empty string, so the branch was dead by
   construction and a timed-out cell surfaced as an EMPTY error message via
   the outer handler. The fix detects the actual ``queue.Empty`` type (plus a
   string fallback for any other timeout-named exception) and reports a clean
   ``'Timeout after <N>s'`` message.
2. **Timeout cell success** -- a timed-out cell must report
   ``success=False``. Previously ``cell_result['success'] = not has_error``
   was True (``has_error`` never flipped on the timeout path), so a timed-out
   cell was BOTH ``successful`` and ``errors`` -- a double-count.

The kernel-client message flow is mocked to mirror the real .NET Interactive
kernel: a successful cell emits an ``idle`` status, an error cell emits the
error message THEN an ``idle`` status (so the loop exits cleanly), and a
hang/timeout emits nothing (raises ``queue.Empty``).

Tests are CPU-only / hermetic: no real .NET kernel, no subprocess, no
network. Mirrors the file-path-load pattern of ``test_execute_sudoku_python``
and stubs ``jupyter_client`` so the module imports without the dependency.
"""
from __future__ import annotations

import importlib.util
import json
import sys
import types
from pathlib import Path
from queue import Empty as QueueEmpty

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
MODULE_PATH = SCRIPTS_DIR / "notebook_tools" / "execute_dotnet_notebook.py"  # relogé #13737 V3


def _load_module(monkeypatch):
    """Load ``execute_dotnet_notebook.py`` by file path with a stubbed
    ``jupyter_client`` (the module imports it at top level).

    The stub KernelManager holds a fake client whose ``get_iopub_msg`` plays a
    script of messages (set per-test via the module-level ``_MODE`` sentinel).
    """
    jc = types.ModuleType("jupyter_client")

    class _FakeClient:
        def __init__(self, mode: str):
            self.mode = mode
            self._n = 0
            self.executed: list[str] = []

        def execute(self, code):
            self.executed.append(code)
            self._n = 0  # each submission replays the scripted scenario

        def get_shell_msg(self, timeout=10):
            return {"content": {"status": "ok"}}

        def get_iopub_msg(self, timeout=300):
            self._n += 1
            # The real kernel announces each submission with `execute_input`,
            # carrying its OWN execution_count; the target notebook is expected
            # to persist that value. Emitted first, except in the timeout
            # scenario where nothing ever arrives.
            if self._n == 1:
                if self.mode == "timeout":
                    raise QueueEmpty()
                return {"msg_type": "execute_input",
                        "content": {"execution_count": len(self.executed)}}
            # Second message per the scripted scenario; thereafter idle so the
            # loop terminates cleanly (the real kernel sends idle after any
            # terminal state -- error or success).
            if self._n == 2:
                if self.mode == "success":
                    return {"msg_type": "status",
                            "content": {"execution_state": "idle"}}
                if self.mode == "error":
                    return {"msg_type": "error",
                            "content": {"ename": "Error",
                                        "evalue": "boom",
                                        "traceback": ["tb"]}}
            # After the scripted messages, emit idle (clean exit) or
            # keep raising Empty (for the timeout mode, never reached because
            # the loop already broke).
            if self.mode == "timeout":
                raise QueueEmpty()
            return {"msg_type": "status",
                    "content": {"execution_state": "idle"}}

        def stop_channels(self):
            pass

    class _FakeKernelManager:
        # Every manager constructed during one test, so tests can assert the
        # cwd it was started with and how many submissions the fake client saw.
        instances: list = []

        # Mirrors the real jupyter_client signature: `KernelManager` carries no
        # `cwd` parameter, so the value is swallowed by `**kwargs` and has NO
        # effect (measured 2026-11-21: no `cwd` attribute is left at all).
        # Keeping the same shape here means the tests fail if the module ever
        # passes cwd to the constructor instead of to `start_kernel`.
        def __init__(self, kernel_name=None, **kwargs):
            self.kernel_name = kernel_name
            self.ctor_kwargs = kwargs
            self.cwd = None
            self._client = _FakeClient(_MODE[0])
            _FakeKernelManager.instances.append(self)

        def start_kernel(self, cwd=None, **kwargs):
            self.cwd = cwd

        def client(self):
            return self._client

        def shutdown_kernel(self):
            pass

    jc.KernelManager = _FakeKernelManager
    monkeypatch.setitem(sys.modules, "jupyter_client", jc)

    # Module-level sentinel the fake client reads to pick its scenario.
    g = {"_MODE": ["timeout"]}
    spec = importlib.util.spec_from_file_location(
        "execute_dotnet_notebook_under_test", MODULE_PATH)
    mod = importlib.util.module_from_spec(spec)
    # Inject the sentinel BEFORE exec so the fake client (constructed at
    # module import time only if it captured globals -- it reads _MODE lazily
    # via the module's globals at call time, so we set it on the module after).
    spec.loader.exec_module(mod)
    # Expose the fake manager class so tests can read the cwd it was given and
    # the submissions its client saw.
    mod._fake_km_class = _FakeKernelManager
    # Make _MODE reachable from the fake client's closure. The closure was
    # built in this test function's scope, so _MODE here IS the one it reads.
    return mod, g


# Shared mutable sentinel: the fake client reads this to script its scenario.
_MODE = ["timeout"]


def _run_one_cell(monkeypatch, mode: str, timeout: int = 1):
    """Execute a minimal 1-code-cell notebook under the scripted `mode`."""
    global _MODE
    _MODE[0] = mode
    mod, _ = _load_module(monkeypatch)
    nb = {
        "cells": [{"cell_type": "code", "source": "var x = 1;",
                   "outputs": [], "execution_count": None}],
        "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
    }
    import io, contextlib, tempfile, os
    f = tempfile.NamedTemporaryFile(
        mode="w", suffix=".ipynb", delete=False, encoding="utf-8")
    json.dump(nb, f)
    f.close()
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            res = mod.execute_dotnet_notebook(f.name, timeout=timeout)
    finally:
        os.unlink(f.name)
    return res


# ── Timeout scenario: the founding defect this module shipped with ────────

class TestTimeoutDiagnostic:
    """A timed-out cell must report a clean 'Timeout after <N>s' message and
    success=False (was: empty error string AND success=True)."""

    def test_timeout_reports_clean_message(self, monkeypatch):
        res = _run_one_cell(monkeypatch, "timeout", timeout=7)
        assert res["cells"][0]["error"] == "Timeout after 7s"

    def test_timeout_cell_is_not_successful(self, monkeypatch):
        res = _run_one_cell(monkeypatch, "timeout")
        assert res["cells"][0]["success"] is False

    def test_timeout_counted_once_in_errors_not_in_successful(self, monkeypatch):
        """Previously a timed-out cell was BOTH `successful` (has_error never
        flipped) AND `errors` -- a double-count. Now it is errors-only."""
        res = _run_one_cell(monkeypatch, "timeout")
        assert res["errors"] == 1
        assert res["successful"] == 0
        assert res["executed"] == 1

    def test_timeout_does_not_raise(self, monkeypatch):
        """The dead branch previously re-raised the Empty, surfacing as an
        empty error via the outer handler. The fix handles it in-loop."""
        res = _run_one_cell(monkeypatch, "timeout")
        # No uncaught exception (we got a result dict); error field populated.
        assert res["errors"] == 1


# ── Success + error scenarios: confirm the fix did not regress them ───────

class TestSuccessAndErrorPaths:
    def test_successful_cell_reports_success(self, monkeypatch):
        res = _run_one_cell(monkeypatch, "success")
        assert res["cells"][0]["success"] is True
        assert res["successful"] == 1
        assert res["errors"] == 0

    def test_error_cell_reports_failure_clean_message(self, monkeypatch):
        res = _run_one_cell(monkeypatch, "error")
        assert res["cells"][0]["success"] is False
        assert res["cells"][0]["error"] == "boom"
        assert res["errors"] == 1
        assert res["successful"] == 0


# ── Bookkeeping invariants across a multi-cell notebook ───────────────────

class TestBookkeeping:
    def test_executed_counts_only_code_cells(self, monkeypatch):
        """Non-code cells (markdown) are skipped; `executed` counts code only."""
        global _MODE
        _MODE[0] = "success"
        mod, _ = _load_module(monkeypatch)
        nb = {
            "cells": [
                {"cell_type": "markdown", "source": "# hi", "outputs": [],
                 "execution_count": None},
                {"cell_type": "code", "source": "var a = 1;", "outputs": [],
                 "execution_count": None},
                {"cell_type": "markdown", "source": "# bye", "outputs": [],
                 "execution_count": None},
                {"cell_type": "code", "source": "var b = 2;", "outputs": [],
                 "execution_count": None},
            ],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
        }
        import io, contextlib, tempfile, os
        f = tempfile.NamedTemporaryFile(
            mode="w", suffix=".ipynb", delete=False, encoding="utf-8")
        json.dump(nb, f)
        f.close()
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                res = mod.execute_dotnet_notebook(f.name, timeout=1)
        finally:
            os.unlink(f.name)
        assert res["total_cells"] == 4
        assert res["code_cells"] == 2
        assert res["executed"] == 2
        assert res["successful"] == 2


# ── Execution evidence: count persisted, cwd given, no setup submission ───

class TestExecutionEvidence:
    """The organ used to leave `execution_count` null on every cell (the
    kernel's own count was never persisted, so check_exec_sequence reported
    PARTIAL) and consumed count 1 with a `SetCurrentDirectory` setup
    submission. Both are fixed here: the count is stored from the kernel's
    `execute_input` message, and the cwd is given to the kernel process
    instead of being set by an extra execution."""

    def _run_and_keep(self, monkeypatch, mode="success"):
        global _MODE
        _MODE[0] = mode
        mod, _ = _load_module(monkeypatch)
        nb = {
            "cells": [
                {"cell_type": "markdown", "source": "# hi", "metadata": {}},
                {"cell_type": "code", "source": "var a = 1;", "outputs": [],
                 "execution_count": None},
                {"cell_type": "code", "source": "var b = 2;", "outputs": [],
                 "execution_count": None},
            ],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
        }
        import io, contextlib, tempfile, os
        f = tempfile.NamedTemporaryFile(
            mode="w", suffix=".ipynb", delete=False, encoding="utf-8")
        json.dump(nb, f)
        f.close()
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                mod.execute_dotnet_notebook(f.name, timeout=1)
            saved = json.loads(Path(f.name).read_text(encoding="utf-8"))
        finally:
            os.unlink(f.name)
        return mod, saved, Path(f.name).resolve()

    def test_execution_count_is_persisted(self, monkeypatch):
        _, saved, _ = self._run_and_keep(monkeypatch)
        counts = [c["execution_count"] for c in saved["cells"]
                  if c["cell_type"] == "code"]
        assert counts == [1, 2], f"counts persistes attendus [1, 2], lu {counts}"

    def test_kernel_started_in_notebook_directory(self, monkeypatch):
        mod, _, path = self._run_and_keep(monkeypatch)
        km = mod._fake_km_class.instances[-1]
        assert km.cwd == str(path.parent), (
            "le noyau doit demarrer dans le dossier du carnet (cwd passe a "
            "start_kernel), pas via une execution de setup")
        # Guard the exact regression measured on 2026-11-21: `KernelManager(...,
        # cwd=...)` is swallowed by **kwargs, so passing cwd there silently
        # leaves the kernel in the launcher's directory and every
        # `#load "file.cs"` fails with CS1504.
        assert "cwd" not in km.ctor_kwargs, (
            "cwd ne doit PAS etre passe au constructeur (ignore par "
            f"jupyter_client) : {km.ctor_kwargs}")

    def test_no_setup_submission_consumes_a_count(self, monkeypatch):
        mod, _, _ = self._run_and_keep(monkeypatch)
        client = mod._fake_km_class.instances[-1]._client
        assert len(client.executed) == 2, (
            "seules les cellules de code doivent etre soumises ; une "
            f"soumission de setup decalerait les comptes : {client.executed}")
