"""Tests for scripts/notebook_tools/dotnet_executor.py — .NET Interactive executor.

The module executes .NET notebooks cell-by-cell via ``jupyter_client`` and is
consumed by ``notebook_helpers.py`` (the pipeline that gives notebooks real
``execution_count`` / outputs). It was a **test orphan**: 0 ``test_`` importers
repo-wide. This suite pins its logic without a live kernel by mocking
``jupyter_client.KernelManager`` — covering the dry-run / no-cells pure paths,
the iopub message-routing (stream / execute_result / display_data / error /
idle), the timeout branch, and ``batch_execute`` glob/skip handling.

No live kernel, no network, no .NET runtime. Fast (``time.sleep`` is patched out).
"""
import json
import sys
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import dotnet_executor  # noqa: E402


# --- fixtures ---------------------------------------------------------------

def _write_nb(path: Path, cells):
    """Write a notebook with the given cells (list of dicts)."""
    path.write_text(json.dumps({"cells": cells, "metadata": {}}), encoding="utf-8")
    return path


def _code_cell(source):
    src = source if isinstance(source, list) else [source]
    return {"cell_type": "code", "source": src, "execution_count": None, "outputs": []}


def _msg(msg_type, parent=None, **content):
    """Build an iopub message. ``parent`` (optional) sets parent_header.msg_id,
    used to exercise the parent_msg_id filter (Fix A). Messages without it mimic
    parentless kernel broadcasts, which the conservative filter keeps."""
    msg = {"msg_type": msg_type, "content": content}
    if parent is not None:
        msg["parent_header"] = {"msg_id": parent}
    return msg


def _fake_kernel(message_seq_by_cell):
    """Build a KernelManager mock whose client yields the given per-cell messages.

    ``message_seq_by_cell`` is a list of lists: each inner list is the iopub
    message sequence for one cell execution. The fake ``get_iopub_msg`` drains
    the current cell's list, then raises ``queue.Empty`` so the caller's
    ``except Exception: continue`` re-checks the deadline without consuming more.
    """
    import queue

    # exec_count = number of kc.execute() calls; the messages for the cell
    # currently executing live at seqs[exec_count - 1]. pos is the cursor
    # within that cell's sequence. execute() is called BEFORE the iopub loop,
    # so it sets up the index the loop then drains.
    state = {"exec_count": 0, "pos": 0}

    def get_iopub_msg(timeout=5):
        idx = state["exec_count"] - 1  # 0-indexed current cell
        if idx < 0 or idx >= len(message_seq_by_cell):
            raise queue.Empty
        seq = message_seq_by_cell[idx]
        if state["pos"] >= len(seq):
            raise queue.Empty
        msg = seq[state["pos"]]
        state["pos"] += 1
        return msg

    def execute(source):
        state["exec_count"] += 1
        state["pos"] = 0
        return f"msg-{state['exec_count']}"

    kc = MagicMock()
    kc.execute.side_effect = execute
    kc.get_iopub_msg.side_effect = get_iopub_msg

    km = MagicMock()
    km.client.return_value = kc
    return km, kc


@pytest.fixture(autouse=True)
def _no_sleep():
    """The executor sleeps 3s waiting for kernel-ready; patch it out for speed."""
    with patch.object(dotnet_executor.time, "sleep", return_value=None):
        yield


@pytest.fixture
def _patch_kernelmanager():
    """Yield a setter that installs the fake KernelManager."""
    holder = {}

    def install(message_seq_by_cell):
        km, kc = _fake_kernel(message_seq_by_cell)
        holder["km"] = km
        holder["kc"] = kc
        return km, kc

    with patch.object(dotnet_executor.jupyter_client, "KernelManager") as MockKM:
        # KernelManager(kernel_name=...) returns the instance we install.
        def factory(kernel_name=None):
            return holder["km"]
        MockKM.side_effect = factory
        yield install


# --- pure paths (no kernel) -------------------------------------------------

def test_no_code_cells_returns_skipped(tmp_path):
    nb = _write_nb(tmp_path / "n.ipynb", [
        {"cell_type": "markdown", "source": ["# hi"]},
    ])
    stats = dotnet_executor.execute_notebook(nb)
    assert stats == {"total": 0, "executed": 0, "errors": 0, "skipped": True}
    # Notebook left untouched (no code cells to update).
    assert json.loads(nb.read_text(encoding="utf-8"))["cells"][0]["cell_type"] == "markdown"


def test_dry_run_counts_executed_without_kernel(tmp_path):
    nb = _write_nb(tmp_path / "n.ipynb", [
        _code_cell("var a = 1;"),
        _code_cell("Console.WriteLine(a);"),  # already executed marker set below
        _code_cell("var b = 2;"),
    ])
    # Mark the 2nd cell as already executed.
    data = json.loads(nb.read_text(encoding="utf-8"))
    data["cells"][1]["execution_count"] = 1
    nb.write_text(json.dumps(data), encoding="utf-8")

    stats = dotnet_executor.execute_notebook(nb, dry_run=True)
    assert stats["skipped"] is True
    assert stats["total"] == 3
    assert stats["executed"] == 1
    assert stats["errors"] == 0


def test_dry_run_zero_executed(tmp_path):
    nb = _write_nb(tmp_path / "n.ipynb", [_code_cell("x"), _code_cell("y")])
    stats = dotnet_executor.execute_notebook(nb, dry_run=True)
    assert stats["executed"] == 0
    assert stats["total"] == 2


def test_dry_run_does_not_start_kernel(tmp_path, _patch_kernelmanager):
    """dry_run must short-circuit before KernelManager is constructed."""
    nb = _write_nb(tmp_path / "n.ipynb", [_code_cell("x")])
    dotnet_executor.execute_notebook(nb, dry_run=True)
    # KernelManager factory was never invoked (no install happened).
    assert dotnet_executor.jupyter_client.KernelManager.call_count == 0


# --- message routing (kernel mocked) ----------------------------------------

def test_stream_and_execute_result_routed(tmp_path, _patch_kernelmanager):
    nb = _write_nb(tmp_path / "n.ipynb", [_code_cell("Console.WriteLine(42);")])
    km, kc = _patch_kernelmanager([[
        _msg("status", execution_state="busy"),
        _msg("stream", name="stdout", text="42\n"),
        _msg("execute_result", data={"text/plain": "43"}),
        _msg("status", execution_state="idle"),
    ]])
    stats = dotnet_executor.execute_notebook(nb)

    assert stats["executed"] == 1
    assert stats["errors"] == 0
    cell = json.loads(nb.read_text(encoding="utf-8"))["cells"][0]
    assert cell["execution_count"] == 1
    types = [o["output_type"] for o in cell["outputs"]]
    assert types == ["stream", "execute_result"]
    assert cell["outputs"][0]["text"] == "42\n"
    assert cell["outputs"][1]["data"] == {"text/plain": "43"}
    assert cell["outputs"][1]["execution_count"] == 1
    km.shutdown_kernel.assert_called_once()


def test_display_data_routed_without_execution_count(tmp_path, _patch_kernelmanager):
    nb = _write_nb(tmp_path / "n.ipynb", [_code_cell("x.Display();")])
    _patch_kernelmanager([[
        _msg("status", execution_state="busy"),
        _msg("display_data", data={"text/html": "<b>hi</b>"}),
        _msg("status", execution_state="idle"),
    ]])
    dotnet_executor.execute_notebook(nb)
    out = json.loads(nb.read_text(encoding="utf-8"))["cells"][0]["outputs"][0]
    assert out["output_type"] == "display_data"
    assert out["data"] == {"text/html": "<b>hi</b>"}
    # display_data carries no execution_count (unlike execute_result).
    assert "execution_count" not in out


def test_error_output_increments_errors(tmp_path, _patch_kernelmanager):
    nb = _write_nb(tmp_path / "n.ipynb", [_code_cell("1/0;")])
    _patch_kernelmanager([[
        _msg("status", execution_state="busy"),
        _msg("error", ename="DivideByZero", evalue="division", traceback=["tb1", "tb2"]),
        _msg("status", execution_state="idle"),
    ]])
    stats = dotnet_executor.execute_notebook(nb)
    assert stats["errors"] == 1
    assert stats["executed"] == 1
    out = json.loads(nb.read_text(encoding="utf-8"))["cells"][0]["outputs"][0]
    assert out["output_type"] == "error"
    assert out["ename"] == "DivideByZero"
    assert out["traceback"] == ["tb1", "tb2"]


def test_execution_count_increments_across_cells(tmp_path, _patch_kernelmanager):
    nb = _write_nb(tmp_path / "n.ipynb", [_code_cell("a"), _code_cell("b"), _code_cell("c")])
    _patch_kernelmanager([
        [_msg("status", execution_state="idle")],
        [_msg("status", execution_state="idle")],
        [_msg("status", execution_state="idle")],
    ])
    stats = dotnet_executor.execute_notebook(nb)
    assert stats["executed"] == 3
    cells = json.loads(nb.read_text(encoding="utf-8"))["cells"]
    assert [c["execution_count"] for c in cells] == [1, 2, 3]


def test_timeout_branch_emits_stderr_and_counts_executed(tmp_path, _patch_kernelmanager):
    """cell_timeout=0 → while-loop skipped → TIMEOUT stderr appended, still 'executed'."""
    nb = _write_nb(tmp_path / "n.ipynb", [_code_cell("while(true);")])
    _patch_kernelmanager([[]])  # no messages needed; loop never runs
    stats = dotnet_executor.execute_notebook(nb, cell_timeout=0)
    assert stats["executed"] == 1
    out = json.loads(nb.read_text(encoding="utf-8"))["cells"][0]["outputs"][0]
    assert out["output_type"] == "stream"
    assert out["name"] == "stderr"
    assert "TIMEOUT" in out["text"]


def test_kernel_shutdown_on_success(tmp_path, _patch_kernelmanager):
    nb = _write_nb(tmp_path / "n.ipynb", [_code_cell("x")])
    km, _ = _patch_kernelmanager([[_msg("status", execution_state="idle")]])
    dotnet_executor.execute_notebook(nb)
    km.shutdown_kernel.assert_called_once()


def test_kernel_shutdown_on_error(tmp_path, _patch_kernelmanager):
    nb = _write_nb(tmp_path / "n.ipynb", [_code_cell("bad")])
    km, _ = _patch_kernelmanager([[
        _msg("error", ename="E", evalue="v", traceback=[]),
        _msg("status", execution_state="idle"),
    ]])
    dotnet_executor.execute_notebook(nb)
    # finally-block still shuts the kernel down even when a cell errored.
    km.shutdown_kernel.assert_called_once()


def test_missing_output_fields_use_defaults(tmp_path, _patch_kernelmanager):
    """An error message with no ename/evalue/traceback falls back to defaults."""
    nb = _write_nb(tmp_path / "n.ipynb", [_code_cell("x")])
    _patch_kernelmanager([[
        _msg("error"),  # empty content
        _msg("status", execution_state="idle"),
    ]])
    dotnet_executor.execute_notebook(nb)
    out = json.loads(nb.read_text(encoding="utf-8"))["cells"][0]["outputs"][0]
    assert out["ename"] == "Error"  # default
    assert out["evalue"] == ""
    assert out["traceback"] == []


# --- batch_execute ----------------------------------------------------------

def test_batch_execute_collects_results(tmp_path, _patch_kernelmanager):
    _write_nb(tmp_path / "a.ipynb", [_code_cell("x")])
    _write_nb(tmp_path / "b.ipynb", [_code_cell("y")])
    _patch_kernelmanager([
        [_msg("status", execution_state="idle")],
        [_msg("status", execution_state="idle")],
    ])
    results = dotnet_executor.batch_execute(str(tmp_path), pattern="*.ipynb")
    assert set(results.keys()) == {"a.ipynb", "b.ipynb"}
    assert all(r["executed"] == 1 for r in results.values())


def test_batch_execute_respects_pattern(tmp_path, _patch_kernelmanager):
    _write_nb(tmp_path / "match.ipynb", [_code_cell("x")])
    _write_nb(tmp_path / "skip.txt", [_code_cell("x")])  # not .ipynb
    _patch_kernelmanager([[_msg("status", execution_state="idle")]])
    results = dotnet_executor.batch_execute(str(tmp_path), pattern="*.ipynb")
    assert list(results.keys()) == ["match.ipynb"]


def test_batch_execute_skipped_notebooks_marked(tmp_path, _patch_kernelmanager):
    _write_nb(tmp_path / "empty.ipynb", [{"cell_type": "markdown", "source": ["# md"]}])
    _patch_kernelmanager([])  # kernel never used
    results = dotnet_executor.batch_execute(str(tmp_path), pattern="*.ipynb")
    assert results["empty.ipynb"]["skipped"] is True
    assert results["empty.ipynb"]["total"] == 0


# --- Fix A: parent_msg_id filter (cross-cell pollution guard) ----------------

def test_mismatched_parent_msg_id_is_skipped(tmp_path, _patch_kernelmanager):
    """Fix A: an iopub message whose parent_header.msg_id names a DIFFERENT
    request must not be collected into this cell's outputs. The fake kernel's
    execute() returns ``msg-1`` for the first cell, so a stream tagged
    ``parent="stale-..."`` is dropped while ``parent="msg-1"`` is kept."""
    nb = _write_nb(tmp_path / "n.ipynb", [_code_cell("x")])
    _patch_kernelmanager([[
        _msg("status", execution_state="busy"),
        _msg("stream", parent="stale-from-prior-cell", name="stdout", text="leftover\n"),
        _msg("stream", parent="msg-1", name="stdout", text="ours\n"),
        _msg("status", execution_state="idle"),
    ]])
    dotnet_executor.execute_notebook(nb)
    out = json.loads(nb.read_text(encoding="utf-8"))["cells"][0]["outputs"]
    texts = [o["text"] for o in out if o["output_type"] == "stream"]
    assert "ours\n" in texts
    assert "leftover\n" not in texts  # cross-cell pollution dropped


def test_stray_idle_from_other_request_does_not_break_loop(tmp_path, _patch_kernelmanager):
    """Fix A: a stray idle status bearing a DIFFERENT parent must NOT terminate
    this cell's iopub loop before its own output arrives. Without the filter a
    late idle from the prior cell would break early and lose ``real-output``."""
    nb = _write_nb(tmp_path / "n.ipynb", [_code_cell("x")])
    _patch_kernelmanager([[
        _msg("status", execution_state="busy"),
        _msg("status", parent="someone-else", execution_state="idle"),  # stray, must NOT break
        _msg("stream", name="stdout", text="real-output\n"),
        _msg("status", execution_state="idle"),  # ours (parentless) -> breaks
    ]])
    dotnet_executor.execute_notebook(nb)
    out = json.loads(nb.read_text(encoding="utf-8"))["cells"][0]["outputs"]
    texts = [o["text"] for o in out if o["output_type"] == "stream"]
    assert texts == ["real-output\n"]  # loop survived the stray idle


def test_parentless_message_is_still_kept(tmp_path, _patch_kernelmanager):
    """Fix A conservative design: messages with NO parent_header (kernel
    broadcasts) are kept, not dropped — pins forward-compatibility."""
    nb = _write_nb(tmp_path / "n.ipynb", [_code_cell("x")])
    _patch_kernelmanager([[
        _msg("stream", name="stdout", text="broadcast\n"),  # no parent_header
        _msg("status", execution_state="idle"),
    ]])
    dotnet_executor.execute_notebook(nb)
    out = json.loads(nb.read_text(encoding="utf-8"))["cells"][0]["outputs"]
    assert out[0]["text"] == "broadcast\n"  # parentless message kept


# --- Fix B: interrupt + drain on timeout ------------------------------------

def test_interrupt_kernel_called_on_timeout(tmp_path, _patch_kernelmanager):
    """Fix B: on timeout the kernel manager is interrupted so the next cell is
    not queued behind the stuck execution."""
    nb = _write_nb(tmp_path / "n.ipynb", [_code_cell("while(true);")])
    km, _ = _patch_kernelmanager([[]])
    dotnet_executor.execute_notebook(nb, cell_timeout=0)
    km.interrupt_kernel.assert_called_once()


def test_interrupt_failure_does_not_crash(tmp_path, _patch_kernelmanager):
    """Fix B: if interrupt_kernel() raises (unsupported kernel), the executor
    must swallow it and still emit the TIMEOUT stderr + count the cell."""
    nb = _write_nb(tmp_path / "n.ipynb", [_code_cell("x")])
    km, _ = _patch_kernelmanager([[]])
    km.interrupt_kernel.side_effect = RuntimeError("interrupt not supported")
    stats = dotnet_executor.execute_notebook(nb, cell_timeout=0)
    assert stats["executed"] == 1
    out = json.loads(nb.read_text(encoding="utf-8"))["cells"][0]["outputs"][0]
    assert out["output_type"] == "stream"
    assert "TIMEOUT" in out["text"]


def test_drain_after_timeout_consumes_interrupted_idle(tmp_path, _patch_kernelmanager):
    """Fix B: after interrupt, _drain_iopub consumes the interrupted request's
    trailing idle (matching parent) and then returns, so the next cell starts
    clean. The drain recognizes ``msg-1`` (cell 1's id) as the parent to sweep."""
    nb = _write_nb(tmp_path / "n.ipynb", [_code_cell("a"), _code_cell("b")])
    _patch_kernelmanager([
        # cell 1: timeout branch drains this idle (parent=msg-1 -> matched -> return)
        [_msg("status", parent="msg-1", execution_state="idle")],
        # cell 2: also times out (cell_timeout=0); its drain finds only a parentless
        # idle (unmatched -> continue) then queue.Empty -> best-effort return.
        [_msg("status", execution_state="idle")],
    ])
    stats = dotnet_executor.execute_notebook(nb, cell_timeout=0)
    assert stats["executed"] == 2  # both cells ran despite cell-1 timeout
    cells = json.loads(nb.read_text(encoding="utf-8"))["cells"]
    assert cells[0]["execution_count"] == 1
    assert cells[1]["execution_count"] == 2
    assert any("TIMEOUT" in o.get("text", "") for o in cells[0]["outputs"])
    assert any("TIMEOUT" in o.get("text", "") for o in cells[1]["outputs"])
