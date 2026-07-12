#!/usr/bin/env python3
"""Tests for the canonical Lean 4 kernel wrapper check (issue #1618).

Verifies that ``inspect_kernel_wrapper`` correctly classifies a kernel.json as:
  - "error"   when it points to the OLD bash wrapper (the #1618 regression)
  - "ok"      when it points to the CORRECT Python wrapper (v5)
  - "warning" when the wrapper is unknown or the file is missing

Run directly (no pytest needed):
    python scripts/lean/tests/test_lean_kernel_check.py

Or via pytest:
    pytest scripts/lean/tests/test_lean_kernel_check.py
"""

import json
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lean_kernel_check import inspect_kernel_wrapper  # noqa: E402


def _write_kernel_json(tmpdir, argv):
    path = Path(tmpdir) / "kernel.json"
    path.write_text(json.dumps({"argv": argv, "display_name": "Lean 4 (WSL)"}), encoding="utf-8")
    return path


def test_old_bash_wrapper_is_error():
    with tempfile.TemporaryDirectory() as tmp:
        kj = _write_kernel_json(tmp, [
            "wsl.exe", "-d", "Ubuntu", "--", "bash", "/home/jesse/lean4-jupyter-wrapper.sh",
            "-f", "{connection_file}",
        ])
        status, message = inspect_kernel_wrapper("lean4-wsl", kernel_json_path=kj)
        assert status == "error", message
        assert "lean4-jupyter-wrapper.sh" in message


def test_python_wrapper_is_ok():
    with tempfile.TemporaryDirectory() as tmp:
        kj = _write_kernel_json(tmp, [
            "wsl.exe", "-d", "Ubuntu", "--",
            "/home/jesse/.lean4-venv/bin/python3", "/home/jesse/.lean4-kernel-wrapper.py",
            "-f", "{connection_file}",
        ])
        status, message = inspect_kernel_wrapper("lean4-wsl", kernel_json_path=kj)
        assert status == "ok", message


def test_unknown_wrapper_is_warning():
    with tempfile.TemporaryDirectory() as tmp:
        kj = _write_kernel_json(tmp, ["python", "-m", "some_other_kernel", "-f", "{connection_file}"])
        status, message = inspect_kernel_wrapper("lean4-wsl", kernel_json_path=kj)
        assert status == "warning", message


def test_missing_file_is_warning():
    missing = Path(tempfile.gettempdir()) / "definitely-not-a-kernel-1618" / "kernel.json"
    status, message = inspect_kernel_wrapper("lean4-wsl", kernel_json_path=missing)
    assert status == "warning", message


def _run_all():
    tests = [
        test_old_bash_wrapper_is_error,
        test_python_wrapper_is_ok,
        test_unknown_wrapper_is_warning,
        test_missing_file_is_warning,
    ]
    failures = 0
    for t in tests:
        try:
            t()
            print(f"PASS {t.__name__}")
        except AssertionError as exc:
            failures += 1
            print(f"FAIL {t.__name__}: {exc}")
    print(f"\n{len(tests) - failures}/{len(tests)} passed")
    return failures


if __name__ == "__main__":
    sys.exit(1 if _run_all() else 0)
