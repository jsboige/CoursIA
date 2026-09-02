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
from lean_kernel_check import (  # noqa: E402
    CORRECT_PY_WRAPPER,
    candidate_kernel_json_paths,
    inspect_kernel_wrapper,
    inspect_wrapper_content_drift,
    wsl_to_unc,
)


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


def test_candidate_paths_return_path_objects():
    paths = candidate_kernel_json_paths("lean4-wsl")
    assert paths
    assert all(isinstance(path, Path) for path in paths)


def test_candidate_paths_include_appdata(monkeypatch):
    monkeypatch.setenv("APPDATA", r"C:\fake\appdata")
    paths = candidate_kernel_json_paths("lean4-wsl")
    assert len([path for path in paths if "fake" in str(path)]) == 1


def test_candidate_paths_without_appdata(monkeypatch):
    monkeypatch.delenv("APPDATA", raising=False)
    paths = candidate_kernel_json_paths("lean4-wsl")
    assert all("appdata" not in str(path).lower() for path in paths)


def test_python_wrapper_fqdn_is_ok():
    with tempfile.TemporaryDirectory() as tmp:
        kj = _write_kernel_json(tmp, [
            "/usr/bin/python3", f"/home/user/{CORRECT_PY_WRAPPER}",
            "{connection_file}",
        ])
        status, message = inspect_kernel_wrapper(
            "lean4-wsl", kernel_json_path=kj
        )
        assert status == "ok", message


def test_malformed_json_is_warning():
    with tempfile.TemporaryDirectory() as tmp:
        kj = Path(tmp) / "kernel.json"
        kj.write_text("{invalid json!!!", encoding="utf-8")
        status, message = inspect_kernel_wrapper(
            "lean4-wsl", kernel_json_path=kj
        )
        assert status == "warning", message
        assert "erreur lecture" in message


def test_empty_kernel_json_is_warning():
    with tempfile.TemporaryDirectory() as tmp:
        kj = Path(tmp) / "kernel.json"
        kj.write_text("{}", encoding="utf-8")
        status, message = inspect_kernel_wrapper(
            "lean4-wsl", kernel_json_path=kj
        )
        assert status == "warning", message
        assert "inconnu" in message


def test_cli_missing_kernel():
    import subprocess

    result = subprocess.run(
        [sys.executable, "-m", "lean_kernel_check", "--kernel",
         "nonexistent-test"],
        capture_output=True,
        text=True,
        cwd=str(Path(__file__).resolve().parent.parent),
    )
    assert result.returncode == 1
    assert "WARNING" in result.stdout or "aucun" in result.stdout


# --- Content drift guard (#13180) ---

_WRAPPER_ARGV = [
    "wsl.exe", "-d", "Ubuntu", "--",
    "/home/jesse/.lean4-venv/bin/python3", "/home/jesse/.lean4-kernel-wrapper.py",
    "-f", "{connection_file}",
]


def test_wsl_to_unc_translation():
    unc = wsl_to_unc("/home/jesse/.lean4-kernel-wrapper.py", "Ubuntu")
    assert str(unc) == r"\\wsl$\Ubuntu\home\jesse\.lean4-kernel-wrapper.py"


def test_drift_ok_when_deployed_matches_repo():
    with tempfile.TemporaryDirectory() as tmp:
        deployed = Path(tmp) / ".lean4-kernel-wrapper.py"
        reference = Path(tmp) / "repo_wrapper.py"
        payload = b"# v6 c.127 canonical\nprint('x')\n"
        deployed.write_bytes(payload)
        reference.write_bytes(payload)
        kj = _write_kernel_json(tmp, [
            "python", str(deployed), "-f", "{connection_file}",
        ])
        status, message = inspect_wrapper_content_drift(
            kj, repo_reference=reference)
        assert status == "ok", message
        assert "repo canonique" in message


def test_drift_warning_when_deployed_differs():
    with tempfile.TemporaryDirectory() as tmp:
        deployed = Path(tmp) / ".lean4-kernel-wrapper.py"
        reference = Path(tmp) / "repo_wrapper.py"
        deployed.write_bytes(b"# v6 c.126 STALE\ncount = 3\n")
        reference.write_bytes(b"# v6 c.127 canonical\ncount = 3\nnew_fix()\n")
        kj = _write_kernel_json(tmp, [
            "python", str(deployed), "-f", "{connection_file}",
        ])
        status, message = inspect_wrapper_content_drift(
            kj, repo_reference=reference)
        assert status == "warning", message
        assert "DRIFT" in message and "13180" in message


def test_drift_warning_when_deployed_unreadable():
    with tempfile.TemporaryDirectory() as tmp:
        kj = _write_kernel_json(tmp, _WRAPPER_ARGV)
        reference = Path(tmp) / "repo_wrapper.py"
        reference.write_bytes(b"x = 1\n")
        # deployed lives at a nonexistent Windows-side path (not WSL-translated
        # because the argv lacks "wsl"): fixture uses a plain path variant.
        kj_plain = _write_kernel_json(tmp, [
            "python", r"C:\nowhere\.lean4-kernel-wrapper.py", "-f", "{connection_file}",
        ])
        status, message = inspect_wrapper_content_drift(
            kj_plain, repo_reference=reference)
        assert status == "warning", message
        assert "illisible" in message or "introuvable" in message


def test_drift_warning_when_repo_reference_missing():
    with tempfile.TemporaryDirectory() as tmp:
        kj = _write_kernel_json(tmp, _WRAPPER_ARGV)
        status, message = inspect_wrapper_content_drift(
            kj, repo_reference=Path(tmp) / "no_such_repo_copy.py")
        assert status == "warning", message
        assert "repo de référence introuvable" in message


def test_drift_never_returns_error():
    # Posture #12740: signal, don't block. Every degenerate input maps to
    # ok/warning, never error.
    with tempfile.TemporaryDirectory() as tmp:
        kj = _write_kernel_json(tmp, _WRAPPER_ARGV)
        reference = Path(tmp) / "repo_wrapper.py"
        reference.write_bytes(b"x = 1\n")
        for kj_arg in (kj, Path(tmp) / "missing.json"):
            status, _ = inspect_wrapper_content_drift(kj_arg, repo_reference=reference)
            assert status in ("ok", "warning")


def _run_all():
    tests = [
        test_old_bash_wrapper_is_error,
        test_python_wrapper_is_ok,
        test_unknown_wrapper_is_warning,
        test_missing_file_is_warning,
        test_candidate_paths_return_path_objects,
        test_python_wrapper_fqdn_is_ok,
        test_malformed_json_is_warning,
        test_empty_kernel_json_is_warning,
        test_wsl_to_unc_translation,
        test_drift_ok_when_deployed_matches_repo,
        test_drift_warning_when_deployed_differs,
        test_drift_warning_when_deployed_unreadable,
        test_drift_warning_when_repo_reference_missing,
        test_drift_never_returns_error,
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
