#!/usr/bin/env python3
"""Tests for scripts/lean/setup_lean4_all.py — Lean 4 kernel setup orchestrator.

Covers the pure / hermetic functions:

- ``_win_to_wsl_path``: Windows drive-letter path -> WSL ``/mnt/<drive>/...``
  (incident po-2024 c.355 — passing ``C:\\dev\\repo`` to ``wsl -- bash``
  yields ``C:devrepo`` -> exit 127).
- ``_detect_wsl_distro``: robust decode of ``wsl -l -q`` output (UTF-16LE with
  embedded NUL bytes on Windows; passing a raw UTF-16LE string to
  ``subprocess.run([..., distro, ...])`` raises ``ValueError: embedded null
  character`` — incident po-2024 c.355).
- ``check_wrapper_registration``: thin delegator to
  ``lean_kernel_check.inspect_kernel_wrapper`` — covered indirectly via the
  status / message prefix contract.

All subprocess invocations are monkeypatched so the suite is CPU-only and
hermetic (no WSL / no PowerShell required).
"""
from __future__ import annotations

import sys
import subprocess
from pathlib import Path

import pytest

# Add scripts/lean to import path so ``setup_lean4_all`` is importable
# (matches the convention used by test_lean_kernel_check.py).
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import setup_lean4_all as sla  # noqa: E402


# ---------------------------------------------------------------------------
# _win_to_wsl_path — drive-letter conversion
# ---------------------------------------------------------------------------

class TestWinToWslPath:
    """Drive-letter paths must be converted to /mnt/<drive>/... form so
    ``wsl -- bash`` can find the script on the Linux filesystem."""

    def test_lowercase_drive(self):
        assert sla._win_to_wsl_path("c:\\dev\\repo") == "/mnt/c/dev/repo"

    def test_uppercase_drive(self):
        assert sla._win_to_wsl_path("D:\\Dev\\CoursIA") == "/mnt/d/Dev/CoursIA"

    def test_forward_slashes_preserved(self):
        assert sla._win_to_wsl_path("c:/dev/repo") == "/mnt/c/dev/repo"

    def test_mixed_separators_normalised(self):
        # Mixed slashes (common in code) must end up all forward.
        assert sla._win_to_wsl_path("c:\\dev/repo\\sub") == "/mnt/c/dev/repo/sub"

    def test_already_wsl_path_unchanged(self):
        assert sla._win_to_wsl_path("/home/user/lean") == "/home/user/lean"

    def test_relative_path_unchanged(self):
        assert sla._win_to_wsl_path("dev/repo") == "dev/repo"

    def test_empty_string_unchanged(self):
        assert sla._win_to_wsl_path("") == ""

    def test_no_false_positive_on_unix_path(self):
        # "C" alone (no colon) must NOT be treated as a drive letter.
        assert sla._win_to_wsl_path("C") == "C"

    def test_bare_drive_colon_unchanged(self):
        # "C:" without a separator is an edge case (Windows command-line
        # referring to current dir on C:); the regex requires [\\/] after
        # the colon, so this is returned unchanged. Documenting the actual
        # behavior — callers should always pass a path with separators.
        assert sla._win_to_wsl_path("C:") == "C:"


# ---------------------------------------------------------------------------
# _detect_wsl_distro — robust UTF-16LE decode
# ---------------------------------------------------------------------------

class TestDetectWslDistro:
    """``wsl -l -q`` returns UTF-16LE bytes on Windows. Embedded NUL bytes
    crash ``subprocess.run``; the function decodes defensively and falls back
    to ``"Ubuntu"`` on any decode failure."""

    def _run_detect(self, monkeypatch, returncode, stdout_bytes):
        """Patch subprocess.run to return a fixed (returncode, stdout) pair
        and call ``_detect_wsl_distro`` once."""

        class _Result:
            def __init__(self, returncode, stdout):
                self.returncode = returncode
                self.stdout = stdout

        def _fake_run(*args, **kwargs):
            return _Result(returncode, stdout_bytes)

        monkeypatch.setattr(sla.subprocess, "run", _fake_run)
        return sla._detect_wsl_distro()

    def test_utf16le_with_bom(self, monkeypatch):
        # UTF-16LE + BOM: 'Ubuntu\n' encoded.
        text = "Ubuntu\n"
        encoded = b"\xff\xfe" + text.encode("utf-16-le")
        assert self._run_detect(monkeypatch, 0, encoded) == "Ubuntu"

    def test_utf16le_without_bom(self, monkeypatch):
        # UTF-16LE without BOM (older Windows).
        text = "Ubuntu\n"
        encoded = text.encode("utf-16-le")
        assert self._run_detect(monkeypatch, 0, encoded) == "Ubuntu"

    def test_utf8_plain_fallback(self, monkeypatch):
        # Plain UTF-8 (some Windows builds / WSL versions).
        assert self._run_detect(monkeypatch, 0, b"Ubuntu\n") == "Ubuntu"

    def test_picks_first_line_when_multi_distro(self, monkeypatch):
        # wsl -l -q may list multiple distros; first non-empty wins.
        text = "Ubuntu\nUbuntu-22.04\n"
        encoded = b"\xff\xfe" + text.encode("utf-16-le")
        assert self._run_detect(monkeypatch, 0, encoded) == "Ubuntu"

    def test_strips_whitespace(self, monkeypatch):
        text = "  Debian  \n"
        encoded = b"\xff\xfe" + text.encode("utf-16-le")
        assert self._run_detect(monkeypatch, 0, encoded) == "Debian"

    def test_non_zero_returncode_falls_back(self, monkeypatch):
        # If wsl itself fails, the safe default is "Ubuntu".
        assert self._run_detect(monkeypatch, 1, b"") == "Ubuntu"

    def test_empty_stdout_falls_back(self, monkeypatch):
        assert self._run_detect(monkeypatch, 0, b"") == "Ubuntu"

    def test_corrupt_decode_with_nul_in_first_line_falls_back(self, monkeypatch):
        # Belt-and-suspenders: if a NUL somehow survives, reject the name.
        assert self._run_detect(monkeypatch, 0, b"\x00\x00\x00") == "Ubuntu"

    def test_subprocess_raises_falls_back(self, monkeypatch):
        # If subprocess.run itself throws (e.g. wsl not installed), fallback.
        def _raise(*args, **kwargs):
            raise FileNotFoundError("wsl not found")

        monkeypatch.setattr(sla.subprocess, "run", _raise)
        assert sla._detect_wsl_distro() == "Ubuntu"

    def test_timeout_falls_back(self, monkeypatch):
        def _timeout(*args, **kwargs):
            raise subprocess.TimeoutExpired(cmd=["wsl"], timeout=10)

        monkeypatch.setattr(sla.subprocess, "run", _timeout)
        assert sla._detect_wsl_distro() == "Ubuntu"


# ---------------------------------------------------------------------------
# check_wrapper_registration — status prefix contract
# ---------------------------------------------------------------------------

class TestCheckWrapperRegistration:
    """The wrapper check is a thin delegator to ``inspect_kernel_wrapper``;
    verify the status->prefix mapping and return-value contract without
    re-testing the underlying classifier (already covered by
    test_lean_kernel_check.py)."""

    @pytest.mark.parametrize(
        "status,expected_prefix,expected_return",
        [
            ("ok", "OK:", True),
            ("warning", "WARNING:", False),
            ("error", "ERROR:", False),
        ],
    )
    def test_status_to_prefix_mapping(
        self, monkeypatch, capsys, status, expected_prefix, expected_return
    ):
        def _fake_inspect(kernel_name):
            return status, f"sample message for {kernel_name}"

        monkeypatch.setattr(sla, "inspect_kernel_wrapper", _fake_inspect)
        result = sla.check_wrapper_registration()
        captured = capsys.readouterr()
        assert result is expected_return
        # The status-prefix line is printed AFTER a banner; check that the
        # exact "<prefix> <message>" line is present, not that the whole
        # stdout starts with it.
        assert f"{expected_prefix} sample message" in captured.out

    def test_delegates_to_canonical_helper(self, monkeypatch):
        """Regression guard: the helper name must stay
        ``inspect_kernel_wrapper`` (canonical, issue #1618)."""
        called = []

        def _fake_inspect(kernel_name):
            called.append(kernel_name)
            return "ok", "ok"

        monkeypatch.setattr(sla, "inspect_kernel_wrapper", _fake_inspect)
        sla.check_wrapper_registration()
        assert called == ["lean4-wsl"]


# ---------------------------------------------------------------------------
# arg defaults — sanity
# ---------------------------------------------------------------------------

class TestModuleConstants:
    def test_default_wsl_distro(self):
        # WSL_DISTRO is the fallback for the orchestrator when auto-detect
        # fails; Ubuntu is the canonical CoursIA dev environment.
        assert sla.WSL_DISTRO == "Ubuntu"

    def test_repo_root_is_absolute(self):
        assert sla.REPO_ROOT.is_absolute()

    def test_gt_scripts_under_repo(self):
        # GameTheory scripts directory must live under the repo root.
        assert sla.GT_SCRIPTS.is_relative_to(sla.REPO_ROOT)
        assert sla.GT_SCRIPTS.name == "scripts"

    def test_lean_scripts_under_repo(self):
        # SymbolicAI/Lean scripts directory must live under the repo root.
        assert sla.LEAN_SCRIPTS.is_relative_to(sla.REPO_ROOT)
        assert "SymbolicAI" in sla.LEAN_SCRIPTS.parts
