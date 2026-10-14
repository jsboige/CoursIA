"""Unit tests for provider response parsing in lean_runner.py."""

import sys
from pathlib import Path
from types import SimpleNamespace

import pytest

LEAN_DIR = Path(__file__).resolve().parents[2]
if str(LEAN_DIR) not in sys.path:
    sys.path.insert(0, str(LEAN_DIR))

from lean_runner import LLMClient, LeanRunner  # noqa: E402


class FakeMessages:
    def __init__(self, response):
        self.response = response

    def create(self, **_kwargs):
        return self.response


def make_client(content):
    client = LLMClient.__new__(LLMClient)
    client.model = "claude-sonnet-4-5"
    response = SimpleNamespace(
        content=content,
        model=client.model,
        usage=SimpleNamespace(input_tokens=12, output_tokens=7),
    )
    client.client = SimpleNamespace(messages=FakeMessages(response))
    return client


def test_anthropic_joins_text_blocks_after_thinking_block():
    client = make_client([
        SimpleNamespace(type="thinking", thinking="Analyse interne"),
        SimpleNamespace(type="text", text="```lean\nby simp\n```"),
        SimpleNamespace(type="text", text="Vérification terminée."),
    ])

    result = client._generate_anthropic("prompt", "system", 0.3)

    assert result["content"] == "```lean\nby simp\n```\nVérification terminée."
    assert result["tokens"] == {"prompt": 12, "completion": 7, "total": 19}


def test_anthropic_rejects_response_without_text_block():
    client = make_client([
        SimpleNamespace(type="thinking", thinking="Analyse interne"),
    ])

    with pytest.raises(RuntimeError, match="aucun bloc texte"):
        client._generate_anthropic("prompt", "system", 0.3)


# ------------------------------------------------------------
# Regression tests for issue #17597
# `LeanRunner._find_lean` previously picked the first `lean` on PATH
# without verifying it was actually Lean 4, so on a kernel that had
# `pip install lean` (QuantConnect CLI) it picked the QC wrapper, which
# responds with the CLI banner instead of Lean 4's `Lean (version 4...`.
# ------------------------------------------------------------


LEAN4_BANNER = (
    "Lean (version 4.34.0, x86_64-unknown-linux-gnu, "
    "commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b, Release)"
)
QC_BANNER = (
    "A new release of the Lean CLI is available (1.0.223 -> 1.0.229)\n"
    "Run `pip install --upgrade lean` to update to the latest version\n"
    "Usage: lean.EXE [OPTIONS] [COMMAND] [ARGS]...\n"
    "Error: No such command '<tmp>\\lean_runner_xxxx\\Main.lean'."
)


class FakeProc:
    """Stand-in for subprocess.run results inside _is_lean4_binary."""

    def __init__(self, returncode, stdout):
        self.returncode = returncode
        self.stdout = stdout


def test_is_lean4_binary_accepts_lean4_banner(monkeypatch):
    captured = {}

    def fake_run(cmd, **kwargs):
        captured["cmd"] = cmd
        return FakeProc(0, LEAN4_BANNER)

    monkeypatch.setattr("subprocess.run", fake_run)

    assert LeanRunner._is_lean4_binary("/fake/lean") is True
    # The probe MUST be exactly `<binary> --version`, never the bare name
    # (which is what would re-enter shutil.which on Windows).
    assert captured["cmd"][0] == "/fake/lean"
    assert captured["cmd"][1:] == ["--version"]


def test_is_lean4_binary_rejects_qc_banner(monkeypatch):
    monkeypatch.setattr(
        "subprocess.run", lambda *a, **k: FakeProc(0, QC_BANNER)
    )

    assert LeanRunner._is_lean4_binary("/fake/qc-lean") is False


def test_is_lean4_binary_rejects_non_zero_exit(monkeypatch):
    monkeypatch.setattr(
        "subprocess.run", lambda *a, **k: FakeProc(2, LEAN4_BANNER)
    )

    # An executable that errors out cannot be safely accepted even if its
    # stdout happens to look like Lean 4 — we never reach the version
    # check on a sane Lean 4 install.
    assert LeanRunner._is_lean4_binary("/fake/broken-lean") is False


def test_find_lean_accepts_path_lean4_and_skips_elan_bin(monkeypatch, tmp_path):
    """When the PATH already has a Lean 4 binary, the runner must use it and
    must NOT silently fall back to elan (which would mask the user's choice).
    """
    monkeypatch.setattr("shutil.which", lambda name: "/fake/path-lean" if name == "lean" else None)
    monkeypatch.setattr("subprocess.run", lambda *a, **k: FakeProc(0, LEAN4_BANNER))

    assert LeanRunner._find_lean(LeanRunner.__new__(LeanRunner)) == "/fake/path-lean"


def test_find_lean_raises_explicit_when_path_has_qc_only(monkeypatch, tmp_path):
    """When the QC wrapper is the ONLY `lean` on PATH and elan is absent,
    the runner must raise FileNotFoundError with a diagnostic that names
    the rejected binary — not silently return it."""
    monkeypatch.setattr("shutil.which", lambda name: "/fake/qc-lean" if name == "lean" else None)
    monkeypatch.setattr("subprocess.run", lambda *a, **k: FakeProc(0, QC_BANNER))
    monkeypatch.setattr("lean_runner.Path.home", lambda: tmp_path)

    with pytest.raises(FileNotFoundError, match="/fake/qc-lean") as excinfo:
        LeanRunner._find_lean(LeanRunner.__new__(LeanRunner))

    # The diagnostic must mention how to fix the situation.
    message = str(excinfo.value)
    assert "Lean (version 4" in message
    assert "pip uninstall lean" in message
