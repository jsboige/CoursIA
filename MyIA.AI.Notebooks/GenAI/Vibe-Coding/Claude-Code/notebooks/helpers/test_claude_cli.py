#!/usr/bin/env python3
"""Pytest suite for `Claude-Code/notebooks/helpers/claude_cli.py`.

Co-located with the module. CPU-only, no network, no real `claude` CLI
invocation. The module is consumed by 5 notebooks (01-05 Claude CLI series)
but had 0 dedicated Python test coverage before this PR.

Strategy: `SIMULATION_MODE` makes every public function deterministic and
side-effect-free (no subprocess, no network), so the full API surface is
exercised without a real Claude installation. The non-simulation error
paths (`verify_installation()` returns False) are covered by monkeypatching
`shutil.which`. Pure helpers (`format_code_block`) are tested directly.

No secrets, no `.env`, no real API key: SIMULATION_MODE short-circuits before
any key check, and the verify_installation=False path returns an error tuple
without invoking the CLI.
"""
from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest

# Load the module by path (it lives under notebooks/helpers/, stdlib-only
# imports, no package path needed).
_MODULE_PATH = Path(__file__).resolve().parent / "claude_cli.py"
_spec = importlib.util.spec_from_file_location("claude_cli", _MODULE_PATH)
claude_cli = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(claude_cli)


@pytest.fixture
def sim_mode(monkeypatch):
    """Enable SIMULATION_MODE for the duration of a test (restored after)."""
    monkeypatch.setattr(claude_cli, "SIMULATION_MODE", True)
    return claude_cli


@pytest.fixture
def real_mode_no_install(monkeypatch):
    """Disable SIMULATION_MODE AND make verify_installation return False.

    This exercises the defensive error paths (CLI not installed) without
    spawning any subprocess.
    """
    monkeypatch.setattr(claude_cli, "SIMULATION_MODE", False)
    monkeypatch.setattr(claude_cli, "verify_installation", lambda: False)
    return claude_cli


# --------------------------------------------------------------------------
# Pure helpers
# --------------------------------------------------------------------------


def test_format_code_block_default_language_python():
    out = claude_cli.format_code_block("x = 1")
    assert out == "```python\nx = 1\n```"


def test_format_code_block_custom_language():
    out = claude_cli.format_code_block("SELECT 1", language="sql")
    assert out.startswith("```sql\n")
    assert out.endswith("\n```")
    assert "SELECT 1" in out


def test_verify_installation_returns_bool():
    # On any CI/host this is a bool; we don't assume claude is present.
    assert isinstance(claude_cli.verify_installation(), bool)


def test_verify_installation_false_when_not_in_path(monkeypatch):
    monkeypatch.setattr(claude_cli.shutil, "which", lambda cmd: None)
    assert claude_cli.verify_installation() is False


def test_verify_installation_true_when_in_path(monkeypatch):
    monkeypatch.setattr(claude_cli.shutil, "which", lambda cmd: "/usr/local/bin/claude")
    assert claude_cli.verify_installation() is True


# --------------------------------------------------------------------------
# run_claude — SIMULATION_MODE (deterministic)
# --------------------------------------------------------------------------


def test_run_claude_sim_returns_3_tuple(sim_mode):
    stdout, stderr, code = sim_mode.run_claude("anything")
    assert isinstance(stdout, str)
    assert isinstance(stderr, str)
    assert isinstance(code, int)
    assert code == 0


def test_run_claude_sim_first_word_lookup_known_key(sim_mode):
    # SIMULATION_MODE looks up SIMULATED_RESPONSES by the first whitespace-
    # delimited word of the prompt. A clean (punctuation-free) first word
    # matches the stored key.
    stdout, _, _ = sim_mode.run_claude("Bonjour qui es tu")
    assert stdout == sim_mode.SIMULATED_RESPONSES["bonjour"]


def test_run_claude_sim_first_word_lookup_is_punctuation_sensitive(sim_mode):
    # Documented behavior (pin, not a claim of correctness): the first-word
    # lookup uses str.split() which splits on whitespace only, so a trailing
    # punctuation mark stays attached to the token and breaks the exact-match
    # against the stored key. "Bonjour," != "bonjour" -> default response.
    stdout, _, _ = sim_mode.run_claude("Bonjour, qui es-tu ?")
    assert stdout == sim_mode.SIMULATED_RESPONSES["default"]


def test_run_claude_sim_version_key(sim_mode):
    stdout, _, _ = sim_mode.run_claude("version du CLI")
    assert stdout == "Claude Code CLI v1.0.0"


def test_run_claude_sim_unknown_first_word_returns_default(sim_mode):
    stdout, _, _ = sim_mode.run_claude("Quelle est la météo")
    assert stdout == sim_mode.SIMULATED_RESPONSES["default"]


def test_run_claude_sim_empty_prompt_returns_default(sim_mode):
    # Empty prompt is falsy → the ternary falls back to "default".
    stdout, _, code = sim_mode.run_claude("")
    assert stdout == sim_mode.SIMULATED_RESPONSES["default"]
    assert code == 0


def test_run_claude_sim_default_model_arg_ignored(sim_mode):
    # SIMULATION_MODE does not build a command, so the model arg has no
    # effect on output; the response is keyed on the prompt only.
    a = sim_mode.run_claude("Bonjour")[0]
    b = sim_mode.run_claude("Bonjour", model="opus")[0]
    assert a == b


# --------------------------------------------------------------------------
# run_claude — non-simulation error path (CLI not installed)
# --------------------------------------------------------------------------


def test_run_claude_real_mode_no_install_returns_error(real_mode_no_install):
    stdout, stderr, code = real_mode_no_install.run_claude("hi")
    assert stdout == ""
    assert "installe" in stderr.lower()
    assert code == 1


# --------------------------------------------------------------------------
# run_claude_continue — SIMULATION_MODE
# --------------------------------------------------------------------------


def test_run_claude_continue_sim_appends_suite_suffix(sim_mode):
    stdout, _, code = sim_mode.run_claude_continue("bonjour")
    assert stdout.endswith(" (suite)")
    assert code == 0


def test_run_claude_continue_sim_fork_suffix(sim_mode):
    stdout, _, code = sim_mode.run_claude_continue("bonjour", fork=True)
    assert stdout.endswith(" (fork)")
    assert "(suite)" not in stdout
    assert code == 0


def test_run_claude_continue_real_mode_no_install_returns_error(real_mode_no_install):
    stdout, stderr, code = real_mode_no_install.run_claude_continue("suite")
    assert code == 1
    assert stdout == ""
    assert "installe" in stderr.lower()


# --------------------------------------------------------------------------
# run_claude_command — SIMULATION_MODE (slash handling + branches)
# --------------------------------------------------------------------------


def test_run_claude_command_sim_sessions_branch(sim_mode):
    stdout, _, code = sim_mode.run_claude_command("sessions")
    assert "session" in stdout.lower()
    assert code == 0


def test_run_claude_command_sim_status_branch(sim_mode):
    stdout, _, code = sim_mode.run_claude_command("status")
    assert "connected" in stdout
    assert code == 0


def test_run_claude_command_sim_prepends_missing_slash(sim_mode):
    # Passing "sessions" (no leading slash) and "/sessions" must behave the
    # same way: the function normalizes by prepending "/" when missing.
    no_slash = sim_mode.run_claude_command("sessions")[0]
    with_slash = sim_mode.run_claude_command("/sessions")[0]
    assert no_slash == with_slash


def test_run_claude_command_sim_generic_fallback(sim_mode):
    stdout, _, code = sim_mode.run_claude_command("/unknown-cmd")
    assert "simulee" in stdout.lower()
    assert code == 0


def test_run_claude_command_real_mode_no_install_returns_error(real_mode_no_install):
    _, stderr, code = real_mode_no_install.run_claude_command("/status")
    assert code == 1
    assert "installe" in stderr.lower()


# --------------------------------------------------------------------------
# check_claude_status — SIMULATION_MODE
# --------------------------------------------------------------------------


def test_check_claude_status_sim_returns_connected_dict(sim_mode):
    status = sim_mode.check_claude_status()
    assert status["connected"] is True
    assert status["model"] == "simulation-mode"
    assert status["base_url"] == "simulation"
    assert status.get("simulation") is True


def test_check_claude_status_real_mode_no_install_returns_not_connected(real_mode_no_install):
    status = real_mode_no_install.check_claude_status()
    assert status["connected"] is False
    assert "installe" in status.get("error", "").lower()


# --------------------------------------------------------------------------
# get_claude_version — SIMULATION_MODE + not-installed path
# --------------------------------------------------------------------------


def test_get_claude_version_sim(sim_mode):
    assert sim_mode.get_claude_version() == "Claude Code CLI v1.0.0"


def test_get_claude_version_real_mode_no_install(real_mode_no_install):
    v = real_mode_no_install.get_claude_version()
    assert "installe" in v.lower()


# --------------------------------------------------------------------------
# run_claude_json — JSON parse path + error path
# --------------------------------------------------------------------------


def test_run_claude_json_parses_valid_json(monkeypatch):
    # In SIMULATION_MODE run_claude returns prose, not JSON. To exercise the
    # JSON-parse-success branch of run_claude_json we monkeypatch run_claude
    # to return a valid JSON document.
    monkeypatch.setattr(claude_cli, "SIMULATION_MODE", True)

    def fake_run(prompt, **kwargs):
        return '{"answer": 42, "model": "test"}', "", 0

    monkeypatch.setattr(claude_cli, "run_claude", fake_run)
    result = claude_cli.run_claude_json("donne moi un json")
    assert result == {"answer": 42, "model": "test"}


def test_run_claude_json_returns_error_on_nonzero_code(monkeypatch):
    monkeypatch.setattr(claude_cli, "SIMULATION_MODE", True)

    def fake_run(prompt, **kwargs):
        return "", "CLI introuvable", 1

    monkeypatch.setattr(claude_cli, "run_claude", fake_run)
    result = claude_cli.run_claude_json("x")
    assert "error" in result
    assert result["code"] == 1


def test_run_claude_json_returns_error_on_invalid_json(monkeypatch):
    monkeypatch.setattr(claude_cli, "SIMULATION_MODE", True)

    def fake_run(prompt, **kwargs):
        return "ceci n'est pas du json", "", 0

    monkeypatch.setattr(claude_cli, "run_claude", fake_run)
    result = claude_cli.run_claude_json("x")
    assert "error" in result
    assert "parsing" in result["error"].lower()
    assert result["raw_output"] == "ceci n'est pas du json"


# --------------------------------------------------------------------------
# print_response — output formatting (capture stdout)
# --------------------------------------------------------------------------


def test_print_response_success_branch(capsys, sim_mode):
    sim_mode.print_response("reponse ok", "", 0)
    captured = capsys.readouterr()
    assert "Reponse Claude" in captured.out
    assert "reponse ok" in captured.out


def test_print_response_error_branch(capsys):
    claude_cli.print_response("", "boom", 1)
    captured = capsys.readouterr()
    assert "Erreur" in captured.out
    assert "1" in captured.out
    assert "boom" in captured.out
