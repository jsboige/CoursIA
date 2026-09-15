"""Tests for wsl_papermill.py — WSL path conversion + native mode + validation."""

import json
import platform
import sys
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

sys.path.insert(0, str(Path(__file__).parent.parent))
from wsl_papermill import (
    _declared_venv_from_kernel_json,
    _default_mode,
    _normalize_venv,
    _validate_output,
    _venv_from_interpreter,
    _venv_mismatch_message,
    batch_execute,
    check_env,
    check_env_native,
    check_env_wsl,
    count_cell_errors,
    execute_notebook,
    execute_notebook_native,
    execute_notebook_wsl,
    win_to_wsl_path,
)


# --- win_to_wsl_path ---


class TestWinToWslPath:
    def test_c_drive_root(self):
        result = win_to_wsl_path("C:\\")
        assert result == "/mnt/c/"

    def test_c_drive_path(self):
        result = win_to_wsl_path("C:\\Users\\test\\file.py")
        assert result == "/mnt/c/Users/test/file.py"

    def test_d_drive(self):
        result = win_to_wsl_path("D:\\projects\\repo")
        assert result == "/mnt/d/projects/repo"

    def test_lowercase_drive(self):
        """Drive letter should be lowercased."""
        result = win_to_wsl_path("E:\\DATA\\file.txt")
        assert result.startswith("/mnt/e/")

    def test_posix_path_passthrough(self):
        """Already-posix path should still be converted (Path handles it)."""
        result = win_to_wsl_path("/home/user/file.py")
        # Path("/home/user/file.py").drive is "" on Windows
        # drive[0].lower() would fail on empty drive
        # Let's check it doesn't crash — behavior depends on OS
        assert isinstance(result, str)

    def test_long_nested_path(self):
        result = win_to_wsl_path(
            "C:\\dev\\CoursIA\\MyIA.AI.Notebooks\\GenAI\\Image\\test.ipynb"
        )
        assert result == "/mnt/c/dev/CoursIA/MyIA.AI.Notebooks/GenAI/Image/test.ipynb"

    def test_forward_slashes_converted(self):
        """Input with forward slashes should work via Path.resolve()."""
        result = win_to_wsl_path("C:/Users/test/file.py")
        assert result == "/mnt/c/Users/test/file.py"


# --- _default_mode ---


class TestDefaultMode:
    def test_windows_returns_wsl(self):
        with patch("wsl_papermill.platform.system", return_value="Windows"):
            assert _default_mode() == "wsl"

    def test_darwin_returns_native(self):
        with patch("wsl_papermill.platform.system", return_value="Darwin"):
            assert _default_mode() == "native"

    def test_linux_returns_native(self):
        with patch("wsl_papermill.platform.system", return_value="Linux"):
            assert _default_mode() == "native"


# --- _validate_output ---


class TestValidateOutput:
    def test_all_cells_executed_no_errors(self, tmp_path):
        nb = {
            "cells": [
                {"cell_type": "code", "execution_count": 1, "outputs": []},
                {"cell_type": "code", "execution_count": 2, "outputs": [
                    {"output_type": "stream", "text": ["ok"]}
                ]},
            ]
        }
        p = tmp_path / "test.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        assert _validate_output(p, 1.0) == 0

    def test_cell_error_returns_3(self, tmp_path):
        nb = {
            "cells": [
                {"cell_type": "code", "execution_count": 1, "outputs": [
                    {"output_type": "error", "ename": "ValueError", "evalue": "bad"}
                ]},
            ]
        }
        p = tmp_path / "test.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        assert _validate_output(p, 1.0) == 3

    def test_invalid_json_returns_0(self, tmp_path):
        p = tmp_path / "bad.ipynb"
        p.write_text("not json", encoding="utf-8")
        assert _validate_output(p, 1.0) == 0

    def test_mixed_code_and_markdown(self, tmp_path):
        nb = {
            "cells": [
                {"cell_type": "markdown", "source": ["# Title"]},
                {"cell_type": "code", "execution_count": 1, "outputs": []},
                {"cell_type": "markdown", "source": ["## Section"]},
            ]
        }
        p = tmp_path / "test.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        assert _validate_output(p, 1.0) == 0


# --- Lean diagnostics are errors too (#16176, finding 1) ---


def _lean_html(messages_json):
    """Sortie Lean telle qu'un notebook la stocke : le JSON du REPL dans un <code>."""
    return ["<details>\n", "    <summary>Raw output</summary>\n",
            f"    <code>{messages_json}</code>\n", "</details>\n"]


class TestLeanSeverityErrors:
    """Un kernel Lean n'emet jamais `output_type: "error"` : il rend une
    `display_data` dont le HTML porte les diagnostics du noyau. Le compteur qui
    ne regardait que le niveau Jupyter rendait donc le meme `0 errors` sur un
    kernel mort et sur un kernel sain."""

    def _nb_with(self, html, exec_count=1):
        return {"cells": [{"cell_type": "code", "execution_count": exec_count,
                           "outputs": [{"output_type": "display_data",
                                        "data": {"text/html": html,
                                                 "text/plain": ["#eval 2+2"]},
                                        "metadata": {}}]}]}

    def test_lean_error_severity_is_counted(self, tmp_path):
        nb = self._nb_with(_lean_html(
            '{"messages": [{"severity": "error", "pos": {"line": 16, "column": 0},'
            ' "endPos": {"line": 16, "column": 4},'
            ' "data": "unexpected identifier; expected command"}], "env": 13}'))
        p = tmp_path / "lean.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        assert _validate_output(p, 1.0) == 3

    def test_lean_warning_and_info_are_not_errors(self, tmp_path):
        nb = self._nb_with(_lean_html(
            '{"messages": [{"severity": "warning", "data": "unused variable `input`"},'
            ' {"severity": "info", "data": "{ inFeatures := 784,"}], "env": 1}'))
        p = tmp_path / "lean_ok.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        assert _validate_output(p, 1.0) == 0

    def test_lean_error_counted_despite_brackets_in_data(self, tmp_path):
        """Le `data` porte du source Lean, donc des `]` et des `{` : l'extraction
        doit etre un vrai parse JSON, pas un `\\[.*?\\]` qui coupe trop tot."""
        nb = self._nb_with(_lean_html(
            '{"messages": [{"severity": "info", "data": "def f := [1, 2] { x := 3 }"},'
            ' {"severity": "error", "data": "failed to synthesize instance"}], "env": 7}'))
        p = tmp_path / "lean_brackets.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        assert _validate_output(p, 1.0) == 3

    def test_count_cell_errors_splits_jupyter_from_lean(self, tmp_path):
        nb = {"cells": [
            {"cell_type": "code", "execution_count": 1,
             "outputs": [{"output_type": "error", "ename": "ValueError", "evalue": "bad"}]},
            {"cell_type": "code", "execution_count": 2,
             "outputs": [{"output_type": "display_data",
                          "data": {"text/html": _lean_html(
                              '{"messages": [{"severity": "error", "data": "boom"}], "env": 0}')}}]},
            {"cell_type": "code", "execution_count": 3, "outputs": []},
        ]}
        assert count_cell_errors(nb) == (1, 1)

    def test_one_lean_error_cell_counted_once_even_with_two_outputs(self, tmp_path):
        """Une cellule qui rend deux sorties fautives reste UNE cellule en erreur."""
        err = {"output_type": "display_data",
               "data": {"text/html": _lean_html(
                   '{"messages": [{"severity": "error", "data": "boom"}], "env": 0}')}}
        nb = {"cells": [{"cell_type": "code", "execution_count": 1, "outputs": [err, err]}]}
        assert count_cell_errors(nb) == (0, 1)

    def test_severity_mentioned_without_a_messages_block_is_not_flagged(self, tmp_path):
        """Un texte qui PARLE de la severite, sans bloc portant la cle `messages`,
        n'est pas un diagnostic."""
        nb = self._nb_with(["La sortie porte \"severity\": \"error\" quand ca casse."])
        p = tmp_path / "prose.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        assert _validate_output(p, 1.0) == 0

    # --- l'ancre doit viser la CLE, pas le prefixe `{"messages"` ---
    #
    # Le REPL Lean ne garantit pas que `messages` soit le premier champ du bloc.
    # Mesure sur le corpus : 108 des 1030 blocs commencent par `sorries`, donc
    # une ancre de prefixe les ratait tous en silence.

    def test_lean_error_counted_when_messages_is_not_the_first_field(self):
        nb = self._nb_with(_lean_html(
            '{"sorries": [], "messages": [{"severity": "error",'
            ' "data": "failed to synthesize instance"}], "env": 11}'))
        assert count_cell_errors(nb) == (0, 1)

    def test_lean_error_counted_when_a_nested_brace_precedes_the_key(self):
        """Le `{` le plus proche de la cle peut appartenir a un AUTRE objet : la
        remontee doit continuer jusqu'a celui qui porte vraiment `messages`."""
        nb = self._nb_with(_lean_html(
            '{"sorries": [{"pos": {"line": 9, "column": 2}}],'
            ' "messages": [{"severity": "error", "data": "boom"}], "env": 3}'))
        assert count_cell_errors(nb) == (0, 1)

    def test_lean_error_and_sorries_count_once_per_cell(self):
        """Un bloc a champs multiples reste UNE cellule en erreur, meme si les
        deux champs portent de la matiere."""
        nb = self._nb_with(_lean_html(
            '{"sorries": [{"pos": {"line": 1}}],'
            ' "messages": [{"severity": "error", "data": "boom"},'
            ' {"severity": "error", "data": "boom2"}], "env": 0}'))
        assert count_cell_errors(nb) == (0, 1)

    def test_lean_error_counted_in_a_non_enumerated_output_type(self):
        """Aucun filtre sur `output_type` : un type non enumere qui porte le
        diagnostic ne doit pas le perdre en silence."""
        nb = {"cells": [{"cell_type": "code", "execution_count": 1,
                         "outputs": [{"output_type": "some_future_kind",
                                      "data": {"text/html": _lean_html(
                                          '{"messages": [{"severity": "error",'
                                          ' "data": "boom"}], "env": 0}')}}]}]}
        assert count_cell_errors(nb) == (0, 1)


# --- execute_notebook dispatch ---


class TestExecuteNotebookDispatch:
    def test_auto_mode_dispatches_correctly(self):
        """execute_notebook with mode='auto' dispatches based on platform."""
        with patch("wsl_papermill._default_mode", return_value="native"):
            with patch("wsl_papermill.execute_notebook_native", return_value=0) as mock:
                result = execute_notebook("test.ipynb", mode="auto")
                mock.assert_called_once()
                assert result == 0

    def test_explicit_wsl_mode(self):
        with patch("wsl_papermill.execute_notebook_wsl", return_value=0) as mock:
            result = execute_notebook("test.ipynb", mode="wsl")
            mock.assert_called_once()

    def test_explicit_native_mode(self):
        with patch("wsl_papermill.execute_notebook_native", return_value=0) as mock:
            result = execute_notebook("test.ipynb", mode="native")
            mock.assert_called_once()

    def test_invalid_mode_returns_1(self):
        result = execute_notebook("test.ipynb", mode="invalid")
        assert result == 1


# --- execute_notebook_native ---


class TestExecuteNotebookNative:
    def test_missing_notebook_returns_1(self):
        result = execute_notebook_native("/nonexistent/path.ipynb")
        assert result == 1

    def test_timeout_returns_2(self, tmp_path):
        nb = {"cells": [], "nbformat": 4}
        p = tmp_path / "test.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")

        with patch("subprocess.run", side_effect=__import__("subprocess").TimeoutExpired("cmd", 300)):
            result = execute_notebook_native(str(p), timeout=300)
            assert result == 2

    def test_failed_execution_returns_1(self, tmp_path):
        nb = {"cells": [], "nbformat": 4}
        p = tmp_path / "test.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")

        mock = MagicMock()
        mock.returncode = 1
        mock.stderr = "Error: kernel not found"

        with patch("subprocess.run", return_value=mock):
            result = execute_notebook_native(str(p))
            assert result == 1


# --- check_env dispatch ---


class TestCheckEnvDispatch:
    def test_auto_mode_dispatches(self):
        with patch("wsl_papermill._default_mode", return_value="native"):
            with patch("wsl_papermill.check_env_native", return_value=True) as mock:
                assert check_env("auto") is True
                mock.assert_called_once()

    def test_wsl_mode(self):
        with patch("wsl_papermill.check_env_wsl", return_value=False) as mock:
            assert check_env("wsl") is False
            mock.assert_called_once()

    def test_invalid_mode(self):
        assert check_env("invalid") is False


# --- venv derivation from kernelspec (#14908) ---


class TestVenvFromInterpreter:
    def test_venv_python3(self):
        assert _venv_from_interpreter("/home/jesse/.lean4-venv/bin/python3") == "/home/jesse/.lean4-venv"

    def test_venv_python(self):
        assert _venv_from_interpreter("/home/jesse/x/bin/python") == "/home/jesse/x"

    def test_system_python_none(self):
        assert _venv_from_interpreter("/usr/bin/python3") is None

    def test_bin_python_none(self):
        assert _venv_from_interpreter("/bin/python3") is None

    def test_bare_python_none(self):
        assert _venv_from_interpreter("python3") is None

    def test_none(self):
        assert _venv_from_interpreter(None) is None


class TestDeclaredVenvFromKernelJson:
    def test_extracts_argv_interpreter(self):
        kj = {"argv": ["/home/jesse/x/bin/python3", "-m", "ipykernel_launcher"]}
        assert _declared_venv_from_kernel_json(kj) == "/home/jesse/x"

    def test_bare_python_returns_none(self):
        assert _declared_venv_from_kernel_json({"argv": ["python", "-m", "x"]}) is None

    def test_empty_returns_none(self):
        assert _declared_venv_from_kernel_json({}) is None

    def test_none_returns_none(self):
        assert _declared_venv_from_kernel_json(None) is None


class TestNormalizeVenv:
    def test_expands_tilde(self):
        assert _normalize_venv("~/coursia-wsl", "/home/jesse") == "/home/jesse/coursia-wsl"

    def test_strips_trailing_slash(self):
        assert _normalize_venv("/home/jesse/coursia-wsl/", "/home/jesse") == "/home/jesse/coursia-wsl"

    def test_empty_none(self):
        assert _normalize_venv(None) == ""


class TestVenvMismatchMessage:
    def test_mismatch_returns_message(self):
        msg = _venv_mismatch_message("python3-wsl", "~/coursia-wsl", "/home/jesse/.lean4-venv", "/home/jesse")
        assert msg is not None and ".lean4-venv" in msg and "--venv" in msg

    def test_same_venv_no_message(self):
        assert _venv_mismatch_message("k", "~/coursia-wsl", "/home/jesse/coursia-wsl", "/home/jesse") is None

    def test_no_declared_no_message(self):
        assert _venv_mismatch_message("k", "~/coursia-wsl", None, "/home/jesse") is None


class TestExecuteNotebookWslVenv:
    def _write_nb(self, tmp_path):
        nb = {"cells": [], "nbformat": 4}
        p = tmp_path / "t.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        return p

    def test_warns_on_declared_mismatch(self, tmp_path, capsys):
        p = self._write_nb(tmp_path)
        kj = {"argv": ["/home/jesse/.lean4-venv/bin/python3", "-m", "ipykernel_launcher"]}
        with patch("wsl_papermill._find_kernel_json_wsl", return_value=kj), \
             patch("wsl_papermill._wsl_home", return_value="/home/jesse"), \
             patch("wsl_papermill.run_wsl", return_value=(0, "", "")):
            rc = execute_notebook_wsl(str(p), kernel="python3-wsl")
        out = capsys.readouterr().out
        assert rc == 0
        assert ".lean4-venv" in out  # divergence is printed, not silent

    def test_default_venv_unchanged(self, tmp_path, capsys):
        p = self._write_nb(tmp_path)
        with patch("wsl_papermill._find_kernel_json_wsl", return_value=None), \
             patch("wsl_papermill.run_wsl", return_value=(0, "", "")):
            rc = execute_notebook_wsl(str(p), kernel="python3-wsl")
        out = capsys.readouterr().out
        assert rc == 0
        assert "~/coursia-wsl" in out  # default venv in use, no silent divergence


# --- batch_execute mode propagation ---


class TestBatchExecuteMode:
    def test_batch_propagates_mode(self, tmp_path):
        """batch_execute passes mode to execute_notebook."""
        nb = {"cells": [], "nbformat": 4}
        p = tmp_path / "test.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")

        with patch("wsl_papermill.execute_notebook", return_value=0) as mock:
            batch_execute(str(tmp_path), mode="native")
            mock.assert_called_once()
            assert mock.call_args.kwargs.get("mode") == "native" or "native" in str(mock.call_args)


# --- check_env_wsl kernelspec listing (#14908 followup) ---


class TestCheckEnvWslKernelspecs:
    def test_lists_registered_kernelspecs(self, capsys):
        """When `jupyter kernelspec list` returns names, they are printed and counted."""
        kspec_out = "Available kernels:\n  python3    /usr/local/share/jupyter/kernels/python3\n  gametheory-wsl    /home/jesse/.local/share/jupyter/kernels/gametheory-wsl\n"
        # Patch sequence: test -d (venv), pip list (must include all 6 pkgs so ok stays True), jupyter kernelspec list
        run_wsl_responses = iter([
            (0, "OK", ""),                                     # test -d
            (0, "papermill 2.5.0\nipykernel 6.0.0\nnashpy 0.0.0\nmatplotlib 3.0.0\nnumpy 1.0.0\nscipy 1.0.0\n", ""),  # pip list
            (0, kspec_out, ""),                                # jupyter kernelspec list
        ])

        def fake_run_wsl(cmd, timeout=300):
            return next(run_wsl_responses)

        with patch("wsl_papermill.run_wsl", side_effect=fake_run_wsl):
            ok = check_env_wsl()
        out = capsys.readouterr().out
        assert ok is True
        assert "kernelspecs registered in venv (2): python3, gametheory-wsl" in out
        assert "WARNING" not in out  # python3 present, no warning

    def test_warns_when_no_python_kernelspec(self, capsys):
        """If no python-prefixed kernelspec is registered, warn — notebooks declaring
        `python3` or `python3-wsl` will hit NoSuchKernel."""
        kspec_out = "Available kernels:\n  gametheory-wsl    /home/jesse/.local/share/jupyter/kernels/gametheory-wsl\n"
        run_wsl_responses = iter([
            (0, "OK", ""),
            (0, "papermill 2.5.0\nipykernel 6.0.0\nnashpy 0.0.0\nmatplotlib 3.0.0\nnumpy 1.0.0\nscipy 1.0.0\n", ""),
            (0, kspec_out, ""),
        ])

        def fake_run_wsl(cmd, timeout=300):
            return next(run_wsl_responses)

        with patch("wsl_papermill.run_wsl", side_effect=fake_run_wsl):
            check_env_wsl()
        out = capsys.readouterr().out
        assert "WARNING: no python-prefixed kernelspec registered" in out

    def test_kernelspec_list_unavailable_does_not_fail(self, capsys):
        """If `jupyter kernelspec list` exits non-zero (jupyter not installed in venv),
        check_env does not blow up — pip-list still passes."""
        run_wsl_responses = iter([
            (0, "OK", ""),
            (0, "papermill 2.5.0\nipykernel 6.0.0\nnashpy 0.0.0\nmatplotlib 3.0.0\nnumpy 1.0.0\nscipy 1.0.0\n", ""),
            (1, "", "jupyter: command not found"),  # kernelspec list fails
        ])

        def fake_run_wsl(cmd, timeout=300):
            return next(run_wsl_responses)

        with patch("wsl_papermill.run_wsl", side_effect=fake_run_wsl):
            ok = check_env_wsl()
        out = capsys.readouterr().out
        assert ok is True
        assert "jupyter kernelspec list unavailable" in out

