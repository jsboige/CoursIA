"""Tests for ``GameTheory/scripts/validate_lean_setup.py`` (CPU-only, hermetic).

``validate_lean_setup.py`` (329L) is the **environment-validation CLI** for the
GameTheory Lean series: it probes Python version, elan/lean/lake commands, Python
packages (nashpy/numpy/sympy/lean4-jupyter), Jupyter kernels (lean4 / lean4-wsl),
the canonical kernel wrapper (regression #1618), and the ``social_choice_lean``
lake + ``lean_runner.py`` presence.

It was a **0-test orphan** (0 importers, 18 sibling test files in
``GameTheory/tests/`` none targeting it, 0 PR history). These tests pin the
check-function decision logic (found / not-found / graceful-degradation branches)
by mocking ``subprocess.run``, ``shutil.which`` and the ``__import__`` path.

The module has an ``if __name__ == "__main__"`` guard and imports cleanly; the
only import-time side effect is ``_inspect_kernel_wrapper = _load_inspect_kernel_wrapper()``
which returns ``None`` gracefully when the shared helper is absent.

Run with: pytest MyIA.AI.Notebooks/GameTheory/tests/test_validate_lean_setup.py -v
"""

import collections
import subprocess
import sys
import types
from pathlib import Path

import pytest

# Locate + import the module under test (NOT a package — add scripts/ to sys.path).
_SCRIPTS = Path(__file__).resolve().parent.parent / "scripts"
sys.path.insert(0, str(_SCRIPTS))
import validate_lean_setup as v  # noqa: E402


# --------------------------------------------------------------------------- #
#  Colors + print helpers                                                      #
# --------------------------------------------------------------------------- #

class TestColors:
    """Colors : constantes ANSI non-vides."""

    def test_color_constants_are_ansi(self):
        for name in ("GREEN", "RED", "YELLOW", "BLUE", "END", "BOLD"):
            assert getattr(v.Colors, name).startswith("\033[")

    def test_end_resets(self):
        assert v.Colors.END == "\033[0m"


class TestPrintHelpers:
    """print_section / print_ok / print_error / print_warning -> stdout formate."""

    def test_print_ok_prefix(self, capsys):
        v.print_ok("all good")
        out = capsys.readouterr().out
        assert "[OK]" in out
        assert "all good" in out
        assert v.Colors.GREEN in out

    def test_print_error_prefix(self, capsys):
        v.print_error("boom")
        out = capsys.readouterr().out
        assert "[X]" in out
        assert "boom" in out
        assert v.Colors.RED in out

    def test_print_warning_prefix(self, capsys):
        v.print_warning("careful")
        out = capsys.readouterr().out
        assert "[!]" in out
        assert "careful" in out
        assert v.Colors.YELLOW in out

    def test_print_section_banner(self, capsys):
        v.print_section("MY TITLE")
        out = capsys.readouterr().out
        assert "MY TITLE" in out
        # Banner has separator rows of '='
        assert "=" * 60 in out


# --------------------------------------------------------------------------- #
#  check_python                                                                #
# --------------------------------------------------------------------------- #

class TestCheckPython:
    """check_python : True si sys.version_info >= (3, 8)."""

    def test_current_version_ok(self, capsys):
        # The test runner itself is >= 3.8.
        assert v.check_python() is True
        assert "Python" in capsys.readouterr().out

    def test_old_version_fails(self, monkeypatch, capsys):
        # sys.version_info supports BOTH attribute access (.major/.minor) AND
        # tuple comparison (>= (3,8)) — a namedtuple satisfies both (plain tuple
        # does not, it has no .major).
        VersionInfo = collections.namedtuple(
            "sys_version_info", ["major", "minor", "micro", "releaselevel", "serial"]
        )
        monkeypatch.setattr(v.sys, "version_info", VersionInfo(3, 7, 0, "final", 0))
        assert v.check_python() is False
        assert "3.8+ requis" in capsys.readouterr().out


# --------------------------------------------------------------------------- #
#  check_command                                                               #
# --------------------------------------------------------------------------- #

class TestCheckCommand:
    """check_command : shutil.which + subprocess.run, + branch special Linux/elan."""

    def test_command_not_found(self, monkeypatch, capsys):
        monkeypatch.setattr(v.shutil, "which", lambda cmd: None)
        # Force non-Linux so the elan special-case is skipped.
        monkeypatch.setattr("platform.system", lambda: "Windows")
        assert v.check_command("elan", "elan") is False
        assert "Non trouve" in capsys.readouterr().out

    def test_command_found_version_ok(self, monkeypatch, capsys):
        monkeypatch.setattr(v.shutil, "which", lambda cmd: "/usr/bin/elan")
        monkeypatch.setattr("platform.system", lambda: "Windows")

        class _R:
            returncode = 0
            stdout = "elan 3.50.1\n"

        monkeypatch.setattr(v.subprocess, "run", lambda *a, **k: _R())
        assert v.check_command("elan", "elan") is True
        out = capsys.readouterr().out
        assert "elan: elan 3.50.1" in out

    def test_command_found_but_version_raises_returns_true_warning(
        self, monkeypatch, capsys
    ):
        # Command present but subprocess.run raises -> "found but version error",
        # still returns True (binary exists, just couldn't read version).
        monkeypatch.setattr(v.shutil, "which", lambda cmd: "/usr/bin/lean")

        def _boom(*a, **k):
            raise OSError("timeout")

        monkeypatch.setattr(v.subprocess, "run", _boom)
        monkeypatch.setattr("platform.system", lambda: "Windows")
        assert v.check_command("lean", "Lean 4") is True
        assert "Trouve mais erreur version" in capsys.readouterr().out

    def test_version_takes_first_line_only(self, monkeypatch, capsys):
        # Multi-line stdout -> version = first line only.
        monkeypatch.setattr(v.shutil, "which", lambda cmd: "/x/lake")

        class _R:
            returncode = 0
            stdout = "Lake version 3.50.1\nsome extra build info\n"

        monkeypatch.setattr(v.subprocess, "run", lambda *a, **k: _R())
        monkeypatch.setattr("platform.system", lambda: "Windows")
        v.check_command("lake", "Lake")
        out = capsys.readouterr().out
        assert "Lake: Lake version 3.50.1" in out
        assert "extra build info" not in out

    def test_linux_elan_specialcase_bash_path(self, monkeypatch, capsys):
        # On Linux, elan/lean/lake/repl are probed via `source ~/.elan/env`.
        monkeypatch.setattr("platform.system", lambda: "Linux")

        calls = []

        class _R:
            returncode = 0
            stdout = "elan 3.50.1\n"

        def _fake_run(cmd, **k):
            calls.append(cmd)
            return _R()

        monkeypatch.setattr(v.subprocess, "run", _fake_run)
        # shutil.which not reached when bash path succeeds.
        which_called = []
        monkeypatch.setattr(v.shutil, "which", lambda cmd: which_called.append(cmd) or None)

        assert v.check_command("elan", "elan") is True
        # The bash invocation was used.
        assert calls and calls[0][0] == "bash"
        assert "source ~/.elan/env" in calls[0][2]
        assert which_called == []  # which NOT consulted.


# --------------------------------------------------------------------------- #
#  check_python_package                                                        #
# --------------------------------------------------------------------------- #

class TestCheckPythonPackage:
    """check_python_package : import_name (default pkg.replace('-','_')) + __version__."""

    def test_installed_with_version(self, monkeypatch, capsys):
        fake = types.ModuleType("fakepkg")
        fake.__version__ = "1.2.3"
        monkeypatch.setitem(sys.modules, "fakepkg", fake)
        assert v.check_python_package("fakepkg") is True
        assert "fakepkg: 1.2.3" in capsys.readouterr().out

    def test_installed_without_version_shows_unknown(self, monkeypatch, capsys):
        fake = types.ModuleType("noversion")
        monkeypatch.setitem(sys.modules, "noversion", fake)
        assert v.check_python_package("noversion") is True
        assert "noversion: unknown" in capsys.readouterr().out

    def test_not_installed_returns_false(self, monkeypatch, capsys):
        monkeypatch.setitem(sys.modules, "absent_pkg", None)  # triggers ImportError on import
        assert v.check_python_package("absent_pkg") is False
        assert "Non installe" in capsys.readouterr().out

    def test_default_import_name_normalizes_dashes(self, monkeypatch, capsys):
        # pkg_name with dashes -> import_name with underscores when import_name=None.
        fake = types.ModuleType("dash_pkg")
        fake.__version__ = "0.1"
        monkeypatch.setitem(sys.modules, "dash_pkg", fake)
        assert v.check_python_package("dash-pkg") is True
        assert "dash-pkg: 0.1" in capsys.readouterr().out

    def test_explicit_import_name_used(self, monkeypatch, capsys):
        fake = types.ModuleType("real_import")
        fake.__version__ = "9.9"
        monkeypatch.setitem(sys.modules, "real_import", fake)
        # pkg_name != import_name explicitly provided.
        assert v.check_python_package("pypi-name", "real_import") is True
        assert "pypi-name: 9.9" in capsys.readouterr().out


# --------------------------------------------------------------------------- #
#  check_jupyter_kernel                                                        #
# --------------------------------------------------------------------------- #

class TestCheckJupyterKernel:
    """check_jupyter_kernel : 'jupyter kernelspec list' stdout, case-insensitive match."""

    def test_kernel_present(self, monkeypatch, capsys):
        class _R:
            returncode = 0
            stdout = "Available kernels:\n  python3    /path/python3\n  lean4-wsl  /path/lean4-wsl\n"

        monkeypatch.setattr(v.subprocess, "run", lambda *a, **k: _R())
        assert v.check_jupyter_kernel("lean4-wsl") is True

    def test_kernel_absent(self, monkeypatch, capsys):
        class _R:
            returncode = 0
            stdout = "Available kernels:\n  python3    /path/python3\n"

        monkeypatch.setattr(v.subprocess, "run", lambda *a, **k: _R())
        assert v.check_jupyter_kernel("lean4-wsl") is False
        assert "non trouve" in capsys.readouterr().out

    def test_match_is_case_insensitive(self, monkeypatch):
        class _R:
            returncode = 0
            stdout = "  LEAN4-WSL  /path\n"

        monkeypatch.setattr(v.subprocess, "run", lambda *a, **k: _R())
        assert v.check_jupyter_kernel("lean4-wsl") is True

    def test_subprocess_error_returns_false(self, monkeypatch, capsys):
        def _boom(*a, **k):
            raise FileNotFoundError("jupyter not on PATH")

        monkeypatch.setattr(v.subprocess, "run", _boom)
        assert v.check_jupyter_kernel("lean4") is False
        assert "Erreur verification" in capsys.readouterr().out


# --------------------------------------------------------------------------- #
#  _load_inspect_kernel_wrapper                                                #
# --------------------------------------------------------------------------- #

class TestLoadInspectKernelWrapper:
    """_load_inspect_kernel_wrapper : walk parents for scripts/lean/lean_kernel_check.py."""

    def test_helper_absent_returns_none(self, tmp_path, monkeypatch):
        # __file__ inside a tree with NO scripts/lean/lean_kernel_check.py.
        fake_file = tmp_path / "scripts" / "validate_lean_setup.py"
        fake_file.parent.mkdir(parents=True)
        fake_file.write_text("# stub")
        monkeypatch.setattr(v, "__file__", str(fake_file))
        assert v._load_inspect_kernel_wrapper() is None

    def test_helper_present_returns_callable(self, tmp_path, monkeypatch):
        # Build scripts/lean/lean_kernel_check.py defining inspect_kernel_wrapper.
        scripts_lean = tmp_path / "scripts" / "lean"
        scripts_lean.mkdir(parents=True)
        (scripts_lean / "lean_kernel_check.py").write_text(
            "def inspect_kernel_wrapper(name):\n"
            "    return ('ok', 'stub wrapper ok for ' + name)\n"
        )
        fake_file = tmp_path / "deep" / "validate_lean_setup.py"
        fake_file.parent.mkdir(parents=True)
        fake_file.write_text("# stub")
        monkeypatch.setattr(v, "__file__", str(fake_file))
        # The module-level import already cached the REAL repo lean_kernel_check;
        # clear it so our tmp stub is re-imported fresh from the injected sys.path.
        monkeypatch.delitem(sys.modules, "lean_kernel_check", raising=False)

        fn = v._load_inspect_kernel_wrapper()
        assert callable(fn)
        assert fn("lean4-wsl") == ("ok", "stub wrapper ok for lean4-wsl")

    def test_helper_present_but_import_fails_returns_none(
        self, tmp_path, monkeypatch
    ):
        scripts_lean = tmp_path / "scripts" / "lean"
        scripts_lean.mkdir(parents=True)
        # Syntactically broken module -> import raises -> None.
        (scripts_lean / "lean_kernel_check.py").write_text("def broken(:\n")
        fake_file = tmp_path / "deep" / "validate_lean_setup.py"
        fake_file.parent.mkdir(parents=True)
        fake_file.write_text("# stub")
        monkeypatch.setattr(v, "__file__", str(fake_file))
        # Clear the cached real module so our broken stub is re-imported.
        monkeypatch.delitem(sys.modules, "lean_kernel_check", raising=False)

        assert v._load_inspect_kernel_wrapper() is None


# --------------------------------------------------------------------------- #
#  check_kernel_wrapper                                                        #
# --------------------------------------------------------------------------- #

class TestCheckKernelWrapper:
    """check_kernel_wrapper : None->warning+True ; sinon status->printer, status=='ok'->True."""

    def test_no_helper_returns_true_with_warning(self, monkeypatch, capsys):
        monkeypatch.setattr(v, "_inspect_kernel_wrapper", None)
        assert v.check_kernel_wrapper("lean4-wsl") is True
        assert "helper lean_kernel_check introuvable" in capsys.readouterr().out

    def test_helper_ok_returns_true(self, monkeypatch, capsys):
        monkeypatch.setattr(
            v, "_inspect_kernel_wrapper", lambda name: ("ok", "wrapper v5 OK")
        )
        assert v.check_kernel_wrapper("lean4-wsl") is True
        assert "wrapper v5 OK" in capsys.readouterr().out

    def test_helper_error_returns_false(self, monkeypatch, capsys):
        monkeypatch.setattr(
            v, "_inspect_kernel_wrapper", lambda name: ("error", "old bash wrapper")
        )
        assert v.check_kernel_wrapper("lean4-wsl") is False
        assert "old bash wrapper" in capsys.readouterr().out

    def test_helper_warning_returns_false(self, monkeypatch):
        # status != "ok" (warning) -> False.
        monkeypatch.setattr(
            v, "_inspect_kernel_wrapper", lambda name: ("warning", "kernel not found")
        )
        assert v.check_kernel_wrapper("lean4-wsl") is False


# --------------------------------------------------------------------------- #
#  check_social_choice_lean                                                    #
# --------------------------------------------------------------------------- #

class TestCheckSocialChoiceLean:
    """check_social_choice_lean : Path(__file__).parent.parent/social_choice_lean/lakefile.lean."""

    def test_lakefile_present(self, tmp_path, monkeypatch, capsys):
        # __file__ = tmp/scripts/validate_lean_setup.py -> parent.parent = tmp.
        scripts = tmp_path / "scripts"
        scripts.mkdir()
        fake_file = scripts / "validate_lean_setup.py"
        fake_file.write_text("# stub")
        (tmp_path / "social_choice_lean" / "lakefile.lean").parent.mkdir(parents=True)
        (tmp_path / "social_choice_lean" / "lakefile.lean").write_text("{}")
        monkeypatch.setattr(v, "__file__", str(fake_file))

        assert v.check_social_choice_lean() is True
        assert "Projet Lake trouve" in capsys.readouterr().out

    def test_lakefile_absent(self, tmp_path, monkeypatch, capsys):
        scripts = tmp_path / "scripts"
        scripts.mkdir()
        fake_file = scripts / "validate_lean_setup.py"
        fake_file.write_text("# stub")
        monkeypatch.setattr(v, "__file__", str(fake_file))

        assert v.check_social_choice_lean() is False
        assert "Projet Lake manquant" in capsys.readouterr().out


# --------------------------------------------------------------------------- #
#  check_lean_runner                                                           #
# --------------------------------------------------------------------------- #

class TestCheckLeanRunner:
    """check_lean_runner : lean_runner.py present + importable."""

    def test_runner_absent_returns_false(self, tmp_path, monkeypatch, capsys):
        # __file__ = tmp/a/b/validate_lean_setup.py -> parent.parent.parent = tmp.
        deep = tmp_path / "a" / "b"
        deep.mkdir(parents=True)
        fake_file = deep / "validate_lean_setup.py"
        fake_file.write_text("# stub")
        monkeypatch.setattr(v, "__file__", str(fake_file))
        # No SymbolicAI/Lean/lean_runner.py created under tmp.

        assert v.check_lean_runner() is False
        assert "Manquant" in capsys.readouterr().out

    def test_runner_present_importable(self, tmp_path, monkeypatch, capsys):
        deep = tmp_path / "a" / "b"
        deep.mkdir(parents=True)
        fake_file = deep / "validate_lean_setup.py"
        fake_file.write_text("# stub")
        lean_dir = tmp_path / "SymbolicAI" / "Lean"
        lean_dir.mkdir(parents=True)
        (lean_dir / "lean_runner.py").write_text("print('lean runner')\n")
        monkeypatch.setattr(v, "__file__", str(fake_file))
        # Inject a fake lean_runner module so __import__ succeeds.
        fake_mod = types.ModuleType("lean_runner")
        monkeypatch.setitem(sys.modules, "lean_runner", fake_mod)

        assert v.check_lean_runner() is True
        assert "lean_runner.py: OK" in capsys.readouterr().out

    def test_runner_present_but_import_fails(self, tmp_path, monkeypatch, capsys):
        deep = tmp_path / "a" / "b"
        deep.mkdir(parents=True)
        fake_file = deep / "validate_lean_setup.py"
        fake_file.write_text("# stub")
        lean_dir = tmp_path / "SymbolicAI" / "Lean"
        lean_dir.mkdir(parents=True)
        (lean_dir / "lean_runner.py").write_text("syntax error {{{")
        monkeypatch.setattr(v, "__file__", str(fake_file))
        # Force import to raise.
        real_import = __import__

        def _fail(name, *a, **k):
            if name == "lean_runner":
                raise ImportError("broken")
            return real_import(name, *a, **k)

        monkeypatch.setattr("builtins.__import__", _fail)

        assert v.check_lean_runner() is False
        assert "Erreur import" in capsys.readouterr().out


# --------------------------------------------------------------------------- #
#  main (argparse routing)                                                     #
# --------------------------------------------------------------------------- #

class TestMain:
    """main : --wsl -> validate_wsl, default -> validate_windows, sys.exit code."""

    def test_default_routes_to_windows(self, monkeypatch):
        called = {}
        monkeypatch.setattr(v, "validate_windows", lambda: called.setdefault("win", True))
        monkeypatch.setattr(v, "validate_wsl", lambda: called.setdefault("wsl", True))
        monkeypatch.setattr(sys, "argv", ["validate_lean_setup.py"])
        with pytest.raises(SystemExit) as exc:
            v.main()
        assert exc.value.code == 0
        assert called.get("win") is True
        assert "wsl" not in called

    def test_wsl_flag_routes_to_wsl(self, monkeypatch):
        called = {}
        monkeypatch.setattr(v, "validate_windows", lambda: called.setdefault("win", True))
        monkeypatch.setattr(v, "validate_wsl", lambda: called.setdefault("wsl", True))
        monkeypatch.setattr(sys, "argv", ["validate_lean_setup.py", "--wsl"])
        with pytest.raises(SystemExit) as exc:
            v.main()
        assert exc.value.code == 0
        assert called.get("wsl") is True
        assert "win" not in called

    def test_failure_exits_nonzero(self, monkeypatch):
        monkeypatch.setattr(v, "validate_windows", lambda: False)
        monkeypatch.setattr(sys, "argv", ["validate_lean_setup.py"])
        with pytest.raises(SystemExit) as exc:
            v.main()
        assert exc.value.code == 1


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
