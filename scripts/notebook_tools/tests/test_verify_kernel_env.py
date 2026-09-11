"""Tests for verify_kernel_env.py -- static kernelspec check (#14908)."""

import json
import sys
from pathlib import Path
from unittest.mock import patch

import pytest

sys.path.insert(0, str(Path(__file__).parent.parent))
from verify_kernel_env import (  # noqa: E402
    _load_kernelspec_via_jupyter_client,
    _normalize_venv,
    _read_nb_kernelspec,
    _venv_from_interpreter,
    main,
    verify_one,
)


# --- _venv_from_interpreter ---


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


# --- _normalize_venv ---


class TestNormalizeVenv:
    def test_expands_tilde(self):
        assert _normalize_venv("~/coursia-wsl", "/home/jesse") == "/home/jesse/coursia-wsl"

    def test_strips_trailing_slash(self):
        assert _normalize_venv("/home/jesse/coursia-wsl/", "/home/jesse") == "/home/jesse/coursia-wsl"

    def test_empty_none(self):
        assert _normalize_venv(None, "/home/jesse") == ""


# --- _read_nb_kernelspec ---


class TestReadNbKernelspec:
    def test_returns_kernelspec(self, tmp_path):
        nb = {"metadata": {"kernelspec": {"name": "python3-wsl", "display_name": "Python"}}}
        p = tmp_path / "test.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        ks = _read_nb_kernelspec(p)
        assert ks == {"name": "python3-wsl", "display_name": "Python"}

    def test_no_metadata_returns_none(self, tmp_path):
        p = tmp_path / "test.ipynb"
        p.write_text(json.dumps({"cells": []}), encoding="utf-8")
        assert _read_nb_kernelspec(p) is None

    def test_no_kernelspec_returns_none(self, tmp_path):
        p = tmp_path / "test.ipynb"
        p.write_text(json.dumps({"metadata": {"language": "python"}}), encoding="utf-8")
        assert _read_nb_kernelspec(p) is None

    def test_invalid_json_returns_none(self, tmp_path):
        p = tmp_path / "bad.ipynb"
        p.write_text("not json", encoding="utf-8")
        assert _read_nb_kernelspec(p) is None


# --- _load_kernelspec_via_jupyter_client ---


class TestLoadKernelspec:
    def test_returns_argv(self):
        # Mock get_kernel_spec to return an object with to_dict()
        mock_spec = type("S", (), {
            "to_dict": lambda self: {"argv": ["/home/jesse/.lean4-venv/bin/python3", "-m", "ipykernel_launcher"]},
            "resource_dir": "/home/jesse/.local/share/jupyter/kernels/python3-wsl",
        })()
        with patch("jupyter_client.kernelspec.get_kernel_spec", return_value=mock_spec):
            spec = _load_kernelspec_via_jupyter_client("python3-wsl")
        assert spec == {
            "argv": ["/home/jesse/.lean4-venv/bin/python3", "-m", "ipykernel_launcher"],
            "resource_dir": "/home/jesse/.local/share/jupyter/kernels/python3-wsl",
        }

    def test_returns_none_when_unregistered(self):
        with patch("jupyter_client.kernelspec.get_kernel_spec",
                   side_effect=KeyError("not found")):
            spec = _load_kernelspec_via_jupyter_client("missing-ks")
        assert spec is None

    def test_returns_none_when_argv_empty(self):
        mock_spec = type("S", (), {
            "to_dict": lambda self: {"argv": []},
            "resource_dir": "",
        })()
        with patch("jupyter_client.kernelspec.get_kernel_spec", return_value=mock_spec):
            spec = _load_kernelspec_via_jupyter_client("bad-ks")
        assert spec is None


# --- verify_one: integration of the helpers ---


def _write_nb(tmp_path, name="python3-wsl", argv0="/home/jesse/coursia-wsl/bin/python3"):
    """Helper: write a notebook declaring the given kernelspec + return its path."""
    nb = {"metadata": {"kernelspec": {"name": name}}}
    p = tmp_path / "test.ipynb"
    p.write_text(json.dumps(nb), encoding="utf-8")
    return p, name, argv0


def _mock_spec(argv0):
    mock = type("S", (), {
        "to_dict": lambda self: {"argv": [argv0, "-m", "ipykernel_launcher"]},
        "resource_dir": "",
    })()
    return mock


class TestVerifyOne:
    def test_matches_default(self, tmp_path):
        """Declared venv == default => OK."""
        nb, name, argv0 = _write_nb(tmp_path,
                                    argv0="/home/jesse/coursia-wsl/bin/python3")
        with patch("jupyter_client.kernelspec.get_kernel_spec",
                   return_value=_mock_spec(argv0)):
            v = verify_one(nb, default_venv="/home/jesse/coursia-wsl")
        assert v["verdict"] == "OK"
        assert v["matches_default_venv"] is True
        assert v["declared_venv"] == "/home/jesse/coursia-wsl"

    def test_divergent_venv(self, tmp_path):
        """Declared venv != default => DIVERGENT_VENV."""
        nb, name, argv0 = _write_nb(tmp_path,
                                    argv0="/home/jesse/.lean4-venv/bin/python3")
        with patch("jupyter_client.kernelspec.get_kernel_spec",
                   return_value=_mock_spec(argv0)):
            v = verify_one(nb, default_venv="/home/jesse/coursia-wsl")
        assert v["verdict"] == "DIVERGENT_VENV"
        assert v["matches_default_venv"] is False
        assert v["declared_venv"] == "/home/jesse/.lean4-venv"
        assert "lean4-venv" in v["message"]

    def test_system_python_ok(self, tmp_path):
        """Argv is /usr/bin/python3 (system) => OK, runtime uses active venv.

        The declared venv is unknown, so matches_default_venv must be None
        (not True) -- nothing proves the match (#15223).
        """
        nb, name, argv0 = _write_nb(tmp_path, argv0="/usr/bin/python3")
        with patch("jupyter_client.kernelspec.get_kernel_spec",
                   return_value=_mock_spec(argv0)):
            v = verify_one(nb)
        assert v["verdict"] == "OK"
        assert v["matches_default_venv"] is None
        assert v["declared_venv"] is None

    def test_bare_python_ok(self, tmp_path):
        """Argv is bare 'python' => OK (system, runtime decides)."""
        nb, name, argv0 = _write_nb(tmp_path, argv0="python")
        with patch("jupyter_client.kernelspec.get_kernel_spec",
                   return_value=_mock_spec(argv0)):
            v = verify_one(nb)
        assert v["verdict"] == "OK"
        assert v["declared_venv"] is None

    def test_unregistered_kernelspec(self, tmp_path):
        """Kernelspec name not in jupyter => KERNELSPEC_UNREGISTERED."""
        nb, name, _ = _write_nb(tmp_path)
        with patch("jupyter_client.kernelspec.get_kernel_spec",
                   side_effect=KeyError("not registered")):
            v = verify_one(nb)
        assert v["verdict"] == "KERNELSPEC_UNREGISTERED"
        assert "not registered" in v["message"].lower()

    def test_no_kernelspec(self, tmp_path):
        """Notebook has no metadata.kernelspec => NO_KERNELSPEC."""
        p = tmp_path / "test.ipynb"
        p.write_text(json.dumps({"cells": []}), encoding="utf-8")
        v = verify_one(p)
        assert v["verdict"] == "NO_KERNELSPEC"

    def test_empty_kernelspec_name(self, tmp_path):
        """kernelspec.name is empty => NO_KERNELSPEC."""
        nb = {"metadata": {"kernelspec": {"name": ""}}}
        p = tmp_path / "test.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        v = verify_one(p)
        assert v["verdict"] == "NO_KERNELSPEC"


# --- main() ---


class TestMain:
    def test_exit_0_all_ok(self, tmp_path, capsys):
        nb1, _, argv1 = _write_nb(tmp_path, name="ks1",
                                  argv0="/home/jesse/coursia-wsl/bin/python3")
        nb_path2 = tmp_path / "t2.ipynb"
        nb_path2.write_text(json.dumps({"metadata": {"kernelspec": {"name": "ks2"}}}),
                            encoding="utf-8")
        with patch("jupyter_client.kernelspec.get_kernel_spec",
                   return_value=_mock_spec(argv1)):
            rc = main([str(nb1), str(nb_path2),
                       "--default-venv", "/home/jesse/coursia-wsl"])
        assert rc == 0
        out = capsys.readouterr().out
        assert "Summary: 2 OK" in out

    def test_exit_1_divergent(self, tmp_path, capsys):
        nb, _, _ = _write_nb(tmp_path, argv0="/home/jesse/.lean4-venv/bin/python3")
        with patch("jupyter_client.kernelspec.get_kernel_spec",
                   return_value=_mock_spec("/home/jesse/.lean4-venv/bin/python3")):
            rc = main([str(nb), "--default-venv", "/home/jesse/coursia-wsl"])
        assert rc == 1
        out = capsys.readouterr().out
        assert "DIVERGENT" in out

    def test_exit_2_unregistered(self, tmp_path, capsys):
        nb, _, _ = _write_nb(tmp_path)
        with patch("jupyter_client.kernelspec.get_kernel_spec",
                   side_effect=KeyError("nope")):
            rc = main([str(nb), "--default-venv", "/home/jesse/coursia-wsl"])
        assert rc == 2
        out = capsys.readouterr().out
        assert "UNREG" in out

    def test_json_output(self, tmp_path, capsys):
        nb, _, argv = _write_nb(tmp_path, argv0="/home/jesse/coursia-wsl/bin/python3")
        with patch("jupyter_client.kernelspec.get_kernel_spec",
                   return_value=_mock_spec(argv)):
            rc = main([str(nb), "--json",
                       "--default-venv", "/home/jesse/coursia-wsl"])
        assert rc == 0
        out = capsys.readouterr().out
        parsed = json.loads(out)
        assert isinstance(parsed, list)
        assert len(parsed) == 1
        assert parsed[0]["verdict"] == "OK"

    def test_default_venv_override(self, tmp_path, capsys):
        """A notebook whose declared venv is /opt/x is OK if --default-venv /opt/x."""
        nb, _, _ = _write_nb(tmp_path, argv0="/opt/x/bin/python3")
        with patch("jupyter_client.kernelspec.get_kernel_spec",
                   return_value=_mock_spec("/opt/x/bin/python3")):
            rc = main([str(nb), "--default-venv", "/opt/x"])
        assert rc == 0
        out = capsys.readouterr().out
        assert "OK" in out
