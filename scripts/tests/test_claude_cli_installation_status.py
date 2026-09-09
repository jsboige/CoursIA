"""Temoins a processus simules pour installation_status()/verify_installation().

Aucun binaire reel n'est invoque : shutil.which et subprocess.run sont
remplaces par des mocks. Reproduit les six cas de #15281 -- le diagnostic
doit rendre son verdict sur ses trois chemins d'echec, jamais lever
NameError (le defaut historique : f-string interpolait resolved_path au
lieu de la variable locale resolved).
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path
from unittest import mock

import pytest

_HELPERS = (
    Path(__file__).resolve().parents[2]
    / "MyIA.AI.Notebooks"
    / "GenAI"
    / "Vibe-Coding"
    / "Claude-Code"
    / "notebooks"
    / "helpers"
)
sys.path.insert(0, str(_HELPERS))

import claude_cli  # noqa: E402

FAKE_PATH = "C:/fake/bin/claude.CMD"


def _run_rc1(*args, **kwargs):
    return subprocess.CompletedProcess(args=[args[0]], returncode=1, stdout="", stderr="boom")


def test_absent_introuvable():
    with mock.patch("shutil.which", return_value=None):
        status = claude_cli.installation_status()
    assert status["state"] == "introuvable"


def test_version_ok_executable():
    with mock.patch("shutil.which", return_value=FAKE_PATH), mock.patch(
        "subprocess.run", return_value=subprocess.CompletedProcess(
            args=["claude", "--version"], returncode=0, stdout="1.0.0", stderr=""
        )
    ):
        status = claude_cli.installation_status()
    assert status["state"] == "executable"
    assert status["resolved_path"] == FAKE_PATH


def test_returncode_1_non_executable_avec_chemin_et_code():
    with mock.patch("shutil.which", return_value=FAKE_PATH), mock.patch(
        "subprocess.run", side_effect=_run_rc1
    ):
        status = claude_cli.installation_status()
    assert status["state"] == "non-executable"
    assert FAKE_PATH in status["message"]
    assert "code 1" in status["message"]
    assert status["resolved_path"] == FAKE_PATH


@pytest.mark.parametrize(
    "exc",
    [
        subprocess.TimeoutExpired(cmd=["claude", "--version"], timeout=15),
        OSError("acces refuse"),
        FileNotFoundError("shim introuvable"),
    ],
)
def test_exceptions_chemins_echec_non_executable(exc):
    with mock.patch("shutil.which", return_value=FAKE_PATH), mock.patch(
        "subprocess.run", side_effect=exc
    ):
        status = claude_cli.installation_status()
    assert status["state"] == "non-executable"
    assert FAKE_PATH in status["message"]
    assert status["resolved_path"] == FAKE_PATH


def test_verify_installation_false_quand_non_executable():
    with mock.patch("shutil.which", return_value=FAKE_PATH), mock.patch(
        "subprocess.run", side_effect=_run_rc1
    ):
        assert claude_cli.verify_installation() is False


def test_verify_installation_false_quand_introuvable():
    with mock.patch("shutil.which", return_value=None):
        assert claude_cli.verify_installation() is False
