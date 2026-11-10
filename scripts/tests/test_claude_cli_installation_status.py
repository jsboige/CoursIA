"""Temoins a processus simules pour installation_status()/verify_installation().

Aucun binaire reel n'est invoque : shutil.which est mocke, et le helper
bas-niveau `_run_with_timeout` (subprocess.Popen + communicate avec
timeout strict) est mocke a la frontiere d'unite. Reproduit les six cas
de #15281 -- le diagnostic doit rendre son verdict sur ses trois chemins
d'echec, jamais lever NameError (le defaut historique : f-string
interpolait resolved_path au lieu de la variable locale resolved).

Adaptation post-#20891 : la PR remplace `subprocess.run` par
`subprocess.Popen` (cf. issue #20879 -- l'arbre Windows cmd.exe -> shim
-> node ne se tuait pas a l'expiration, ce qui figeait le noyau).
Les anciens temoins mockaient `subprocess.run`, qui n'est plus appele
par `installation_status()`. On mocke maintenant a la **frontiere
d'unite** (`claude_cli._run_with_timeout`), en conservant les memes
trois chemins d'echec et leur controle negatif.
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


def _ok_version(*args, **kwargs):
    """Mock de _run_with_timeout : succes, version 1.0.0."""
    return "1.0.0", "", 0


def _rc1(*args, **kwargs):
    """Mock de _run_with_timeout : code retour 1, stderr explicite."""
    return "", "boom", 1


def _timeout(*args, **kwargs):
    """Mock de _run_with_timeout : expire, code -1, stderr Timeout."""
    return "", "Erreur: Timeout apres 15 secondes (arbre tue)", -1


def test_absent_introuvable():
    with mock.patch("shutil.which", return_value=None):
        status = claude_cli.installation_status()
    assert status["state"] == "introuvable"


def test_version_ok_executable():
    with mock.patch("shutil.which", return_value=FAKE_PATH), mock.patch.object(
        claude_cli, "_run_with_timeout", side_effect=_ok_version
    ):
        status = claude_cli.installation_status()
    assert status["state"] == "executable"
    assert status["resolved_path"] == FAKE_PATH


def test_returncode_1_non_executable_avec_chemin_et_code():
    with mock.patch("shutil.which", return_value=FAKE_PATH), mock.patch.object(
        claude_cli, "_run_with_timeout", side_effect=_rc1
    ):
        status = claude_cli.installation_status()
    assert status["state"] == "non-executable"
    assert FAKE_PATH in status["message"]
    assert "code 1" in status["message"]
    assert status["resolved_path"] == FAKE_PATH


@pytest.mark.parametrize(
    "exc",
    [
        # TimeoutExpired : _run_with_timeout ne leve PAS l'exception, il rend
        # (-1, "Timeout apres ...", "arbre tue"). On verifie la voie negative
        # par le mock _timeout ci-dessus dans test_timeout_rendu_non_executable.
        OSError("acces refuse"),
        FileNotFoundError("shim introuvable"),
    ],
)
def test_exceptions_chemins_echec_non_executable(exc):
    """Popen leve OSError / FileNotFoundError -> chemin d'echec capte."""
    with mock.patch("shutil.which", return_value=FAKE_PATH), mock.patch.object(
        claude_cli, "_run_with_timeout", side_effect=exc
    ):
        status = claude_cli.installation_status()
    assert status["state"] == "non-executable"
    assert FAKE_PATH in status["message"]
    assert status["resolved_path"] == FAKE_PATH


def test_timeout_rendu_non_executable():
    """_run_with_timeout rend (-1, 'Timeout ...', stderr) -> non-executable.

    Le helper ne leve pas TimeoutExpired : il capture l'expiration, tue
    l'arbre, vide les tubes, puis rend le triplet. Le diagnostic doit
    interpreter returncode=-1 et stderr 'Timeout' comme non-executable.
    """
    with mock.patch("shutil.which", return_value=FAKE_PATH), mock.patch.object(
        claude_cli, "_run_with_timeout", side_effect=_timeout
    ):
        status = claude_cli.installation_status()
    assert status["state"] == "non-executable"
    assert FAKE_PATH in status["message"]
    assert "code -1" in status["message"]
    assert status["resolved_path"] == FAKE_PATH


def test_verify_installation_false_quand_non_executable():
    with mock.patch("shutil.which", return_value=FAKE_PATH), mock.patch.object(
        claude_cli, "_run_with_timeout", side_effect=_rc1
    ):
        assert claude_cli.verify_installation() is False


def test_verify_installation_false_quand_introuvable():
    with mock.patch("shutil.which", return_value=None):
        assert claude_cli.verify_installation() is False
