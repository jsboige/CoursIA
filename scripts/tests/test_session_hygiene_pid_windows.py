"""Tests de la sonde Windows `_pid_windows` (session_hygiene) -- incident #27380.

Mesure fondatrice (19/11, myia-po-2023:CoursIA) : apres la MAJ vscode, l'ancien
claude.exe de la lane etait TERMINE (GetExitCodeProcess = 0) mais son objet
persistait (handle ouvert chez le processus hote de la mise a jour). Il
reussissait OpenProcess et GetProcessTimes, donc la sonde le declarait VIVANT :
ROUGE `session-double` permanent sur un cadavre, lane bloquee en « n'edite
rien » 6 h durant, alors que tasklist / Get-Process / Win32_Process le
donnaient absent a l'unanimite.

Ces tests pinnent (Windows uniquement -- la sonde est Windows-seule, la CI
Linux passe par `_pid_posix`) :

* controle positif : un processus vivant est vivant, avec heure de creation ;
* controle NEGATIF exact du cas reel : un enfant termine SANS wait() (le
  handle Popen maintient l'objet reference = zombie) est rendu MORT par le
  seul code de sortie, bien qu'OpenProcess reussisse encore sur son numero.
"""
from __future__ import annotations

import importlib.util
import os
import subprocess
import sys
import time
from pathlib import Path

import pytest

# Module plat importe via spec, comme test_session_hygiene.py (le nom
# "session_hygiene" peut deja etre enregistre par cette suite : on reprend).
if "session_hygiene" in sys.modules:
    session_hygiene = sys.modules["session_hygiene"]
else:
    _HERE = Path(__file__).resolve().parent
    _SCRIPT = _HERE.parent / "coordination" / "session_hygiene.py"
    _spec = importlib.util.spec_from_file_location("session_hygiene", _SCRIPT)
    session_hygiene = importlib.util.module_from_spec(_spec)
    sys.modules["session_hygiene"] = session_hygiene
    _spec.loader.exec_module(session_hygiene)

pytestmark = pytest.mark.skipif(
    os.name != "nt", reason="sonde _pid_windows : Windows uniquement")


@pytest.fixture()
def enfant_endormi():
    """Un enfant vivant, termine proprement dans le test, handle NON relache."""
    p = subprocess.Popen(
        [sys.executable, "-c", "import time; time.sleep(60)"],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    yield p
    if p.poll() is None:
        p.kill()
    p.wait()  # ne relache le handle zombie qu'apres le test, jamais avant


def test_pid_vivant_est_vivant(enfant_endormi):
    vivant, creation = session_hygiene._pid_windows(enfant_endormi.pid)
    assert vivant
    assert isinstance(creation, float) and creation > 0


def test_pid_zombie_reference_est_mort(enfant_endormi):
    """Cas reel #27380 : termine sans wait() -> handle ouvert -> objet zombie.

    OpenProcess reussit encore sur le numero ; seul le code de sortie tranche.
    """
    enfant_endormi.terminate()
    time.sleep(0.5)  # laisser la terminaison completer (exit code visible)
    vivant, creation = session_hygiene._pid_windows(enfant_endormi.pid)
    assert not vivant
    assert creation is None


def test_pid_absent_est_mort():
    """Un numero libre (jamais attribue recemment) : parametre invalide (87)."""
    vivant, creation = session_hygiene._pid_windows(0xFFFFFF)
    assert not vivant
    assert creation is None
