"""
Tests pour le helper claude_cli.py : timeout strict qui tue l'ARBRE de
processus. Cf. issue #20879 (timeout ne tuant que le direct child sous
Windows, ce qui figeait le noyau Jupyter au lieu de rendre l'erreur).

Cible : 3 controles.
1. Controle positif : un script qui dort > timeout leve _run_with_timeout,
   le helper rend ('', '...Timeout...', -1) en `timeout + quelques secondes`,
   et il n'y a pas de processus orphelin.
2. Controle negatif : un script qui rend immediatement -> retour (stdout, '', 0).
3. Controle de regression : _kill_process_tree est idempotent (peut etre
   appele deux fois sans crash).

Ces tests ne touchent pas Claude CLI reelle (qui n'est pas installee dans
cet environnement CI). Ils utilisent un script de remplacement (shim) que
_run_with_timeout peut viser directement.
"""
import os
import sys
import time
import shutil
import tempfile
import subprocess
import platform

import pytest

# On importe directement le module pour eviter de depender du kernel Jupyter
sys.path.insert(0, os.path.join(
    os.path.dirname(__file__),
    "..", "..",
    "MyIA.AI.Notebooks", "GenAI", "Vibe-Coding", "Claude-Code", "notebooks"
))
from helpers import claude_cli  # noqa: E402


# Shim script : dort N secondes puis sort 0 (stdout="ok", stderr="")
# Utilise pour mimer un binaire `claude` qui prend du temps.
@pytest.fixture
def slow_shim(tmp_path):
    """Cree un shim executable qui dort puis rend. Cross-platform.

    Windows : ping localhost en boucle (30+ fois avec -w 1000) — robuste
    quel que soit le shell hote, dort au moins 30s, eteint par l'arbre.
    POSIX : `sleep 30` classique.
    """
    if platform.system() == "Windows":
        shim = tmp_path / "slow.cmd"
        # ping -n 35 : 35 envois espaces de 1s = ~34s, assez pour timeout=2 + marge
        shim.write_text("@echo off\r\nping -n 35 127.0.0.1 > nul\r\necho ok\r\n", encoding="ascii")
    else:
        shim = tmp_path / "slow.sh"
        shim.write_text("#!/bin/sh\nsleep 30\necho ok\n", encoding="ascii")
        os.chmod(shim, 0o755)
    return str(shim)


@pytest.fixture
def fast_shim(tmp_path):
    """Cree un shim executable qui sort immediatement avec stdout='ok'."""
    if platform.system() == "Windows":
        shim = tmp_path / "fast.cmd"
        shim.write_text("@echo off\r\necho ok\r\n", encoding="ascii")
    else:
        shim = tmp_path / "fast.sh"
        shim.write_text("#!/bin/sh\necho ok\n", encoding="ascii")
        os.chmod(shim, 0o755)
    return str(shim)


def test_run_with_timeout_fast_returns_stdout(fast_shim):
    """Controle negatif : un binaire rapide rend (stdout, '', 0)."""
    t0 = time.time()
    stdout, stderr, code = claude_cli._run_with_timeout(
        [fast_shim], timeout=10
    )
    elapsed = time.time() - t0
    assert code == 0, f"expected returncode=0, got {code}, stderr={stderr!r}"
    assert "ok" in stdout, f"expected 'ok' in stdout, got {stdout!r}"
    assert elapsed < 5, f"fast shim should return quickly, took {elapsed:.1f}s"


def test_run_with_timeout_slow_kills_tree(slow_shim):
    """Controle positif : un binaire lent (> timeout) est tue, helper rend -1.

    Le helper doit rendre en `timeout + quelques secondes` (pas attendre la
    fin du binaire qui dort 30s). Le test est borne a 10s : timeout=2 + 8s
    de marge pour le kill d'arbre cross-platform.
    """
    t0 = time.time()
    stdout, stderr, code = claude_cli._run_with_timeout(
        [slow_shim], timeout=2
    )
    elapsed = time.time() - t0
    assert code == -1, f"expected returncode=-1, got {code}, stderr={stderr!r}"
    assert "Timeout" in stderr, f"expected 'Timeout' in stderr, got {stderr!r}"
    # Le helper doit rendre bien avant les 30s du shim (sinon le test timeout)
    assert elapsed < 10, (
        f"helper took {elapsed:.1f}s, expected < 10s (timeout=2 + marge kill) "
        f"-- l'arbre n'a pas ete tue correctement (cf. issue #20879)"
    )


def test_kill_process_tree_idempotent(slow_shim):
    """Controle de regression : _kill_process_tree est idempotent."""
    # Lance le shim
    if platform.system() == "Windows":
        proc = subprocess.Popen(
            [slow_shim],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            creationflags=claude_cli._CREATE_NEW_PROCESS_GROUP,
        )
    else:
        proc = subprocess.Popen(
            [slow_shim],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            start_new_session=True,
        )
    # Premier kill : doit fonctionner
    claude_cli._kill_process_tree(proc)
    # Second kill : ne doit pas crash (poll() retourne un code non-None)
    claude_cli._kill_process_tree(proc)
    # Le process doit etre termine
    assert proc.poll() is not None, "process should be terminated after kill"


def test_run_with_timeout_no_orphan(slow_shim):
    """Controle d'absence d'orphelin : apres timeout, ps ne doit plus voir
    le shim dans la liste des processus actifs.

    Cross-platform : utilise `tasklist` sous Windows, `ps` sous POSIX.
    Note : ce test peut etre un peu flaky sur les VM partagees (latence
    apparition/disparition dans la table des process). On retry 3 fois.
    """
    t0 = time.time()
    stdout, stderr, code = claude_cli._run_with_timeout(
        [slow_shim], timeout=2
    )
    elapsed = time.time() - t0
    assert code == -1

    # Le shim est mort, mais on verifie qu'aucun descendant ne traine
    # (en l'occurrence il n'y en a pas, donc on s'attend a 0 occurrences)
    shim_basename = os.path.basename(slow_shim)
    for _ in range(3):
        if platform.system() == "Windows":
            out = subprocess.run(
                ["tasklist", "/FI", f"IMAGENAME eq {shim_basename}"],
                capture_output=True, text=True, timeout=5
            ).stdout
        else:
            out = subprocess.run(
                ["ps", "-A", "-o", "comm"],
                capture_output=True, text=True, timeout=5
            ).stdout
        if shim_basename.lower() not in out.lower():
            return  # OK
        time.sleep(0.5)
    # Si on arrive ici, le shim est toujours present -- orphelin probable
    pytest.fail(
        f"orphan shim {shim_basename} still present after timeout "
        f"(elapsed={elapsed:.1f}s, cf. issue #20879)"
    )
