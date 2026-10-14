"""Tests de `run_guarded` -- les deux plafonds et l'anti-orphelin.

L'organe existe pour l'incident du 2026-10-05 (po-2023) : un run de mesure de
6 h a retenu 38,6 Go (machine a 99,3 %, 0,43 Go libres), **orphelin** (session
parente morte) et **sans garde** -- seule la chance l'a fini. Chaque test cidessous
ferme une des portes ouvertes ce jour-la :

  1. plafond processus franchi -> arbre tue, code 3 (et non « il s'est fini seul ») ;
  2. plancher machine non tenable des le demarrage -> refus AVANT de lancer ;
  3. commande normale -> code de sortie de l'enfant transmis, rapport ecrit ;
  4. le lanceur meurt -> l'enfant meurt (Job Object KILL_ON_JOB_CLOSE, Windows).

Les tests 1 et 2 sont volontairement des **controles negatifs** : ils verifient
que la garde refuse, pas seulement qu'elle laisse passer.
"""
import importlib.util
import os
import subprocess
import sys
import time
from pathlib import Path

import pytest

_SPEC = importlib.util.spec_from_file_location(
    "run_guarded",
    Path(__file__).resolve().parents[1] / "run_guarded.py",
)
mod = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(mod)

PY = sys.executable


def _run(args, timeout=90):
    """Lance le garde in-process et rend (rc, stdout+stderr)."""
    import io
    from contextlib import redirect_stdout, redirect_stderr

    buf = io.StringIO()
    with redirect_stdout(buf), redirect_stderr(buf):
        rc = mod.main(args)
    return rc, buf.getvalue()


def test_plafond_processus_tue_larbre_et_rend_3(tmp_path):
    """Un enfant qui depasse --limit-gib est tue : rc 3, et il n'est plus la."""
    child = f"import time; x = bytearray(400 * 2**20); time.sleep(120)"
    log = tmp_path / "run.log"
    rc, out = _run(["--limit-gib", "0.2", "--reserve-gib", "0.5", "--poll", "0.2",
                    "--report-every", "0", "--log", str(log), "--",
                    PY, "-c", child])
    assert rc == mod.RC_LIMIT, out
    assert "plafond processus franchi" in log.read_text(encoding="utf-8")
    assert "bilan : pic RSS" in log.read_text(encoding="utf-8")


def test_plancher_machine_refuse_avant_de_lancer(tmp_path):
    """RAM libre < plancher des le demarrage : rc 5, et la commande n'a pas tourne."""
    marker = tmp_path / "lance.txt"
    child = f"from pathlib import Path; Path(r'{marker}').write_text('vu')"
    rc, out = _run(["--limit-gib", "1", "--reserve-gib", "999999", "--",
                    PY, "-c", child])
    assert rc == mod.RC_REFUSED, out
    assert "REFUS" in out
    assert not marker.exists(), "la commande a tourne malgre le refus de demarrage"


def test_code_de_sortie_de_lenfant_est_transmis(tmp_path):
    """Sous les deux plafonds, le rc de l'enfant devient le rc du garde."""
    log = tmp_path / "run.log"
    rc, out = _run(["--limit-gib", "2", "--reserve-gib", "0.5", "--poll", "0.2",
                    "--report-every", "0", "--log", str(log), "--",
                    PY, "-c", "import sys; sys.exit(7)"])
    assert rc == 7, out
    texte = log.read_text(encoding="utf-8")
    assert "termine rc=7" in texte
    assert "sous les deux plafonds" in texte


def test_commande_absente_refusee():
    """Sans `-- <cmd>`, l'organe refuse au lieu de lancer quelque chose au hasard."""
    with pytest.raises(SystemExit):
        _run(["--limit-gib", "1", "--"])


@pytest.mark.skipif(os.name != "nt", reason="Job Object = mecanisme Windows")
def test_lenfant_meurt_avec_le_lanceur(tmp_path):
    """Le controle decisif : tuer le lanceur tue l'enfant (plus d'orphelin).

    C'est la porte exacte par laquelle le run du 2026-10-05 est passe : son
    parent etait mort et personne ne surveillait sa fin. Ici le lanceur est tue
    -- brutalement, comme un crash de session -- et l'enfant doit disparaitre
    avec lui, sans qu'aucun code de l'enfant ne coopere.
    """
    psutil = pytest.importorskip("psutil")
    log = tmp_path / "run.log"
    proc = subprocess.Popen(
        [PY, str(Path(__file__).resolve().parents[1] / "run_guarded.py"),
         "--limit-gib", "4", "--reserve-gib", "0.5", "--poll", "0.2",
         "--report-every", "0", "--log", str(log), "--",
         PY, "-c", "import time; time.sleep(300)"],
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        text=True, encoding="utf-8", errors="replace")

    try:
        pid_enfant = None
        deadline = time.time() + 30
        while time.time() < deadline and pid_enfant is None:
            time.sleep(0.3)
            if proc.poll() is not None:
                break
            if log.exists():
                for ligne in log.read_text(encoding="utf-8").splitlines():
                    if "anti-orphelin : pid" in ligne:
                        pid_enfant = int(ligne.split("pid")[1].split()[0])
        assert pid_enfant, f"pid enfant non journalise : {log.read_text() if log.exists() else ''}"
        assert psutil.pid_exists(pid_enfant)

        proc.kill()          # le lanceur meurt sans menagement
        proc.wait(timeout=30)

        fin = time.time() + 15
        while time.time() < fin and psutil.pid_exists(pid_enfant):
            time.sleep(0.3)
        assert not psutil.pid_exists(pid_enfant), (
            "l'enfant a survecu a son lanceur : l'anti-orphelin n'est pas pose")
    finally:
        if proc.poll() is None:
            proc.kill()


@pytest.mark.skipif(os.name != "nt", reason="Job Object = mecanisme Windows")
def test_sans_job_object_lenfant_survit():
    """Faux negatif du test precedent : sans Job Object, l'orphelin survit.

    Sans ce controle, `test_lenfant_meurt_avec_le_lanceur` passerait aussi si la
    plateforme tuait d'elle-meme les enfants a la mort du parent -- il ne
    mesurerait alors rien. Ici un parent Python ordinaire (aucun Job Object)
    lance un enfant ; on tue le parent ; l'enfant doit **survivre**. C'est la
    porte par laquelle le run du 2026-10-05 est passe : parent mort, enfant
    vivant, personne pour le surveiller. Si ce test venait a echouer un jour,
    c'est que la plateforme a change et que le Job Object du lanceur n'est plus
    ce qui protege.
    """
    psutil = pytest.importorskip("psutil")
    enfant = "import time; time.sleep(300)"
    parent = subprocess.Popen(
        [PY, "-c", "import subprocess, sys, time; "
                   f"subprocess.Popen([sys.executable, '-c', {enfant!r}]); "
                   "time.sleep(300)"])
    pid = None
    try:
        time.sleep(2.0)
        petits = psutil.Process(parent.pid).children(recursive=True)
        assert petits, "l'enfant de controle n'a pas demarre"
        pid = petits[0].pid
        assert psutil.pid_exists(pid)

        parent.kill()
        parent.wait(timeout=30)
        time.sleep(2.5)

        assert psutil.pid_exists(pid), (
            "l'enfant est mort avec un parent SANS Job Object : la plateforme "
            "tue d'elle-meme les enfants, le test du lanceur ne mesure plus rien")
    finally:
        if parent.poll() is None:
            parent.kill()
        if pid is not None:
            try:
                psutil.Process(pid).kill()
            except Exception:
                pass
