"""Tests du lanceur plafonne ``scripts/ci/run_guarded.py`` (issue #21661).

Ce que ces tests doivent prouver, mecanisme par mecanisme :

* le **plafond dur de memoire** du Job Object arrete bien l'entrainement quand
  l'allocation depasse le plafond, et l'arret vient du **noyau** (MemoryError
  chez l'enfant) -- pas d'une heurique du lanceur ;
* le **controle negatif** : sans Job Object (``--no-job``), la meme allocation
  passe. Sans ce contre-tour, le test positif ne prouve rien (il pourrait
  passer pour une raison étrangère au plafond) ;
* la **garde de charge de commit** refuse un demarrage au-dessus du seuil, et
  refuse **aussi** quand la mesure est illisible (fail-CLOSED) ;
* le **verrou N=1** refuse un second lancement concurrent ;
* le **fichier de PID** est ecrit ;
* le lanceur de production porte bien le **defaut de 48 Go** (l'engagement
  pris aupres de la lane Maintenance d'ai-01).

Ces tests ne s'executent que sur Windows : le Job Object est une API
Windows. Hors Windows, ils sont ignores (le lanceur y mesure et tue, mais ne
plafonne pas l'allocation).
"""
import importlib.util
import os
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
GUARDED = REPO_ROOT / "scripts" / "ci" / "run_guarded.py"
LAUNCHER = (REPO_ROOT / "MyIA.AI.Notebooks" / "QuantConnect" / "ML-Training-Pipeline"
            / "scripts" / "launchers" / "launch_capped.ps1")

pytestmark = pytest.mark.skipif(os.name != "nt", reason="Job Object : API Windows")

# Enfant qui alloue plus que le plafond. Il alloue par blocs pour que
# l'echec d'allocation soit net (MemoryError) et non un crash du process.
ALLOC_CHILD = (
    "import sys\n"
    "blocks = []\n"
    "try:\n"
    "    for _ in range(64):\n"
    "        blocks.append(bytearray(16 * 1024 * 1024))\n"
    "except MemoryError:\n"
    "    print('MEMORYERROR', flush=True)\n"
    "    sys.exit(1)\n"
    "print('ALLOC_OK', flush=True)\n"
)

TRIVIAL_CHILD = "print('TRIVIAL_OK', flush=True)\n"


def _load_guarded():
    spec = importlib.util.spec_from_file_location("run_guarded_mod", GUARDED)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


@pytest.fixture(scope="module")
def guarded():
    return _load_guarded()


def _run(guarded, argv, tmp_path, extra=()):
    """Lance le lanceur et rend ``(rc, stdout_console, journal)``."""
    log = tmp_path / "run.log"
    cmd = [sys.executable, str(GUARDED), "--log", str(log), *extra, "--", *argv]
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=300,
                          encoding="utf-8", errors="replace")
    journal = log.read_text(encoding="utf-8") if log.exists() else ""
    return proc.returncode, proc.stdout, journal


def test_plafond_job_arrete_l_allocation(guarded, tmp_path):
    """Le plafond du Job Object fait ECHOUE l'allocation chez l'enfant.

    Le plafond RSS du lanceur (``--limit-gib``) est volontairement laisse
    haut : l'arret observe doit venir du noyau (rc de l'enfant), pas de la
    garde de RSS (rc 3).
    """
    rc, out, journal = _run(
        guarded,
        [sys.executable, "-c", ALLOC_CHILD],
        tmp_path,
        extra=["--limit-gib", "8", "--reserve-gib", "1",
               "--job-memory-limit-gib", "0.25"],
    )
    # La sortie de l'enfant est redirigee vers le journal (--log), pas vers la
    # console du lanceur : c'est la que se lit la preuve de l'echec.
    assert "MEMORYERROR" in journal, f"l'enfant aurait du echouer d'allocation :\n{out}\n{journal}"
    assert rc == 1, f"rc {rc} attendu (MemoryError de l'enfant), journal :\n{journal}"
    assert "plafond job" in journal, journal


def test_controle_negatif_sans_job_object_l_allocation_passe(guarded, tmp_path):
    """CONTROLE NEGATIF : sans Job Object, la meme allocation reussit.

    C'est ce test qui prouve que l'arret du test precedent vient bien du
    plafond et pas d'une coincidence de l'environnement.
    """
    rc, out, journal = _run(
        guarded,
        [sys.executable, "-c", ALLOC_CHILD],
        tmp_path,
        extra=["--limit-gib", "8", "--reserve-gib", "1", "--no-job"],
    )
    assert "ALLOC_OK" in journal, f"l'allocation aurait du reussir sans plafond :\n{out}\n{journal}"
    assert rc == 0, f"rc {rc} attendu (0) sans plafond, journal :\n{journal}"


def test_garde_de_charge_de_commit_refuse_au_dessus_du_seuil(guarded, tmp_path):
    """Un seuil de 1 % est franchi par toute machine vivante : refus garanti."""
    rc, out, journal = _run(
        guarded,
        [sys.executable, "-c", TRIVIAL_CHILD],
        tmp_path,
        extra=["--limit-gib", "8", "--reserve-gib", "1", "--max-commit-charge-pct", "1"],
    )
    assert rc == 5, f"rc {rc} attendu (5 = refus), journal :\n{journal}"
    assert "charge de commit" in journal, journal
    assert "TRIVIAL_OK" not in journal, "rien ne doit avoir ete lance"


def test_garde_de_charge_de_commit_illisible_refuse(guarded, tmp_path, monkeypatch):
    """Fail-CLOSED : une mesure ILLISIBLE refuse aussi le demarrage."""
    monkeypatch.setattr(guarded, "_commit_charge_pct", lambda: None)
    log = tmp_path / "illisible.log"
    rc = guarded.main([
        "--limit-gib", "8", "--reserve-gib", "1",
        "--max-commit-charge-pct", "50",
        "--log", str(log),
        "--", sys.executable, "-c", TRIVIAL_CHILD,
    ])
    assert rc == 5, f"rc {rc} attendu (5 = refus fail-CLOSED)"
    journal = log.read_text(encoding="utf-8")
    assert "ILLISIBLE" in journal, journal


def test_verrou_n1_refuse_un_second_lancement(guarded, tmp_path):
    """Un verrou deja pris refuse le second lancement (N = 1)."""
    lock = tmp_path / "train.lock"
    holder = guarded._acquire_exclusive_lock(str(lock))
    assert holder is not None, "verrou impossible a prendre sur un fichier libre"
    try:
        rc, out, journal = _run(
            guarded,
            [sys.executable, "-c", TRIVIAL_CHILD],
            tmp_path,
            extra=["--limit-gib", "8", "--reserve-gib", "1",
                   "--exclusive-lock", str(lock)],
        )
        assert rc == 5, f"rc {rc} attendu (5 = refus), journal :\n{journal}"
        assert "verrou exclusif" in journal, journal
        assert "TRIVIAL_OK" not in out, "rien ne doit avoir ete lance"
    finally:
        holder.close()


def test_fichier_de_pid_ecrit(guarded, tmp_path):
    """Le PID du processus lance est ecrit dans le fichier demande."""
    pidfile = tmp_path / "pid.txt"
    rc, out, journal = _run(
        guarded,
        [sys.executable, "-c", TRIVIAL_CHILD],
        tmp_path,
        extra=["--limit-gib", "8", "--reserve-gib", "1", "--pid-file", str(pidfile)],
    )
    assert rc == 0, journal
    assert pidfile.exists(), "fichier de PID absent"
    pid = int(pidfile.read_text(encoding="utf-8").strip())
    assert pid > 0


def test_defaut_de_production_48_go():
    """Le lanceur de production porte 48 Go et 85 % (engagement Maintenance)."""
    texte = LAUNCHER.read_text(encoding="utf-8")
    assert "[double]$MemoryCapGiB = 48" in texte, "defaut de memoire absent du lanceur"
    assert "[int]$MaxCommitChargePct = 85" in texte, "defaut de charge de commit absent"
    assert "--job-memory-limit-gib" in texte, "le lanceur ne pose pas de plafond de job"
    assert "--exclusive-lock" in texte, "le lanceur ne pose pas de verrou N=1"
    assert "--max-commit-charge-pct" in texte, "le lanceur ne pose pas de garde d'admission"
