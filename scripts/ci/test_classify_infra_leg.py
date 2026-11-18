"""Tests de scripts/ci/classify_infra_leg.py (#21745).

Chaque cause est verifiee par un CONTROLE POSITIF (la forme mesuree est
reconnue) ET par son CONTROLE NEGATIF (une panne de contenu ordinaire ne
doit pas etre classee infra -- un faux positif ferait ignorer une vraie
regression).
"""

import pathlib
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
SCRIPT = HERE / "classify_infra_leg.py"

sys.path.insert(0, str(HERE))
from classify_infra_leg import classify  # noqa: E402


def test_externals_manquant():
    log = """2026-10-20T12:02:19.6075076Z ##[error]An error occurred trying to start process
'/opt/runner/externals/node24/bin/node' with working directory '/home/runner/_work/CoursIA/CoursIA'.
No such file or directory
"""
    verdict = classify(log)
    assert verdict["is_infra"] is True
    assert verdict["cause"] == "INFRA_EXTERNALS_MISSING"


def test_marqueur_explicite_du_crochet():
    log = "job-start-disarm: INFRA_EXTERNALS_MISSING externals/node24/bin/node absent\n"
    assert classify(log)["cause"] == "INFRA_EXTERNALS_MISSING"


def test_ref_dangling():
    log = "fatal: Could not read 8658ba98b8a9dac1dd45666d\nfatal: Could not read b8a9dac1\n"
    verdict = classify(log)
    assert verdict["is_infra"] is True
    assert verdict["cause"] == "INFRA_DANGLING_REF"


def test_bad_object_ref():
    log = "error: fatal: bad object refs/remotes/origin/chore/11840-iit-zero-pad\n"
    assert classify(log)["cause"] == "INFRA_DANGLING_REF"


def test_cache_repair():
    log = "work_cache: repack ECHEC dans /home/runner/_work/X/X (24 packs, echec consecutif 3/3)\n"
    assert classify(log)["cause"] == "INFRA_CACHE_REPAIR"


def test_timeout_declare():
    log = (
        "FAIL -- checks that hit their declared timeout-minutes: "
        "Validate Quarto build (PR) (cancelled, 1h00m, declared timeout-minutes: 60)\n"
    )
    assert classify(log)["cause"] == "INFRA_TIMEOUT"


def test_runner_perdu():
    log = "The self-hosted runner lost communication with the server.\n"
    assert classify(log)["cause"] == "INFRA_RUNNER_LOST"


def test_controle_negatif_echec_de_contenu():
    log = """Traceback (most recent call last):
  File "cell.py", line 12, in <module>
AssertionError: expected 3, got 4
FAILED tests/test_data.py::test_parse - assert 0 == 1
"""
    verdict = classify(log)
    assert verdict["is_infra"] is False
    assert verdict["cause"] is None


def test_controle_negatif_mot_generique_error():
    """« error » seul ne classe rien : les motifs sont ancres, pas generiques."""
    assert classify("Error: something failed. build error.\n")["is_infra"] is False


def test_cli_exit_codes():
    ok = subprocess.run(
        [sys.executable, str(SCRIPT)],
        input="fatal: Could not read deadbeef\n",
        capture_output=True,
        text=True,
    )
    assert ok.returncode == 0, ok.stdout + ok.stderr
    assert "INFRA_DANGLING_REF" in ok.stdout

    ko = subprocess.run(
        [sys.executable, str(SCRIPT)],
        input="all tests passed\n",
        capture_output=True,
        text=True,
    )
    assert ko.returncode == 1
