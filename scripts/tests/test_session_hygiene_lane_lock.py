"""Tests du verrou de lane (session_hygiene.check_lane_lock) -- incident du 14/11.

Mesure fondatrice : sur myia-po-2027:CoursIA, une seconde session de la meme
lane a pousse un commit sur la branche d'une PR pendant que la premiere y
travaillait ; `check_lane_claim.py` traite deux sessions d'une meme lane
comme une reprise legitime (#14323), il ne peut pas voir ce cas.

Ces tests pinnent :

* controle positif : un PID VIVANT different du sien -> ROUGE nomme, remede
  CronList/CronDelete dans la session qui porte le doublon, verrou NON repris ;
* controle NEGATIF : premiere session -> verrou pose, vert ; PID mort ->
  reprise silencieuse, vert (robustesse exigee) ; numero reutilise par un
  autre processus -> reprise, vert ;
* le verrou preservant les AUTRES lanes du depot ;
* le cablage main() : --lane pose le verrou, sans --lane rien n'est ecrit ;
* bout en bout : un vrai processus vivant dans le verrou -> ROUGE de main().
"""
from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

# cf. test_session_hygiene.py : subprocess git paralleles vs RLIMIT_NPROC.
os.environ.setdefault("GIT_OPTIONAL_LOCKS", "0")
pytestmark = [
    pytest.mark.skipif(
        os.environ.get("CI") == "true"
        and os.environ.get("RUNNER_OS") == "Linux"
        and os.environ.get("PYTEST_XDIST_WORKER") is not None,
        reason="RLIMIT_NPROC sous xdist WSL self-hosted (cf. #17496)",
    ),
]

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

LANE = "myia-po-2027:CoursIA"
VERROU = ".tmp/lane-session.json"


def _etat_par_pid(fronteau: dict):
    """Un faux `pid_etat` pilote par table : PID -> (vivant, creation epoch s)."""
    def etat(pid):
        return fronteau.get(pid, (False, None))
    return etat


def _poser_verrou(root: Path, lane: str, pid: int, debut_proc=1.0,
                  debut: str = "2026-11-14T20:00:00Z") -> None:
    path = root / VERROU
    path.parent.mkdir(parents=True, exist_ok=True)
    verrous = {}
    if path.exists():
        try:
            verrous = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            verrous = {}
    verrous[lane] = {"pid": pid, "debut": debut, "debut_proc": debut_proc,
                     "session": "autre", "machine": "test"}
    path.write_text(json.dumps(verrous), encoding="utf-8")


# --- controle NEGATIF : premiere session, verrou pose ------------------------


def test_premiere_session_pose_le_verrou(tmp_path):
    """Sans verrou : vert, et le fichier porte PID / debut UTC / session / machine."""
    checks = session_hygiene.check_lane_lock(
        tmp_path, LANE, pid=100, session_id="sess-1", maintenant=1000000.0,
        etat_pid=_etat_par_pid({}))
    assert len(checks) == 1 and checks[0].level == session_hygiene.GREEN
    entree = json.loads((tmp_path / VERROU).read_text(encoding="utf-8"))[LANE]
    assert entree["pid"] == 100 and entree["session"] == "sess-1"
    assert entree["debut"].endswith("Z"), "le debut doit etre un UTC explicite"
    assert entree["machine"], "la machine doit etre enregistree"


def test_meme_processus_reprend_son_verrou_sans_recrire(tmp_path):
    """Le meme PID repasse l'hygiene : vert, fichier inchange."""
    session_hygiene.check_lane_lock(tmp_path, LANE, pid=100, etat_pid=_etat_par_pid({}))
    avant = (tmp_path / VERROU).read_text(encoding="utf-8")
    checks = session_hygiene.check_lane_lock(tmp_path, LANE, pid=100,
                                             etat_pid=_etat_par_pid({}))
    assert checks[0].level == session_hygiene.GREEN
    assert "deja pose" in checks[0].detail
    assert (tmp_path / VERROU).read_text(encoding="utf-8") == avant


# --- controle positif : PID vivant different ---------------------------------


def test_pid_vivant_different_donne_un_rouge_nomme(tmp_path):
    """L'incident : un AUTRE processus vivant sous la meme lane -> ROUGE.

    Le verrou n'est PAS repris (le porteur vit) et le remede est celui de la
    regle de flotte : CronList puis CronDelete dans la session qui porte le
    doublon.
    """
    _poser_verrou(tmp_path, LANE, pid=200, debut_proc=1.0)
    checks = session_hygiene.check_lane_lock(
        tmp_path, LANE, pid=100, etat_pid=_etat_par_pid({200: (True, 1.0)}))
    assert checks[0].level == session_hygiene.RED
    assert checks[0].name == "session-double"
    assert "200" in checks[0].detail and "SECONDE session" in checks[0].detail
    assert "CronList" in checks[0].fix and "CronDelete" in checks[0].fix
    assert checks[0].data == {"lane": LANE, "autre_pid": 200}
    apres = json.loads((tmp_path / VERROU).read_text(encoding="utf-8"))[LANE]
    assert apres["pid"] == 200, "le verrou du porteur vivant ne se reprend pas"


# --- controle NEGATIF : PID mort, numero reutilise ---------------------------


def test_pid_mort_reprise_silencieuse(tmp_path):
    """Robustesse exigee : un PID mort ne fait pas de faux rouge."""
    _poser_verrou(tmp_path, LANE, pid=300, debut_proc=1.0)
    checks = session_hygiene.check_lane_lock(
        tmp_path, LANE, pid=100, etat_pid=_etat_par_pid({300: (False, None)}))
    assert checks[0].level == session_hygiene.GREEN
    assert "repris" in checks[0].detail and "mort" in checks[0].detail
    entree = json.loads((tmp_path / VERROU).read_text(encoding="utf-8"))[LANE]
    assert entree["pid"] == 100


def test_numero_reutilise_pas_un_doublon(tmp_path):
    """Sous Windows le numero est rendu a un AUTRE processus : l'heure de
    creation ne suit pas le numero -- le porteur est mort, reprise."""
    _poser_verrou(tmp_path, LANE, pid=400, debut_proc=1.0)
    checks = session_hygiene.check_lane_lock(
        tmp_path, LANE, pid=100, etat_pid=_etat_par_pid({400: (True, 99000.0)}))
    assert checks[0].level == session_hygiene.GREEN
    assert "reutilise" in checks[0].detail
    entree = json.loads((tmp_path / VERROU).read_text(encoding="utf-8"))[LANE]
    assert entree["pid"] == 100


def test_creation_inconnue_le_pid_vivant_reste_rouge(tmp_path):
    """Sans heure de creation (POSIX, ou sonde eloignee), la vivance seule tranche."""
    _poser_verrou(tmp_path, LANE, pid=500, debut_proc=None)
    checks = session_hygiene.check_lane_lock(
        tmp_path, LANE, pid=100, etat_pid=_etat_par_pid({500: (True, None)}))
    assert checks[0].level == session_hygiene.RED


# --- verrou illisible, autres lanes preservees --------------------------------


def test_verrou_illisible_remplace(tmp_path):
    (tmp_path / VERROU).parent.mkdir(parents=True, exist_ok=True)
    (tmp_path / VERROU).write_text("pas du tout json{", encoding="utf-8")
    checks = session_hygiene.check_lane_lock(tmp_path, LANE, pid=100,
                                             etat_pid=_etat_par_pid({}))
    assert checks[0].level == session_hygiene.GREEN
    assert "illisible" in checks[0].detail
    assert json.loads((tmp_path / VERROU).read_text(encoding="utf-8"))[LANE]["pid"] == 100


def test_les_autres_lanes_sont_preservees(tmp_path):
    """Une machine porte plusieurs lanes : poser SON verrou n'efface pas les autres."""
    autre_lane = "myia-po-2027:CoursIA-2"
    _poser_verrou(tmp_path, autre_lane, pid=700, debut_proc=1.0)
    session_hygiene.check_lane_lock(tmp_path, LANE, pid=100,
                                    etat_pid=_etat_par_pid({700: (True, 1.0)}))
    verrous = json.loads((tmp_path / VERROU).read_text(encoding="utf-8"))
    assert verrous[autre_lane]["pid"] == 700
    assert verrous[LANE]["pid"] == 100


# --- cablage main() -----------------------------------------------------------


def test_main_avec_lane_pose_le_verrou(tmp_path, monkeypatch, capsys):
    """--lane cable le check : il apparait dans le JSON et le fichier est ecrit."""
    monkeypatch.setattr(session_hygiene, "repo_root", lambda: tmp_path)
    monkeypatch.setattr(session_hygiene, "check_fetch", lambda root: [])
    rc = session_hygiene.main(["--json", "--lane", LANE, "--session-id", "s-main"])
    assert rc in (0, 1)  # d'autres checks peuvent rougir sur un depot factice
    donnees = json.loads(capsys.readouterr().out)
    noms = [c["name"] for c in donnees["checks"]]
    assert "session-double" in noms
    entree = json.loads((tmp_path / VERROU).read_text(encoding="utf-8"))[LANE]
    assert entree["session"] == "s-main"


def test_main_sans_lane_n_ecrit_aucun_verrou(tmp_path, monkeypatch, capsys):
    """Controle negatif du cablage : sans --lane, aucun fichier n'est ecrit."""
    monkeypatch.setattr(session_hygiene, "repo_root", lambda: tmp_path)
    monkeypatch.setattr(session_hygiene, "check_fetch", lambda root: [])
    session_hygiene.main(["--json"])
    capsys.readouterr()
    assert not (tmp_path / VERROU).exists()


def test_main_rougit_sur_un_vrai_processus_vivant(tmp_path, monkeypatch, capsys):
    """Bout en bout : un VRAI processus vivant dans le verrou -> ROUGE, sortie 1."""
    enfant = subprocess.Popen(
        [sys.executable, "-c", "import time; time.sleep(60)"],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    try:
        _poser_verrou(tmp_path, LANE, pid=enfant.pid, debut_proc=None)
        monkeypatch.setattr(session_hygiene, "repo_root", lambda: tmp_path)
        monkeypatch.setattr(session_hygiene, "check_fetch", lambda root: [])
        rc = session_hygiene.main(["--json", "--lane", LANE])
        donnees = json.loads(capsys.readouterr().out)
        verrou = next(c for c in donnees["checks"] if c["name"] == "session-double")
        assert verrou["level"] == "RED" and str(enfant.pid) in verrou["detail"]
        assert rc == 1, "un ROUGE de session double doit rendre la sortie 1"
        # le verrou du porteur vivant n'a pas ete repris
        apres = json.loads((tmp_path / VERROU).read_text(encoding="utf-8"))[LANE]
        assert apres["pid"] == enfant.pid
    finally:
        enfant.terminate()
        enfant.wait(timeout=30)
