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

Depuis la review 5908186749 (#26634) le verrou porte le **processus de
session du harnais** (ancetre `claude`/`node`), jamais `os.getpid()` du script :
le cas reel -- deux executions du script, PID de script differents et morts,
sous deux ancetres de session vivants ou sous le meme -- est pinne ci-dessous.
Les deux tests de cablage de `main()` injectent l'ancetre (`trouver_ancetre_session`)
la ou ils s'appuyaient auparavant sur `os.getpid()` comme porteur.
"""
from __future__ import annotations

import ctypes
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


@pytest.mark.skipif(os.name != "nt", reason="semantique des handles de processus Windows")
def test_pid_windows_termine_mais_handle_conserve_n_est_pas_vivant():
    """Incident #27363 : OpenProcess reussit encore apres la fin du processus.

    Le handle volontairement conserve reproduit le cas du verrou stale : CIM ne
    voit plus le PID, mais GetProcessTimes reussit et rend sa date de creation.
    """
    import ctypes.wintypes as wt

    enfant = subprocess.Popen(
        [sys.executable, "-c", "pass"],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    k32 = ctypes.WinDLL("kernel32", use_last_error=True)
    k32.OpenProcess.argtypes = [wt.DWORD, wt.BOOL, wt.DWORD]
    k32.OpenProcess.restype = wt.HANDLE
    k32.CloseHandle.argtypes = [wt.HANDLE]
    handle = k32.OpenProcess(0x1000, False, enfant.pid)
    assert handle, f"OpenProcess a echoue : {ctypes.get_last_error()}"
    try:
        assert enfant.wait(timeout=30) == 0
        vivant, creation = session_hygiene._pid_windows(enfant.pid)
        assert not vivant, "un processus termine reste ouvrable, il n'est pas vivant"
        assert isinstance(creation, float), "la date reste utile au diagnostic"
    finally:
        k32.CloseHandle(handle)


def test_echec_wait_for_single_object_reste_vivant(monkeypatch):
    """Une mesure d'etat impossible est fail-closed, jamais un PID declare mort."""
    if os.name != "nt":
        pytest.skip("le faux kernel32 simule la surface Windows")
    enfant = subprocess.Popen(
        [sys.executable, "-c", "import time; time.sleep(60)"],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    try:
        original = ctypes.WinDLL

        class _WaitEnEchec:
            """WaitForSingleObject qui echoue : WAIT_FAILED, en acceptant la
            configuration restype/argtypes que la sonde pose avant l'appel."""

            restype = None
            argtypes = None

            def __call__(self, *args, **kwargs):
                return 0xFFFFFFFF  # WAIT_FAILED

        class KernelSansEtat:
            def __init__(self, *args, **kwargs):
                self._k32 = original("kernel32", use_last_error=True)

            def __getattr__(self, nom):
                if nom == "WaitForSingleObject":
                    return _WaitEnEchec()
                return getattr(self._k32, nom)

        monkeypatch.setattr(ctypes, "WinDLL", KernelSansEtat)
        assert session_hygiene._pid_windows(enfant.pid) == (True, None)
    finally:
        enfant.terminate()
        enfant.wait(timeout=30)


@pytest.mark.skipif(os.name != "nt", reason="semantique des handles de processus Windows")
def test_pid_windows_vivant_reste_vivant():
    """Temoins exige par la review : un processus reellement vivant est vivant.

    La sonde passe par WaitForSingleObject (WAIT_TIMEOUT attendu) et rend
    aussi la date de creation, utile au verrou pour defaire la reutilisation
    de numero.
    """
    enfant = subprocess.Popen(
        [sys.executable, "-c", "import time; time.sleep(60)"],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    try:
        vivant, creation = session_hygiene._pid_windows(enfant.pid)
        assert vivant, "un processus qui dort est vivant"
        assert isinstance(creation, float), "la date de creation reste utile au verrou"
    finally:
        enfant.terminate()
        enfant.wait(timeout=30)


@pytest.mark.skipif(os.name != "nt", reason="semantique des handles de processus Windows")
def test_pid_windows_sortie_259_termine_est_mort():
    """Temoins exige par la review : sortie 259 legitime != STILL_ACTIVE.

    GetExitCodeProcess seul est ambigu (259 = STILL_ACTIVE est aussi un code
    de sortie choisi) ; l'etat signale du handle leve l'ambiguite : le
    processus termine qui a choisi 259 est MORT. Le handle conserve assure
    que le verdict vient de WaitForSingleObject, pas d'un OpenProcess
    refuse en erreur 87 (PID absent).
    """
    import ctypes.wintypes as wt

    enfant = subprocess.Popen(
        [sys.executable, "-c", "import sys; sys.exit(259)"],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    k32 = ctypes.WinDLL("kernel32", use_last_error=True)
    k32.OpenProcess.argtypes = [wt.DWORD, wt.BOOL, wt.DWORD]
    k32.OpenProcess.restype = wt.HANDLE
    k32.CloseHandle.argtypes = [wt.HANDLE]
    handle = k32.OpenProcess(0x1000, False, enfant.pid)
    assert handle, f"OpenProcess a echoue : {ctypes.get_last_error()}"
    try:
        assert enfant.wait(timeout=30) == 259
        vivant, creation = session_hygiene._pid_windows(enfant.pid)
        assert not vivant, "un processus termine avec le code 259 n'est pas vivant"
        assert isinstance(creation, float), "la date reste utile au diagnostic"
    finally:
        k32.CloseHandle(handle)


# --- cas reel de la review 5908186749 : ancetre de session vs PID de script ---


def test_deux_sessions_sous_ancetres_differents_rougit(tmp_path):
    """Le cas mesure : deux executions du script, PID de script differents et
    MORTS, sous deux processus de session VIVANTS (A puis B) -> ROUGE.

    Avant le fix, le verrou portait le PID du script : mort au cycle suivant,
    donc reprise silencieuse et doublon invisible. Ici le verrou porte
    l'ancetre A (vivant) ; la seconde execution tourne sous l'ancetre B
    (vivant) avec un PID de script 222 mort -> `session-double`.
    """
    etat = _etat_par_pid({111: (True, 1.0), 112: (True, 2.0), 222: (False, None)})
    premier = session_hygiene.check_lane_lock(
        tmp_path, LANE, session_id="sess-A", etat_pid=etat,
        session_proc=lambda: (111, "claude.exe"))
    assert premier[0].level == session_hygiene.GREEN
    entree = json.loads((tmp_path / VERROU).read_text(encoding="utf-8"))[LANE]
    assert entree["pid"] == 111, "le verrou porte l'ancetre de session, pas le PID du script"
    assert entree["proc"] == "claude.exe"

    second = session_hygiene.check_lane_lock(
        tmp_path, LANE, session_id="sess-B", etat_pid=etat,
        session_proc=lambda: (112, "claude.exe"))
    assert second[0].level == session_hygiene.RED
    assert second[0].name == "session-double"
    assert "111" in second[0].detail and "SECONDE session" in second[0].detail
    assert "sess-A" in second[0].detail and "sess-B" in second[0].detail
    apres = json.loads((tmp_path / VERROU).read_text(encoding="utf-8"))[LANE]
    assert apres["pid"] == 111, "le verrou du porteur vivant ne se reprend pas"


def test_meme_ancetre_reste_vert(tmp_path):
    """Meme processus de session (deux executions du script, PID de script
    differents et morts) : vert « deja pose », aucun ROUGE."""
    etat = _etat_par_pid({111: (True, 1.0), 221: (False, None), 222: (False, None)})
    session_hygiene.check_lane_lock(
        tmp_path, LANE, session_id="sess-A", etat_pid=etat,
        session_proc=lambda: (111, "claude.exe"))
    checks = session_hygiene.check_lane_lock(
        tmp_path, LANE, session_id="sess-A", etat_pid=etat,
        session_proc=lambda: (111, "claude.exe"))
    assert checks[0].level == session_hygiene.GREEN
    assert "deja pose" in checks[0].detail


def test_sans_ancetre_session_non_mesurable_et_aucune_ecriture(tmp_path):
    """Aucun ancetre claude/node : AMBER nomme, jamais vert, aucun verrou ecrit."""
    checks = session_hygiene.check_lane_lock(
        tmp_path, LANE, session_id="sess-A", etat_pid=_etat_par_pid({}),
        session_proc=lambda: None)
    assert len(checks) == 1 and checks[0].name == "session-double"
    assert checks[0].level == session_hygiene.AMBER
    assert checks[0].level != session_hygiene.GREEN
    assert "non mesurable" in checks[0].detail
    assert checks[0].data.get("mesurable") is False
    assert not (tmp_path / VERROU).exists(), "un non-mesurable n'ecrit pas de verrou"


def test_session_differente_mais_pid_mort_reprise_silencieuse(tmp_path):
    """Un redemarrage change d'ID de session : un PID mort -> reprise, pas de faux ROUGE."""
    _poser_verrou(tmp_path, LANE, pid=300, debut_proc=1.0)  # session "autre"
    checks = session_hygiene.check_lane_lock(
        tmp_path, LANE, session_id="sess-B",
        etat_pid=_etat_par_pid({300: (False, None)}),
        session_proc=lambda: (112, "claude.exe"))
    assert checks[0].level == session_hygiene.GREEN
    assert "repris" in checks[0].detail


# --- remontee de la chaine des parents ---------------------------------------


def test_remontee_prefere_claude_a_node():
    """Un `claude*` l'emporte sur un `node*` plus proche (harnais sous Node)."""
    table = {100: (200, "python.exe"), 200: (300, "node.exe"), 300: (1, "claude.exe")}
    assert session_hygiene.trouver_ancetre_session(depart=100, table=table) == (
        300, "claude.exe")


def test_remontee_repli_sur_node():
    """Sans `claude*` dans la chaine, le premier `node*` fait foi."""
    table = {100: (200, "python.exe"), 200: (1, "node.exe")}
    assert session_hygiene.trouver_ancetre_session(depart=100, table=table) == (
        200, "node.exe")


def test_remontee_bornee_sans_cycle_et_sans_faux_positif():
    """Cycle -> arret ; chaine trop longue -> borne ; autre nom -> None."""
    cycle = {100: (200, "python.exe"), 200: (100, "bash.exe")}
    assert session_hygiene.trouver_ancetre_session(depart=100, table=cycle) is None
    assert session_hygiene.trouver_ancetre_session(
        depart=100, table={100: (200, "python.exe"), 200: (1, "explorer.exe")}) is None
    longue = {i: (i + 1, "intermediaire.exe") for i in range(1000, 1100)}
    longue[1100] = (1, "claude.exe")
    assert session_hygiene.trouver_ancetre_session(depart=1000, table=longue) is None


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
    """--lane cable le check : il apparait dans le JSON et le fichier est ecrit.

    Adapte au fix : le porteur est desormais l'ancetre de session rendu par
    `trouver_ancetre_session` (avant, `main()` enregistrait `os.getpid()`).
    On l'injecte pour ne pas dependre de la chaine de processus de la CI.
    """
    monkeypatch.setattr(session_hygiene, "repo_root", lambda: tmp_path)
    monkeypatch.setattr(session_hygiene, "check_fetch", lambda root: [])
    monkeypatch.setattr(session_hygiene, "trouver_ancetre_session",
                        lambda: (43210, "claude.exe"))
    rc = session_hygiene.main(["--json", "--lane", LANE, "--session-id", "s-main"])
    assert rc in (0, 1)  # d'autres checks peuvent rougir sur un depot factice
    donnees = json.loads(capsys.readouterr().out)
    noms = [c["name"] for c in donnees["checks"]]
    assert "session-double" in noms
    entree = json.loads((tmp_path / VERROU).read_text(encoding="utf-8"))[LANE]
    assert entree["session"] == "s-main"
    assert entree["pid"] == 43210, "le porteur est l'ancetre de session, pas le script"


def test_main_sans_lane_n_ecrit_aucun_verrou(tmp_path, monkeypatch, capsys):
    """Controle negatif du cablage : sans --lane, aucun fichier n'est ecrit."""
    monkeypatch.setattr(session_hygiene, "repo_root", lambda: tmp_path)
    monkeypatch.setattr(session_hygiene, "check_fetch", lambda root: [])
    session_hygiene.main(["--json"])
    capsys.readouterr()
    assert not (tmp_path / VERROU).exists()


def test_main_sans_ancetre_rend_amber_sans_ecrire(tmp_path, monkeypatch, capsys):
    """Cablage du non-mesurable : AMBER dans le JSON, aucun verrou ecrit."""
    monkeypatch.setattr(session_hygiene, "repo_root", lambda: tmp_path)
    monkeypatch.setattr(session_hygiene, "check_fetch", lambda root: [])
    monkeypatch.setattr(session_hygiene, "trouver_ancetre_session", lambda: None)
    session_hygiene.main(["--json", "--lane", LANE])
    donnees = json.loads(capsys.readouterr().out)
    verrou = next(c for c in donnees["checks"] if c["name"] == "session-double")
    assert verrou["level"] == "AMBER"
    assert not (tmp_path / VERROU).exists()


def test_main_rougit_sur_un_vrai_processus_vivant(tmp_path, monkeypatch, capsys):
    """Bout en bout : un VRAI processus vivant dans le verrou -> ROUGE, sortie 1.

    Adapte au fix : l'ancetre de session est injecte (celui du processus de
    test, vivant), la ou `main()` enregistrait auparavant `os.getpid()`.
    """
    enfant = subprocess.Popen(
        [sys.executable, "-c", "import time; time.sleep(60)"],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    try:
        _poser_verrou(tmp_path, LANE, pid=enfant.pid, debut_proc=None)
        monkeypatch.setattr(session_hygiene, "repo_root", lambda: tmp_path)
        monkeypatch.setattr(session_hygiene, "check_fetch", lambda root: [])
        monkeypatch.setattr(session_hygiene, "trouver_ancetre_session",
                            lambda: (os.getpid(), "python.exe"))
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
