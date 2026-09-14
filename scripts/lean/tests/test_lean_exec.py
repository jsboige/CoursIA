#!/usr/bin/env python3
"""Tests de l'organe d'execution Lean confine (T1+T2, issue #15666).

Discriminants exiges par le cahier des charges §6 et le dispatch P0 :

- ``test_admission_cap_machine_wide_two_worktrees`` : deux demandeurs
  concurrents depuis deux repertoires distincts ne depassent JAMAIS ensemble
  le cap — c'est le controle qui distingue un cap machine-wide d'un cap par
  arbre.
- ``test_timeout_kills_whole_tree`` : le timeout tue TOUTE la descendance.
- ``test_planted_orphan_is_detected`` : controle par **faux negatif** du
  detecteur — un enfant orphelin qui DOIT etre attrape l'est ; sans ce
  controle, l'organe rendrait « propre » exactement comme sur une machine
  sans Lean.
- ``test_positive_control_real_lake`` : une compilation ciblee REELLE
  (``lake env lean``) passe sous le budget et publie ses metriques.

Discriminants T2 (admission raffinee — lease/file/budget) :

- ``test_compute_granted_min_of_sources`` : le parallelisme accorde est le
  MINIMUM des budgets CPU/RAM/commit, porte disque incluse, contrainte
  serrante NOMMEE.
- ``test_fail_closed_missing_telemetry_source`` : telemetrie manquante =
  refus fail-closed nommant la source (pression SIMULEE, pas reelle).
- ``test_tree_lease_same_tree_second_refused_then_released`` : UN SEUL
  acteur par arbre, refus actionnable, lease libere en fin de run.
- ``test_tree_lease_stale_autobroken`` / ``test_tree_lease_foreign_host_never_broken`` :
  peremption reprise de tree_lock (meme-host pid mort uniquement).
- ``test_queue_wait_admits_after_release`` / ``test_queue_timeout_refuses`` /
  ``test_queue_full_refuses`` : file bornee observable, refus explicites.
- ``test_status_shows_queue_and_tree_leases`` : observabilite de la file et
  des leases.

Les tests d'admission et de confinement tournent avec des enfants Python
(sleepers) : ils ne dependent pas du toolchain Lean. Le controle positif, lui,
est skippe si ``lake`` est absent.

Execution directe (sans pytest) :
    python scripts/lean/tests/test_lean_exec.py
Ou via pytest :
    pytest scripts/lean/tests/test_lean_exec.py
"""

import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from contextlib import contextmanager
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import lean_exec as le  # noqa: E402

LEAN_EXEC = str(Path(__file__).resolve().parent.parent / "lean_exec.py")
PY = sys.executable
REPO_ROOT = Path(__file__).resolve().parents[3]

SLEEP_CMD = [PY, "-c", "import time; time.sleep(4)"]


def _env(state: Path, **extra) -> dict:
    env = os.environ.copy()
    env["LEAN_EXEC_STATE_DIR"] = str(state)
    env["LEAN_EXEC_WSL"] = "off"
    env.update({k: str(v) for k, v in extra.items()})
    return env


def _run(state: Path, args: list[str], cwd: Path | None = None,
         timeout: float = 120, **extra) -> subprocess.CompletedProcess:
    return subprocess.run(
        [PY, LEAN_EXEC, *args], env=_env(state, **extra),
        cwd=str(cwd) if cwd else None,
        capture_output=True, text=True, timeout=timeout,
        encoding="utf-8", errors="replace",
    )


def _last(state: Path) -> dict:
    return json.loads(
        (state / "last_run.json").read_text(encoding="utf-8")
    )


# ---------------------------------------------------------------------------
# Resolution d'etat + bornage de commande (pur, sans spawn)
# ---------------------------------------------------------------------------

def test_state_dir_resolution():
    """Meme chaine que gpu.py:438, plus un override d'isolation pour les tests."""
    saved = {k: os.environ.get(k) for k in
             ("LEAN_EXEC_STATE_DIR", "LOCALAPPDATA", "XDG_STATE_HOME")}
    try:
        for k in saved:
            os.environ.pop(k, None)
        os.environ["LEAN_EXEC_STATE_DIR"] = r"C:\tmp\iso"
        assert le.state_dir() == Path(r"C:\tmp\iso")
        os.environ.pop("LEAN_EXEC_STATE_DIR")
        os.environ["LOCALAPPDATA"] = r"C:\Users\x\AppData\Local"
        os.environ["XDG_STATE_HOME"] = "/xdg"
        assert le.state_dir() == Path(r"C:\Users\x\AppData\Local") / (
            "CoursIA" if os.name == "nt" else "coursia") / "lean_exec"
        os.environ.pop("LOCALAPPDATA")
        got = le.state_dir()
        assert "xdg" in got.parts, got
        os.environ.pop("XDG_STATE_HOME")
        assert ".local" in str(le.state_dir())
    finally:
        for k, v in saved.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v


def test_bound_command_inserts_kjobs():
    """Le parallelisme est borne explicitement, jamais le defaut."""
    assert le.bound_command(["lake", "build"], 5) == [
        "lake", "build", "-Kjobs=5"]
    # Un flag deja pose par l'appelant est respecte (decidable, pas ecrase).
    assert le.bound_command(["lake", "build", "-Kjobs=2"], 5) == [
        "lake", "build", "-Kjobs=2"]
    # Hors build : jamais de reecriture de la ligne de commande.
    assert le.bound_command(["lake", "env", "lean", "X.lean"], 5) == [
        "lake", "env", "lean", "X.lean"]
    assert le.bound_command(["lean", "X.lean"], 5) == ["lean", "X.lean"]


# ---------------------------------------------------------------------------
# Admission machine-wide — deux worktrees concurrents
# ---------------------------------------------------------------------------

def test_admission_cap_machine_wide_two_worktrees():
    with tempfile.TemporaryDirectory() as td:
        state = Path(td) / "state"
        w1, w2, w3 = (Path(td) / n for n in ("w1", "w2", "w3"))
        for w in (w1, w2, w3):
            w.mkdir()
        cap = dict(LEAN_EXEC_CAP=2, LEAN_EXEC_BUDGET=1)
        procs = [
            subprocess.Popen(
                [PY, LEAN_EXEC, "run", "--json", "--", *SLEEP_CMD],
                env=_env(state, **cap), cwd=str(w),
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            )
            for w in (w1, w2)
        ]
        # Synchronisation sur l'etat OBSERVABLE, pas sur une duree : le 3e
        # demandeur ne doit partir qu'une fois les DEUX premiers enregistres.
        # L'enregistrement est ecrit sous le verrou d'admission, juste apres
        # le spawn+resume (lean_exec.py:854), donc sa presence prouve que le
        # run occupe deja sa part du cap. Un delai fixe courait apres la
        # machine : mesure #15940, sleep(0.5) laissait w2 non enregistre et
        # le 3e demandeur se faisait admettre a sa place -> {w1, w3}.
        def _registered() -> int:
            return len(list((state / "runs").glob("*.json")))

        deadline = time.monotonic() + 30.0
        while _registered() < 2 and time.monotonic() < deadline:
            time.sleep(0.05)
        assert _registered() >= 2, (
            "les deux premiers runs devaient s'enregistrer sous 30 s, "
            f"vu {_registered()}")

        third = _run(state, ["run", "--json", "--", *SLEEP_CMD],
                     cwd=w3, **cap)
        for p in procs:
            p.wait(timeout=60)
        codes = [p.returncode for p in procs] + [third.returncode]
        assert codes.count(0) == 2, f"attendu 2 admissions, vu {codes}"
        assert third.returncode == le.EXIT_REFUSED, (
            f"le 3e demandeur devait etre refuse, vu {third.returncode}")
        # Le refus se lit sur le stdout du 3e run : last_run.json est partage
        # par le state dir et les 3 runs concurrents y ecrivent.
        refused = json.loads(third.stdout[third.stdout.index("{"):])
        assert "cap" in (refused.get("reason") or ""), refused.get("reason")


def test_admission_refuses_when_population_unmeasurable():
    """Fail-closed : pas de telemetrie = pas de lancement optimiste.

    Le scan est patche plutot que rendu introuvable : sous Windows
    ``tasklist.exe`` se resout via System32 meme avec un PATH vide, donc
    vider PATH ne testerait pas la branche fail-closed.
    """
    saved_state = os.environ.get("LEAN_EXEC_STATE_DIR")
    saved_scan = le.scan_native_population
    with tempfile.TemporaryDirectory() as td:
        os.environ["LEAN_EXEC_STATE_DIR"] = str(Path(td) / "s")
        le.scan_native_population = lambda: (-1, "unavailable: test")
        try:
            rc = le.run_command(SLEEP_CMD, timeout_s=10, as_json=True)
            assert rc == le.EXIT_REFUSED, rc
            res = json.loads(
                (le.state_dir() / "last_run.json").read_text("utf-8"))
            assert "unmeasurable" in res["reason"], res["reason"]
        finally:
            le.scan_native_population = saved_scan
            if saved_state is None:
                os.environ.pop("LEAN_EXEC_STATE_DIR", None)
            else:
                os.environ["LEAN_EXEC_STATE_DIR"] = saved_state


# ---------------------------------------------------------------------------
# Confinement : le timeout tue toute la descendance
# ---------------------------------------------------------------------------

def test_timeout_kills_whole_tree():
    with tempfile.TemporaryDirectory() as td:
        state = Path(td) / "state"
        pidfile = Path(td) / "grandchild.pid"
        root = (
            "import subprocess,sys,time;"
            "p=subprocess.Popen([sys.executable,'-c',"
            "'import time;time.sleep(120)']);"
            f"open(r'{pidfile}','w').write(str(p.pid));"
            "time.sleep(120)"
        )
        rc = _run(state, ["run", "--json", "--timeout", "3", "--",
                          PY, "-c", root], timeout=90)
        res = _last(state)
        assert rc.returncode == le.EXIT_TIMEOUT, (
            f"attendu {le.EXIT_TIMEOUT}, vu {rc.returncode}")
        assert res["status"] == "timeout"
        assert res["orphans"] == [], f"orphelins: {res['orphans']}"
        deadline = time.time() + 10
        while time.time() < deadline and not pidfile.exists():
            time.sleep(0.2)
        if pidfile.exists():
            gpid = int(pidfile.read_text().strip())
            time.sleep(1.5)
            assert not le.pid_alive(gpid), (
                f"le petit-fils {gpid} a survecu au timeout")


def test_normal_exit_is_clean():
    with tempfile.TemporaryDirectory() as td:
        state = Path(td) / "state"
        rc = _run(state, ["run", "--json", "--", PY, "-c", "print('ok')"],
                  timeout=60)
        res = _last(state)
        assert rc.returncode == le.EXIT_OK, rc.returncode
        assert res["orphans"] == []
        assert res["child_exit_code"] == 0


def test_child_failure_maps_to_exit_1():
    with tempfile.TemporaryDirectory() as td:
        state = Path(td) / "state"
        rc = _run(state, ["run", "--json", "--", PY, "-c", "import sys; sys.exit(3)"],
                  timeout=60)
        res = _last(state)
        assert rc.returncode == le.EXIT_CHILD, rc.returncode
        assert res["child_exit_code"] == 3
        assert res["status"] == "child_failed"


@pytest.mark.skipif(
    os.name != "nt",
    reason=(
        "propriete Windows : un orphelin garde le PID de son parent mort "
        "comme PPID ; sous POSIX le noyau reparente a PID 1 et "
        "descendants_of(parent_mort) est structurellement vide -- le test "
        "mesurerait le noyau, pas find_orphans (reserve 2, arbitrage #15666)"
    ),
)
def test_planted_orphan_is_detected():
    """Controle par faux negatif : un orphelin qui DOIT etre attrape l'est.

    L'enfant est plante HORS confinement (parent mort, enfant vivant) : le
    detecteur doit le lister — sinon l'organe rendrait « propre » a tort.
    """
    with tempfile.TemporaryDirectory() as td:
        pidfile = Path(td) / "orphan.pid"
        planter = (
            "import subprocess,sys,time;"
            "p=subprocess.Popen([sys.executable,'-c',"
            "'import time;time.sleep(120)']);"
            f"open(r'{pidfile}','w').write(str(p.pid));"
            "time.sleep(1)"
        )
        parent = subprocess.Popen([PY, "-c", planter])
        parent.wait(timeout=30)
        deadline = time.time() + 10
        while time.time() < deadline and not pidfile.exists():
            time.sleep(0.2)
        assert pidfile.exists(), "le planteur n'a pas ecrit le pid"
        orphan = int(pidfile.read_text().strip())
        try:
            time.sleep(0.5)
            orphans = le.find_orphans(parent.pid, None)
            assert orphan in orphans, (
                f"orphelin {orphan} non detecte (vu {orphans})")
        finally:
            le.kill_pids([orphan])


# ---------------------------------------------------------------------------
# Registre : peremption (reprise de tree_lock)
# ---------------------------------------------------------------------------

def test_stale_run_record_is_swept_foreign_host_preserved():
    with tempfile.TemporaryDirectory() as td:
        state = Path(td) / "state"
        runs = state / "runs"
        runs.mkdir(parents=True)
        dead = {"pid": 999999999, "host": le.host_id(), "budget": 2}
        foreign = {"pid": 1, "host": "autre-machine/nt", "budget": 2}
        (runs / "dead.json").write_text(json.dumps(dead), encoding="utf-8")
        (runs / "foreign.json").write_text(json.dumps(foreign), encoding="utf-8")
        saved = os.environ.get("LEAN_EXEC_STATE_DIR")
        os.environ["LEAN_EXEC_STATE_DIR"] = str(state)
        try:
            swept = le.sweep_stale_runs()
            assert "dead" in swept
            assert (runs / "foreign.json").exists(), (
                "un run d'un autre namespace de pids ne doit jamais etre "
                "auto-retire (tree_lock.py:138)")
            total, live = le.live_registered_budgets()
            assert total == 0 and live == []
        finally:
            if saved is None:
                os.environ.pop("LEAN_EXEC_STATE_DIR", None)
            else:
                os.environ["LEAN_EXEC_STATE_DIR"] = saved


# ---------------------------------------------------------------------------
# Controle positif : compilation ciblee reelle sous le cap
# ---------------------------------------------------------------------------

def _find_toolchain() -> str | None:
    """Un toolchain du depot DEJA installe (elan), pour ne pas declencher de
    telechargement pendant un test. Override : LEAN_EXEC_CONTROL_TOOLCHAIN."""
    override = os.environ.get("LEAN_EXEC_CONTROL_TOOLCHAIN")
    if override:
        return override
    try:
        out = subprocess.run(["elan", "toolchain", "list"],
                             capture_output=True, text=True, timeout=30,
                             encoding="utf-8", errors="replace")
        installed = {ln.strip() for ln in out.stdout.splitlines() if ln.strip()}
    except (OSError, subprocess.SubprocessError):
        installed = set()
    for candidate in REPO_ROOT.rglob("lean-toolchain"):
        if ".lake" in candidate.parts:
            continue
        content = candidate.read_text(encoding="utf-8").strip()
        if content in installed:
            return content
    return None


def test_positive_control_real_lake():
    """Une compilation ciblee REELLE passe sous le budget et publie ses metriques."""
    # Reserve 3 (arbitrage #15666) : un print+return rend « passed » sans
    # rien controler -- pire que pas de controle. pytest.skip rend un « s »
    # visible dans le rapport.
    if shutil.which("lake") is None:
        pytest.skip("lake absent du PATH")
    toolchain = _find_toolchain()
    if not toolchain:
        pytest.skip("aucun lean-toolchain du depot n'est installe via elan")
    with tempfile.TemporaryDirectory() as td:
        state = Path(td) / "state"
        proj = Path(td) / "control"
        proj.mkdir()
        (proj / "lean-toolchain").write_text(toolchain, encoding="utf-8")
        (proj / "lakefile.toml").write_text(
            'name = "t1control"\nversion = "0.1.0"\n'
            "defaultTargets = [\"T1Control\"]\n\n"
            "[[lean_lib]]\nname = \"T1Control\"\n",
            encoding="utf-8",
        )
        (proj / "T1Control.lean").write_text(
            "theorem t1_control : 1 + 1 = 2 := rfl\n", encoding="utf-8")
        rc = _run(
            state,
            ["run", "--json", "--timeout", "900", "--budget", "2", "--",
             "lake", "env", "lean", "T1Control.lean"],
            cwd=proj, timeout=1200,
            LEAN_EXEC_CAP=4, LEAN_NUM_THREADS=4,
        )
        res = _last(state)
        assert rc.returncode == le.EXIT_OK, (
            f"compilation reelle en echec: {rc.returncode}\n"
            f"stderr={rc.stderr[-2000:]}\nstdout={rc.stdout[-2000:]}")
        assert res["orphans"] == []
        print(
            f"POSITIVE CONTROL OK: duration={res['duration_s']}s "
            f"backend={res['backend']} cap={res['cap']} "
            f"population_before={res['population_before']} "
            f"cmd={res.get('cmd_effective')}"
        )


# ---------------------------------------------------------------------------
# T2 : budget au minimum des sources, fail-closed telemetrie
# ---------------------------------------------------------------------------

_T2_KNOBS = (
    "LEAN_EXEC_RESERVE_CORES", "LEAN_EXEC_MEM_PER_JOB_MB",
    "LEAN_EXEC_COMMIT_PER_JOB_MB", "LEAN_EXEC_MIN_FREE_GB",
)


def _plenty_resources() -> dict:
    return {
        "cpu": {"ok": True, "logical_cores": 16},
        "ram": {"ok": True, "avail_mb": 32768},
        "commit": {"ok": True, "avail_mb": 49152},
        "disk": {"ok": True, "free_gb": 100.0},
    }


def test_compute_granted_min_of_sources():
    """Le parallelisme accorde est le MIN des budgets CPU/RAM/commit, et la
    porte disque refuse (spec #15666 §2) — chacune des sources doit pouvoir
    etre la contrainte serrante, nommee dans le detail."""
    saved = {k: os.environ.get(k) for k in _T2_KNOBS}
    try:
        os.environ["LEAN_EXEC_RESERVE_CORES"] = "2"
        os.environ["LEAN_EXEC_MEM_PER_JOB_MB"] = "2048"
        os.environ["LEAN_EXEC_COMMIT_PER_JOB_MB"] = "3072"
        os.environ["LEAN_EXEC_MIN_FREE_GB"] = "2"
        plenty = _plenty_resources()
        granted, detail = le.compute_granted(4, plenty, 0)
        assert granted == 4 and detail["binding"] is None, (granted, detail)

        low_ram = {**plenty, "ram": {"ok": True, "avail_mb": 2048}}
        granted, detail = le.compute_granted(4, low_ram, 0)
        assert granted == 1 and detail["binding"] == "ram", (granted, detail)

        low_commit = {**plenty, "commit": {"ok": True, "avail_mb": 3072}}
        granted, detail = le.compute_granted(4, low_commit, 0)
        assert granted == 1 and detail["binding"] == "commit", (granted, detail)

        # Population active mangee par le budget CPU : 16 - 2 - 14 = 0.
        granted, detail = le.compute_granted(4, plenty, 14)
        assert granted == 0 and detail["binding"] == "cpu", (granted, detail)

        low_disk = {**plenty, "disk": {"ok": True, "free_gb": 1.0}}
        granted, detail = le.compute_granted(4, low_disk, 0)
        assert granted == 0 and detail["binding"] == "disk", (granted, detail)
    finally:
        for k, v in saved.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v


def test_fail_closed_missing_telemetry_source():
    """Fail-closed par source : une telemetrie manquante refuse le run en
    NOMMANT la source (spec #15666 §2), jamais de lancement optimiste.

    Pression SIMULEE (telemetrie patchee), pas une vraie saturation —
    exigence explicite du cahier des charges §6."""
    saved_state = os.environ.get("LEAN_EXEC_STATE_DIR")
    saved_measure = le.measure_resources
    with tempfile.TemporaryDirectory() as td:
        os.environ["LEAN_EXEC_STATE_DIR"] = str(Path(td) / "s")

        def _broken_ram():
            res = saved_measure()
            res["ram"] = {"ok": False}
            return res

        le.measure_resources = _broken_ram
        try:
            rc = le.run_command(SLEEP_CMD, timeout_s=10, as_json=True)
            assert rc == le.EXIT_REFUSED, rc
            res = json.loads(
                (le.state_dir() / "last_run.json").read_text("utf-8"))
            assert "telemetry unavailable" in res["reason"], res["reason"]
            assert "ram" in res["reason"], res["reason"]
        finally:
            le.measure_resources = saved_measure
            if saved_state is None:
                os.environ.pop("LEAN_EXEC_STATE_DIR", None)
            else:
                os.environ["LEAN_EXEC_STATE_DIR"] = saved_state


def test_granted_jobs_reported_and_thread_capped():
    """Le run admis publie le budget detaille ; LEAN_NUM_THREADS jamais au
    dela du granted (demande explicite respectee en dessous)."""
    with tempfile.TemporaryDirectory() as td:
        state = Path(td) / "state"
        rc = _run(state, ["run", "--json", "--",
                          PY, "-c", "import os; print(os.environ.get('LEAN_NUM_THREADS'))"],
                  timeout=60, LEAN_EXEC_JOBS=1)
        assert rc.returncode == le.EXIT_OK, rc.stdout + rc.stderr
        res = _last(state)
        assert res["granted_jobs"] == 1, res.get("granted_jobs")
        assert res["budgets"]["requested"] == 1
        assert "1" in (rc.stdout or ""), rc.stdout


# ---------------------------------------------------------------------------
# T2 : lease par arbre — second etage d'admission (reprise tree_lock)
# ---------------------------------------------------------------------------

def _lake_fixture(td: Path, name: str = "t2lake") -> Path:
    proj = td / name
    proj.mkdir(parents=True, exist_ok=True)
    (proj / "lakefile.toml").write_text(
        'name = "t2"\nversion = "0.1.0"\n', encoding="utf-8")
    return proj


@contextmanager
def _state_env(state: Path):
    """LEAN_EXEC_STATE_DIR pose pour le PRESENT processus : tree_lease_path
    et queue_dir calculent alors dans le state isole du test, pas dans le
    %LOCALAPPDATA% reel de la machine (piege des 4 premiers echecs)."""
    saved = os.environ.get("LEAN_EXEC_STATE_DIR")
    os.environ["LEAN_EXEC_STATE_DIR"] = str(state)
    try:
        yield
    finally:
        if saved is None:
            os.environ.pop("LEAN_EXEC_STATE_DIR", None)
        else:
            os.environ["LEAN_EXEC_STATE_DIR"] = saved


def test_tree_lease_same_tree_second_refused_then_released():
    """Discriminant : UN SEUL acteur par arbre, vu machine-wide. Le refus du
    second demandeur est ACTIONNABLE (pid/host/caller du holder), et le
    lease est libere a la fin du premier run."""
    with tempfile.TemporaryDirectory() as td:
        state = Path(td) / "state"
        proj = _lake_fixture(Path(td))
        with _state_env(state):
            lease = le.tree_lease_path(proj.resolve())
        cap = dict(LEAN_EXEC_CAP=8, LEAN_EXEC_BUDGET=1)
        first = subprocess.Popen(
            [PY, LEAN_EXEC, "run", "--json", "--caller", "t2-first", "--",
             *SLEEP_CMD],
            env=_env(state, **cap), cwd=str(proj),
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        )
        deadline = time.monotonic() + 30.0
        while time.monotonic() < deadline and not lease.exists():
            time.sleep(0.05)
        assert lease.exists(), "le lease du 1er run n'est pas apparu sous 30 s"

        second = _run(state, ["run", "--json", "--caller", "t2-second", "--",
                              *SLEEP_CMD], cwd=proj, timeout=60, **cap)
        assert second.returncode == le.EXIT_REFUSED, second.returncode
        refused = json.loads(second.stdout[second.stdout.index("{"):])
        reason = refused.get("reason") or ""
        assert "tree" in reason, reason
        assert "t2-first" in reason, reason  # refus actionnable
        assert first.wait(timeout=60) == 0

        deadline = time.monotonic() + 15.0
        while time.monotonic() < deadline and lease.exists():
            time.sleep(0.1)
        assert not lease.exists(), "lease non libere apres la fin du 1er run"


def test_tree_lease_stale_autobroken():
    """Peremption reprise de tree_lock.py:139 : holder du MEME host au pid
    mort => break visible (TREE_LEASE_BROKEN), puis acquisition."""
    with tempfile.TemporaryDirectory() as td:
        state = Path(td) / "state"
        proj = _lake_fixture(Path(td))
        with _state_env(state):
            lease = le.tree_lease_path(proj.resolve())
        lease.parent.mkdir(parents=True, exist_ok=True)
        lease.write_text(json.dumps({
            "pid": 999999999, "host": le.host_id(), "tree": str(proj),
            "cmd": ["lake", "build"], "caller": "dead-holder",
            "budget": 1, "started_epoch": 0.0,
        }), encoding="utf-8")
        rc = _run(state, ["run", "--json", "--",
                          PY, "-c", "print('ok')"], cwd=proj, timeout=60,
                  LEAN_EXEC_CAP=8)
        assert rc.returncode == le.EXIT_OK, rc.stdout + rc.stderr
        assert "TREE_LEASE_BROKEN" in rc.stderr, rc.stderr
        assert "stale" in rc.stderr, rc.stderr


def test_tree_lease_foreign_host_never_broken():
    """Reprise tree_lock.py:138 : un holder d'un host etranger n'est JAMAIS
    auto-casse (pids non comparables entre namespaces)."""
    with tempfile.TemporaryDirectory() as td:
        state = Path(td) / "state"
        proj = _lake_fixture(Path(td))
        with _state_env(state):
            lease = le.tree_lease_path(proj.resolve())
        lease.parent.mkdir(parents=True, exist_ok=True)
        lease.write_text(json.dumps({
            "pid": 1, "host": "autre-machine/nt", "tree": str(proj),
            "cmd": ["lake", "build"], "caller": "etranger",
            "budget": 1, "started_epoch": 0.0,
        }), encoding="utf-8")
        rc = _run(state, ["run", "--json", "--",
                          PY, "-c", "print('ok')"], cwd=proj, timeout=60,
                  LEAN_EXEC_CAP=8)
        assert rc.returncode == le.EXIT_REFUSED, rc.returncode
        refused = json.loads(rc.stdout[rc.stdout.index("{"):])
        reason = refused.get("reason") or ""
        assert "tree" in reason and "autre-machine" in reason, reason
        assert lease.exists(), "un lease etranger ne doit pas etre auto-casse"


# ---------------------------------------------------------------------------
# T2 : file bornee observable
# ---------------------------------------------------------------------------

def _wait_for(condition, timeout_s: float = 30.0, what: str = "condition"):
    deadline = time.monotonic() + timeout_s
    while time.monotonic() < deadline:
        if condition():
            return
        time.sleep(0.05)
    assert condition(), f"{what} non atteinte sous {timeout_s} s"


def test_queue_wait_admits_after_release():
    """--wait : le demandeur attend en file, est admis quand le cap se
    libere, et publie son temps d'attente."""
    with tempfile.TemporaryDirectory() as td:
        state = Path(td) / "state"
        cap = dict(LEAN_EXEC_CAP=1, LEAN_EXEC_BUDGET=1)
        first = subprocess.Popen(
            [PY, LEAN_EXEC, "run", "--json", "--timeout", "12", "--",
             PY, "-c", "import time; time.sleep(3)"],
            env=_env(state, **cap), cwd=str(td),
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        )
        runs = state / "runs"
        _wait_for(lambda: len(list(runs.glob("*.json"))) >= 1, what="1er run enregistre")

        second = _run(state, ["run", "--json", "--wait", "25", "--",
                              PY, "-c", "print('ok')"], timeout=120, **cap)
        assert first.wait(timeout=60) == 0
        assert second.returncode == le.EXIT_OK, second.stdout + second.stderr
        res = _last(state)
        assert res["status"] == "ok", res
        assert res.get("queue_wait_s", 0.0) >= 0.5, res


def test_queue_timeout_refuses():
    """Delai de file depasse = refus explicite 'wait timeout' (jamais
    d'attente infinie)."""
    with tempfile.TemporaryDirectory() as td:
        state = Path(td) / "state"
        cap = dict(LEAN_EXEC_CAP=1, LEAN_EXEC_BUDGET=1)
        first = subprocess.Popen(
            [PY, LEAN_EXEC, "run", "--json", "--timeout", "10", "--",
             PY, "-c", "import time; time.sleep(30)"],
            env=_env(state, **cap), cwd=str(td),
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        )
        runs = state / "runs"
        _wait_for(lambda: len(list(runs.glob("*.json"))) >= 1, what="1er run enregistre")

        second = _run(state, ["run", "--json", "--wait", "2", "--",
                              PY, "-c", "print('ok')"], timeout=60, **cap)
        assert second.returncode == le.EXIT_REFUSED, second.returncode
        refused = json.loads(second.stdout[second.stdout.index("{"):])
        assert "wait timeout" in (refused.get("reason") or ""), \
            refused.get("reason")
        assert first.wait(timeout=60) == le.EXIT_TIMEOUT


def test_queue_full_refuses():
    """File bornee : queue_max atteint = refus explicite du 3e demandeur,
    jamais de croissance silencieuse de la file."""
    with tempfile.TemporaryDirectory() as td:
        state = Path(td) / "state"
        cap = dict(LEAN_EXEC_CAP=1, LEAN_EXEC_BUDGET=1,
                   LEAN_EXEC_QUEUE_MAX=1)
        first = subprocess.Popen(
            [PY, LEAN_EXEC, "run", "--json", "--timeout", "20", "--",
             PY, "-c", "import time; time.sleep(8)"],
            env=_env(state, **cap), cwd=str(td),
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        )
        runs = state / "runs"
        _wait_for(lambda: len(list(runs.glob("*.json"))) >= 1, what="1er run enregistre")
        second = subprocess.Popen(
            [PY, LEAN_EXEC, "run", "--json", "--wait", "25", "--",
             PY, "-c", "print('ok')"],
            env=_env(state, **cap), cwd=str(td),
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        )
        queue = state / "queue"
        _wait_for(lambda: len(list(queue.glob("*.json"))) >= 1,
                  what="2e demandeur en file")

        third = _run(state, ["run", "--json", "--wait", "1", "--",
                             PY, "-c", "print('ok')"], timeout=60, **cap)
        assert third.returncode == le.EXIT_REFUSED, third.returncode
        refused = json.loads(third.stdout[third.stdout.index("{"):])
        assert "queue full" in (refused.get("reason") or ""), \
            refused.get("reason")
        assert first.wait(timeout=60) == 0
        assert second.wait(timeout=60) == 0


def test_status_shows_queue_and_tree_leases():
    """Observabilite (spec #15666 §1) : status expose la file et les leases
    d'arbre tenus."""
    with tempfile.TemporaryDirectory() as td:
        state = Path(td) / "state"
        proj = _lake_fixture(Path(td))
        with _state_env(state):
            lease = le.tree_lease_path(proj.resolve())
            qdir = le.queue_dir()
        lease.parent.mkdir(parents=True, exist_ok=True)
        lease.write_text(json.dumps({
            "pid": os.getpid(), "host": le.host_id(), "tree": str(proj),
            "cmd": ["lake", "build"], "caller": "t2-status",
            "budget": 1, "started_epoch": time.time(),
        }), encoding="utf-8")
        qdir.mkdir(parents=True, exist_ok=True)
        (qdir / "probe.json").write_text(json.dumps({
            "pid": os.getpid(), "host": le.host_id(),
            "cmd": ["lake", "build"], "caller": "t2-queue-probe",
            "since_epoch": time.time(),
        }), encoding="utf-8")

        rc = _run(state, ["status", "--json"], timeout=60)
        payload = json.loads(rc.stdout[rc.stdout.index("{"):])
        assert any(
            e.get("caller") == "t2-queue-probe" for e in payload["queue"]
        ), payload["queue"]
        assert any(
            t.get("caller") == "t2-status" for t in payload["tree_leases"]
        ), payload["tree_leases"]


# ---------------------------------------------------------------------------
# Runner direct (convention des tests scripts/lean)
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    failed = 0
    for fn in tests:
        started = time.time()
        try:
            fn()
            print(f"PASS {fn.__name__} ({time.time() - started:.1f}s)")
        except Exception as exc:  # noqa: BLE001
            failed += 1
            print(f"FAIL {fn.__name__}: {type(exc).__name__}: {exc}")
    print(f"\n{len(tests) - failed}/{len(tests)} tests passes")
    sys.exit(1 if failed else 0)
