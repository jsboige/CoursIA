"""Organe canonique d'execution Lean — T1 : cap machine-wide + confinement kill-tree (See #15666).

Incident du 12 septembre 2026 : ~30 processus ``lean.exe`` a ~95 % CPU ont etouffe
une machine worker (DriveFS tombe, puis Claudish, puis reboot du cluster). Cause
structurelle : chaque appelant lance ``lake``/``lean`` comme il peut, le lease
``.prover.lock`` n'est que par-arbre, et aucun timeout parent ne garantit la mort
de la descendance.

T1 (cette tranche de l'EPIC #15666) ajoute UNIQUEMENT ce qui empeche la recidive :

1. **Cap strict machine-wide** de la population ``lean``/``lake`` admise. L'etat
   vit hors de tout worktree, dans ``%LOCALAPPDATA%\\CoursIA\\lean_exec\\`` sur
   Windows / ``$XDG_STATE_HOME/coursia/lean_exec/`` sinon — meme chaine de
   resolution que ``scripts/genai-stack/commands/gpu.py:438`` (LOCALAPPDATA puis
   XDG_STATE_HOME puis ``~/.local/state``). Le cap se compte par machine, pas par
   arbre : deux worktrees distincts ne peuvent pas depasser ensemble le plafond.
2. **Confinement de l'arbre de processus** : Job Object Windows avec
   ``kill-on-close``, plafonds memoire/CPU et priorite reduite. La fermeture du
   handle (timeout, interruption, fin du superviseur, crash du parent) tue TOUTE
   la descendance. Sous POSIX/WSL : scope systemd si disponible, sinon
   ``setsid`` + ``kill(-pgid)``.
3. **Postcondition « zero descendant orphelin »** verifiee apres chaque run et
   visible en echec (exit 126 + liste des survivants). Un cleanup non prouve
   est un cleanup absent.

Le lease par arbre ``agent_tests/prover/tree_lock.py`` RESTE (second etage sous
l'admission machine-wide, pour l'exclusivite d'un acteur prover par arbre) ; cet
organe reprend sa logique de detection de peremption (pid_alive + host) plutot
que de la doubler.

Tout run passe par l'admission sous verrou machine-wide, impose un parallelisme
borne aux enfants (``LEAN_NUM_THREADS``, ``-Kjobs=N`` pour ``lake build``) et
publie ses metriques en JSON.

Codes de sortie stables :
  0    succes (commande terminee, nettoyage prouve)
  1    echec de la commande enfant (code reel dans le JSON)
  124  timeout (arbre tue, nettoyage prouve)
  125  admission refusee (cap atteint / environnement non mesurable)
  126  cleanup incomplet : orphelins detectes apres termination
  127  erreur interne a l'organe
  130  interruption (SIGINT) : arbre tue, nettoyage prouve

Env de configuration : ``LEAN_EXEC_STATE_DIR`` (isolation tests), ``LEAN_EXEC_CAP``,
``LEAN_EXEC_BUDGET``, ``LEAN_EXEC_JOBS``, ``LEAN_EXEC_MEM_FRAC``, ``LEAN_EXEC_CPU_PCT``.
"""

from __future__ import annotations

import argparse
import ctypes
import json
import os
import platform
import shutil
import signal
import subprocess
import sys
import time
import uuid
from pathlib import Path

EXIT_OK = 0
EXIT_CHILD = 1
EXIT_TIMEOUT = 124
EXIT_REFUSED = 125
EXIT_ORPHANS = 126
EXIT_INTERNAL = 127
EXIT_INTERRUPTED = 130

# winbase.h:416 -- CREATE_SUSPENDED n'est exporte ni par subprocess ni par
# _winapi (mesure Hermes c.5649329240 sur Modules/_winapi.c v3.13.5 : les
# cinq constantes CREATE_* exportees ne l'incluent pas, et le cycle
# suspendu->assigne->repris n'est pas completable en Python pur via _winapi).
# Valeur ABI Win32 stable depuis Windows NT : le litteral est la forme
# robuste. JAMAIS de getattr(..., 0) sur ce drapeau -- une retombee silencieuse
# lance la racine courante et fabrique un run vert non confine (reserve 1 de
# l'arbitrage #15666, issuecomment-5649841267).
CREATE_SUSPENDED = 0x00000004

LEAN_PROC_NAMES = {"lean", "lean.exe", "lake", "lake.exe"}

_STATE_SUBDIR_WIN = ("CoursIA", "lean_exec")
_STATE_SUBDIR_POSIX = ("coursia", "lean_exec")


# ---------------------------------------------------------------------------
# Etat machine-wide — meme chaine de resolution que gpu.py:438
# ---------------------------------------------------------------------------

def machine_state_base() -> Path:
    """Base d'etat user-scope, hors repo. Chaine identique a gpu.py:438
    (LOCALAPPDATA puis XDG_STATE_HOME puis ~/.local/state) — les deux autres
    sites (`scripts/genai-stack/commands/gpu.py`, `scripts/ci/install_prune_task.py:37`)
    l'inlinent avec un sous-repertoire different ; leur consolidation sur ce
    helper est un suivi hors T1 (perimetre = scripts/lean/lean_exec.py)."""
    return Path(
        os.environ.get("LOCALAPPDATA")
        or os.environ.get("XDG_STATE_HOME")
        or str(Path.home() / ".local" / "state")
    )


def state_dir() -> Path:
    """Repertoire d'etat machine-wide de l'organe, hors de tout worktree."""
    override = os.environ.get("LEAN_EXEC_STATE_DIR")
    if override:
        return Path(override)
    subdir = _STATE_SUBDIR_WIN if os.name == "nt" else _STATE_SUBDIR_POSIX
    return machine_state_base().joinpath(*subdir)


def runs_dir() -> Path:
    return state_dir() / "runs"


# ---------------------------------------------------------------------------
# Liveness pid — reprise de tree_lock.py:51-74 (jamais os.kill(pid, 0) sur
# Windows : CPython y TERMINE le processus cible ; probe ctypes a la place).
# ---------------------------------------------------------------------------

_STILL_ACTIVE = 259
_PROCESS_QUERY_LIMITED_INFORMATION = 0x1000


def host_id() -> str:
    """Identite du namespace de pids (tree_lock.py:46-48) — les pids Windows
    et WSL vivent dans des namespaces separes."""
    return f"{platform.node()}/{os.name}"


def pid_alive(pid: int) -> bool:
    """True si ``pid`` est vivant sur CE host (tree_lock.py:51-74)."""
    if pid <= 0:
        return False
    if os.name == "nt":
        kernel32 = ctypes.windll.kernel32
        handle = kernel32.OpenProcess(
            _PROCESS_QUERY_LIMITED_INFORMATION, False, pid
        )
        if not handle:
            return False
        try:
            exit_code = ctypes.c_ulong()
            ok = kernel32.GetExitCodeProcess(handle, ctypes.byref(exit_code))
            return bool(ok) and exit_code.value == _STILL_ACTIVE
        finally:
            kernel32.CloseHandle(handle)
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


# ---------------------------------------------------------------------------
# Scan de population machine-wide lean/lake
# ---------------------------------------------------------------------------

def _count_from_lines(lines: list[str]) -> int:
    n = 0
    for line in lines:
        name = line.strip().strip('"').split(",")[0].strip('"')
        name = name.rsplit("\\", 1)[-1].rsplit("/", 1)[-1]
        if name.lower() in LEAN_PROC_NAMES:
            n += 1
    return n


def scan_native_population() -> tuple[int, str]:
    """Compte les lean/lake vivants cote natif. Echec = mesurable=false."""
    try:
        if os.name == "nt":
            out = subprocess.run(
                ["tasklist", "/FO", "CSV", "/NH"],
                capture_output=True, text=True, timeout=15,
                encoding="utf-8", errors="replace",
                creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0),
            )
            names = [
                ln.split('","')[0].strip('"') if ln.strip() else ln
                for ln in out.stdout.splitlines()
            ]
            return _count_from_lines(names), "tasklist"
        out = subprocess.run(
            ["ps", "-eo", "comm="], capture_output=True, text=True, timeout=15,
            encoding="utf-8", errors="replace",
        )
        return _count_from_lines(out.stdout.splitlines()), "ps"
    except (OSError, subprocess.SubprocessError) as exc:
        return -1, f"unavailable: {exc}"


def scan_wsl_population() -> tuple[int, str]:
    """Best-effort : population lean/lake cote WSL vu depuis Windows.
    WSL absent -> (0, "off"). Sonde morte -> (-1, raison) sans bloquer
    l'admission native (rapporte dans le JSON)."""
    if os.name != "nt":
        return 0, "off"
    if os.environ.get("LEAN_EXEC_WSL", "").lower() in ("off", "0", "no"):
        return 0, "off"
    if shutil.which("wsl.exe") is None:
        return 0, "off"
    try:
        out = subprocess.run(
            ["wsl.exe", "--", "ps", "-eo", "comm="],
            capture_output=True, timeout=10,
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0),
        )
        raw = out.stdout
        for enc in ("utf-8", "utf-16-le"):
            try:
                text = raw.decode(enc)
                break
            except UnicodeDecodeError:
                continue
        else:
            text = raw.decode("utf-8", errors="replace")
        return _count_from_lines(text.splitlines()), "wsl ps"
    except (OSError, subprocess.SubprocessError) as exc:
        return -1, f"unavailable: {exc}"


# ---------------------------------------------------------------------------
# Registre des runs — staleness reprise de tree_lock.py:122-151
# ---------------------------------------------------------------------------

def read_run(path: Path) -> dict:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}


def sweep_stale_runs() -> list[str]:
    """Retire les runs dont le pid racine est mort sur CE host. Un run d'un
    host etranger n'est JAMAIS auto-retire (pids non comparables entre
    namespaces, cf tree_lock.py:138) — il ne compte pas non plus comme vivant
    pour le budget : seul un pid vivant du meme host est credible."""
    swept = []
    try:
        paths = list(runs_dir().glob("*.json"))
    except OSError:
        return swept
    for path in paths:
        run = read_run(path)
        pid = int(run.get("pid") or -1)
        h = run.get("host", "<unreadable>")
        if h == host_id() and not pid_alive(pid):
            try:
                path.unlink()
                swept.append(path.stem)
            except OSError:
                pass
    return swept


def live_registered_budgets() -> tuple[int, list[dict]]:
    """Somme des budgets des runs vivants (meme host, pid vivant)."""
    total = 0
    live = []
    try:
        paths = list(runs_dir().glob("*.json"))
    except OSError:
        return 0, live
    for path in paths:
        run = read_run(path)
        if run.get("host") != host_id():
            continue
        if not pid_alive(int(run.get("pid") or -1)):
            continue
        total += max(1, int(run.get("budget") or 1))
        live.append(run)
    return total, live


# ---------------------------------------------------------------------------
# Verrou d'admission machine-wide (ferme la fenetre TOCTOU count->spawn)
# ---------------------------------------------------------------------------

class AdmissionLock:
    """Verrou fichier exclusif dans le state dir : ouvre, lock non-bloquant
    en boucle bornee, unlock/close. msvcrt cote Windows, fcntl cote POSIX."""

    def __init__(self, timeout_s: float = 10.0):
        self.path = state_dir() / "admission.lock"
        self.timeout_s = timeout_s
        self._fh = None

    def __enter__(self) -> "AdmissionLock":
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self._fh = open(self.path, "a+b")
        deadline = time.monotonic() + self.timeout_s
        while True:
            if _try_lock(self._fh):
                return self
            if time.monotonic() >= deadline:
                self._fh.close()
                self._fh = None
                raise TimeoutError(
                    f"admission lock busy: {self.path}"
                )
            time.sleep(0.05)

    def __exit__(self, *exc) -> None:
        if self._fh is not None:
            _unlock(self._fh)
            self._fh.close()
            self._fh = None


if os.name == "nt":
    import msvcrt

    def _try_lock(fh) -> bool:
        try:
            msvcrt.locking(fh.fileno(), msvcrt.LK_NBLCK, 1)
            return True
        except OSError:
            return False

    def _unlock(fh) -> None:
        try:
            fh.seek(0)
            msvcrt.locking(fh.fileno(), msvcrt.LK_UNLCK, 1)
        except OSError:
            pass
else:
    import fcntl

    def _try_lock(fh) -> bool:
        try:
            fcntl.flock(fh.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            return True
        except OSError:
            return False

    def _unlock(fh) -> None:
        try:
            fcntl.flock(fh.fileno(), fcntl.LOCK_UN)
        except OSError:
            pass


# ---------------------------------------------------------------------------
# Confinement Windows — Job Object kill-on-close + plafonds + priorite
# ---------------------------------------------------------------------------

if os.name == "nt":
    class _JOBOBJECT_BASIC_LIMIT_INFORMATION(ctypes.Structure):
        _fields_ = [
            ("PerProcessUserTimeLimit", ctypes.c_longlong),
            ("PerJobUserTimeLimit", ctypes.c_longlong),
            ("LimitFlags", ctypes.c_ulong),
            ("MinimumWorkingSetSize", ctypes.c_size_t),
            ("MaximumWorkingSetSize", ctypes.c_size_t),
            ("ActiveProcessLimit", ctypes.c_ulong),
            ("Affinity", ctypes.c_size_t),
            ("PriorityClass", ctypes.c_ulong),
            ("SchedulingClass", ctypes.c_ulong),
        ]

    class _IO_COUNTERS(ctypes.Structure):
        _fields_ = [(n, ctypes.c_ulonglong) for n in (
            "ReadOperationCount", "WriteOperationCount", "OtherOperationCount",
            "ReadTransferCount", "WriteTransferCount", "OtherTransferCount",
        )]

    class _JOBOBJECT_EXTENDED_LIMIT_INFORMATION(ctypes.Structure):
        _fields_ = [
            ("BasicLimitInformation", _JOBOBJECT_BASIC_LIMIT_INFORMATION),
            ("IoInfo", _IO_COUNTERS),
            ("ProcessMemoryLimit", ctypes.c_size_t),
            ("JobMemoryLimit", ctypes.c_size_t),
            ("PeakProcessMemoryUsed", ctypes.c_size_t),
            ("PeakJobMemoryUsed", ctypes.c_size_t),
        ]

    class _JOBOBJECT_CPU_RATE_CONTROL_INFORMATION(ctypes.Structure):
        # union { DWORD CpuRate; DWORD Weight; } -> un seul DWORD (8o total) ;
        # une Structure imbriquee donnerait 12o et l'API rejetterait.
        _fields_ = [
            ("ControlFlags", ctypes.c_ulong),
            ("CpuRate", ctypes.c_ulong),
        ]

    class _MEMORYSTATUSEX(ctypes.Structure):
        _fields_ = [
            ("dwLength", ctypes.c_ulong),
            ("dwMemoryLoad", ctypes.c_ulong),
            ("ullTotalPhys", ctypes.c_ulonglong),
            ("ullAvailPhys", ctypes.c_ulonglong),
            ("ullTotalPageFile", ctypes.c_ulonglong),
            ("ullAvailPageFile", ctypes.c_ulonglong),
            ("ullTotalVirtual", ctypes.c_ulonglong),
            ("ullAvailVirtual", ctypes.c_ulonglong),
            ("ullAvailExtendedVirtual", ctypes.c_ulonglong),
        ]

    JOB_OBJECT_LIMIT_PRIORITY_CLASS = 0x00000020
    JOB_OBJECT_LIMIT_PROCESS_MEMORY = 0x00000100
    JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE = 0x00002000
    BELOW_NORMAL_PRIORITY_CLASS = 0x00004000
    JOB_OBJECT_CPU_RATE_CONTROL_ENABLE = 0x00000001
    JOB_OBJECT_CPU_RATE_CONTROL_HARD_CAP = 0x00000004
    JobObjectExtendedLimitInformation = 9
    JobObjectCpuRateControlInformation = 15
    JobObjectBasicProcessIdList = 3
    PROCESS_TERMINATE = 0x0001
    PROCESS_SET_QUOTA = 0x0100

    def _total_physical_bytes() -> int:
        stat = _MEMORYSTATUSEX()
        stat.dwLength = ctypes.sizeof(stat)
        ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(stat))
        return int(stat.ullTotalPhys)


class WindowsJob:
    """Job Object kill-on-close. Le handle reste ouvert pendant tout le run :
    si le superviseur meurt (crash, kill -9), Windows tue l'arbre lui-meme."""

    def __init__(self, mem_frac: float, cpu_pct: int):
        self.handle = None
        self.ok = False
        self.reason = ""
        k32 = ctypes.windll.kernel32
        self._k32 = k32
        handle = k32.CreateJobObjectW(None, None)
        if not handle:
            self.reason = "CreateJobObjectW failed"
            return
        mem_limit = int(_total_physical_bytes() * mem_frac)
        info = _JOBOBJECT_EXTENDED_LIMIT_INFORMATION()
        info.BasicLimitInformation.LimitFlags = (
            JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE
            | JOB_OBJECT_LIMIT_PRIORITY_CLASS
            | JOB_OBJECT_LIMIT_PROCESS_MEMORY
        )
        info.BasicLimitInformation.PriorityClass = BELOW_NORMAL_PRIORITY_CLASS
        info.ProcessMemoryLimit = mem_limit
        if not k32.SetInformationJobObject(
            handle, JobObjectExtendedLimitInformation,
            ctypes.byref(info), ctypes.sizeof(info),
        ):
            self.reason = "SetInformationJobObject(extended) failed"
            k32.CloseHandle(handle)
            return
        rate = _JOBOBJECT_CPU_RATE_CONTROL_INFORMATION()
        rate.ControlFlags = (
            JOB_OBJECT_CPU_RATE_CONTROL_ENABLE
            | JOB_OBJECT_CPU_RATE_CONTROL_HARD_CAP
        )
        rate.CpuRate = cpu_pct * 100
        if not k32.SetInformationJobObject(
            handle, JobObjectCpuRateControlInformation,
            ctypes.byref(rate), ctypes.sizeof(rate),
        ):
            # Plafond CPU non pose : le kill-tree + priorite restent valides.
            self.reason = "cpu-rate-cap-unavailable"
        self.handle = handle
        self.ok = True

    def assign(self, pid: int) -> bool:
        k32 = self._k32
        hproc = k32.OpenProcess(
            PROCESS_TERMINATE | PROCESS_SET_QUOTA, False, pid
        )
        if not hproc:
            self.reason = "OpenProcess failed"
            return False
        try:
            if not k32.AssignProcessToJobObject(self.handle, hproc):
                # Nesting de jobs incompatible (parent deja dans un job sans
                # breakaway) : on continue sans confinement job, le fallback
                # PPID-chain prendra le relais a la termination.
                self.reason = "assign-failed-nested-job"
                return False
            return True
        finally:
            k32.CloseHandle(hproc)

    def member_pids(self) -> list[int]:
        k32 = self._k32
        cap = 512
        class _LIST(ctypes.Structure):
            _fields_ = [
                ("NumberOfAssignedProcesses", ctypes.c_ulong),
                ("NumberOfProcessIdsInList", ctypes.c_ulong),
                ("ProcessIdList", ctypes.c_size_t * cap),
            ]
        buf = _LIST()
        buf.NumberOfAssignedProcesses = cap
        if not k32.QueryInformationJobObject(
            self.handle, JobObjectBasicProcessIdList,
            ctypes.byref(buf), ctypes.sizeof(buf), None,
        ):
            return []
        n = buf.NumberOfProcessIdsInList
        return [int(buf.ProcessIdList[i]) for i in range(min(n, cap))]

    def terminate(self) -> None:
        self._k32.TerminateJobObject(self.handle, 1)

    def close(self) -> None:
        if self.handle:
            self._k32.CloseHandle(self.handle)
            self.handle = None


# ---------------------------------------------------------------------------
# Terminaison par chaine PPID — fallback sans Job Object ET sonde d'orphelins
# ---------------------------------------------------------------------------

def snapshot_processes() -> dict[int, int]:
    """{pid: ppid} de tous les processus. Windows: Toolhelp32Snapshot.
    POSIX: ps -o pid=,ppid=."""
    table: dict[int, int] = {}
    if os.name == "nt":
        k32 = ctypes.windll.kernel32
        TH32CS_SNAPPROCESS = 0x00000002

        class _PE(ctypes.Structure):
            _fields_ = [
                ("dwSize", ctypes.c_ulong),
                ("cntUsage", ctypes.c_ulong),
                ("th32ProcessID", ctypes.c_ulong),
                ("th32DefaultHeapID", ctypes.c_size_t),
                ("th32ModuleID", ctypes.c_ulong),
                ("cntThreads", ctypes.c_ulong),
                ("th32ParentProcessID", ctypes.c_ulong),
                ("pcPriClassBase", ctypes.c_long),
                ("dwFlags", ctypes.c_ulong),
                ("szExeFile", ctypes.c_char * 260),
            ]

        snap = k32.CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0)
        if snap == -1 or not snap:
            return table
        try:
            entry = _PE()
            entry.dwSize = ctypes.sizeof(entry)
            if k32.Process32First(snap, ctypes.byref(entry)):
                while True:
                    table[int(entry.th32ProcessID)] = int(
                        entry.th32ParentProcessID
                    )
                    if not k32.Process32Next(snap, ctypes.byref(entry)):
                        break
        finally:
            k32.CloseHandle(snap)
    else:
        out = subprocess.run(
            ["ps", "-eo", "pid=,ppid="],
            capture_output=True, text=True, timeout=15,
            encoding="utf-8", errors="replace",
        )
        for line in out.stdout.splitlines():
            parts = line.split()
            if len(parts) == 2:
                try:
                    table[int(parts[0])] = int(parts[1])
                except ValueError:
                    continue
    return table


def resume_process(pid: int) -> int:
    """Reprend un processus cree suspendu (CREATE_SUSPENDED) : resume chaque
    thread du pid. Necessaire pour que la racine n'execute rien avant d'etre
    assignee au Job Object — c'est ce qui ferme la fenetre ou un enfant
    pourrait naitre hors du job."""
    if os.name != "nt":
        return 0
    k32 = ctypes.windll.kernel32
    TH32CS_SNAPTHREAD = 0x00000004
    THREAD_SUSPEND_RESUME = 0x0002

    class _TE(ctypes.Structure):
        _fields_ = [
            ("dwSize", ctypes.c_ulong),
            ("cntUsage", ctypes.c_ulong),
            ("th32ThreadID", ctypes.c_ulong),
            ("th32OwnerProcessID", ctypes.c_ulong),
            ("tpBasePri", ctypes.c_long),
            ("tpDeltaPri", ctypes.c_long),
            ("dwFlags", ctypes.c_ulong),
        ]

    snap = k32.CreateToolhelp32Snapshot(TH32CS_SNAPTHREAD, 0)
    if not snap or snap == -1:
        return 0
    resumed = 0
    try:
        entry = _TE()
        entry.dwSize = ctypes.sizeof(entry)
        if k32.Thread32First(snap, ctypes.byref(entry)):
            while True:
                if entry.th32OwnerProcessID == pid:
                    h = k32.OpenThread(
                        THREAD_SUSPEND_RESUME, False, entry.th32ThreadID
                    )
                    if h:
                        k32.ResumeThread(h)
                        k32.CloseHandle(h)
                        resumed += 1
                if not k32.Thread32Next(snap, ctypes.byref(entry)):
                    break
    finally:
        k32.CloseHandle(snap)
    return resumed


def descendants_of(root_pid: int, table: dict[int, int] | None = None) -> set[int]:
    """Descendants vivants de ``root_pid``. Sous Windows un orphelin GARDE le
    pid de son parent mort comme PPID : la chaine reste donc traicable meme
    apres la mort de la racine et des intermediaires."""
    table = table if table is not None else snapshot_processes()
    children: dict[int, list[int]] = {}
    for pid, ppid in table.items():
        children.setdefault(ppid, []).append(pid)
    found: set[int] = set()
    frontier = list(children.get(root_pid, []))
    while frontier:
        pid = frontier.pop()
        if pid in found:
            continue
        found.add(pid)
        frontier.extend(children.get(pid, []))
    return found


def kill_pids(pids: list[int]) -> None:
    if os.name == "nt":
        k32 = ctypes.windll.kernel32
        for pid in pids:  # bottom-up fourni par l'appelant
            hproc = k32.OpenProcess(PROCESS_TERMINATE, False, pid)
            if hproc:
                k32.TerminateProcess(hproc, 1)
                k32.CloseHandle(hproc)
    else:
        for pid in pids:
            try:
                os.kill(pid, signal.SIGKILL)
            except OSError:
                pass


def find_orphans(root_pid: int, job: "WindowsJob | None") -> list[int]:
    """Postcondition : orphelins = job non vide apres grace, OU descendants
    vivants de la racine (chaine PPID) encore presents."""
    orphans: set[int] = set()
    if os.name == "nt" and job is not None and job.handle:
        orphans.update(job.member_pids())
    table = snapshot_processes()
    orphans.update(
        p for p in descendants_of(root_pid, table) if p in table
    )
    return sorted(orphans)


# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

def config() -> dict:
    cpu = os.cpu_count() or 4
    return {
        "cap": int(os.environ.get("LEAN_EXEC_CAP", max(2, min(8, cpu // 2)))),
        "budget": int(os.environ.get("LEAN_EXEC_BUDGET", 2)),
        "jobs": int(os.environ.get("LEAN_EXEC_JOBS", max(1, cpu // 4))),
        "mem_frac": float(os.environ.get("LEAN_EXEC_MEM_FRAC", 0.80)),
        "cpu_pct": int(os.environ.get("LEAN_EXEC_CPU_PCT", 90)),
    }


def bound_command(cmd: list[str], jobs: int) -> list[str]:
    """Parallelisme explicitement borne (regle interim de flotte #15666) :
    ``-Kjobs=N`` insere pour ``lake build`` nu, le flag reste decidable."""
    if (
        len(cmd) >= 2
        and cmd[0].rsplit("\\", 1)[-1].rsplit("/", 1)[-1].lower()
        in ("lake", "lake.exe")
        and cmd[1] == "build"
        and not any(a.startswith("-K") or a.startswith("--jobs")
                    for a in cmd[2:])
    ):
        return [cmd[0], cmd[1], f"-Kjobs={jobs}", *cmd[2:]]
    return cmd


# ---------------------------------------------------------------------------
# Le run
# ---------------------------------------------------------------------------

def _write_run_record(run_id: str, record: dict) -> Path:
    runs_dir().mkdir(parents=True, exist_ok=True)
    path = runs_dir() / f"{run_id}.json"
    path.write_text(json.dumps(record, indent=2), encoding="utf-8")
    return path


def _remove_run_record(run_id: str) -> None:
    try:
        (runs_dir() / f"{run_id}.json").unlink()
    except OSError:
        pass


def _emit(result: dict, as_json: bool) -> int:
    state_dir().mkdir(parents=True, exist_ok=True)
    (state_dir() / "last_run.json").write_text(
        json.dumps(result, indent=2), encoding="utf-8"
    )
    if as_json:
        print(json.dumps(result, indent=2))
    else:
        print(
            f"[lean_exec] {result['status']} exit={result['exit_code']} "
            f"duration={result.get('duration_s', 0):.1f}s "
            f"orphans={len(result.get('orphans', []))}",
            file=sys.stderr,
        )
        for key in ("child_exit_code", "reason", "budget_violation"):
            if result.get(key) is not None:
                print(f"[lean_exec] {key}: {result[key]}", file=sys.stderr)
    return result["exit_code"]


def run_command(
    cmd: list[str],
    timeout_s: float | None = None,
    cap_override: int | None = None,
    budget_override: int | None = None,
    as_json: bool = False,
) -> int:
    cfg = config()
    cap = cap_override if cap_override is not None else cfg["cap"]
    budget = budget_override if budget_override is not None else cfg["budget"]
    run_id = uuid.uuid4().hex[:12]
    started = time.time()

    result: dict = {
        "run_id": run_id,
        "cmd": cmd,
        "backend": "windows-job" if os.name == "nt" else "posix",
        "cap": cap,
        "budget": budget,
        "jobs": cfg["jobs"],
        "orphans": [],
        "child_exit_code": None,
        "budget_violation": None,
        "reason": None,
        "duration_s": 0.0,
        "population_before": None,
    }

    # --- Admission machine-wide sous verrou (ferme count->spawn TOCTOU) ---
    try:
        with AdmissionLock():
            swept = sweep_stale_runs()
            native_pop, native_src = scan_native_population()
            if native_pop < 0:
                # Fail-closed : impossible de compter = impossible de plafonner.
                result.update(
                    status="refused", exit_code=EXIT_REFUSED,
                    reason=f"population unmeasurable ({native_src})",
                )
                return _emit(result, as_json)
            registered, _live = live_registered_budgets()
            if native_pop + budget > cap:
                result.update(
                    status="refused", exit_code=EXIT_REFUSED,
                    reason=(
                        f"machine-wide cap {cap}: native population "
                        f"{native_pop} + requested budget {budget} > cap"
                    ),
                    population_before={"native": native_pop},
                )
                return _emit(result, as_json)
            if registered + budget > cap:
                result.update(
                    status="refused", exit_code=EXIT_REFUSED,
                    reason=(
                        f"machine-wide cap {cap}: live registered budgets "
                        f"{registered} + requested budget {budget} > cap"
                    ),
                    population_before={"native": native_pop},
                )
                return _emit(result, as_json)

            env = os.environ.copy()
            env.setdefault("LEAN_NUM_THREADS", str(cfg["jobs"]))
            spawn_cmd = bound_command(cmd, cfg["jobs"])
            result["cmd_effective"] = spawn_cmd

            job = None
            popen_kwargs: dict = {"env": env}
            if os.name == "nt":
                job = WindowsJob(cfg["mem_frac"], cfg["cpu_pct"])
                # SUSPENDED -> assign -> resume : la racine est dans le job
                # AVANT de pouvoir exécuter la moindre instruction, aucun
                # enfant ne peut naitre hors du job.
                popen_kwargs["creationflags"] = (
                    getattr(subprocess, "CREATE_NO_WINDOW", 0) | CREATE_SUSPENDED
                )
            else:
                popen_kwargs["start_new_session"] = True

            try:
                proc = subprocess.Popen(spawn_cmd, **popen_kwargs)
            except OSError as exc:
                if job:
                    job.close()
                result.update(
                    status="refused", exit_code=EXIT_REFUSED,
                    reason=f"spawn failed: {exc}",
                )
                return _emit(result, as_json)

            confined = True
            if job is not None:
                if not job.ok or not job.assign(proc.pid):
                    confined = False
                    result["backend"] = f"windows-fallback ({job.reason})"
                # La racine n'execute rien tant qu'elle n'est pas dans le job.
                n_resumed = resume_process(proc.pid)
                result["threads_resumed"] = n_resumed
                if n_resumed == 0:
                    # Reserve 1 (arbitrage #15666) : un root cree suspendu et
                    # non repris n'a PAS ete confine -- l'echec doit invalider
                    # le run, pas decorer le backend d'un suffixe vert. Le root
                    # est encore suspendu : on tue le job avant de rendre
                    # l'echec (meme ordre que terminate_tree).
                    confined = False
                    if job is not None and job.handle:
                        job.terminate()
                        time.sleep(1.0)
                    kill_pids(sorted(descendants_of(proc.pid), reverse=True))
                    result.update(
                        status="internal-error",
                        exit_code=EXIT_INTERNAL,
                        reason=(
                            "resume_process resumed 0 threads: the root was "
                            "spawned with CREATE_SUSPENDED and could not be "
                            "resumed -- confinement is NOT delivered"
                        ),
                        backend=f"{result['backend']}-resume-failed",
                    )
                    return _emit(result, as_json)

            _write_run_record(run_id, {
                "pid": proc.pid,
                "host": host_id(),
                "cmd": cmd,
                "cwd": os.getcwd(),
                "budget": budget,
                "cap": cap,
                "started_utc": time.strftime(
                    "%Y-%m-%dT%H:%M:%SZ", time.gmtime()
                ),
                "started_epoch": started,
                "confined": confined,
            })
            result["population_before"] = {
                "native": native_pop,
                "wsl": scan_wsl_population()[0],
            }
    except TimeoutError as exc:
        result.update(
            status="refused", exit_code=EXIT_REFUSED, reason=str(exc)
        )
        return _emit(result, as_json)

    # --- Supervision : timeout / interruption / violation de budget ---
    def terminate_tree() -> list[int]:
        """Tue l'arbre par tous les moyens, puis verifie la postcondition."""
        if os.name == "nt":
            if confined and job is not None and job.handle:
                job.terminate()
                time.sleep(1.0)
            kill_pids(sorted(descendants_of(proc.pid), reverse=True))
        else:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except OSError:
                pass
            kill_pids(sorted(descendants_of(proc.pid), reverse=True))
        orphans = []
        for _ in range(4):  # grace ~6 s, re-sonde
            time.sleep(1.5)
            orphans = find_orphans(proc.pid, job if confined else None)
            if not orphans:
                break
            kill_pids(orphans)
        return orphans

    status = "ok"
    child_exit = None
    killed = False
    orphans: list[int] = []
    try:
        while True:
            try:
                child_exit = proc.wait(timeout=2.0)
                break
            except subprocess.TimeoutExpired:
                if timeout_s is not None and time.time() - started > timeout_s:
                    status = "timeout"
                    killed = True
                    orphans = terminate_tree()
                    break
                # Budget supervise : ce run ne doit jamais heberger plus de
                # lean/lake vivants que son budget declare.
                if confined and os.name == "nt" and job is not None:
                    table = snapshot_processes()
                    own = sum(
                        1 for p in descendants_of(proc.pid, table)
                        if _proc_name(p, table) in LEAN_PROC_NAMES
                    )
                    if own > budget:
                        result["budget_violation"] = (
                            f"{own} lean/lake descendants > budget {budget}"
                        )
                        status = "timeout"
                        killed = True
                        orphans = terminate_tree()
                        break
    except KeyboardInterrupt:
        status = "interrupted"
        killed = True
        orphans = terminate_tree()

    # --- Postcondition finale : zero descendant orphelin, echec visible ---
    if not killed:
        for _ in range(2):
            time.sleep(1.0)
            orphans = find_orphans(proc.pid, job if confined else None)
            if not orphans:
                break
            kill_pids(orphans)
        time.sleep(1.0)
        orphans = find_orphans(proc.pid, job if confined else None)
        if orphans:
            kill_pids(orphans)
            time.sleep(1.5)
            orphans = find_orphans(proc.pid, job if confined else None)

    if job is not None:
        job.close()  # kill-on-close : dernier filet, meme sur chemin lent
    _remove_run_record(run_id)

    result.update({
        "pid": proc.pid,
        "status": status,
        "child_exit_code": child_exit,
        "killed": killed,
        "orphans": orphans,
        "duration_s": round(time.time() - started, 2),
    })
    if orphans:
        result["exit_code"] = EXIT_ORPHANS
        result["reason"] = f"cleanup incomplete: survivors {orphans}"
    elif status == "timeout":
        result["exit_code"] = EXIT_TIMEOUT
    elif status == "interrupted":
        result["exit_code"] = EXIT_INTERRUPTED
    elif child_exit is not None and child_exit != 0:
        result["exit_code"] = EXIT_CHILD
        result["status"] = "child_failed"
    else:
        result["exit_code"] = EXIT_OK
    return _emit(result, as_json)


def _proc_name(pid: int, _table: dict[int, int]) -> str:
    """Nom executable d'un pid (best-effort, pour le filtre lean/lake)."""
    try:
        if os.name == "nt":
            out = subprocess.run(
                ["tasklist", "/FI", f"PID eq {pid}", "/FO", "CSV", "/NH"],
                capture_output=True, text=True, timeout=10,
                encoding="utf-8", errors="replace",
                creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0),
            )
            for line in out.stdout.splitlines():
                if line.strip():
                    return line.split('","')[0].strip('"').lower()
            return ""
        out = subprocess.run(
            ["ps", "-o", "comm=", "-p", str(pid)],
            capture_output=True, text=True, timeout=10,
            encoding="utf-8", errors="replace",
        )
        return out.stdout.strip().lower()
    except (OSError, subprocess.SubprocessError):
        return ""


# ---------------------------------------------------------------------------
# status
# ---------------------------------------------------------------------------

def status(as_json: bool = False) -> int:
    cfg = config()
    swept = sweep_stale_runs()
    native_pop, native_src = scan_native_population()
    wsl_pop, wsl_src = scan_wsl_population()
    _registered, live = live_registered_budgets()
    payload = {
        "state_dir": str(state_dir()),
        "config": cfg,
        "population": {
            "native": native_pop, "native_src": native_src,
            "wsl": wsl_pop, "wsl_src": wsl_src,
        },
        "live_runs": live,
        "swept_stale": swept,
        "headroom": max(0, cfg["cap"] - native_pop),
    }
    if as_json:
        print(json.dumps(payload, indent=2))
    else:
        print(f"state: {payload['state_dir']}")
        print(
            f"population: native={native_pop} ({native_src}) "
            f"wsl={wsl_pop} ({wsl_src}) cap={cfg['cap']}"
        )
        print(f"live runs: {len(live)} (swept {len(swept)} stale)")
    return EXIT_OK


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Organe d'execution Lean confine (T1, See #15666)"
    )
    sub = parser.add_subparsers(dest="action")

    p_run = sub.add_parser("run", help="Executer une commande lean/lake confinee")
    p_run.add_argument("--timeout", type=float, default=None,
                       help="Timeout en secondes (l'arbre entier meurt)")
    p_run.add_argument("--cap", type=int, default=None,
                       help="Cap machine-wide pour CE run uniquement")
    p_run.add_argument("--budget", type=int, default=None,
                       help="Budget lean/lake max de ce run")
    p_run.add_argument("--json", action="store_true",
                       help="Resultat JSON sur stdout")
    p_run.add_argument("cmd", nargs=argparse.REMAINDER,
                       help="commande apres --")

    p_status = sub.add_parser("status", help="Population, cap, runs vivants")
    p_status.add_argument("--json", action="store_true")

    args = parser.parse_args(argv)
    try:
        if args.action == "status":
            return status(as_json=args.json)
        if args.action == "run":
            cmd = args.cmd
            if cmd and cmd[0] == "--":
                cmd = cmd[1:]
            if not cmd:
                parser.error("run: commande requise (run -- lake build ...)")
            return run_command(
                cmd, timeout_s=args.timeout, cap_override=args.cap,
                budget_override=args.budget, as_json=args.json,
            )
    except Exception as exc:  # l'organe echoue visiblement, jamais en trace
        print(f"[lean_exec] internal error: {exc}", file=sys.stderr)
        return EXIT_INTERNAL
    parser.print_help()
    return EXIT_INTERNAL


if __name__ == "__main__":
    sys.exit(main())
