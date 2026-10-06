#!/usr/bin/env python3
"""Lance une commande longue sous deux plafonds durs : RAM du processus, RAM libre machine.

Incident fondateur -- 2026-10-05, po-2023 : un run de mesure de 6 h (banc
sigma/K sur Qwen3.5-27B, #18112) a retenu 38,6 Go et porte la machine a 99,3 %
(0,43 Go libres, commit 181,7/210,7 Go), en trajectoire identique au BSOD de la
veille. Le processus etait de surcroit **orphelin** -- session parente morte,
plus personne pour surveiller sa fin -- et **aucun garde ne l'a arrete** : la
non-recidive a tenu a la chance (il s'est fini seul a 12:56), pas a un
mecanisme.

Ce lanceur remplace la chance par deux mecanismes independants :

1. **plafonds durs** -- si le RSS cumule du processus et de ses descendants
   depasse ``--limit-gib``, ou si la RAM physique disponible de la machine
   passe sous ``--reserve-gib``, l'arbre est tue et le lanceur sort en 3
   (plafond processus) ou 4 (plancher machine) ;
2. **anti-orphelin** -- sous Windows, l'enfant est place dans un Job Object
   ``KILL_ON_JOB_CLOSE`` : si CE lanceur meurt (session fermee, kill -9,
   crash), le systeme tue l'enfant. Un run ne survit plus a son observateur.

Le rapport de fin (pic de RSS, minimum de RAM libre, raison de l'arret) part
dans le journal : un run garde se relit avec son enveloppe de ressources.

Usage :
    python scripts/ci/run_guarded.py --limit-gib 24 --reserve-gib 4 \\
        --log runs/27b.log -- python measure_sigma_jailbreak_bridge.py --full ...

Codes de sortie : 0 commande terminee sous les deux plafonds · 3 plafond
processus franchi · 4 plancher machine franchi · 5 demarrage refuse (RAM libre
insuffisante, ou Job Object indisponible sans ``--allow-no-job``) · 6 la
commande n'a pas demarre · 130 interruption clavier · sinon le code de sortie
de la commande.
"""
import argparse
import os
import subprocess
import sys
import time
from pathlib import Path

GiB = 2**30

RC_OK = 0
RC_LIMIT = 3
RC_FLOOR = 4
RC_REFUSED = 5
RC_NOSTART = 6
RC_INTERRUPT = 130


def _win_job_kill_on_close():
    """Job Object Windows avec ``KILL_ON_JOB_CLOSE`` (anti-orphelin structurel).

    Retourne ``(job, kernel32)`` ou ``None`` si indisponible. L'enfant assigne
    a ce job est tue par le systeme des que le handle se ferme -- c'est-a-dire
    des que ce lanceur meurt, quelle qu'en soit la cause (fermeture de session,
    kill -9, crash). Sans ce job, un enfant survit a son observateur : c'est
    exactement le mode de defaillance de l'incident du 2026-10-05.
    """
    if os.name != "nt":
        return None
    import ctypes
    from ctypes import wintypes

    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)

    class _IoCounters(ctypes.Structure):
        _fields_ = [(n, ctypes.c_ulonglong) for n in (
            "ReadOperationCount", "WriteOperationCount", "OtherOperationCount",
            "ReadTransferCount", "WriteTransferCount", "OtherTransferCount")]

    class _BasicLimit(ctypes.Structure):
        _fields_ = [("PerProcessUserTimeLimit", ctypes.c_longlong),
                    ("PerJobUserTimeLimit", ctypes.c_longlong),
                    ("LimitFlags", wintypes.DWORD),
                    ("MinimumWorkingSetSize", ctypes.c_size_t),
                    ("MaximumWorkingSetSize", ctypes.c_size_t),
                    ("ActiveProcessLimit", wintypes.DWORD),
                    ("Affinity", ctypes.c_size_t),      # ULONG_PTR
                    ("PriorityClass", wintypes.DWORD),
                    ("SchedulingClass", wintypes.DWORD)]

    class _ExtLimit(ctypes.Structure):
        _fields_ = [("BasicLimitInformation", _BasicLimit),
                    ("IoInfo", _IoCounters),
                    ("ProcessMemoryLimit", ctypes.c_size_t),
                    ("JobMemoryLimit", ctypes.c_size_t),
                    ("PeakProcessMemoryUsed", ctypes.c_size_t),
                    ("PeakJobMemoryUsed", ctypes.c_size_t)]

    kernel32.CreateJobObjectW.restype = wintypes.HANDLE
    kernel32.CreateJobObjectW.argtypes = [ctypes.c_void_p, wintypes.LPCWSTR]
    job = kernel32.CreateJobObjectW(None, None)
    if not job:
        return None
    info = _ExtLimit()
    info.BasicLimitInformation.LimitFlags = 0x2000      # KILL_ON_JOB_CLOSE
    if not kernel32.SetInformationJobObject(
            job, 9, ctypes.byref(info), ctypes.sizeof(info)):   # 9=Extended
        return None
    return job, kernel32


def _assign_to_job(handle_pair, proc):
    """Assigne l'enfant au Job Object. False si le systeme refuse."""
    if handle_pair is None:
        return False
    import ctypes
    from ctypes import wintypes

    job, kernel32 = handle_pair
    kernel32.AssignProcessToJobObject.argtypes = [wintypes.HANDLE, wintypes.HANDLE]
    return bool(kernel32.AssignProcessToJobObject(
        job, wintypes.HANDLE(int(proc._handle))))


def _rss_bytes(pid):
    """RSS cumule du processus et de ses descendants (0 si process parti)."""
    import psutil

    try:
        proc = psutil.Process(pid)
        procs = [proc] + proc.children(recursive=True)
    except psutil.NoSuchProcess:
        return 0
    total = 0
    for p in procs:
        try:
            total += p.memory_info().rss
        except (psutil.NoSuchProcess, psutil.AccessDenied):
            pass
    return total


def _available_bytes():
    import psutil

    return psutil.virtual_memory().available


def _kill_tree(pid):
    """Tue l'arbre du pid : descendants d'abord, puis la racine."""
    import psutil

    try:
        proc = psutil.Process(pid)
    except psutil.NoSuchProcess:
        return
    procs = []
    try:
        procs = proc.children(recursive=True)
    except (psutil.NoSuchProcess, psutil.AccessDenied):
        pass
    for p in procs + [proc]:
        try:
            p.kill()
        except (psutil.NoSuchProcess, psutil.AccessDenied):
            pass


def _say(fh, msg):
    """Ecrit une ligne horodatee sur la console ET dans le journal."""
    line = f"[{time.strftime('%H:%M:%S')}] {msg}"
    print(line, flush=True)
    if fh is not None:
        fh.write(line + "\n")
        fh.flush()


def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Lance une commande sous plafond de RAM et plancher de RAM libre.",
        epilog="Exemple : run_guarded.py --limit-gib 24 --log run.log -- python train.py")
    ap.add_argument("--limit-gib", type=float, required=True,
                    help="plafond de RSS cumule du processus et de ses descendants")
    ap.add_argument("--reserve-gib", type=float, default=4.0,
                    help="RAM physique libre a ne jamais franchir vers le bas (defaut 4)")
    ap.add_argument("--poll", type=float, default=5.0,
                    help="periode de mesure en secondes (defaut 5)")
    ap.add_argument("--report-every", type=float, default=300.0,
                    help="ligne de suivi toutes les N s, 0 = aucune (defaut 300)")
    ap.add_argument("--log", default=None,
                    help="journal de la commande (la garde y ecrit aussi son rapport)")
    ap.add_argument("--cwd", default=None, help="repertoire de travail de la commande")
    ap.add_argument("--allow-no-job", action="store_true",
                    help="accepter de lancer sans Job Object (l'enfant survivrait "
                         "a ce lanceur) -- refus par defaut, cf incident 2026-10-05")
    ap.add_argument("cmd", nargs=argparse.REMAINDER,
                    help="commande a lancer, precedee de --")
    args = ap.parse_args(argv)

    cmd = args.cmd
    if cmd and cmd[0] == "--":
        cmd = cmd[1:]
    if not cmd:
        ap.error("aucune commande : terminer par -- <cmd> [args...]")

    try:
        import psutil  # noqa: F401
    except ImportError:
        print("run_guarded: psutil requis (pip install psutil)", file=sys.stderr)
        return RC_REFUSED

    limit = int(args.limit_gib * GiB)
    reserve = int(args.reserve_gib * GiB)

    fh = None
    if args.log:
        Path(args.log).parent.mkdir(parents=True, exist_ok=True)
        fh = open(args.log, "a", encoding="utf-8")
        _say(fh, f"run_guarded : plafond processus {args.limit_gib:.1f} GiB, "
                 f"plancher machine {args.reserve_gib:.1f} GiB, journal {args.log}")
        child_out = fh
    else:
        child_out = None

    free0 = _available_bytes()
    if free0 < reserve:
        _say(fh, f"REFUS : RAM libre {free0 / GiB:.1f} GiB < plancher "
                 f"{args.reserve_gib:.1f} GiB des le demarrage -- rien n'est lance.")
        if fh:
            fh.close()
        return RC_REFUSED

    job = _win_job_kill_on_close()
    if os.name == "nt" and job is None:
        _say(fh, "ATTENTION : Job Object KILL_ON_JOB_CLOSE indisponible sur cette "
                 "machine -- l'anti-orphelin ne sera pas pose.")
    elif os.name != "nt":
        _say(fh, "anti-orphelin : non implemente hors Windows (pas de Job "
                 "Object) -- la garde mesure et tue, mais un enfant survivrait "
                 "a la mort de ce lanceur.")

    t0 = time.time()
    try:
        proc = subprocess.Popen(
            cmd, cwd=args.cwd,
            stdout=child_out if child_out is not None else None,
            stderr=subprocess.STDOUT if child_out is not None else None)
    except (OSError, ValueError) as exc:
        _say(fh, f"la commande n'a pas demarre : {type(exc).__name__}: {exc}")
        if fh:
            fh.close()
        return RC_NOSTART

    assigned = _assign_to_job(job, proc)
    if os.name == "nt" and not assigned and not args.allow_no_job:
        _say(fh, "REFUS : l'enfant n'a pas pu etre place dans le Job Object -- "
                 "il pourrait survivre a ce lanceur (orphelin). Relancer avec "
                 "--allow-no-job pour l'assumer explicitement.")
        _kill_tree(proc.pid)
        if fh:
            fh.close()
        return RC_REFUSED
    if os.name == "nt" and assigned:
        _say(fh, f"anti-orphelin : pid {proc.pid} place dans le Job Object "
                 "KILL_ON_JOB_CLOSE -- il mourra avec ce lanceur")
    elif os.name == "nt":
        _say(fh, f"anti-orphelin DESACTIVE (--allow-no-job) : pid {proc.pid} "
                 "survivrait a ce lanceur")

    peak_rss, min_free, reason = 0, free0, None
    next_report = t0 + args.report_every if args.report_every > 0 else None
    try:
        while proc.poll() is None:
            time.sleep(args.poll)
            rss, free = _rss_bytes(proc.pid), _available_bytes()
            peak_rss = max(peak_rss, rss)
            min_free = min(min_free, free)
            if rss > limit:
                reason = (f"plafond processus franchi : RSS {rss / GiB:.1f} GiB "
                          f"> {args.limit_gib:.1f} GiB")
                break
            if free < reserve:
                reason = (f"plancher machine franchi : RAM libre "
                          f"{free / GiB:.1f} GiB < {args.reserve_gib:.1f} GiB")
                break
            if next_report is not None and time.time() >= next_report:
                _say(fh, f"suivi : RSS {rss / GiB:.1f} GiB, libre {free / GiB:.1f} GiB, "
                         f"{int(time.time() - t0)} s")
                next_report = time.time() + args.report_every
    except KeyboardInterrupt:
        _say(fh, "interruption clavier : arret de l'arbre")
        _kill_tree(proc.pid)
        if fh:
            fh.close()
        return RC_INTERRUPT

    if reason is not None:
        _say(fh, f"ARRET -- {reason} ; arbre tue apres {int(time.time() - t0)} s")
        _kill_tree(proc.pid)
        try:
            proc.wait(timeout=30)
        except subprocess.TimeoutExpired:
            pass
        _say(fh, f"bilan : pic RSS {peak_rss / GiB:.1f} GiB, RAM libre minimale "
                 f"{min_free / GiB:.1f} GiB, duree {int(time.time() - t0)} s")
        if fh:
            fh.close()
        return RC_LIMIT if reason.startswith("plafond") else RC_FLOOR

    rc = proc.returncode
    _say(fh, f"termine rc={rc} en {int(time.time() - t0)} s -- sous les deux "
             f"plafonds (pic RSS {peak_rss / GiB:.1f} GiB / {args.limit_gib:.1f} GiB, "
             f"RAM libre minimale {min_free / GiB:.1f} GiB)")
    if fh:
        fh.close()
    return rc


if __name__ == "__main__":
    sys.exit(main())
