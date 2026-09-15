"""Validation charge bornee de l'organe lean_exec (T5a, See #15666).

Incident fondateur (12 septembre 2026) : ~30 processus ``lean.exe`` a ~95 % CPU
ont etouffe une machine worker -- DriveFS tombe, puis les services de fond,
puis reboot du cluster. L'organe ``scripts/lean/lean_exec.py`` (T1-T3) confine
chaque invocation : admission machine-wide sous cap, Job Object kill-on-close,
budget supervise, postcondition zero orphelin. Cette tranche valide l'organe
SUR CHARGE REELLE : une compilation lake effective, echantillonnee pendant
qu'elle tourne.

Le harnais mesure PENDANT la compilation (l'organe garantit le cap ; le
harnais verifie que la machine reste vivable) :

  - **population native lean/lake** : echantillonnee avec la MEME fonction de
    mesure que l'organe (``lean_exec.scan_native_population``) -- le max
    observe doit rester <= cap. C'est la contradiction directe du regime de
    l'incident (30 lean sous cap 8).
  - **sonde DriveFS** : ``listdir`` chronometre sur le lecteur monte (defaut
    ``G:\\Mon Drive``). Un TIMEOUT de sonde = ECHEC : c'est le premier
    symptome mesurable de l'asphyxie de septembre. Lecteur absent = sonde
    ``unavailable``, notee honnetement, sans faux pass. La latence (hors
    timeout) est rapportee, pas seuillee -- le regime mortel est le hang, pas
    la milliseconde.
  - **latence de spawn** : lancer un python trivial et attendre sa mort --
    proxy de la sante ordonnanceur du systeme, ce qui meurt en premier dans
    l'incident. p95 pendant la charge <= max(rapport x p95 baseline, plancher).
  - **RAM libre** : rapportee sans seuil invente (l'organe plafonne deja la
    memoire du run via Job Object).

Post-conditions lues dans l'enregistrement de l'organe (``last_run.json``,
ecrit a CHAQUE sortie de ``run``, y compris refuse) : status ``ok``,
orphelins vides, sortie 0.

Generation de la charge : le harnais ne fabrique pas de charge fictive. Il
lance ``lean_exec.py run -- lake build`` dans le lake fourni ; pour qu'un
build cache-chaud produise du travail reel, ``--touch N`` augmente le mtime
de N modules propres du lake (contenu inchange, arbre git propre) -- la
recompilation en cascade qui suit est la charge.

Codes de sortie : 0 = PASS, 1 = FAIL (chaque critere dur violé est nomme).
"""

from __future__ import annotations

import argparse
import ctypes
import json
import os
import subprocess
import tempfile
import sys
import threading
import time
from pathlib import Path

# L'organe est un sibling du present script ; l'importer plutot que dupliquer
# sa mesure de population (memes regles de comptage, meme source tasklist).
sys.path.insert(0, str(Path(__file__).resolve().parent))
import lean_exec  # noqa: E402

DRIVEFS_OK = "ok"
DRIVEFS_TIMEOUT = "timeout"
DRIVEFS_ERROR = "error"
DRIVEFS_UNAVAILABLE = "unavailable"

DEFAULT_DRIVEFS_ROOT = r"G:\Mon Drive"


# ---------------------------------------------------------------------------
# Sondes
# ---------------------------------------------------------------------------

def probe_spawn_ms() -> float:
    """Latence pour spawner un processus trivial et attendre sa mort."""
    t0 = time.monotonic()
    subprocess.run(
        [sys.executable, "-c", "pass"],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0),
    )
    return (time.monotonic() - t0) * 1000.0


def probe_drivefs(root: str | None, timeout_s: float) -> tuple[str, float | None]:
    """Listdir chronometre sous garde-fou temps.

    Le listdir d'un DriveFS mort peut se bloquer des minutes : la sonde court
    dans un fil daemon et est abandonnee au bout de ``timeout_s`` -- c'est le
    comportement a detecter, pas un cas d'erreur a contourner.
    """
    if not root or not os.path.isdir(root):
        return DRIVEFS_UNAVAILABLE, None
    box: dict = {}

    def _list() -> None:
        try:
            t0 = time.monotonic()
            os.listdir(root)
            box["ms"] = (time.monotonic() - t0) * 1000.0
        except OSError as exc:
            box["error"] = str(exc)

    thread = threading.Thread(target=_list, daemon=True)
    thread.start()
    thread.join(timeout_s)
    if thread.is_alive():
        return DRIVEFS_TIMEOUT, None
    if "error" in box:
        return DRIVEFS_ERROR, None
    return DRIVEFS_OK, box.get("ms")


class _MemoryStatusEx(ctypes.Structure):
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


def ram_free_mb() -> float | None:
    """RAM physiquement disponible, None si non mesurable."""
    try:
        if os.name == "nt":
            stat = _MemoryStatusEx()
            stat.dwLength = ctypes.sizeof(_MemoryStatusEx)
            if ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(stat)):
                return round(stat.ullAvailPhys / (1024 * 1024), 1)
            return None
        with open("/proc/meminfo", encoding="ascii") as fh:
            for line in fh:
                if line.startswith("MemAvailable:"):
                    return round(int(line.split()[1]) / 1024, 1)
        return None
    except OSError:
        return None


def take_sample(phase: str, drivefs_root: str | None,
                probe_timeout_s: float) -> dict:
    pop, pop_src = lean_exec.scan_native_population()
    state, ms = probe_drivefs(drivefs_root, probe_timeout_s)
    return {
        "t": round(time.time(), 3),
        "phase": phase,
        "population": pop,
        "population_src": pop_src,
        "spawn_ms": round(probe_spawn_ms(), 1),
        "drivefs": state,
        "drivefs_ms": round(ms, 1) if ms is not None else None,
        "ram_free_mb": ram_free_mb(),
    }


# ---------------------------------------------------------------------------
# Echantillonnage pendant la charge
# ---------------------------------------------------------------------------

class Sampler:
    """Preleve des echantillons tant que le processus de charge vit."""

    def __init__(self, drivefs_root: str | None, probe_timeout_s: float,
                 sample_fn=None) -> None:
        self._sample = sample_fn or (
            lambda phase: take_sample(phase, drivefs_root, probe_timeout_s)
        )

    def collect(self, proc: subprocess.Popen, interval: float,
                max_wall: float) -> tuple[list[dict], bool]:
        """Echantillonne jusqu'a la mort de ``proc`` ou depassement du mur.

        Renvoie (echantillons, mur_depasse). Le premier echantillon est pris
        immediatement : un build court ne doit pas echapper a la mesure.
        """
        samples: list[dict] = []
        start = time.monotonic()
        while proc.poll() is None:
            samples.append(self._sample("load"))
            if time.monotonic() - start > max_wall:
                return samples, True
            time.sleep(interval)
        return samples, False


# ---------------------------------------------------------------------------
# Verdict
# ---------------------------------------------------------------------------

def _p95(values: list[float]) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    idx = min(len(ordered) - 1, max(0, int(0.95 * len(ordered) + 0.5)))
    return ordered[idx]


def evaluate(baseline: list[dict], load: list[dict],
             organ_record: dict | None, cap: int,
             spawn_ratio: float, spawn_floor_ms: float) -> dict:
    """Verdict : chaque critere dur est cite avec sa mesure, PASS ou FAIL."""
    checks: list[dict] = []

    def hard(name: str, ok: bool, detail: str) -> None:
        checks.append({"criterion": name, "pass": bool(ok), "detail": detail})

    status = (organ_record or {}).get("status")
    orphans = (organ_record or {}).get("orphans") or []
    hard(
        "organ_postcondition",
        organ_record is not None and status == "ok" and not orphans,
        f"organ status={status!r} orphelins={len(orphans)}",
    )

    pops = [s["population"] for s in load]
    max_pop = max(pops) if pops else None
    hard(
        "population_cap",
        bool(pops) and max_pop is not None and max_pop <= cap,
        (f"max population observee {max_pop} <= cap {cap} "
         f"({len(pops)} echantillons)")
        if pops else
        f"0 echantillon pendant la charge -- critere non verifiable",
    )

    timeouts = [s for s in load if s["drivefs"] == DRIVEFS_TIMEOUT]
    unavailable = [s for s in load if s["drivefs"] == DRIVEFS_UNAVAILABLE]
    hard(
        "drivefs_alive",
        not timeouts,
        (f"{len(timeouts)} sonde(s) DriveFS en timeout")
        if timeouts else
        (f"aucun timeout ({len(unavailable)} sonde(s) unavailable)"
         if unavailable else "aucune sonde DriveFS en timeout"),
    )

    base_spawn = _p95([s["spawn_ms"] for s in baseline])
    load_spawn = _p95([s["spawn_ms"] for s in load])
    bound = spawn_floor_ms
    if base_spawn is not None:
        bound = max(spawn_ratio * base_spawn, spawn_floor_ms)
    hard(
        "spawn_p95",
        load_spawn is not None and load_spawn <= bound,
        f"spawn p95 charge {load_spawn} ms <= borne {round(bound, 1)} ms "
        f"(baseline p95 {base_spawn} ms, rapport max {spawn_ratio}, "
        f"plancher {spawn_floor_ms} ms)",
    )

    ram_values = [s["ram_free_mb"] for s in load if s["ram_free_mb"] is not None]
    drivefs_ms = [s["drivefs_ms"] for s in load if s["drivefs_ms"] is not None]
    return {
        "pass": all(c["pass"] for c in checks),
        "checks": checks,
        "report": {
            "echantillons_baseline": len(baseline),
            "echantillons_charge": len(load),
            "population_max": max_pop,
            "spawn_p95_baseline_ms": base_spawn,
            "spawn_p95_charge_ms": load_spawn,
            "drivefs_p95_ms": _p95(drivefs_ms) if drivefs_ms else None,
            "ram_libre_min_mb": min(ram_values) if ram_values else None,
        },
    }


# ---------------------------------------------------------------------------
# Charge
# ---------------------------------------------------------------------------

def touch_own_modules(lake_dir: Path, n: int) -> list[str]:
    """Mtime-bump des n modules propres les plus anciens du lake.

    Contenu strictement inchange (seul le mtime bouge) : l'arbre git reste
    propre, mais lake considere les oleans perimes et recompile -- c'est la
    charge. Les modules sous ``.lake/`` (paquets vendores) sont exclus.
    """
    modules = [
        p for p in lake_dir.rglob("*.lean")
        if ".lake" not in p.parts and p.name != "lakefile.lean"
    ]
    modules.sort(key=lambda p: p.stat().st_mtime)
    now = time.time()
    touched = []
    for path in modules[:n]:
        os.utime(path, (now, now))
        touched.append(path.relative_to(lake_dir).as_posix())
    return touched


def read_organ_record(expected_cmd: list[str]) -> dict | None:
    """Lit ``last_run.json`` ; None si absent ou manifestement stale.

    Un enregistrement d'un run precedent (cmd differente) n'est pas une
    preuve pour CE run : le harnais le rejete plutot que de valider sur du
    stale.
    """
    path = lean_exec.state_dir() / "last_run.json"
    try:
        record = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None
    if record.get("cmd") != expected_cmd:
        return None
    return record


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Validation charge bornee de l'organe lean_exec (T5a, #15666)")
    parser.add_argument("--lake-dir", required=True,
                        help="repertoire du lake a compiler (reel)")
    parser.add_argument("--cmd", nargs=argparse.REMAINDER,
                        default=["lake", "build"],
                        help="commande de charge (defaut: lake build) ; "
                             "REMAINDER : dernier argument du harnais, "
                             "tout ce qui suit est la commande")
    parser.add_argument("--cap", type=int, default=None,
                        help="cap machine-wide transmis a l'organe")
    parser.add_argument("--budget", type=int, default=None,
                        help="budget lean/lake transmis a l'organe")
    parser.add_argument("--timeout", type=float, default=None,
                        help="timeout (s) transmis a l'organe")
    parser.add_argument("--touch", type=int, default=0, metavar="N",
                        help="mtime-bump de N modules propres pour generer "
                             "la charge (contenu inchange)")
    parser.add_argument("--baselines", type=int, default=3)
    parser.add_argument("--interval", type=float, default=2.0)
    parser.add_argument("--probe-timeout", type=float, default=10.0)
    parser.add_argument("--drivefs-root", default=DEFAULT_DRIVEFS_ROOT)
    parser.add_argument("--spawn-ratio", type=float, default=5.0)
    parser.add_argument("--spawn-floor-ms", type=float, default=5000.0)
    parser.add_argument("--max-wall", type=float, default=None,
                        help="mur du harnais en s (defaut: timeout organe "
                             "+ 120, sinon 1200)")
    parser.add_argument("--json", action="store_true",
                        help="verdict complet en JSON sur stdout")
    args = parser.parse_args(argv)

    load_cmd = list(args.cmd)
    if load_cmd and load_cmd[0] == "--":
        load_cmd = load_cmd[1:]
    if not load_cmd:
        parser.error("commande de charge vide")

    lake_dir = Path(args.lake_dir).resolve()
    if not ((lake_dir / "lakefile.lean").exists()
            or (lake_dir / "lakefile.toml").exists()):
        parser.error(f"pas de lakefile.lean/.toml sous {lake_dir}")

    max_wall = args.max_wall
    if max_wall is None:
        max_wall = (args.timeout + 120.0) if args.timeout else 1200.0

    touched: list[str] = []
    if args.touch > 0:
        touched = touch_own_modules(lake_dir, args.touch)

    cap = args.cap if args.cap is not None else lean_exec.config()["cap"]

    baseline = [
        take_sample("baseline", args.drivefs_root, args.probe_timeout)
        for _ in range(max(1, args.baselines))
    ]

    organ_cli = [
        sys.executable,
        str(Path(__file__).resolve().parent / "lean_exec.py"),
        "run",
    ]
    if args.cap is not None:
        organ_cli += ["--cap", str(args.cap)]
    if args.budget is not None:
        organ_cli += ["--budget", str(args.budget)]
    if args.timeout is not None:
        organ_cli += ["--timeout", str(args.timeout)]
    organ_cli += ["--", *load_cmd]

    started = time.monotonic()
    # Sortie de l'organe vers FICHIER, jamais vers un pipe non lu : un build
    # lake emet bien plus que le buffer de pipe, et personne ne draine tant
    # que le harnais echantillonne -- un PIPE ici est un deadlock garanti.
    log_fd, log_path = tempfile.mkstemp(
        prefix="t5a_organ_log_", suffix=".txt"
    )
    log_file = os.fdopen(log_fd, "w", encoding="utf-8")
    proc = subprocess.Popen(
        organ_cli,
        cwd=str(lake_dir),
        stdout=log_file,
        stderr=subprocess.STDOUT,
        creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0),
    )
    sampler = Sampler(args.drivefs_root, args.probe_timeout)
    load, wall_exceeded = sampler.collect(proc, args.interval, max_wall)
    if wall_exceeded:
        proc.kill()
    proc.wait()
    log_file.close()
    with open(log_path, encoding="utf-8", errors="replace") as fh:
        output_tail = fh.read().splitlines()[-15:]

    record = read_organ_record(load_cmd)
    verdict = evaluate(baseline, load, record, cap,
                       args.spawn_ratio, args.spawn_floor_ms)
    if wall_exceeded:
        verdict["checks"].append({
            "criterion": "harness_max_wall",
            "pass": False,
            "detail": f"mur du harnais {max_wall} s depasse -- charge tuee",
        })
        verdict["pass"] = False
    verdict["wall_s"] = round(time.monotonic() - started, 1)
    verdict["cap"] = cap
    verdict["lake_dir"] = str(lake_dir)
    verdict["touched_modules"] = touched
    verdict["organ_exit_code"] = proc.returncode
    verdict["organ_output_tail"] = output_tail
    verdict["organ_log"] = log_path
    verdict["organ_record"] = record

    if args.json:
        print(json.dumps(verdict, indent=2))
    else:
        rep = verdict["report"]
        print(f"[T5a] charge : {' '.join(load_cmd)} dans {lake_dir} "
              f"({len(touched)} modules touches, wall {verdict['wall_s']} s)")
        print(f"[T5a] organ : exit={proc.returncode} "
              f"record={'lu' if record else 'ABSENT/stale'}")
        for check in verdict["checks"]:
            mark = "PASS" if check["pass"] else "FAIL"
            print(f"[T5a] {mark} {check['criterion']}: {check['detail']}")
        print(f"[T5a] drivefs p95 {rep['drivefs_p95_ms']} ms ; "
              f"spawn p95 {rep['spawn_p95_charge_ms']} ms "
              f"(baseline {rep['spawn_p95_baseline_ms']}) ; "
              f"ram libre min {rep['ram_libre_min_mb']} MB")
        print(f"[T5a] VERDICT : {'PASS' if verdict['pass'] else 'FAIL'} "
              f"({sum(1 for c in verdict['checks'] if c['pass'])}/"
              f"{len(verdict['checks'])} criteres durs)")

    return 0 if verdict["pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
