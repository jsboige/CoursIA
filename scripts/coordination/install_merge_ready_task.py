#!/usr/bin/env python3
r"""Installateur de la tache planifiee merge_ready (Q40, mandat 2026-09-22).

L'organe (scripts/coordination/merge_ready.py) existe mais aucun cycle ne
le rappelle : une prescription en prose ne s'execute pas seule (meme
constat que #14473 pour prune_merged_worktrees). Le cablage est LOCAL :
une tache planifiee Windows toutes les 20 minutes qui lance
``merge_ready.py --apply`` sous l'identite coordinateur (myia-ai-01).

Modes :
    --dry-run [--repo PATH] [--interval N]   imprime la commande schtasks
                                              EXACTE sans l'executer
                                              (discipline UAC : la sortie
                                              du dry-run precede toute
                                              inscription schtasks)
    --install    [--repo PATH] [--interval N] cree la tache (idempotent)
    --status                                      etat de la tache
    --uninstall                                   supprime la tache
    --run                     execute l'organe en --apply (invoque PAR la
                              tache) : journal horodate, jamais de TTY

Garde : --install REFUSE de cabler --apply si l'organe cible est absent
(installer un cron vers un fichier qui n'existe pas deployerait un echec
silencieux toutes les 20 minutes).

Journal de la tache : %LOCALAPPDATA%\CoursIA\merge_ready\logs\
merge_ready_YYYYMMDD.log ; journal de l'organe :
%LOCALAPPDATA%\CoursIA\merge_ready\journal.jsonl.
"""
from __future__ import annotations

import argparse
import datetime as _dt
import os
import subprocess
import sys
from pathlib import Path

TASK_NAME = r"CoursIA\merge_ready"
THIS_FILE = Path(__file__).resolve()
LOG_DIR = (
    Path(os.environ.get("LOCALAPPDATA", str(Path.home() / "AppData" / "Local")))
    / "CoursIA"
    / "merge_ready"
    / "logs"
)
# Siege coordinateur (ai-01) : un worktree DEDIE a `origin/main`, pas le
# checkout principal. D:\CoursIA est le siege interactif, souvent sur une
# branche de travail : l'organe y executerait le gate et B.0 de CETTE branche,
# pas ceux de `main`. Le worktree dedie ne peut PAS porter la branche `main`
# (git la refuse a un second worktree tant que le checkout principal la
# tient) : il est en HEAD DETACHE, ramene sur origin/main avant chaque tour
# (voir sync_repo). Les autres machines passent --repo explicitement.
DEFAULT_REPO = Path(r"D:\CoursIA-wt-merge-ready")
INTERVAL_MINUTES = 20


def _run(cmd: list[str], **kw) -> subprocess.CompletedProcess:
    return subprocess.run(
        cmd, capture_output=True, text=True, encoding="utf-8",
        errors="replace", **kw
    )


def organ_path(repo: Path) -> Path:
    return repo / "scripts" / "coordination" / "merge_ready.py"


def check_organ_present(repo: Path) -> tuple[bool, str]:
    """L'organe cible doit exister avant tout cablage --apply."""
    target = organ_path(repo)
    if not target.is_file():
        return False, f"introuvable : {target}"
    return True, f"organe present : {target}"


def task_command(repo: Path) -> list[str]:
    """Commande enregistree dans le planificateur : ce script --run, qui
    journalise et appelle l'organe en --apply."""
    return [
        sys.executable,
        str(repo / "scripts" / "coordination" / "install_merge_ready_task.py"),
        "--run", "--repo", str(repo),
    ]


def build_schtasks_install(cmd: list[str], interval_minutes: int) -> list[str]:
    """Ligne schtasks /Create : toutes les N minutes, contexte utilisateur
    courant (gh auth vit au niveau utilisateur), fenetre masquee."""
    # Quoter chaque element, jamais la ligne entiere : un /TR "python.exe script.py
    # --run" enregistre la ligne comme NOM d'executable, et la tache echoue
    # a chaque tour avec 0x80070002 (fichier introuvable) sans rien journaliser.
    tr = subprocess.list2cmdline(cmd)
    return [
        "schtasks", "/Create", "/F",
        "/TN", TASK_NAME,
        "/SC", "MINUTE",
        "/MO", str(interval_minutes),
        "/TR", tr,
    ]


def log_path_for(day: _dt.date | None = None) -> Path:
    day = day or _dt.date.today()
    return LOG_DIR / f"merge_ready_{day:%Y%m%d}.log"


def task_exists() -> bool:
    return _run(["schtasks", "/Query", "/TN", TASK_NAME]).returncode == 0


def cmd_dry_run(repo: Path, interval: int) -> int:
    """Imprime la commande EXACTE que --install enregistrerait. N'execute
    RIEN : c'est la sortie que la discipline UAC exige de voir avant toute
    inscription schtasks."""
    command = build_schtasks_install(task_command(repo), interval)
    print("DRY-RUN -- commande schtasks que --install enregistrerait :")
    print(" ".join(command))
    print(f"journal de la tache : {log_path_for()}")
    return 0


def cmd_install(repo: Path, interval: int) -> int:
    ok, msg = check_organ_present(repo)
    if not ok:
        print(f"REFUSE : {msg}", file=sys.stderr)
        return 2
    print(f"garde OK : {msg}")
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    proc = _run(build_schtasks_install(task_command(repo), interval))
    if proc.returncode != 0:
        print(
            f"schtasks /Create echoue (rc={proc.returncode}) : "
            f"{proc.stdout.strip()} {proc.stderr.strip()}",
            file=sys.stderr,
        )
        return 2
    print(f"tache installee : {TASK_NAME} toutes les {interval} minutes")
    print(f"commande : {' '.join(task_command(repo))}")
    print(f"journal  : {log_path_for()}")
    print(
        "verification : schtasks /Query /TN " + TASK_NAME + " /V /FO LIST"
    )
    return 0


def cmd_status() -> int:
    if not task_exists():
        print(f"tache ABSENTE : {TASK_NAME}")
        return 1
    proc = _run(["schtasks", "/Query", "/TN", TASK_NAME, "/V", "/FO", "LIST"])
    print(proc.stdout)
    return 0


def cmd_uninstall() -> int:
    proc = _run(["schtasks", "/Delete", "/TN", TASK_NAME, "/F"])
    if proc.returncode != 0:
        print(
            f"suppression echouee : {proc.stdout.strip()} {proc.stderr.strip()}",
            file=sys.stderr,
        )
        return 2
    print(f"tache supprimee : {TASK_NAME}")
    return 0


def sync_repo(repo: Path) -> tuple[bool, str]:
    """Ramene le depot de l'organe sur origin/main, ou refuse le tour.

    Deux sieges acceptes : la branche `main`, ou un HEAD DETACHE (le worktree
    dedie d'ai-01, qui ne peut pas porter `main` tant que le checkout
    principal la tient). Refuse (sans rien toucher) toute autre branche, un
    depot qui porte des modifications suivies, et un HEAD detache qui n'est
    pas un ancetre d'origin/main (des commits locaux seraient abandonnes) :
    un tour ne doit jamais executer un gate ou un B.0 de branche, ni ecraser
    un travail local. Sinon fetch + avance rapide.
    """
    branch = _run(["git", "-C", str(repo), "rev-parse", "--abbrev-ref", "HEAD"])
    if branch.returncode != 0:
        return False, f"git rev-parse rc={branch.returncode} : {branch.stderr.strip()[:200]}"
    seat = branch.stdout.strip()
    if seat not in ("main", "HEAD"):
        return False, f"le depot {repo} est sur '{seat}', pas sur main ni detache"
    dirty = _run(["git", "-C", str(repo), "status", "--porcelain", "--untracked-files=no"])
    if dirty.returncode != 0 or dirty.stdout.strip():
        return False, f"le depot {repo} porte des modifications suivies : tour refuse"
    fetch = ["git", "-C", str(repo), "fetch", "-q", "origin", "main"]
    if seat == "main":
        steps = (fetch, ["git", "-C", str(repo), "merge", "--ff-only", "-q", "origin/main"])
    else:
        steps = (
            fetch,
            ["git", "-C", str(repo), "merge-base", "--is-ancestor", "HEAD", "origin/main"],
            ["git", "-C", str(repo), "checkout", "-q", "--detach", "origin/main"],
        )
    for cmd in steps:
        res = _run(cmd)
        if res.returncode != 0:
            return False, f"{' '.join(cmd[3:])} rc={res.returncode} : {res.stderr.strip()[:200]}"
    return True, "origin/main"


def cmd_run(repo: Path) -> int:
    """Invoque par la tache planifiee : journal horodate, pas de TTY.

    L'organe part en dry-run par defaut a l'ecran, mais le cablage est le
    geste : la tache lance --apply (c'est le mandat Q40 -- sans --apply le
    cablage ne ferait rien).
    """
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    log = log_path_for()
    stamp = _dt.datetime.now().strftime("%Y-%m-%dT%H:%M:%S")
    with log.open("a", encoding="utf-8") as fh:
        fh.write(f"\n=== {stamp} run start ===\n")
        ok, msg = sync_repo(repo)
        if not ok:
            fh.write(f"=== tour REFUSE : {msg} ===\n")
            return 2
        fh.write(f"depot synchronise sur {msg}\n")
        fh.flush()
        proc = subprocess.run(
            [sys.executable, str(organ_path(repo)), "--apply"],
            stdout=fh,
            stderr=subprocess.STDOUT,
        )
        fh.write(
            f"=== {_dt.datetime.now().strftime('%Y-%m-%dT%H:%M:%S')} "
            f"run end rc={proc.returncode} ===\n"
        )
    # exit code non zero si l'organe a echoue -- visible dans le journal
    return proc.returncode


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--install", action="store_true")
    parser.add_argument(
        "--dry-run",
        dest="dry_run",
        action="store_true",
        help="imprime la commande schtasks exacte sans l'executer",
    )
    parser.add_argument("--status", action="store_true")
    parser.add_argument("--uninstall", action="store_true")
    parser.add_argument(
        "--run",
        action="store_true",
        help="mode interne (invoque par la tache planifiee)",
    )
    parser.add_argument(
        "--repo",
        type=Path,
        default=DEFAULT_REPO,
        help=f"checkout principal du depot (defaut {DEFAULT_REPO})",
    )
    parser.add_argument(
        "--interval",
        type=int,
        default=INTERVAL_MINUTES,
        metavar="N",
        help=f"cadence en minutes (defaut {INTERVAL_MINUTES})",
    )
    args = parser.parse_args(argv)
    if args.interval <= 0:
        parser.error("--interval doit etre > 0")

    repo = args.repo.resolve()
    # --dry-run d'abord : un --install --dry-run combine fait le geste sur.
    if args.dry_run:
        return cmd_dry_run(repo, args.interval)
    if args.install:
        return cmd_install(repo, args.interval)
    if args.status:
        return cmd_status()
    if args.uninstall:
        return cmd_uninstall()
    if args.run:
        return cmd_run(repo)
    parser.print_help()
    return 1


if __name__ == "__main__":
    sys.exit(main())
