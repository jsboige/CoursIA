#!/usr/bin/env python3
r"""Installateur de la tache planifiee quotidienne prune_merged_worktrees (#14473).

Le organe (scripts/ci/prune_merged_worktrees.py, #14195) etait livre mais
rappelé par personne : une prescription en prose dans .claude/rules/ ne
s'execute pas (regles injectees au DEMARRAGE de session, fin de cycle
disparait en crash/compaction). Le cablage est necessairement LOCAL : un
workflow GitHub Actions ne voit que son checkout ephemerre, jamais les
worktrees de l'hote (missing-tool-turns-a-guard-green).

Modes :
    --install [--repo PATH] [--time HH:MM]   cree la tache planifiee (idempotent)
    --status                                  etat de la tache
    --uninstall                               supprime la tache
    --run                                     execute la purge (invoqué PAR la tache) :
                                              journal horodate, jamais de couleur/TTY

Garde de securite (#14476) : --install REFUSE de cabler --apply si le script
cible ne contient pas encore les deux voies du fix PR #14481 (resolution
par numero + _normalize) -- installer le cron avec l'ancien predicat
d'intersection de jetons deploierait l'attribution fausse (et destructive)
TOUS LES JOURS.

Journal : %LOCALAPPDATA%\CoursIA\prune_task\logs\prune_YYYYMMDD.log
"""
from __future__ import annotations

import argparse
import datetime as _dt
import os
import subprocess
import sys
from pathlib import Path

TASK_NAME = r"CoursIA\prune_merged_worktrees"
THIS_FILE = Path(__file__).resolve()
LOG_DIR = Path(os.environ.get("LOCALAPPDATA", str(Path.home() / "AppData" / "Local"))) / "CoursIA" / "prune_task" / "logs"

# Marqueurs du fix #14476/#14481 dans le script cible -- voir garde ci-dessus.
# Alignes sur le contenu REEL merge par #14481 (voie 1 : resolution par
# numero ; voie 2 : egalite normalisee du sujet via _normalize). Le marqueur
# historique 'def _normalize_subject' ne correspondait a AUCUN symbole du
# fichier merge -- la garde etait insatisfaisable et refusait tout --install,
# y compris sur un main frais contenant le fix (mesure 2026-09-04).
REQUIRED_FIX_MARKERS = ("Resolution directe par numero", "def _normalize")


def _run(cmd: list[str], **kw) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8",
                          errors="replace", **kw)


def prune_script_path(repo: Path) -> Path:
    return repo / "scripts" / "ci" / "prune_merged_worktrees.py"


def check_prune_fix_present(repo: Path) -> tuple[bool, str]:
    """Le predicat detached-head doit etre la version corrigee (#14476).

    L'ancienne heuristique (intersection de jetons) attribuait n'importe
    quelle PR recente partageant un mot du domaine -> retraits faux. Une
    tache quotidienne --apply ne doit JAMAIS la deployer.
    """
    target = prune_script_path(repo)
    if not target.is_file():
        return False, f"introuvable : {target}"
    text = target.read_text(encoding="utf-8", errors="replace")
    missing = [m for m in REQUIRED_FIX_MARKERS if m not in text]
    if missing:
        return False, (
            f"{target.name} ne contient pas le fix #14476 "
            f"(marqueurs absents : {', '.join(missing)}). Installer le "
            "cron --apply avec l'heuristique d'intersection de jetons "
            "deploierait l'attribution fausse quotidiennement (cf #14481). "
            "Rebase/merge d'abord, puis relancer --install."
        )
    return True, "fix #14476 present"


def task_command(repo: Path) -> list[str]:
    """Commande enregistree dans le planificateur : ce script --run, qui
    journalise et appelle l'organe en --apply."""
    return [sys.executable, str(THIS_FILE), "--run", "--repo", str(repo)]


def build_schtasks_install(cmd: list[str], time: str) -> list[str]:
    """Ligne schtasks /Create : quotidienne, contexte utilisateur courant
    (gh auth vit au niveau utilisateur), fenêtre masquee."""
    tr = " ".join(cmd)
    return [
        "schtasks", "/Create", "/F",
        "/TN", TASK_NAME,
        "/SC", "DAILY",
        "/ST", time,
        "/TR", f'"{tr}"',
    ]


def log_path_for(day: _dt.date | None = None) -> Path:
    day = day or _dt.date.today()
    return LOG_DIR / f"prune_{day:%Y%m%d}.log"


def task_exists() -> bool:
    return _run(["schtasks", "/Query", "/TN", TASK_NAME]).returncode == 0


def cmd_install(repo: Path, time: str) -> int:
    ok, msg = check_prune_fix_present(repo)
    if not ok:
        print(f"REFUSE : {msg}", file=sys.stderr)
        return 2
    print(f"garde OK : {msg}")
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    proc = _run(build_schtasks_install(task_command(repo), time))
    if proc.returncode != 0:
        print(f"schtasks /Create echoue (rc={proc.returncode}) : "
              f"{proc.stdout.strip()} {proc.stderr.strip()}", file=sys.stderr)
        return 2
    print(f"tache installee : {TASK_NAME} quotidienne a {time}")
    print(f"commande : {' '.join(task_command(repo))}")
    print(f"journal  : {log_path_for()}")
    print("verification : schtasks /Query /TN "
          + TASK_NAME.replace("\\", "\\") + " /V /FO LIST")
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
        print(f"suppression echouee : {proc.stdout.strip()} "
              f"{proc.stderr.strip()}", file=sys.stderr)
        return 2
    print(f"tache supprimee : {TASK_NAME}")
    return 0


def cmd_run(repo: Path) -> int:
    """Invoque par la tache planifiee : journal horodate, pas de TTY."""
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    log = log_path_for()
    stamp = _dt.datetime.now().strftime("%Y-%m-%dT%H:%M:%S")
    with log.open("a", encoding="utf-8") as fh:
        fh.write(f"\n=== {stamp} run start ===\n")
        fh.flush()
        proc = subprocess.run(
            [sys.executable, str(prune_script_path(repo)),
             "--path", str(repo), "--apply"],
            stdout=fh, stderr=subprocess.STDOUT,
        )
        fh.write(f"=== {_dt.datetime.now().strftime('%Y-%m-%dT%H:%M:%S')} "
                 f"run end rc={proc.returncode} ===\n")
    # exit code non zero si l'organe a echoue -- visible dans le journal
    return proc.returncode


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--install", action="store_true")
    p.add_argument("--status", action="store_true")
    p.add_argument("--uninstall", action="store_true")
    p.add_argument("--run", action="store_true",
                   help="mode interne (invoque par la tache planifiee)")
    p.add_argument("--repo", type=Path,
                   default=Path(r"C:\dev\CoursIA"),
                   help="checkout principal du depot (defaut C:\\dev\\CoursIA)")
    p.add_argument("--time", default="03:17",
                   help="heure quotidienne HH:MM (defaut 03:17, hors heures ouvrables)")
    args = p.parse_args(argv)

    repo = args.repo.resolve()
    if args.install:
        return cmd_install(repo, args.time)
    if args.status:
        return cmd_status()
    if args.uninstall:
        return cmd_uninstall()
    if args.run:
        return cmd_run(repo)
    p.print_help()
    return 1


if __name__ == "__main__":
    sys.exit(main())
