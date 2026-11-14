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
    --dry-run (--install | --uninstall)       affiche argv schtasks sans l'executer
    --run                                     execute la purge (invoqué PAR la tache) :
                                              journal horodate, jamais de couleur/TTY ;
                                              relaie --warn-threshold (defaut 20, #3895)
                                              a l'organe : ligne [WARN][prune-task] en
                                              journal au-dela du seuil de refus ;
                                              relaie aussi --quarantine-submodules
                                              (#21743) : un worktree MERGED a
                                              sous-modules sort par decontamination
                                              (deplacement en quarantaine, jamais
                                              --force) au lieu d'etre refuse pour
                                              toujours (#127)

Garde de securite (#14476) : --install REFUSE de cabler --apply si le script
cible ne contient pas encore les deux voies du fix PR #14481 (resolution
par numero + _normalize) -- installer le cron avec l'ancien predicat
d'intersection de jetons deploierait l'attribution fausse (et destructive)
TOUS LES JOURS.

Journal : %LOCALAPPDATA%\CoursIA\prune_task\logs\prune_YYYYMMDD.log

#3895 (roo-extensions) : les REFUS de l'organe ne sont plus un echec (rc=0) ;
le rc de la tache ne rougit plus que sur panne gh/git ou echec d'application.
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

# Meme correction que le controleur des runners : une tache planifiee qui
# lance directement python.exe fait clignoter une console (le planificateur
# alloue une console neuve au binaire console). Le lanceur VBS passe par
# wscript.exe avec SW_HIDE : rien ne clignote, et `WScript.Quit rc` rend le
# code retour de la commande (mesure 2026-11-04, Maintenance#75).
LAUNCHER_NAME = "prune-launcher.vbs"

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


def build_schtasks_install(launcher: Path, time: str) -> list[str]:
    """Ligne schtasks /Create : quotidienne, contexte utilisateur courant
    (gh auth vit au niveau utilisateur), fenetre masquee.

    `/TR` porte le lanceur VBS, pas la commande : le planificateur alloue une
    console a un binaire console, et elle clignote (mesure 2026-11-04). Le
    guillement reste sur chaque element de la commande, qui vit DANS le VBS.
    """
    tr = f'wscript.exe //B //Nologo "{launcher}"'
    return [
        "schtasks", "/Create", "/F",
        "/TN", TASK_NAME,
        "/SC", "DAILY",
        "/ST", time,
        "/TR", tr,
    ]


def launcher_path() -> Path:
    """Le lanceur cache que la tache planifiee execute."""
    return LOG_DIR.parent / LAUNCHER_NAME


def _vbs_literal(text: str) -> str:
    """Un litteral VBS : chaque guillemet du texte est double ("" -> ")."""
    return text.replace('"', '""')


def launcher_vbs(cmd: list[str]) -> str:
    """Le lanceur VBS : la commande, sans fenetre, avec son code retour.

    `sh.Run(commande, 0, True)` : style SW_HIDE (rien ne clignote) et
    attente ; le rc de la commande est rendu par `WScript.Quit rc`, donc la
    tache planifiee porte toujours le rc de l'organe (le journal du run
    reste lisible par la lane).
    """
    command_line = subprocess.list2cmdline(cmd)
    return (
        "' Genere par scripts/ci/install_prune_task.py -- ne pas editer a la main.\r\n"
        "Option Explicit\r\n"
        "Dim sh, rc\r\n"
        'Set sh = CreateObject("WScript.Shell")\r\n'
        f'rc = sh.Run("{_vbs_literal(command_line)}", 0, True)\r\n'
        "WScript.Quit rc\r\n"
    )


def log_path_for(day: _dt.date | None = None) -> Path:
    day = day or _dt.date.today()
    return LOG_DIR / f"prune_{day:%Y%m%d}.log"


def task_exists() -> bool:
    return _run(["schtasks", "/Query", "/TN", TASK_NAME]).returncode == 0


def cmd_install(repo: Path, time: str, dry_run: bool = False) -> int:
    ok, msg = check_prune_fix_present(repo)
    if not ok:
        print(f"REFUSE : {msg}", file=sys.stderr)
        return 2
    print(f"garde OK : {msg}")
    launcher = launcher_path()
    command = build_schtasks_install(launcher, time)
    if dry_run:
        print(f"lanceur : {launcher}")
        print(f"lanceur VBS :\n{launcher_vbs(task_command(repo))}")
        print(f"schtasks argv : {command!r}")
        print(f"schtasks commande : {subprocess.list2cmdline(command)}")
        return 0
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    # Le lanceur est ecrit AVANT la tache : une tache installee dont le
    # lanceur manque echoue a chaque tour, sans rien journaliser.
    launcher.parent.mkdir(parents=True, exist_ok=True)
    launcher.write_text(launcher_vbs(task_command(repo)), encoding="utf-8", newline="")
    proc = _run(command)
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


def cmd_uninstall(dry_run: bool = False) -> int:
    command = ["schtasks", "/Delete", "/TN", TASK_NAME, "/F"]
    if dry_run:
        print(f"schtasks argv : {command!r}")
        print(f"schtasks commande : {subprocess.list2cmdline(command)}")
        return 0
    proc = _run(command)
    if proc.returncode != 0:
        print(f"suppression echouee : {proc.stdout.strip()} "
              f"{proc.stderr.strip()}", file=sys.stderr)
        return 2
    # Le lanceur part avec la tache : il ne sert plus a rien et pointerait vers
    # une tache absente. Il est regenere par le prochain --install.
    launcher = launcher_path()
    existed = launcher.is_file()
    launcher.unlink(missing_ok=True)
    print(f"tache supprimee : {TASK_NAME}")
    if existed:
        print(f"lanceur supprime : {launcher}")
    return 0


def cmd_run(repo: Path, warn_threshold: int = 20) -> int:
    """Invoque par la tache planifiee : journal horodate, pas de TTY.

    `--warn-threshold` (#3895) est relaie a l'organe : au-dela, il emet sa
    ligne [WARN][prune-task] (stderr, fusionne ici dans le journal) -- le
    rapport detaille des refus ne vit plus seulement en fin de journal, il
    porte un marqueur qu'une lane peut relever et poster sur le dashboard
    workspace au cycle suivant.

    `--quarantine-submodules` (#21743) est passe a l'organe : c'est la voie
    de decontamination d'un worktree MERGED a sous-modules, dont le `modules/`
    de son gitdir est DEPLACE en quarantaine (les objets sont preserves, la
    preuve est faite au moment du deplacement) -- jamais `--force`. Sans ce
    drapeau, l'organe refuse (`contains_submodules`) tout worktree a
    sous-modules, et le travail nocturne laissait alors en place, nuit apres
    nuit, des worktrees deja livres (#127, mesure du 11/11 : 6 worktrees
    refuses sur 90, dont `CoursIA-22741-portage`, PR 22811 MERGED). Le
    drapeau ne touche que CE cas : tous les autres predicats de l'organe
    (PR MERGED, commits non pousses, source sale, activite recente) restent
    inchanges. La quarantaine n'est PAS purgee ici : `--purge-quarantine`
    reste un geste nomme.
    """
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    log = log_path_for()
    stamp = _dt.datetime.now().strftime("%Y-%m-%dT%H:%M:%S")
    with log.open("a", encoding="utf-8") as fh:
        fh.write(f"\n=== {stamp} run start ===\n")
        fh.flush()
        proc = subprocess.run(
            [sys.executable, str(prune_script_path(repo)),
             "--path", str(repo), "--apply",
             "--warn-threshold", str(warn_threshold),
             "--quarantine-submodules"],
            stdout=fh, stderr=subprocess.STDOUT,
        )
        fh.write(f"=== {_dt.datetime.now().strftime('%Y-%m-%dT%H:%M:%S')} "
                 f"run end rc={proc.returncode} ===\n")
    # exit code non zero si l'organe a echoue -- visible dans le journal.
    # Depuis #3895, les REFUS de l'organe ne comptent plus comme echec :
    # rc!=0 = panne gh/git ou echec d'application, uniquement.
    return proc.returncode


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--install", action="store_true")
    p.add_argument("--status", action="store_true")
    p.add_argument("--uninstall", action="store_true")
    p.add_argument("--dry-run", action="store_true",
                   help="affiche la commande schtasks sans l'executer (install/uninstall)")
    p.add_argument("--run", action="store_true",
                   help="mode interne (invoque par la tache planifiee)")
    p.add_argument("--repo", type=Path,
                   default=Path(r"D:\Dev\CoursIA-2"),
                   help="checkout principal du depot (defaut D:\\Dev\\CoursIA-2)")
    p.add_argument("--time", default="03:17",
                   help="heure quotidienne HH:MM (defaut 03:17, hors heures ouvrables)")
    p.add_argument("--warn-threshold", type=int, default=20, metavar="N",
                   help="seuil refused > N pour l'emission [WARN][prune-task] "
                        "de l'organe en mode --run (defaut 20, #3895)")
    args = p.parse_args(argv)

    if args.dry_run and (args.install == args.uninstall or args.status or args.run):
        p.error("--dry-run requiert exactement --install ou --uninstall")
    repo = args.repo.resolve()
    if args.install:
        return cmd_install(repo, args.time, dry_run=args.dry_run)
    if args.status:
        return cmd_status()
    if args.uninstall:
        return cmd_uninstall(dry_run=args.dry_run)
    if args.run:
        return cmd_run(repo, warn_threshold=args.warn_threshold)
    p.print_help()
    return 1


if __name__ == "__main__":
    sys.exit(main())
