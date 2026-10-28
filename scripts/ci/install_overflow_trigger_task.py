#!/usr/bin/env python3
r"""Installateur de la tache planifiee de declenchement du controleur de
debordement (#22937, volet "declencheur").

Pourquoi une tache LOCALE
-------------------------
Le declencheur `workflow_run` est **impossible** ici, pour deux raisons
mesurees (voir le body de la PR) :

1. la politique d'isolation du depot REFUSE `workflow_run` sur un runner
   self-hosted (`scripts/ci/check_self_hosted_runner_policy.py`, code
   `WORKFLOW_RUN` : « workflow_run artifacts must never reach a self-hosted
   runner ») ; or le controleur tourne sur le parc local -- le mettre sur
   l'offre hebergee le ferait faire la queue dans l'offre qu'il observe
   (review ai-01 du 27/10) ;
2. un declencheur place sur `ubuntu-latest` ferait la queue dans l'offre
   **saturee** -- mesure du coordinateur du 28/10 : des gardes de quelques
   secondes crees entre 15:56 et 16:21Z n'ont demarre qu'entre 17:03 et
   17:10Z, soit environ une heure.

Le declencheur local, lui, ne traverse aucune file : il **declenche** le
workflow du depot, et c'est le workflow qui mesure et decide (avec les
secrets du depot). Le role du siege est donc celui d'un **minuterie**, pas
celui d'un decisionnaire.

Identite : le jeton n'est JAMAIS ecrit sur disque. La tache appelle
`gh auth token --user <compte>` au moment de l'execution : le jeton vit
dans le trousseau du siege, il n'apparait dans aucun fichier.

Modes :
    --dry-run [--interval N] [--start HH:MM]   imprime la commande
                                                 schtasks EXACTE et le
                                                 contenu EXACT des deux
                                                 lanceurs, sans rien ecrire
                                                 ni executer (discipline UAC :
                                                 la sortie du dry-run precede
                                                 toute inscription schtasks)
    --install    [--interval N] [--start HH:MM] ecrit les lanceurs puis cree
                                                 la tache (idempotent)
    --status                                      etat de la tache
    --uninstall                                   supprime la tache ET les
                                                 lanceurs
    --run                                         declenche UNE fois le
                                                 workflow du depot (le
                                                 controle de bout en bout de
                                                 la chaine, non elevee)

Garde : `--install` REFUSE de cabler si le workflow cible n'existe pas sur
le depot (cabler un declencheur vers un workflow absent deployerait un
echec silencieux toutes les N minutes -- meme garde que
`install_merge_ready_task.py`).

Fichiers :
    tache      : CoursIA\overflow_trigger
    lanceur    : %LOCALAPPDATA%\CoursIA\overflow_trigger\dispatch_overflow.cmd
    fenetre    : %LOCALAPPDATA%\CoursIA\overflow_trigger\run_hidden.vbs
    journal    : %LOCALAPPDATA%\CoursIA\overflow_trigger\logs\
                 overflow_trigger.log
"""
from __future__ import annotations

import argparse
import base64
import datetime as _dt
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

TASK_NAME = r"CoursIA\overflow_trigger"
THIS_FILE = Path(__file__).resolve()
BASE_DIR = (
    Path(os.environ.get("LOCALAPPDATA", str(Path.home() / "AppData" / "Local")))
    / "CoursIA"
    / "overflow_trigger"
)
LOG_DIR = BASE_DIR / "logs"
CMD_PATH = BASE_DIR / "dispatch_overflow.cmd"
VBS_PATH = BASE_DIR / "run_hidden.vbs"
# Lanceur masque (meme forme que `install_merge_ready_task.py`, audit de
# flotte du 24/09) : python.exe/gh sont des programmes console, donc chaque
# tour faisait flasher une fenetre noire sur le bureau interactif.
WSH_PATH = (
    Path(os.environ.get("SystemRoot", r"C:\Windows")) / "System32" / "wscript.exe"
)

DEFAULT_REPO = "jsboige/CoursIA"
DEFAULT_WORKFLOW = "ci-overflow-controller.yml"
# Compte sous lequel le declenchement est pose. Le jeton est lu dans le
# trousseau du siege AU MOMENT de l'execution ; il n'est jamais ecrit.
DEFAULT_ACCOUNT = "jsboige"
# Cadence : 15 min. Assez pour reagir dans la fenetre de saturation, assez
# peu pour ne pas occuper le parc local (le controleur tourne SUR ce parc).
DEFAULT_INTERVAL_MINUTES = 15
# Phase de depart : 00:07 -> 07, 22, 37, 52. Le cron du depot est a :31
# (le workflow `ci-overflow-controller.yml` porte `cron: '31 * * * *'`) :
# une phase decalee evite de faire decide deux fois en une minute.
DEFAULT_START = "00:07"
# Intervalle minimal passe au workflow : deux declenchements qui se
# chevauchent ne declenchent qu'une decision.
DEFAULT_MIN_INTERVAL_MINUTES = 15


def _run(cmd: list[str], **kw) -> subprocess.CompletedProcess:
    return subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        check=False,
        encoding="utf-8",
        errors="replace",
        **kw,
    )


def log_path_for(day: _dt.date | None = None) -> Path:
    day = day or _dt.date.today()
    return LOG_DIR / f"overflow_trigger_{day:%Y%m%d}.log"


def workflow_inputs(repo: str, workflow: str) -> tuple[set[str], str]:
    """Inputs `workflow_dispatch` que le workflow declare SUR LE DEPOT.

    Lu dans le fichier tel qu'il est sur la branche par defaut, pas dans le
    checkout local : c'est cette version que le declencheur executera
    reellement. Le declencheur ne passe QUE les inputs declares -- un input
    existant dans une PR mais absent de `main` ferait echouer chaque tir
    (`gh workflow run` rejette un input inconnu).
    """
    path = f".github/workflows/{workflow}"
    proc = _run(["gh", "api", f"repos/{repo}/contents/{path}"])
    if proc.returncode != 0:
        return set(), "contenu du workflow illisible"
    try:
        payload = json.loads(proc.stdout)
        text = base64.b64decode(payload["content"]).decode("utf-8")
    except Exception:  # pragma: no cover - forme de reponse inattendue
        return set(), "contenu du workflow illisible"
    try:
        import yaml
    except ImportError:
        return set(), "PyYAML indisponible"
    # `on:` se lit comme un booleen en YAML 1.1 : il faut le requoter.
    lines = [
        ('"on":' + line[3:]) if line.startswith("on:") else line
        for line in text.splitlines()
    ]
    try:
        data = yaml.safe_load("\n".join(lines))
    except Exception:  # pragma: no cover - YAML invalide
        return set(), "YAML du workflow illisible"
    if not isinstance(data, dict):
        return set(), "YAML du workflow inattendu"
    on = data.get("on")
    if not isinstance(on, dict):
        return set(), "declencheur workflow_dispatch absent"
    if "workflow_dispatch" not in on:
        return set(), "declencheur workflow_dispatch absent"
    dispatch = on.get("workflow_dispatch")
    inputs = dispatch.get("inputs") if isinstance(dispatch, dict) else None
    if not isinstance(inputs, dict):
        # `workflow_dispatch:` sans valeur = declencheur SANS input : la
        # distinction importe (l'un se cable, l'autre non).
        return set(), "workflow_dispatch sans input"
    return set(inputs), ""


def cmd_content(
    repo: str,
    workflow: str,
    account: str,
    min_interval: int,
    pass_min_interval: bool = True,
) -> str:
    """Contenu du lanceur .cmd : capture du jeton AU MOMENT de l'execution,
    puis declenchement du workflow du depot, puis journalisation.

    Le jeton n'est jamais ecrit dans le fichier : il est lu dans le
    trousseau du siege par `gh auth token`, au moment ou la tache tourne.
    """
    log = "%LOCALAPPDATA%\\CoursIA\\overflow_trigger\\logs\\overflow_trigger.log"
    dispatch = "gh workflow run %GH_WORKFLOW% --repo %GH_REPO%"
    if pass_min_interval:
        dispatch += " -f min_interval=%GH_MIN_INTERVAL%"
    return (
        "@echo off\r\n"
        "REM Genere par install_overflow_trigger_task.py -- ecrase a chaque\r\n"
        "REM --install, ne pas editer a la main. Aucun jeton n'est ecrit\r\n"
        "REM ici : il est lu dans le trousseau du siege au moment du tir.\r\n"
        "setlocal\r\n"
        f'set "GH_USER={account}"\r\n'
        f'set "GH_REPO={repo}"\r\n'
        f'set "GH_WORKFLOW={workflow}"\r\n'
        f'set "GH_MIN_INTERVAL={min_interval}"\r\n'
        f'set "LOG={log}"\r\n'
        'for /f "delims=" %%t in (\'gh auth token --user %GH_USER% 2^>nul\') '
        'do set "GH_TOKEN=%%t"\r\n'
        'if not defined GH_TOKEN (\r\n'
        '  echo [%DATE% %TIME%] jeton absent pour %GH_USER% -- rien declenche\r\n'
        f'  >> "%LOG%" echo [%DATE% %TIME%] jeton absent pour %GH_USER%\r\n'
        "  exit /b 2\r\n"
        ")\r\n"
        f'echo [%DATE% %TIME%] declenchement de %GH_WORKFLOW% sur %GH_REPO% '
        f'(intervalle minimal %GH_MIN_INTERVAL% min)>> "%LOG%"\r\n'
        f'{dispatch} >> "%LOG%" 2>&1\r\n'
        "echo %ERRORLEVEL% > \"%LOG%.rc\"\r\n"
        "exit /b %ERRORLEVEL%\r\n"
    )


def vbs_content(cmd_path: Path) -> str:
    """Contenu du lanceur run_hidden.vbs : le .cmd est execute en fenetre 0
    (masquee) et le code de sortie remonte a la tache planifiee.

    Le fichier est ecrit en ASCII : wscript lit les .vbs en ANSI, tout
    caractere non-ASCII casserait la ligne de commande silencieusement.
    """
    cmdline = f'cmd.exe /c ""{cmd_path}""'
    try:
        cmdline.encode("ascii")
    except UnicodeEncodeError as exc:  # pragma: no cover - garde
        raise ValueError(f"ligne de commande non-ASCII : {cmdline!r}") from exc
    escaped = cmdline.replace('"', '""')
    return (
        "' Lanceur genere par install_overflow_trigger_task.py -- ecrase a\r\n"
        "' chaque --install, ne pas editer a la main.\r\n"
        "' Fenetre 0 (masquee) et attente de fin : le code de sortie remonte.\r\n"
        "Dim WshShell\r\n"
        "Set WshShell = CreateObject(\"WScript.Shell\")\r\n"
        f"WScript.Quit WshShell.Run(\"{escaped}\", 0, True)\r\n"
    )


def task_action() -> list[str]:
    """Action enregistree dans le planificateur : wscript execute le lanceur
    VBS sans fenetre."""
    return [str(WSH_PATH), "//B", "//Nologo", str(VBS_PATH)]


def build_schtasks_install(
    cmd: list[str], interval_minutes: int, start: str
) -> list[str]:
    """Ligne schtasks /Create : toutes les N minutes, dans le contexte de
    l'utilisateur courant (le trousseau `gh` vit au niveau utilisateur)."""
    tr = subprocess.list2cmdline(cmd)
    return [
        "schtasks", "/Create", "/F",
        "/TN", TASK_NAME,
        "/SC", "MINUTE",
        "/MO", str(interval_minutes),
        "/ST", start,
        "/TR", tr,
    ]


def task_exists() -> bool:
    return _run(["schtasks", "/Query", "/TN", TASK_NAME]).returncode == 0


def workflow_exists(repo: str, workflow: str) -> tuple[bool, str]:
    """Le workflow cible existe-t-il sur le depot ? (garde de câblage)"""
    if shutil.which("gh") is None:
        return False, "gh est absent du PATH"
    proc = _run(
        ["gh", "workflow", "view", workflow, "--repo", repo]
    )
    if proc.returncode != 0:
        message = (proc.stderr or proc.stdout or "").strip().splitlines()
        return False, (
            f"workflow {workflow} introuvable sur {repo} "
            f"({message[-1] if message else 'raison inconnue'})"
        )
    return True, ""


def cmd_dry_run(
    repo: str,
    workflow: str,
    account: str,
    interval: int,
    start: str,
    min_interval: int,
) -> int:
    """N'ecrit RIEN et n'execute RIEN : la commande `schtasks` exacte et le
    contenu exact des deux lanceurs."""
    command = build_schtasks_install(task_action(), interval, start)
    inputs, inputs_reason = workflow_inputs(repo, workflow)
    pass_min_interval = "min_interval" in inputs
    if not pass_min_interval:
        print(
            f"DRY-RUN -- le workflow {workflow} sur {repo} ne declare PAS "
            f"l'input `min_interval` ({inputs_reason}) : le declencheur ne le "
            f"passera pas (un input inconnu fait echouer chaque tir)."
        )
    print("DRY-RUN -- commande schtasks que --install enregistrerait :")
    print("  " + subprocess.list2cmdline(command))
    print()
    print(f"DRY-RUN -- contenu de {CMD_PATH} que --install ecrirait :")
    print("-" * 60)
    print(cmd_content(repo, workflow, account, min_interval, pass_min_interval))
    print("-" * 60)
    print()
    print(f"DRY-RUN -- contenu de {VBS_PATH} que --install ecrirait :")
    print("-" * 60)
    print(vbs_content(CMD_PATH))
    print("-" * 60)
    print()
    print(f"DRY-RUN -- journal : {LOG_DIR}\\overflow_trigger.log")
    return 0


def cmd_install(
    repo: str,
    workflow: str,
    account: str,
    interval: int,
    start: str,
    min_interval: int,
) -> int:
    ok, reason = workflow_exists(repo, workflow)
    if not ok:
        print(f"REFUS -- {reason}", file=sys.stderr)
        print(
            "Le declencheur ne serait cable que vers un workflow inexistant : "
            "chaque tour echouerait en silence.",
            file=sys.stderr,
        )
        return 2
    inputs, _inputs_reason = workflow_inputs(repo, workflow)
    pass_min_interval = "min_interval" in inputs
    BASE_DIR.mkdir(parents=True, exist_ok=True)
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    CMD_PATH.write_text(
        cmd_content(repo, workflow, account, min_interval, pass_min_interval),
        encoding="ascii",
    )
    VBS_PATH.write_text(vbs_content(CMD_PATH), encoding="ascii")
    command = build_schtasks_install(task_action(), interval, start)
    proc = _run(command)
    if proc.returncode != 0:
        print(
            f"schtasks /Create echoue (rc={proc.returncode}) : "
            f"{(proc.stderr or proc.stdout or '').strip()}",
            file=sys.stderr,
        )
        return 1
    print(f"tache creee : {TASK_NAME} (toutes les {interval} min, depart {start})")
    print(f"lanceur cmd : {CMD_PATH}")
    print(f"lanceur vbs : {VBS_PATH}")
    print(f"journal     : {LOG_DIR}")
    print(
        "verification : schtasks /Query /TN \"" + TASK_NAME + "\" /V /FO LIST"
    )
    return 0


def cmd_status() -> int:
    proc = _run(["schtasks", "/Query", "/TN", TASK_NAME, "/V", "/FO", "LIST"])
    print(proc.stdout or proc.stderr or f"rc={proc.returncode}")
    return 0 if proc.returncode == 0 else 1


def cmd_uninstall() -> int:
    proc = _run(["schtasks", "/Delete", "/TN", TASK_NAME, "/F"])
    print(
        f"tache supprimee (rc={proc.returncode})"
        if proc.returncode == 0
        else f"tache absente ou suppression impossible (rc={proc.returncode})"
    )
    for path in (CMD_PATH, VBS_PATH):
        if path.exists():
            path.unlink()
            print(f"lanceur supprime : {path}")
    return 0


def cmd_run() -> int:
    """Declenche UNE fois le workflow du depot : c'est le controle de bout
    en bout de la chaine, non eleve (le lanceur inclus)."""
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    proc = _run(["cmd.exe", "/c", str(CMD_PATH)])
    if proc.returncode != 0:
        print(
            f"declenchement echoue (rc={proc.returncode}) : "
            f"{(proc.stderr or proc.stdout or '').strip()}",
            file=sys.stderr,
        )
    else:
        print(f"declenchement effectue (rc={proc.returncode})")
    print(f"journal : {log_path_for()}")
    return proc.returncode


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Tache planifiee locale de declenchement du controleur de "
            "debordement (#22937)."
        )
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="imprime la commande schtasks exacte sans l'executer",
    )
    parser.add_argument("--install", action="store_true")
    parser.add_argument("--status", action="store_true")
    parser.add_argument("--uninstall", action="store_true")
    parser.add_argument("--run", action="store_true")
    parser.add_argument("--repo", default=DEFAULT_REPO)
    parser.add_argument("--workflow", default=DEFAULT_WORKFLOW)
    parser.add_argument("--account", default=DEFAULT_ACCOUNT)
    parser.add_argument("--interval", type=int, default=DEFAULT_INTERVAL_MINUTES)
    parser.add_argument("--start", default=DEFAULT_START)
    parser.add_argument(
        "--min-interval", type=int, default=DEFAULT_MIN_INTERVAL_MINUTES
    )
    args = parser.parse_args(argv)

    if args.install:
        return cmd_install(
            args.repo, args.workflow, args.account, args.interval,
            args.start, args.min_interval,
        )
    if args.status:
        return cmd_status()
    if args.uninstall:
        return cmd_uninstall()
    if args.run:
        return cmd_run()
    return cmd_dry_run(
        args.repo, args.workflow, args.account, args.interval,
        args.start, args.min_interval,
    )


if __name__ == "__main__":
    sys.exit(main())
