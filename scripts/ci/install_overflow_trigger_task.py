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

Deux formes cohabitent (`--mode`), et la forme retenue le 2026-11-12
(arbitrage de l'adjoint du coordinateur) est `local` :

- `local` (forme (b)) : le controleur **tourne sur le siege**. Le parc
  self-hosted fait la queue -- mesure du 2026-11-12 sur 12 declenchements
  horaires consecutifs : mediane ~40 min entre la creation du run et le
  demarrage de son job, pire cas ~2 h, 4 runs sur 30 annules avant
  demarrage -- et le controleur y agit donc sur un etat vieux de deux
  heures. La cadence est bornee par le **marqueur local**, qui est l'etat
  VIVANT du declencheur : l'API des runs du controleur decrit un etat
  MORT pour un passage local (aucun run n'est cree), et une garde qui lit
  un etat mort ne garde rien.
- `dispatch` (forme historique) : le siege declenche le workflow du depot,
  qui mesure et decide avec les secrets du depot.

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
import json
import os
import re
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
# Variable de depot pilotee par le controleur.
DEFAULT_VARIABLE = "CI_OVERFLOW_LOCAL"
# Formes du declencheur. `local` execute le controleur SUR LE SIEGE ;
# `dispatch` declenche le workflow du depot (forme historique). La forme
# retenue le 2026-11-12 est `local` : le parc self-hosted fait la queue
# (mesure dans l'en-tete du module), et l'API des runs du controleur
# decrit un etat MORT pour un passage local.
MODE_LOCAL = "local"
MODE_DISPATCH = "dispatch"
MODES = (MODE_LOCAL, MODE_DISPATCH)
DEFAULT_MODE = MODE_LOCAL
# Marqueur de cadence LOCAL : l'etat vivant du declencheur (forme (b)).
# C'est lui que la garde d'intervalle minimal lit et ecrit.
MARKER_PATH = BASE_DIR / "cadence.json"
# Resume JSON du passage (verdict, ecarte ou mesure) : le lanceur le lit
# pour distinguer un passage ECARTE par la garde d'un passage mesure.
SUMMARY_PATH = LOG_DIR / "overflow_trigger.json"
# Checkout local ou le controleur est execute (forme `local`). Par defaut,
# la racine du depot d'ou vient ce script.
DEFAULT_CHECKOUT = THIS_FILE.parents[2]
# Interpreteur python du siege (forme `local`).
DEFAULT_PYTHON = "python"
# Motifs de LECTURE IMPOSSIBLE du workflow du depot : dans ces cas, l'ecart
# entre le lanceur installe et le lanceur genere ne peut pas etre etabli,
# et le dire « diverge » serait faux. Ces cas rendent « inconnu », sous
# leur PROPRE code de sortie (distinct de celui du drift).
UNKNOWN_INPUT_REASONS = frozenset(
    {
        "contenu du workflow illisible",
        "PyYAML indisponible",
        "YAML du workflow illisible",
        "YAML du workflow inattendu",
    }
)
# Compte sous lequel le declenchement est pose. Le jeton est lu dans le
# trousseau du siege AU MOMENT de l'execution ; il n'est jamais ecrit.
DEFAULT_ACCOUNT = "jsboige"
# Cadence : 60 min. Elle est fixee par le COUT, pas par une preference :
# une mesure coute 313 appels `gh` (mesure du 2026-10-27) et le jeton du
# depot (`github.token`) plafonne a 1 000 appels/h pour le repo -- plafond
# partage avec les autres jobs. Le cron horaire du depot consomme deja
# 313 appels/h : la minuterie locale ne peut donc ajouter qu'UN passage par
# heure (313/h) pour tenir sous ~630 appels/h, soit 63 % du plafond. Ce
# que la minuterie locale apporte n'est pas de la frequence mais de la
# FIABILITE : la livraison des crons du depot est mesuree a 22 % des tics
# servis (mediane 289 min de retard), la minuterie locale garantit une
# decision au moins horaire.
DEFAULT_INTERVAL_MINUTES = 60
# Phase de depart : 00:07 -> 07 de chaque heure. Le cron du depot est a
# :31 (le workflow `ci-overflow-controller.yml` porte `cron: '31 * * * *'`) :
# une phase decalee evite de faire decide deux fois en une minute.
DEFAULT_START = "00:07"
# Intervalle minimal passe au workflow : deux declenchements qui se
# chevauchent ne declenchent qu'une decision. Il vaut 30 min, soit la MOITIE
# de la cadence : l'ecart se lit sur le dernier PASSAGE (run confondu --
# mesure ou ecarte), donc une garde egale a la cadence rendrait la minuterie
# locale dependante du cron du depot -- qui mesure a :31, soit 36 min avant
# le tic local de :07 : le tic local serait alors ecarte. Avec 30 min, le
# tic local passe toujours (36 min d'ecart), et le cron du depot -- qui
# mesure sans garde -- reste le filet horaire si la minuterie locale meurt.
DEFAULT_MIN_INTERVAL_MINUTES = 30


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


def log_path_for(day: object | None = None) -> Path:
    """Journal du declencheur.

    Le lanceur `.cmd` ecrit un fichier de NOM FIXE (`overflow_trigger.log`) :
    c'est le seul nom qu'un fichier batch peut garantir (la date du systeme
    y depend de la locale). Le parametre `day` est donc ignore -- il reste
    ici pour que l'appelant n'ait pas a le connaître.
    """
    return LOG_DIR / "overflow_trigger.log"


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


def local_cmd_content(
    checkout: Path,
    python_exe: str,
    repo: str,
    account: str,
    min_interval: int,
) -> str:
    """Contenu du lanceur .cmd, forme (b) : le controleur TOURNE SUR LE SIEGE.

    Le parc self-hosted fait la queue (mesure du 2026-11-12 : mediane
    ~40 min entre la creation du run et le demarrage de son job, pire cas
    ~2 h, 4 runs sur 30 annules avant demarrage) ; le controleur y agit
    donc sur un etat vieux de deux heures. Ici il s'execute sur le siege,
    au moment du tic.

    L'EFFET est constate dans le MARQUEUR LOCAL : le passage ecrit le
    marqueur, un passage ecarte par la garde de cadence ne l'ecrit pas.
    L'instrument regarde donc l'etat, pas son propre code de sortie -- le
    defaut qu'E2/1 corrigeait sur la forme `dispatch` (#25510).

    Les trois canaux du controleur (mesure, ecriture de la variable,
    inventaire des runners) sont servis par le jeton DU SIEGE : les
    secrets du depot ne sont pas lisibles depuis le siege. Le jeton
    d'ecriture est pose EXPLICITEMENT -- le controleur ne fait aucun
    repli sur un autre jeton.
    """
    controller = (
        Path(checkout) / "scripts" / "ci" / "ci_overflow_controller.py"
    )
    command = subprocess.list2cmdline(
        [
            python_exe,
            str(controller),
            "--repo", repo,
            "--variable", DEFAULT_VARIABLE,
            "--apply",
            "--min-interval", str(min_interval),
            "--local-marker", str(MARKER_PATH),
            "--summary-out", str(SUMMARY_PATH),
        ]
    )
    return (
        "@echo off\r\n"
        "REM Genere par install_overflow_trigger_task.py -- ecrase a chaque\r\n"
        "REM --install, ne pas editer a la main. Aucun jeton n'est ecrit\r\n"
        "REM ici : il est lu dans le trousseau du siege au moment du tir.\r\n"
        "REM\r\n"
        "REM FORME (b) : le controleur s'execute SUR LE SIEGE. Le parc\r\n"
        "REM self-hosted fait la queue (mesure du 2026-11-12 : mediane\r\n"
        "REM ~40 min, pire cas ~2 h), et le controleur y agirait sur un\r\n"
        "REM etat vieux de deux heures. La cadence est bornee par le\r\n"
        "REM MARQUEUR LOCAL : etat VIVANT du declencheur, la ou l'API\r\n"
        "REM des runs du controleur decrit un etat MORT pour un passage\r\n"
        "REM local (aucun run n'est cree).\r\n"
        "setlocal\r\n"
        f'set "GH_USER={account}"\r\n'
        f'set "GH_REPO={repo}"\r\n'
        f'set "GH_MIN_INTERVAL={min_interval}"\r\n'
        f'set "MARKER={MARKER_PATH}"\r\n'
        f'set "SUMMARY={SUMMARY_PATH}"\r\n'
        f'set "LOG={LOG_DIR}\\overflow_trigger.log"\r\n'
        'for /f "delims=" %%t in (\'gh auth token --user %GH_USER% 2^>nul\') '
        'do set "GH_TOKEN=%%t"\r\n'
        'if not defined GH_TOKEN (\r\n'
        '  echo [%DATE% %TIME%] jeton absent pour %GH_USER% -- rien declenche\r\n'
        f'  >> "%LOG%" echo [%DATE% %TIME%] jeton absent pour %GH_USER%\r\n'
        "  exit /b 2\r\n"
        ")\r\n"
        "REM Les trois canaux du controleur sont servis par le jeton du\r\n"
        "REM siege : les secrets du depot ne sont pas lisibles d'ici. Le\r\n"
        "REM jeton d'ECRITURE est pose EXPLICITEMENT (aucun repli).\r\n"
        'set "ACTIONS_VARIABLES_PAT=%GH_TOKEN%"\r\n'
        'set "RUNNERS_READ_PAT=%GH_TOKEN%"\r\n'
        "REM AVANT : l'etat du marqueur de cadence.\r\n"
        'set "MARKER_BEFORE="\r\n'
        'if exist "%MARKER%" for %%f in ("%MARKER%") do set "MARKER_BEFORE=%%~tf"\r\n'
        f'echo [%DATE% %TIME%] passage local du controleur '
        f'(intervalle minimal %GH_MIN_INTERVAL% min)>> "%LOG%"\r\n'
        f"{command} >> \"%LOG%\" 2>&1\r\n"
        'set "RC=%ERRORLEVEL%"\r\n'
        'if not "%RC%"=="0" (\r\n'
        '  >> "%LOG%" echo [%DATE% %TIME%] passage REFUSE rc=%RC% '
        '-- aucune decision rendue\r\n'
        '  echo %RC% > "%LOG%.rc"\r\n'
        "  exit /b %RC%\r\n"
        ")\r\n"
        "REM APRES : le marqueur a-t-il bouge ? Un passage MESURE l'ecrit ;\r\n"
        "REM un passage ECARTE par la garde de cadence ne l'ecrit pas -- et\r\n"
        "REM le resume le dit (\"skipped\"), ce qui n'est pas un echec.\r\n"
        'set "MARKER_AFTER="\r\n'
        'if exist "%MARKER%" for %%f in ("%MARKER%") do set "MARKER_AFTER=%%~tf"\r\n'
        'findstr /c:"verdict : SKIPPED" "%SUMMARY%" >nul 2>&1\r\n'
        'if not errorlevel 1 (\r\n'
        '  >> "%LOG%" echo [%DATE% %TIME%] ecarte par la garde de cadence, '
        'intervalle minimal %GH_MIN_INTERVAL% min -- aucune mesure\r\n'
        '  echo 0 > "%LOG%.rc"\r\n'
        "  exit /b 0\r\n"
        ")\r\n"
        'if not defined MARKER_AFTER (\r\n'
        '  >> "%LOG%" echo [%DATE% %TIME%] EFFET NON CONSTATE : le marqueur '
        'de cadence est absent apres un passage mesure\r\n'
        '  echo 3 > "%LOG%.rc"\r\n'
        "  exit /b 3\r\n"
        ")\r\n"
        'if "%MARKER_AFTER%"=="%MARKER_BEFORE%" (\r\n'
        '  >> "%LOG%" echo [%DATE% %TIME%] EFFET NON CONSTATE : le marqueur '
        'de cadence n\'a pas bouge : avant=%MARKER_BEFORE% '
        'apres=%MARKER_AFTER%\r\n'
        '  echo 3 > "%LOG%.rc"\r\n'
        "  exit /b 3\r\n"
        ")\r\n"
        '>> "%LOG%" echo [%DATE% %TIME%] effet constate : marqueur de '
        'cadence %MARKER_AFTER%\r\n'
        'echo 0 > "%LOG%.rc"\r\n'
        "exit /b 0\r\n"
    )


def cmd_content(
    repo: str,
    workflow: str,
    account: str,
    min_interval: int,
    pass_min_interval: bool = True,
) -> str:
    """Contenu du lanceur .cmd : capture du jeton AU MOMENT de l'execution,
    declenchement du workflow du depot, VERIFICATION DE L'EFFET, puis
    journalisation.

    Le jeton n'est jamais ecrit dans le fichier : il est lu dans le
    trousseau du siege par `gh auth token`, au moment ou la tache tourne.

    La verification de l'effet (#25510, E2) lit l'id du plus recent run du
    workflow AVANT et APRES le declenchement : si l'id n'a pas change, le
    declenchement n'a produit AUCUN run, et le lanceur sort en 3 avec un
    motif nomme. Mesure du 2026-11-12 (19:07Z, ai-01) : la tache a rendu
    rc 0, son journal n'a trace que « declenchement », et AUCUN run n'a ete
    cree -- l'instrument voyait son propre code de sortie, pas l'effet.
    """
    log = "%LOCALAPPDATA%\\CoursIA\\overflow_trigger\\logs\\overflow_trigger.log"
    dispatch = "gh workflow run %GH_WORKFLOW% --repo %GH_REPO%"
    if pass_min_interval:
        dispatch += " -f min_interval=%GH_MIN_INTERVAL%"

    def read_run(var: str) -> str:
        """Lecture de l'id du plus recent run DECLENCHE (pas de cron).

        Le filtre `--event workflow_dispatch` est indispensable : le
        workflow porte aussi un cron horaire (`:31`), et un run de cron ne
        prouve pas qu'un declenchement manuel a abouti. Sans lui, l'effet
        mesure pouvait etre celui du cron.
        """
        return (
            'for /f "delims=" %%r in (\'gh run list --workflow %GH_WORKFLOW% '
            '--repo %GH_REPO% --event workflow_dispatch --limit 1 '
            '--json databaseId --jq ".[0].databaseId" 2^>nul\') '
            f'do set "{var}=%%r"\r\n'
        )

    read_before = read_run("RUN_BEFORE")
    read_after = read_run("RUN_AFTER")

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
        # AVANT : l'id du plus recent run du workflow, pour comparer l'effet.
        + read_before
        + f'echo [%DATE% %TIME%] declenchement de %GH_WORKFLOW% sur %GH_REPO% '
        f'(intervalle minimal %GH_MIN_INTERVAL% min)>> "%LOG%"\r\n'
        f'{dispatch} >> "%LOG%" 2>&1\r\n'
        # Le code de sortie est capture DANS une variable : dans un bloc
        # `if (...)`, `%ERRORLEVEL%` est developpe a la PARSE du bloc, donc
        # il vaudrait celui d'avant le declenchement.
        'set "RC=%ERRORLEVEL%"\r\n'
        'if not "%RC%"=="0" (\r\n'
        '  >> "%LOG%" echo [%DATE% %TIME%] declenchement REFUSE rc=%RC%'
        " -- aucun run demande\r\n"
        '  echo %RC% > "%LOG%.rc"\r\n'
        "  exit /b %RC%\r\n"
        ")\r\n"
        # ATTENTE BORNEE : le run apparait 2 a 3 s apres la ligne
        # "declenchement" (mesure du 2026-11-12, 19:07Z sur ai-01) ; lire
        # trop tot conclurait a tort qu'aucun run n'a ete cree. `timeout`
        # ne marche pas sans console : l'attente se fait par `ping -n 11`
        # (10 s), six fois au plus.
        'set /a WAITED=0\r\n'
        'set "RUN_AFTER="\r\n'
        ":WAIT_RUN\r\n"
        "set /a WAITED+=10\r\n"
        "ping -n 11 127.0.0.1 >nul\r\n"
        + read_after
        + 'if defined RUN_AFTER goto WAIT_RUN_END\r\n'
        + "if %WAITED% GEQ 60 goto WAIT_RUN_END\r\n"
        + "goto WAIT_RUN\r\n"
        ":WAIT_RUN_END\r\n"
        '>> "%LOG%" echo [%DATE% %TIME%] attente de l\'apparition du run : '
        "%WAITED% s\r\n"
        # APRES : l'id a-t-il change ? Un declenchement accepte peut ne
        # produire AUCUN run (mesure du 2026-11-12, 19:07Z sur ai-01 : la
        # tache a rendu rc 0, le journal n'a rien trace, et AUCUN run n'a
        # ete cree). Un instrument qui ne voit que son propre code de sortie
        # croit avoir declenche ; il faut voir l'EFFET.
        # Un id ILLISIBLE (lecture des runs echouee) echoue FERME : sans
        # "avant", la comparaison n'a pas de sens -- le cas "avant vide,
        # apres lu" ne vaut PAS "effet constate".
        'if not defined RUN_BEFORE (\r\n'
        '  >> "%LOG%" echo [%DATE% %TIME%] EFFET NON CONSTATE : l\'id du run '
        'precedent est illisible : lecture des runs echouee\r\n'
        '  echo 3 > "%LOG%.rc"\r\n'
        "  exit /b 3\r\n"
        ")\r\n"
        'if not defined RUN_AFTER (\r\n'
        '  >> "%LOG%" echo [%DATE% %TIME%] EFFET NON CONSTATE : aucun run cree '
        ': id absent apres l\'attente bornee\r\n'
        '  echo 3 > "%LOG%.rc"\r\n'
        "  exit /b 3\r\n"
        ")\r\n"
        'if "%RUN_AFTER%"=="%RUN_BEFORE%" (\r\n'
        '  >> "%LOG%" echo [%DATE% %TIME%] EFFET NON CONSTATE : aucun run cree '
        ': id avant=%RUN_BEFORE% id apres=%RUN_AFTER%\r\n'
        '  echo 3 > "%LOG%.rc"\r\n'
        "  exit /b 3\r\n"
        ")\r\n"
        '>> "%LOG%" echo [%DATE% %TIME%] effet constate : run %RUN_AFTER%\r\n'
        "echo 0 > \"%LOG%.rc\"\r\n"
        "exit /b 0\r\n"
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


def checkout_usable(checkout: Path) -> tuple[bool, str]:
    """Le checkout local peut-il executer le controleur ?

    La forme `local` execute le controleur DEPUIS le checkout : sans le
    script, le passage echoue ; sans le repertoire des workflows, la
    cohorte n'est pas etablie, la mesure est illisible et le controleur
    n'ecrit rien (fail-CLOSED).
    """
    controller = Path(checkout) / "scripts" / "ci" / "ci_overflow_controller.py"
    if not controller.is_file():
        return False, f"controleur absent du checkout ({controller})"
    workflows = Path(checkout) / ".github" / "workflows"
    if not workflows.is_dir():
        return False, f"repertoire des workflows absent du checkout ({workflows})"
    return True, ""


def launcher_content(
    mode: str,
    checkout: Path,
    python_exe: str,
    repo: str,
    workflow: str,
    account: str,
    min_interval: int,
) -> tuple[str, str]:
    """Contenu du lanceur .cmd pour la forme demandee.

    Rend `(contenu, avertissement)`. L'avertissement est non vide quand
    la forme ne peut pas etre cablee telle quelle (input absent du
    workflow, dans la forme `dispatch`).
    """
    if mode == MODE_LOCAL:
        return (
            local_cmd_content(
                checkout, python_exe, repo, account, min_interval
            ),
            "",
        )
    inputs, reason = workflow_inputs(repo, workflow)
    pass_min_interval = "min_interval" in inputs
    if not pass_min_interval:
        reason = (
            f"le workflow {workflow} sur {repo} ne declare PAS l'input "
            f"`min_interval` ({reason}) : le declencheur ne le passera pas "
            f"(un input inconnu fait echouer chaque tir)"
        )
    return (
        cmd_content(repo, workflow, account, min_interval, pass_min_interval),
        reason,
    )


def cmd_dry_run(
    mode: str,
    checkout: Path,
    python_exe: str,
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
    content, warning = launcher_content(
        mode, checkout, python_exe, repo, workflow, account, min_interval
    )
    print(f"DRY-RUN -- forme du declencheur : {mode}")
    if mode == MODE_LOCAL:
        ok, reason = checkout_usable(checkout)
        print(
            f"DRY-RUN -- checkout : {checkout} "
            f"({'exploitable' if ok else reason})"
        )
        print(f"DRY-RUN -- marqueur de cadence : {MARKER_PATH}")
    if warning:
        print(f"DRY-RUN -- {warning}")
    print("DRY-RUN -- commande schtasks que --install enregistrerait :")
    print("  " + subprocess.list2cmdline(command))
    print()
    print(f"DRY-RUN -- contenu de {CMD_PATH} que --install ecrirait :")
    print("-" * 60)
    print(content)
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
    mode: str,
    checkout: Path,
    python_exe: str,
    repo: str,
    workflow: str,
    account: str,
    interval: int,
    start: str,
    min_interval: int,
) -> int:
    if mode == MODE_LOCAL:
        ok, reason = checkout_usable(checkout)
    else:
        ok, reason = workflow_exists(repo, workflow)
    if not ok:
        print(f"REFUS -- {reason}", file=sys.stderr)
        print(
            "Le declencheur ne serait cable que vers une cible inexistante : "
            "chaque tour echouerait en silence.",
            file=sys.stderr,
        )
        return 2
    content, _warning = launcher_content(
        mode, checkout, python_exe, repo, workflow, account, min_interval
    )
    BASE_DIR.mkdir(parents=True, exist_ok=True)
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    # `newline=""` : le contenu porte deja ses "\r\n" explicites. Sans ce
    # parametre, `write_text` traduit chaque "\n" en os.linesep et ecrit
    # "\r\r\n" -- mesure sur l'artefact installe le 2026-11-12 : 20 lignes
    # sur 20 portaient le CR supplementaire. Le fichier etait tolere par
    # cmd.exe, mais il n'etait plus byte-identique a ce que le generateur
    # declare, et la detection de drift ne aurait pu rien dire.
    CMD_PATH.write_text(content, encoding="ascii", newline="")
    VBS_PATH.write_text(vbs_content(CMD_PATH), encoding="ascii", newline="")
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
    print(f"forme        : {mode}")
    print(f"lanceur cmd : {CMD_PATH}")
    print(f"lanceur vbs : {VBS_PATH}")
    print(f"journal     : {LOG_DIR}")
    print(
        "verification : schtasks /Query /TN \"" + TASK_NAME + "\" /V /FO LIST"
    )
    return 0


def _norm_lines(text: str) -> list[str]:
    """Lignes normalisees (fins de ligne unifiees a "\\n").

    Le lanceur installe peut porter des fins de ligne doubles ("\\r\\r\\n",
    mesure du 2026-11-12) : sans normalisation, `splitlines()` y voit des
    lignes VIDES et le rapport de driftdesigne la ligne 2 comme vide --
    un rapport qui ne dit pas ce qui differe.
    """
    return re.sub(r"\r+\n", "\n", text).replace("\r", "\n").split("\n")


def _first_diff(got: str, want: str) -> str:
    """Premiere difference entre le lanceur installe et le lanceur genere,
    en une phrase courte (le journal doit rester lisible)."""
    got_lines = _norm_lines(got)
    want_lines = _norm_lines(want)
    for index, (a, b) in enumerate(zip(got_lines, want_lines), start=1):
        if a != b:
            return (
                f"ligne {index} : installe={a.strip()!r} "
                f"attendu={b.strip()!r}"
            )
    if len(got_lines) != len(want_lines):
        return (
            f"{len(got_lines)} ligne(s) installee(s) contre "
            f"{len(want_lines)} attendue(s)"
        )
    return "memes lignes, fins de ligne differentes"


def launcher_drift(
    mode: str,
    checkout: Path,
    python_exe: str,
    repo: str,
    workflow: str,
    account: str,
    min_interval: int,
) -> tuple[list[str], list[str]]:
    """Ecarts entre les lanceurs INSTALLES et ceux que le generateur ecrit.

    Un artefact installe derriere son generateur s'ecarte sans bruit : le
    declencheur peut alors faire autre chose que ce que le depot declare.
    Mesure du 2026-11-12 (ai-01) : le lanceur installe ne passait pas
    `min_interval` -- que le generateur ecrit depuis -- et chacune de ses
    20 lignes portait un CR supplementaire ; rien ne le signalait.

    Rend `(ecarts, inconnus)`. Un ecart est une DIFFERENCE mesuree ;
    un inconnu est une LECTURE IMPOSSIBLE (le workflow du depot n'a pas pu
    etre lu) : dans ce cas, l'ecart ne peut pas etre etabli, et le dire
    « diverge » serait faux. Le cas inconnu porte son PROPRE code de
    sortie, distinct de celui du drift.
    """
    unknowns: list[str] = []
    if mode == MODE_DISPATCH:
        _inputs, inputs_reason = workflow_inputs(repo, workflow)
        if inputs_reason in UNKNOWN_INPUT_REASONS:
            unknowns.append(
                f"contenu du workflow {workflow} sur {repo} illisible "
                f"({inputs_reason}) : l'ecart avec le lanceur installe ne "
                f"peut pas etre etabli"
            )
            return [], unknowns
    expected = {
        CMD_PATH: launcher_content(
            mode, checkout, python_exe, repo, workflow, account, min_interval
        )[0],
        VBS_PATH: vbs_content(CMD_PATH),
    }
    drifts: list[str] = []
    for path, want in expected.items():
        if not path.exists():
            drifts.append(f"{path} absent (declencheur non installe)")
            continue
        # Lecture en BYTES : `read_text` traduit les fins de ligne, donc un
        # lanceur parfaitement ecrit serait lu different de ce que le
        # generateur declare -- et l'ecart de fins de ligne, qui est
        # exactement ce qu'on cherche ici, serait invisible.
        got = path.read_bytes().decode("ascii", errors="replace")
        if got == want:
            continue
        drifts.append(
            f"{path} DIVERGE du lanceur genere : {_first_diff(got, want)}"
        )
    return drifts, unknowns


def cmd_status(
    mode: str,
    checkout: Path,
    python_exe: str,
    repo: str,
    workflow: str,
    account: str,
    min_interval: int,
) -> int:
    proc = _run(["schtasks", "/Query", "/TN", TASK_NAME, "/V", "/FO", "LIST"])
    print(proc.stdout or proc.stderr or f"rc={proc.returncode}")
    drifts, unknowns = launcher_drift(
        mode, checkout, python_exe, repo, workflow, account, min_interval
    )
    if drifts:
        print(
            "DRIFT -- les lanceurs INSTALLES different de ce que le "
            "generateur ecrit :"
        )
        for line in drifts:
            print(f"  - {line}")
        print(
            "  remedy : python scripts/ci/install_overflow_trigger_task.py "
            "--install"
        )
        return 3
    if unknowns:
        print("INCONNU -- l'ecart avec le lanceur installe n'a pas pu etre etabli :")
        for line in unknowns:
            print(f"  - {line}")
        return 4
    print("lanceurs conformes au generateur")
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


def cmd_run(
    mode: str,
    checkout: Path,
    python_exe: str,
    repo: str,
    account: str,
    min_interval: int,
    ignore_cadence: bool = False,
) -> int:
    """Declenche UNE fois le declencheur : c'est le controle de bout en
    bout de la chaine, non eleve (le lanceur inclus).

    `ignore_cadence` court-circuite la garde d'intervalle minimal (la
    forme `local` rend `SKIPPED` quand le marqueur est trop recent) :
    c'est un DIAGNOSTIC, pas le declencheur installe -- la garde du
    declencheur installe, elle, reste a son intervalle.
    """
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    if ignore_cadence and mode == MODE_LOCAL:
        command = [
            python_exe,
            str(Path(checkout) / "scripts" / "ci" / "ci_overflow_controller.py"),
            "--repo", repo,
            "--variable", DEFAULT_VARIABLE,
            "--apply",
            "--min-interval", "0",
            "--local-marker", str(MARKER_PATH),
            "--summary-out", str(SUMMARY_PATH),
        ]
        proc = _run(command)
    else:
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
    parser.add_argument(
        "--ignore-cadence",
        action="store_true",
        help=(
            "avec --run : court-circuite la garde d'intervalle minimal "
            "(diagnostic ; la garde du declencheur installe reste en place)"
        ),
    )
    parser.add_argument(
        "--mode",
        choices=MODES,
        default=DEFAULT_MODE,
        help=(
            "forme du declencheur : `local` execute le controleur sur le "
            "siege (forme (b) de #25510, retenue le 2026-11-12), "
            "`dispatch` declenche le workflow du depot (forme historique)"
        ),
    )
    parser.add_argument(
        "--checkout",
        type=Path,
        default=DEFAULT_CHECKOUT,
        help=(
            "checkout local ou le controleur est execute (forme `local`) ; "
            "par defaut, la racine du depot d'ou vient ce script"
        ),
    )
    parser.add_argument(
        "--python",
        dest="python_exe",
        default=DEFAULT_PYTHON,
        help="interpreteur python du siege (forme `local`)",
    )
    parser.add_argument("--repo", default=DEFAULT_REPO)
    parser.add_argument("--workflow", default=DEFAULT_WORKFLOW)
    parser.add_argument("--account", default=DEFAULT_ACCOUNT)
    parser.add_argument("--interval", type=int, default=DEFAULT_INTERVAL_MINUTES)
    parser.add_argument("--start", default=DEFAULT_START)
    parser.add_argument(
        "--min-interval", type=int, default=DEFAULT_MIN_INTERVAL_MINUTES
    )
    args = parser.parse_args(argv)

    # `--dry-run` l'EMPORTE sur `--install`.
    #
    # Mesure du 2026-11-12 (lane myia-ai-01:CoursIA-2) : `--install
    # --dry-run` INSTALLAIT la tache et ecrivait les deux lanceurs. La
    # cause est l'ordre des tests : `args.install` etait teste avant que
    # `args.dry_run` soit lu -- et il n'etait jamais lu du tout : le
    # dry-run n'etait que la branche par defaut (aucun drapeau), donc
    # `--dry-run` n'etait qu'un drapeau MORT. Un drapeau nomme "dry-run"
    # qui installe quand meme casse la preparation du geste : la discipline
    # UAC exige que la sortie du dry-run precede l'inscription.
    if args.dry_run:
        return cmd_dry_run(
            args.mode, args.checkout, args.python_exe, args.repo,
            args.workflow, args.account, args.interval, args.start,
            args.min_interval,
        )
    if args.install:
        return cmd_install(
            args.mode, args.checkout, args.python_exe, args.repo,
            args.workflow, args.account, args.interval, args.start,
            args.min_interval,
        )
    if args.status:
        return cmd_status(
            args.mode, args.checkout, args.python_exe, args.repo,
            args.workflow, args.account, args.min_interval,
        )
    if args.uninstall:
        return cmd_uninstall()
    if args.run:
        return cmd_run(
            args.mode, args.checkout, args.python_exe, args.repo,
            args.account, args.min_interval, args.ignore_cadence,
        )
    return cmd_dry_run(
        args.mode, args.checkout, args.python_exe, args.repo, args.workflow,
        args.account, args.interval, args.start, args.min_interval,
    )


if __name__ == "__main__":
    sys.exit(main())
