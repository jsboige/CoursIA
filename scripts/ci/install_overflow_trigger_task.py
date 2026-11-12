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
        'for /f "delims=" %%r in (\'gh run list --workflow %GH_WORKFLOW% '
        '--repo %GH_REPO% --limit 1 --json databaseId --jq ".[0].databaseId" '
        '2^>nul\') do set "RUN_BEFORE=%%r"\r\n'
        f'echo [%DATE% %TIME%] declenchement de %GH_WORKFLOW% sur %GH_REPO% '
        f'(intervalle minimal %GH_MIN_INTERVAL% min)>> "%LOG%"\r\n'
        f'{dispatch} >> "%LOG%" 2>&1\r\n'
        "if errorlevel 1 (\r\n"
        '  >> "%LOG%" echo [%DATE% %TIME%] declenchement REFUSE (rc=%ERRORLEVEL%)'
        " -- aucun run demande\r\n"
        "  echo %ERRORLEVEL% > \"%LOG%.rc\"\r\n"
        "  exit /b %ERRORLEVEL%\r\n"
        ")\r\n"
        # APRES : l'id a-t-il change ? Un declenchement accepte peut ne
        # produire AUCUN run (mesure du 2026-11-12, 19:07Z sur ai-01 : la
        # tache a rendu rc 0, le journal n'a rien trace, et AUCUN run n'a
        # ete cree). Un instrument qui ne voit que son propre code de sortie
        # croit avoir declenche ; il faut voir l'EFFET.
        'for /f "delims=" %%r in (\'gh run list --workflow %GH_WORKFLOW% '
        '--repo %GH_REPO% --limit 1 --json databaseId --jq ".[0].databaseId" '
        '2^>nul\') do set "RUN_AFTER=%%r"\r\n'
        'if "%RUN_AFTER%"=="%RUN_BEFORE%" (\r\n'
        '  >> "%LOG%" echo [%DATE% %TIME%] EFFET NON CONSTATE : aucun run cree '
        '(id avant=%RUN_BEFORE% id apres=%RUN_AFTER% -- ids vides : la '
        'lecture des runs a echoue)\r\n'
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
    # `newline=""` : le contenu porte deja ses "\r\n" explicites. Sans ce
    # parametre, `write_text` traduit chaque "\n" en os.linesep et ecrit
    # "\r\r\n" -- mesure sur l'artefact installe le 2026-11-12 : 20 lignes
    # sur 20 portaient le CR supplementaire. Le fichier etait tolere par
    # cmd.exe, mais il n'etait plus byte-identique a ce que le generateur
    # declare, et la detection de drift ne aurait pu rien dire.
    CMD_PATH.write_text(
        cmd_content(repo, workflow, account, min_interval, pass_min_interval),
        encoding="ascii",
        newline="",
    )
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
    repo: str, workflow: str, account: str, min_interval: int
) -> list[str]:
    """Ecarts entre les lanceurs INSTALLES et ceux que le generateur ecrit.

    Un artefact installe derriere son generateur s'ecarte sans bruit : le
    declencheur peut alors faire autre chose que ce que le depot declare.
    Mesure du 2026-11-12 (ai-01) : le lanceur installe ne passait pas
    `min_interval` -- que le generateur ecrit depuis -- et chacune de ses
    20 lignes portait un CR supplementaire ; rien ne le signalait.

    Rend la liste des ecarts (vide = conforme).
    """
    inputs, _inputs_reason = workflow_inputs(repo, workflow)
    expected = {
        CMD_PATH: cmd_content(
            repo, workflow, account, min_interval,
            "min_interval" in inputs,
        ),
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
    return drifts


def cmd_status(
    repo: str, workflow: str, account: str, min_interval: int
) -> int:
    proc = _run(["schtasks", "/Query", "/TN", TASK_NAME, "/V", "/FO", "LIST"])
    print(proc.stdout or proc.stderr or f"rc={proc.returncode}")
    drifts = launcher_drift(repo, workflow, account, min_interval)
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
        return cmd_status(
            args.repo, args.workflow, args.account, args.min_interval,
        )
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
