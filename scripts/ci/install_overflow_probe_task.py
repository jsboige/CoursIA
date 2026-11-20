#!/usr/bin/env python3
r"""Installateur de la tache planifiee locale de la sonde de debordement
(#26939, volet cadence).

Pourquoi une tache LOCALE
-------------------------
La sonde (`ci-overflow-probe.yml`, organe `ci_overflow_probe.py`) est fusionnee
depuis le 2026-11-17 12:49Z (#26959), mais son cron de depot ('4-59/12 * * * *')
n'a JAMAIS emis d'evenement `schedule` (mesure du 17/11 : un seul run, en
`workflow_dispatch` manuel). Ce n'est pas la seule sonde touchee : la livraison
des crons du depot est mesuree a 22 % des tics servis, mediane 289 min de retard
(mesure citee dans l'en-tete de `install_overflow_trigger_task.py`). Le
planificateur heberge n'est pas un organe sur lequel on peut compter pour une
latence de 15 min.

La parade est celle du CONTROLEUR, mesuree et adoptee le 2026-11-12 (arbitrage
de l'adjoint, forme (b)) : une minuterie LOCALE sur le siege ai-01 porte la
cadence. Ici, la sonde s'execute SUR LE SIEGE au moment du tic :

- elle fait ses 2 appels `gh` (file + variable) depuis le siege, avec le jeton
  du trousseau -- aucun secret du depot n'est requis (lecture des runs et de la
  variable, dispatch eventuel du controleur) ;
- le cron de depot reste en place : si la minuterie locale meurt, le filet
  heberge subsiste (et reciproquement, le timer local compense les 78 % de tics
  non servis) ;
- le workflow GitHub reste la forme executable a la main (`workflow_dispatch`)
  et la trace publique des passages qui ont dispatche le controleur.

Diffence avec le declencheur du controleur : la sonde n'a PAS de garde de
cadence locale (marqueur). Son anti-repetition vit DANS l'organe -- l'age du
dernier passage du controleur (DEFAULT_SATURATION_MINUTES, 15 min) : un passage
sonde « idle » est le regime nominal (10 appels/h au total), il n'y a rien a
ecarter. La tache ne fait donc que jouer l'organe et journaliser sa ligne JSON.

Identite : le jeton n'est JAMAIS ecrit sur disque. Le lanceur appelle
`gh auth token --user <compte>` au moment de l'execution : le jeton vit dans le
trousseau du siege, il n'apparait dans aucun fichier.

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
    --status                                      etat de la tache + drift des
                                                 lanceurs installes
    --uninstall                                   supprime la tache ET les
                                                 lanceurs
    --run                                         joue UNE fois le lanceur
                                                 (controle de bout en bout,
                                                 non eleve)

Garde : `--install` REFUSE de cabler si l'organe sonde n'existe pas dans le
checkout (cabler une minuterie vers un organe absent deployerait un echec
silencieux toutes les 12 min -- meme garde que le declencheur du controleur).

Fichiers :
    tache   : CoursIA\overflow_probe
    lanceur : %LOCALAPPDATA%\CoursIA\overflow_probe\dispatch_probe.cmd
    fenetre : %LOCALAPPDATA%\CoursIA\overflow_probe\run_hidden.vbs
    journal : %LOCALAPPDATA%\CoursIA\overflow_probe\logs\overflow_probe.log
"""
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

TASK_NAME = r"CoursIA\overflow_probe"
THIS_FILE = Path(__file__).resolve()
BASE_DIR = (
    Path(os.environ.get("LOCALAPPDATA", str(Path.home() / "AppData" / "Local")))
    / "CoursIA"
    / "overflow_probe"
)
LOG_DIR = BASE_DIR / "logs"
CMD_PATH = BASE_DIR / "dispatch_probe.cmd"
VBS_PATH = BASE_DIR / "run_hidden.vbs"
# Lanceur masque (meme forme que `install_overflow_trigger_task.py`, audit de
# flotte du 24/09) : python.exe/gh sont des programmes console, chaque tour
# ferait flasher une fenetre noire sur le bureau interactif.
WSH_PATH = (
    Path(os.environ.get("SystemRoot", r"C:\Windows")) / "System32" / "wscript.exe"
)

DEFAULT_REPO = "jsboige/CoursIA"
DEFAULT_ACCOUNT = "jsboige"
# Cadence : 12 min, celle du cron de depot ('4-59/12' : minutes 4, 16, 28, 40,
# 52). C'est le CONTRAT de latence de l'issue #26939 qui la fixe : deux
# passages sonde a moins de 15 min d'ecart. Le budget suit : 5 passages/h x 2
# appels = 10 appels/h au repos, ~4 x 313 en pire cas candidat persistant
# (anti-repetition de l'organe, cf ci_overflow_probe.py) -- sous le plafond de
# 1 000 appels/h partage avec le cron horaire du controleur (313/h).
DEFAULT_INTERVAL_MINUTES = 12
# Phase de depart : 00:04 -> minute 4 de chaque heure. Le cron de depot sonde
# les minutes 4-59/12, le declencheur local du controleur part a :07, son cron
# a :31 : la phase :04 ne collisionne avec aucun des trois.
DEFAULT_START = "00:04"
# Checkout local ou la sonde est executee. Par defaut, la racine du depot d'ou
# vient ce script.
DEFAULT_CHECKOUT = THIS_FILE.parents[2]
# Interpreteur python du siege.
DEFAULT_PYTHON = "python"


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
    """Journal de la minuterie (nom fixe, la date y depend de la locale)."""
    return LOG_DIR / "overflow_probe.log"


def probe_usable(checkout: Path) -> tuple[bool, str]:
    """Le checkout local peut-il executer la sonde ?

    La forme `local` execute l'organe DEPUIS le checkout : sans le script, le
    passage echoue a chaque tic. La sonde importe le module du controleur
    (`from ci_overflow_controller import ...`), qui doit donc etre present au
    meme endroit.
    """
    scripts = Path(checkout) / "scripts" / "ci"
    for name in ("ci_overflow_probe.py", "ci_overflow_controller.py"):
        organ = scripts / name
        if not organ.is_file():
            return False, f"organe absent du checkout ({organ})"
    return True, ""


def cmd_content(
    checkout: Path,
    python_exe: str,
    repo: str,
    account: str,
) -> str:
    """Contenu du lanceur .cmd : capture du jeton AU MOMENT de l'execution,
    passage de la sonde sur le siege, journalisation de sa ligne JSON.

    Le jeton n'est jamais ecrit dans le fichier : il est lu dans le trousseau
    du siege par `gh auth token`, au moment ou la tache tourne.

    Pas de garde de cadence locale : l'anti-repetition vit dans l'organe (age
    du dernier passage du controleur) -- un passage « idle » est le regime
    nominal de la sonde, pas un passage a ecarter.
    """
    probe = Path(checkout) / "scripts" / "ci" / "ci_overflow_probe.py"
    command = subprocess.list2cmdline(
        [
            python_exe,
            "-X", "utf8",
            str(probe),
            "--repo", repo,
            "--json",
        ]
    )
    return (
        "@echo off\r\n"
        "REM Genere par install_overflow_probe_task.py -- ecrase a chaque\r\n"
        "REM --install, ne pas editer a la main. Aucun jeton n'est ecrit\r\n"
        "REM ici : il est lu dans le trousseau du siege au moment du tir.\r\n"
        "REM\r\n"
        "REM La sonde s'execute SUR LE SIEGE (forme du declencheur du\r\n"
        "REM controleur, retenue le 2026-11-12) : le cron de depot n'a jamais\r\n"
        "REM emis d'evenement schedule, la minuterie locale porte la cadence.\r\n"
        "REM L'anti-repetition vit DANS l'organe -- un passage idle est le\r\n"
        "REM regime nominal, il n'y a rien a ecarter.\r\n"
        "setlocal\r\n"
        f'set "GH_USER={account}"\r\n'
        f'set "LOG={LOG_DIR}\\overflow_probe.log"\r\n'
        'for /f "delims=" %%t in (\'gh auth token --user %GH_USER% 2^>nul\') '
        'do set "GH_TOKEN=%%t"\r\n'
        'if not defined GH_TOKEN (\r\n'
        f'  >> "%LOG%" echo [%DATE% %TIME%] jeton absent pour %GH_USER% '
        "-- passage sonde sans mesure\r\n"
        "  exit /b 2\r\n"
        ")\r\n"
        f'>> "%LOG%" echo [%DATE% %TIME%] passage sonde -- '
        "organe ci_overflow_probe.py\r\n"
        f"{command} >> \"%LOG%\" 2>&1\r\n"
        'set "RC=%ERRORLEVEL%"\r\n'
        'echo %RC% > "%LOG%.rc"\r\n'
        "REM rc 0 = nominal -- idle, hold ou dispatch sont TOUS des passages\r\n"
        "REM sains de la sonde ; rc 1 = mesure impossible, deja journalisee\r\n"
        "REM par l'organe avec son motif. La minuterie ne retraduit rien.\r\n"
        "exit /b %RC%\r\n"
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
        "' Lanceur genere par install_overflow_probe_task.py -- ecrase a\r\n"
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


def cmd_dry_run(
    checkout: Path,
    python_exe: str,
    repo: str,
    account: str,
    interval: int,
    start: str,
) -> int:
    """N'ecrit RIEN et n'execute RIEN : la commande `schtasks` exacte et le
    contenu exact des deux lanceurs."""
    command = build_schtasks_install(task_action(), interval, start)
    content = cmd_content(checkout, python_exe, repo, account)
    ok, reason = probe_usable(checkout)
    print(
        f"DRY-RUN -- checkout : {checkout} "
        f"({'exploitable' if ok else reason})"
    )
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
    print(f"DRY-RUN -- journal : {LOG_DIR}\\overflow_probe.log")
    return 0


def cmd_install(
    checkout: Path,
    python_exe: str,
    repo: str,
    account: str,
    interval: int,
    start: str,
) -> int:
    ok, reason = probe_usable(checkout)
    if not ok:
        print(f"REFUS -- {reason}", file=sys.stderr)
        print(
            "La minuterie ne serait cablee que vers un organe inexistant : "
            "chaque tour echouerait en silence.",
            file=sys.stderr,
        )
        return 2
    content = cmd_content(checkout, python_exe, repo, account)
    BASE_DIR.mkdir(parents=True, exist_ok=True)
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    # `newline=""` : le contenu porte deja ses "\r\n" explicites. Sans ce
    # parametre, `write_text` traduit chaque "\n" en os.linesep et ecrit
    # "\r\r\n" -- defaut mesure sur le declencheur du controleur le
    # 2026-11-12 (20 lignes sur 20 portaient le CR supplementaire).
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
    lignes VIDES et le rapport de drift designe la ligne 2 comme vide.
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
    checkout: Path,
    python_exe: str,
    repo: str,
    account: str,
) -> list[str]:
    """Ecarts entre les lanceurs INSTALLES et ceux que le generateur ecrit.

    Un artefact installe derive sans bruit derriere son generateur : la
    minuterie peut alors faire autre chose que ce que le depot declare
    (mesure du 2026-11-12 sur le declencheur du controleur).
    """
    expected = {
        CMD_PATH: cmd_content(checkout, python_exe, repo, account),
        VBS_PATH: vbs_content(CMD_PATH),
    }
    drifts: list[str] = []
    for path, want in expected.items():
        if not path.exists():
            drifts.append(f"{path} absent (minuterie non installee)")
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
    checkout: Path,
    python_exe: str,
    repo: str,
    account: str,
) -> int:
    proc = _run(["schtasks", "/Query", "/TN", TASK_NAME, "/V", "/FO", "LIST"])
    print(proc.stdout or proc.stderr or f"rc={proc.returncode}")
    drifts = launcher_drift(checkout, python_exe, repo, account)
    if drifts:
        print(
            "DRIFT -- les lanceurs INSTALLES different de ce que le "
            "generateur ecrit :"
        )
        for line in drifts:
            print(f"  - {line}")
        print(
            "  remedy : python scripts/ci/install_overflow_probe_task.py "
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
    """Declenche UNE fois le lanceur : controle de bout en bout de la
    chaine, non eleve (le lanceur inclus)."""
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    proc = _run(["cmd.exe", "/c", str(CMD_PATH)])
    if proc.returncode != 0:
        print(
            f"passage sonde echoue (rc={proc.returncode}) : "
            f"{(proc.stderr or proc.stdout or '').strip()}",
            file=sys.stderr,
        )
    else:
        print(f"passage sonde effectue (rc={proc.returncode})")
    print(f"journal : {log_path_for()}")
    return proc.returncode


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Tache planifiee locale de la sonde de debordement CI (#26939) : "
            "elle porte la cadence que le cron du depot ne livre pas."
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
        "--checkout",
        type=Path,
        default=DEFAULT_CHECKOUT,
        help=(
            "checkout local ou la sonde est executee ; par defaut, la "
            "racine du depot d'ou vient ce script"
        ),
    )
    parser.add_argument(
        "--python",
        dest="python_exe",
        default=DEFAULT_PYTHON,
        help="interpreteur python du siege",
    )
    parser.add_argument("--repo", default=DEFAULT_REPO)
    parser.add_argument("--account", default=DEFAULT_ACCOUNT)
    parser.add_argument("--interval", type=int, default=DEFAULT_INTERVAL_MINUTES)
    parser.add_argument("--start", default=DEFAULT_START)
    args = parser.parse_args(argv)

    # `--dry-run` l'EMPORTE sur `--install` (defaut mesure le 2026-11-12 sur
    # le declencheur du controleur : un drapeau dry-run mort qui installait
    # la tache quand meme casse la preparation du geste UAC).
    if args.dry_run:
        return cmd_dry_run(
            args.checkout, args.python_exe, args.repo, args.account,
            args.interval, args.start,
        )
    if args.install:
        return cmd_install(
            args.checkout, args.python_exe, args.repo, args.account,
            args.interval, args.start,
        )
    if args.status:
        return cmd_status(args.checkout, args.python_exe, args.repo, args.account)
    if args.uninstall:
        return cmd_uninstall()
    if args.run:
        return cmd_run()
    return cmd_dry_run(
        args.checkout, args.python_exe, args.repo, args.account,
        args.interval, args.start,
    )


if __name__ == "__main__":
    sys.exit(main())
