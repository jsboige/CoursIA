"""Controleur de re-enregistrement des runners ephemeres (#12704).

Un runner --ephemeral traite AU PLUS UN job puis se desenregistre : chaque
job consomme l'inscription. Le gestionnaire (manage_self_hosted_runner.py)
prepare une invocation unique ; ce controleur la supervise — decision ai-01
2026-08-28T14:33Z : controleur de re-enregistrement, pas broker de tokens
JIT, pas one-shot. L'ephemere est preserve : chaque job garde une
inscription fraiche, donc un token fraichement negocie a chaque cycle.

Le controleur est idempotent : autant de passages que de ticks Planificateur,
un seul etat stable (au plus un runner online pour le profil). Le token
d'enregistrement est negocie via `gh` a CHAQUE re-enregistrement, ne transite
jamais par argv, commit, PR, commentaire ou dashboard, et n'est jamais logue.

Commandes :

  status                       etat distant + local + plan, aucun effet
  ensure    [--apply]          idempotent : online -> no-op ; absent ->
                               token frais + register + verify du gestionnaire
  deregister [--apply]         arret propre : token de retrait + config.cmd
                               remove (l'installation demeure, l'etat
                               redevient « prepare, pas active »)
  task-install [--apply]       enregistre la tache planifiee qui declenche
                               ensure --apply toutes les minutes (LE bouton)
  task-remove  [--apply]       retire la tache (retour arriere du bouton)

Les tests injectent des callables `run` : aucune commande reseau ou machine
n'est executee par la suite de tests.
"""

from __future__ import annotations

import argparse
import ctypes
import json
import os
import subprocess
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from manage_self_hosted_runner import (  # noqa: E402
    ACCOUNT_PASSWORD_ENV,
    EXIT_BROKEN,
    EXIT_OK,
    PROFILE_PATH,
    RUNNER_PRIVATE_FILES,
    Broken,
    Profile,
    apply_register,
    apply_verify,
    load_profile,
)

REGISTRATION_TOKEN_ENV = "GITHUB_RUNNER_REGISTRATION_TOKEN"
REMOVAL_TOKEN_ENV = "GITHUB_RUNNER_REMOVAL_TOKEN"
TASK_NAME = "CoursIA-Runner-Controller"
TASK_TICK_SECONDS = 60
TASK_LAUNCHER_NAME = "controller-task.vbs"

CommandRunner = subprocess.run


def _gh(repo: str, args: list[str], run: CommandRunner) -> str:
    completed = run(
        ["gh", *args], capture_output=True, text=True, encoding="utf-8", check=False,
    )
    if completed.returncode != 0:
        raise Broken(f"gh {' '.join(args[:2])} failed: {(completed.stderr or '').strip()[:200]}")
    return completed.stdout.strip()


def remote_runners(profile: Profile, run: CommandRunner) -> list[dict]:
    """Liste les runners du depot via l'API GitHub (aucun secret en jeu)."""
    out = _gh(profile.repository, [
        "api", f"repos/{profile.repository}/actions/runners", "--paginate",
        "--jq", ".runners[] | {name, status, busy}",
    ], run)
    return [json.loads(line) for line in out.splitlines() if line.strip()]


def runner_online(profile: Profile, run: CommandRunner) -> dict | None:
    for entry in remote_runners(profile, run):
        if entry.get("name") == profile.runner_name and entry.get("status") == "online":
            return entry
    return None


def _fetch_token(profile: Profile, kind: str, run: CommandRunner) -> str:
    endpoint = f"repos/{profile.repository}/actions/runners/{kind}"
    out = _gh(profile.repository, [
        "api", "--method", "POST", "-H", "Accept: application/vnd.github+json",
        endpoint, "--jq", ".token",
    ], run)
    if not out or len(out) < 20:
        raise Broken(f"{kind} fetch returned no usable token")
    return out


def plan_for(profile: Profile, run: CommandRunner) -> dict:
    online = runner_online(profile, run)
    return {
        "profile": profile.name,
        "runner_name": profile.runner_name,
        "remote_online": bool(online),
        "planned_actions": [] if online else ["fetch-registration-token", "register", "verify"],
    }


def apply_ensure(profile: Profile, run: CommandRunner) -> dict:
    if runner_online(profile, run):
        return {"action": "noop", "reason": "runner already online"}
    password = os.environ.get(ACCOUNT_PASSWORD_ENV)
    if not password:
        raise Broken(f"{ACCOUNT_PASSWORD_ENV} is required to re-register the runner")
    os.environ[REGISTRATION_TOKEN_ENV] = _fetch_token(profile, "registration-token", run)
    try:
        apply_register(profile, run=run)
        apply_verify(profile, run=run)
    finally:
        os.environ.pop(REGISTRATION_TOKEN_ENV, None)
    return {"action": "registered"}


def apply_deregister(profile: Profile, run: CommandRunner) -> dict:
    if not runner_online(profile, run) and not any(
        (profile.root / name).exists() for name in RUNNER_PRIVATE_FILES
    ):
        return {"action": "noop", "reason": "runner already absent"}
    token = _fetch_token(profile, "remove-token", run)
    completed = run(
        [str(profile.config_cmd), "remove", "--unattended"], cwd=profile.root,
        capture_output=True, text=True, encoding="utf-8",
        env={"ACTIONS_RUNNER_INPUT_TOKEN": token, **_baseline_env()},
        check=False,
    )
    if completed.returncode != 0:
        detail = (completed.stderr or completed.stdout or "runner removal failed")
        raise Broken(detail.replace(token, "[REDACTED]").strip()[:300])
    return {"action": "deregistered"}


def _baseline_env() -> dict:
    keep = {"SYSTEMROOT", "SYSTEMDRIVE", "PATH", "TEMP", "TMP", "COMSPEC", "PATHEXT", "WINDIR"}
    return {k: v for k, v in os.environ.items() if k.upper() in keep}


def _is_elevated() -> bool:
    try:
        return bool(ctypes.windll.shell32.IsUserAnAdmin())
    except AttributeError:
        return False


def task_action(profile: Profile, command: list[str] | None = None) -> str:
    """Le CORPS du script de la tache : lit le mot de passe du fichier machine local
    conventionnel, negocie tout le reste a chaud, logue a cote des autres logs.

    Ne porte ni interpreteur ni enrobage `-Command "..."` : c'est le lanceur VBS
    qui declare `<Command>pwsh.exe</Command>` et ses arguments (cf. `task_launcher`),
    et l'XML de la tache ne porte plus que `wscript.exe`. L'ancien enrobage
    empilait deux `pwsh.exe -Command "..."` (le second avec des guillemets
    imbriques non echappes) et rendait l'XML invalide — mesure #20174.

    `command` remplace la commande du controleur : c'est un point d'entree pour
    les tests, qui ne peuvent pas lancer `ensure --apply` (il enregistre un
    runner). Sans lui, le corps est exactement celui de la tache installee.
    """
    secrets_file = profile.root.parent / "secrets" / "runner_pwd.txt"
    logs_dir = profile.root.parent / "logs"
    python = Path(sys.executable)
    controller = Path(__file__).resolve()
    log = logs_dir / "controller.log"
    if command is None:
        # La forme d'origine est conservee mot pour mot (`ensure --profile X
        # --apply` d'un seul tenant) : c'est elle que les controles existants
        # assertent, et un lanceur VBS qui la recopie doit la retrouver.
        call = (f"'{python}' '{controller}' ensure --profile {profile.name} --apply")
    else:
        # Chaque element est quote comme un litteral PowerShell : un chemin qui
        # porte un espace ne doit pas se faire couper en deux.
        call = " ".join("'" + a.replace("'", "''") + "'" for a in command)
    # Tout le flux passe par controller.log : sortie du controleur ET raison de
    # l'echec. La redirection shell `*>>` ne portait que la DERNIERE instruction,
    # donc un echec preparatoire (fichier de mot de passe absent) partait vers la
    # sortie invisible de la tache : le journal restait absent ou vide alors que
    # le code retour portait 1 (mesure 2026-11-04, Maintenance#75). Ici l'echec
    # est attrape et ecrit dans le journal, et la sortie du controleur est
    # capturee puis ecrite -- ecriture .NET en UTF-8 sans BOM, qui n'ouvre pas
    # le fichier en exclusif (une ecriture dans le catch ne peut pas se faire
    # refuser par la redirection, cf. la sonde du 04/11).
    return (
        f"$log='{log}';"
        f"try {{"
        f"New-Item -ItemType Directory -Force -Path '{logs_dir}' | Out-Null;"
        f"$ErrorActionPreference='Stop';"
        f"$env:{ACCOUNT_PASSWORD_ENV}=(Get-Content -LiteralPath '{secrets_file}' -Raw).Trim();"
        f"$ErrorActionPreference='Continue';"
        f"$out = & {call} 2>&1 | Out-String;"
        f"$code = $LASTEXITCODE;"
        # FILET, pas correction d'un defaut reproduit : un executable
        # introuvable ne met PAS `$LASTEXITCODE` a jour (la commande n'a
        # jamais demarre -> `$LASTEXITCODE` reste `$null`, et `exit $null`
        # rendrait 0). Mesure sur les DEUX moteurs du poste (pwsh 7 et
        # Windows PowerShell 5.1) : l'exception « commande introuvable »
        # est toutefois TERMINANTE pour le `try` du corps -- elle est donc
        # attrapee par le `catch` ci-dessous, qui ecrit la raison dans le
        # journal et rend deja 1. Le rc ne ment donc pas aujourd'hui ; la
        # garde le garantit meme si cette exception devenait non
        # terminante. Le temoin qui verrouille le comportement mesure est
        # dans scripts/tests/test_runner_controller.py.
        f"if ($null -eq $code) {{ $code = 1 }};"
        f"$ErrorActionPreference='Stop';"
        f"[IO.File]::AppendAllText($log, $out);"
        f"if ($code -ne 0) {{ exit $code }}"
        f"}} catch {{"
        f"New-Item -ItemType Directory -Force -Path '{logs_dir}' | Out-Null;"
        f"[IO.File]::AppendAllText($log, ('{{0}} ERREUR : {{1}}' -f (Get-Date -Format s),"
        f" ($_ | Out-String)));"
        f"exit 1"
        f"}}"
    )


def task_launcher_path(profile: Profile) -> Path:
    """Emplacement du lanceur sans fenetre, derive du profil.

    Le chemin n'est jamais code en dur : un chemin fixe deploye le defaut sur une
    autre machine des que la racine des runners differe, et le controle de
    non-regression cesserait alors de couvrir la machine reellement installee.
    """
    return profile.root.parent / "launchers" / TASK_LAUNCHER_NAME


def _vbs_escape(text: str) -> str:
    """Echappe un litteral de chaine VBScript : un `"` s'y ecrit `""`."""
    return text.replace('"', '""')


def task_launcher(profile: Profile, command: str | None = None) -> str:
    """Le lanceur `wscript.exe` qui masque la fenetre du tick.

    `<Command>wscript.exe</Command>` seul ne suffit pas : `pwsh.exe` lance
    directement par le Planificateur ouvre une console a chaque tick. La tache se
    repete toutes les 60 s et n'a pas de condition « seulement si l'utilisateur
    est absent » — d'ou 60 fenetres par heure sur l'ecran de la session ouverte
    (mesure lane Maintenance, 2026-11-04). `WScript.Shell.Run` avec le second
    argument a `0` demande au systeme une fenetre masquee ; le troisieme a
    `True` attend la fin du tick et rend son code de sortie, propage par
    `WScript.Quit rc` (detail au commentaire du corps ci-dessous, review #24707).

    Le corps execute est exactement `task_action` : la seule difference avec
    l'ancienne action est l'enveloppe, pas le travail.
    """
    if command is None:
        command = (
            "pwsh.exe -NoProfile -NonInteractive -WindowStyle Hidden "
            f'-Command "{task_action(profile)}"'
        )
    # Troisieme argument a True + WScript.Quit rc : sans cela (False, forme
    # initiale de cette PR, review #24707) le code retour du controleur ne
    # remonte jamais -- LastTaskResult vaut 0 quel que soit le sort du tick --
    # et la tache se terminant aussitot, MultipleInstancesPolicy=IgnoreNew ne
    # protege plus contre les ticks qui se chevauchent. Meme forme que
    # install_merge_ready_task.py et install_overflow_trigger_task.py.
    return (
        "Option Explicit\n"
        "Dim shell, rc\n"
        'Set shell = CreateObject("WScript.Shell")\n'
        f'rc = shell.Run("{_vbs_escape(command)}", 0, True)\n'
        "Set shell = Nothing\n"
        "WScript.Quit rc\n"
    )


def _xml_escape(text: str) -> str:
    """Echappe les metacaracteres XML d'un contenu d'element.

    Le corps du script porte le `&` de l'operateur d'appel PowerShell et `*>>`
    (redirection) : `&` et `<` sont illicites en XML et `schtasks /Create /XML`
    refuse le document. L'ordre compte : `&` d'abord, sinon les entites produites
    par les remplacements suivants sont re-echappees.
    """
    return text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def _validate_task_xml(xml: str) -> None:
    """Valide l'XML de la tache avant toute elevation.

    Un XML malforme doit rougir en dry-run non-eleve, pas se reveler dans la
    session elevee : c'est une fenetre UAC utilisateur qui paie la decouverte
    (mesure #20174, fenetre du 2026-10-20).
    """
    try:
        ET.fromstring(xml)
    except ET.ParseError as exc:
        raise Broken(f"task XML malformed: {exc}") from exc


def task_xml(profile: Profile) -> str:
    return f"""<?xml version="1.0" encoding="UTF-16"?>
<Task version="1.2" xmlns="http://schemas.microsoft.com/windows/2004/02/mit/task">
  <Triggers>
    <TimeTrigger>
      <Repetition>
        <Interval>PT{TASK_TICK_SECONDS}S</Interval>
        <StopAtDurationEnd>false</StopAtDurationEnd>
      </Repetition>
      <StartBoundary>2026-01-01T00:00:00</StartBoundary>
      <Enabled>true</Enabled>
    </TimeTrigger>
  </Triggers>
  <Principals>
    <Principal id="Author">
      <RunLevel>HighestAvailable</RunLevel>
    </Principal>
  </Principals>
  <Settings>
    <MultipleInstancesPolicy>IgnoreNew</MultipleInstancesPolicy>
    <DisallowStartIfOnBatteries>false</DisallowStartIfOnBatteries>
    <StopIfGoingOnBatteries>false</StopIfGoingOnBatteries>
    <ExecutionTimeLimit>PT10M</ExecutionTimeLimit>
    <Enabled>true</Enabled>
  </Settings>
  <Actions Context="Author">
    <Exec>
      <Command>wscript.exe</Command>
      <Arguments>//B //Nologo &quot;{_xml_escape(str(task_launcher_path(profile)))}&quot;</Arguments>
    </Exec>
  </Actions>
</Task>
"""


def apply_task_install(profile: Profile, run: CommandRunner) -> dict:
    # L'XML se construit et se valide AVANT le controle d'elevation : la garde
    # passait en premier, donc un dry-run non-eleve ne pouvait structurellement
    # pas voir un XML malforme -- le defaut n'apparaissait qu'en session elevee,
    # une fenetre UAC utilisateur consommee pour rien (mesure #20174).
    xml = task_xml(profile)
    _validate_task_xml(xml)
    if not _is_elevated():
        raise Broken("task-install --apply requires an elevated session (RunLevel Highest)")
    xml_file = profile.root.parent / "logs" / "controller-task.xml"
    xml_file.parent.mkdir(parents=True, exist_ok=True)
    xml_file.write_text(xml, encoding="utf-16")
    # Le lanceur est ECRIT par le generateur, jamais pose a la main : un
    # durcissement manuel de la tache est annule au premier `task-install
    # --apply` (mesure 2026-11-04 : durcissement a 18:33:21Z, annule a 18:33:22Z).
    launcher = task_launcher_path(profile)
    launcher.parent.mkdir(parents=True, exist_ok=True)
    launcher.write_text(task_launcher(profile), encoding="ascii")
    # Un seul appel : le niveau d'execution est porte par `<Principals>` dans le
    # XML (voir task_xml). Le `schtasks /Change /TN ... /RL HIGHEST` qui suivait
    # la creation exige le mot de passe du compte des lors que le principal
    # differe de l'appelant, donc il **bloque une session elevee non
    # interactive** sur une invite que personne ne verra (mesure 2026-11-04 :
    # processus suspendus > 180 s, fenetre UAC utilisateur consommee pour rien).
    completed = run(
        ["schtasks", "/Create", "/TN", TASK_NAME, "/XML", str(xml_file), "/F"],
        capture_output=True, text=True, encoding="utf-8", check=False,
    )
    if completed.returncode != 0:
        raise Broken(f"schtasks failed: {(completed.stderr or '').strip()[:200]}")
    return {"action": "task-installed", "task": TASK_NAME, "launcher": str(launcher)}


def apply_task_remove(profile: Profile, run: CommandRunner) -> dict:
    if not _is_elevated():
        raise Broken("task-remove --apply requires an elevated session (RunLevel Highest)")
    completed = run(
        ["schtasks", "/Delete", "/TN", TASK_NAME, "/F"],
        capture_output=True, text=True, encoding="utf-8", check=False,
    )
    # Un second passage sur un etat absent est un succes explicite.
    if completed.returncode != 0 and "ne peut pas trouver" not in (completed.stderr or "") \
            and "cannot find" not in (completed.stderr or "").lower():
        raise Broken(f"schtasks /Delete failed: {(completed.stderr or '').strip()[:200]}")
    (profile.root.parent / "logs" / "controller-task.xml").unlink(missing_ok=True)
    return {"action": "task-removed", "task": TASK_NAME}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "command",
        choices=("status", "ensure", "deregister", "task-install", "task-remove"),
    )
    parser.add_argument("--profile", required=True)
    parser.add_argument("--profiles", type=Path, default=PROFILE_PATH, help=argparse.SUPPRESS)
    parser.add_argument("--apply", action="store_true", help="perform the planned mutations")
    args = parser.parse_args(argv)
    try:
        profile = load_profile(args.profile, args.profiles)
        if args.command == "task-install":
            plan = {"planned_actions": ["create-scheduled-task"]}
            if args.apply:
                plan["result"] = apply_task_install(profile, subprocess.run)
            else:
                xml = task_xml(profile)
                _validate_task_xml(xml)
                plan["xml"] = xml
        elif args.command == "task-remove":
            plan = {"planned_actions": ["delete-scheduled-task"]}
            if args.apply:
                plan["result"] = apply_task_remove(profile, subprocess.run)
        elif args.command == "status":
            plan = plan_for(profile, subprocess.run)
        elif args.command == "ensure":
            plan = plan_for(profile, subprocess.run)
            if args.apply:
                if plan["planned_actions"]:
                    plan["result"] = apply_ensure(profile, subprocess.run)
                else:
                    plan["result"] = {"action": "noop", "reason": "runner already online"}
        elif args.command == "deregister":
            plan = {"planned_actions": ["fetch-remove-token", "config-remove"]}
            if args.apply:
                plan["result"] = apply_deregister(profile, subprocess.run)
        print(json.dumps(plan, indent=2, sort_keys=True, ensure_ascii=False))
        return EXIT_OK
    except Broken as exc:
        print(json.dumps({"ok": False, "error": str(exc), "kind": "broken"},
                         ensure_ascii=False), file=sys.stderr)
        return EXIT_BROKEN


if __name__ == "__main__":
    raise SystemExit(main())
