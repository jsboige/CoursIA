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
    token = _fetch_token(profile, "removal-token", run)
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


def task_action(profile: Profile) -> str:
    """L'action de la tache : lit le mot de passe du fichier machine local
    conventionnel, negocie tout le reste a chaud, logue a cote des autres logs."""
    secrets_file = profile.root.parent / "secrets" / "runner_pwd.txt"
    logs_dir = profile.root.parent / "logs"
    python = Path(sys.executable)
    controller = Path(__file__).resolve()
    inner = (
        f"$ErrorActionPreference='Stop';"
        f"$env:{ACCOUNT_PASSWORD_ENV}=(Get-Content -LiteralPath '{secrets_file}' -Raw).Trim();"
        f"& '{python}' '{controller}' ensure --profile {profile.name} --apply"
    )
    return (
        f"pwsh.exe -NoProfile -NonInteractive -WindowStyle Hidden -Command \""
        f"New-Item -ItemType Directory -Force -Path '{logs_dir}' | Out-Null;"
        f"{inner} *>> '{logs_dir}\\controller.log'\""
    )


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
  <Settings>
    <MultipleInstancesPolicy>IgnoreNew</MultipleInstancesPolicy>
    <DisallowStartIfOnBatteries>false</DisallowStartIfOnBatteries>
    <StopIfGoingOnBatteries>false</StopIfGoingOnBatteries>
    <ExecutionTimeLimit>PT10M</ExecutionTimeLimit>
    <Enabled>true</Enabled>
  </Settings>
  <Actions Context="Author">
    <Exec>
      <Command>pwsh.exe</Command>
      <Arguments>-NoProfile -NonInteractive -WindowStyle Hidden -Command &quot;{task_action(profile)}&quot;</Arguments>
    </Exec>
  </Actions>
</Task>
"""


def apply_task_install(profile: Profile, run: CommandRunner) -> dict:
    if not _is_elevated():
        raise Broken("task-install --apply requires an elevated session (RunLevel Highest)")
    xml = task_xml(profile)
    xml_file = profile.root.parent / "logs" / "controller-task.xml"
    xml_file.parent.mkdir(parents=True, exist_ok=True)
    xml_file.write_text(xml, encoding="utf-16")
    for args in (
        ["schtasks", "/Create", "/TN", TASK_NAME, "/XML", str(xml_file), "/F"],
        ["schtasks", "/Change", "/TN", TASK_NAME, "/RL", "HIGHEST"],
    ):
        completed = run(args, capture_output=True, text=True, encoding="utf-8", check=False)
        if completed.returncode != 0:
            raise Broken(f"schtasks failed: {(completed.stderr or '').strip()[:200]}")
    return {"action": "task-installed", "task": TASK_NAME}


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
            plan = {"planned_actions": ["fetch-removal-token", "config-remove"]}
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
