#!/usr/bin/env python3
"""
Verify post-rotation state of running GenAI containers.

`render_envs.py --check` is a STATIC gate: it compares ``master.env`` to the
on-disk ``.env`` files. That's necessary but not sufficient. The actual
working state is the running container -- it was launched with whatever
``.env`` was current at ``docker compose up`` time, and stays at THAT value
until restarted. Drift between master.env and a running container is
INVISIBLE to ``--check`` until the next compose restart.

This script closes that gap by comparing master.env → container env at
runtime, for every GenAI service whose docker-compose.yml exposes an
``API_KEY`` / ``*_TOKEN`` / ``*_BEARER_TOKEN`` env var. It's a one-shot
audit invoked by operators after a rotation (or by CI as a periodic check)
to answer the concrete question: "for every running service, does the
container's working credential match the canonical master.env value?"

Output: one line per service with ``OK`` / ``DRIFT`` / ``NOT_RUNNING`` /
``NO_AUTH_VAR``, exit 1 on any ``DRIFT``. Secret values are NEVER printed
(masks with last 4 chars only, consistent with render_envs.py).

Usage:
  python scripts/secrets/verify_running_containers.py [--json]
  python scripts/secrets/verify_running_containers.py --service whisper-api
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
MASTER_ENV = REPO_ROOT / ".secrets" / "master.env"
SERVICES_ROOT = REPO_ROOT / "docker-configurations" / "services"

# Compose env-var pattern -> container env-var name. When the compose maps
# ``${FOO_API_KEY}`` to ``API_KEY``, the container sees ``API_KEY`` not
# ``FOO_API_KEY``. This dict captures the rename so we compare the right
# pair (master's ``FOO_API_KEY`` vs container's ``API_KEY``).
#
# Convention: only auth-related vars are listed. Non-secret CONFIG vars
# (PORTS, GPU ids, model names, TZ) are excluded -- they drift harmlessly
# and per-instance ones (ComfyUI instance passwords, see secrets-hygiene.md)
# are intentionally NOT centralized.
_AUTH_VAR_RENAMES: dict[str, str] = {
    "WHISPER_API_KEY": "API_KEY",
    "DEMUCS_API_KEY": "API_KEY",
    "FUNASR_API_KEY": "API_KEY",
    "MUSICGEN_API_KEY": "API_KEY",
    "QWEN_ASR_API_KEY": "API_KEY",
    "TTS_API_KEY": "API_KEY",
    "TTS_GATEWAY_API_KEY": "API_KEY",
    "SD_FORGE_API_KEY": "API_KEY",
    # ComfyUI services: compose uses the same name on both sides.
    "COMFYUI_API_TOKEN": "COMFYUI_API_TOKEN",
    "COMFYUI_VIDEO_TOKEN": "COMFYUI_VIDEO_TOKEN",
    "COMFYUI_BEARER_TOKEN": "COMFYUI_BEARER_TOKEN",
}


def _read_master_env() -> dict[str, str]:
    """Parse master.env -> {KEY: raw_value}. Same parser as render_envs."""
    out: dict[str, str] = {}
    if not MASTER_ENV.exists():
        return out
    line_re = re.compile(r"^\s*(?:export\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.*)$")
    for raw in MASTER_ENV.read_text(encoding="utf-8").splitlines():
        m = line_re.match(raw)
        if not m:
            continue
        key, raw_val = m.group(1), m.group(2)
        v = raw_val.strip()
        if len(v) >= 2 and v[0] in "\"'":
            v = v[1:-1]
        out[key] = v.strip()
    return out


def _detect_auth_vars(compose_path: Path) -> dict[str, str]:
    """Return {master_key: container_env_var_name} declared in compose.

    Only returns entries whose MASTER-side key is present in ``_AUTH_VAR_RENAMES``
    (so we audit the centralized ones, not per-instance passwords).
    """
    if not compose_path.exists():
        return {}
    text = compose_path.read_text(encoding="utf-8")
    out: dict[str, str] = {}
    # Match ``- COMFYUI_BEARER_TOKEN=${COMFYUI_BEARER_TOKEN}`` etc.
    for master_key, container_var in _AUTH_VAR_RENAMES.items():
        # Pattern: $-reference to master_key in compose env block
        pattern = re.compile(
            rf"-\s+{re.escape(container_var)}\s*=\s*\${{?{re.escape(master_key)}",
            re.MULTILINE,
        )
        if pattern.search(text):
            out[master_key] = container_var
    return out


def _container_env(container: str) -> dict[str, str] | None:
    """Return container env as dict, or None if container not running."""
    try:
        out = subprocess.run(
            ["docker", "inspect", container, "--format", "{{json .Config.Env}}"],
            capture_output=True, text=True, timeout=10,
            check=False,
        )
    except subprocess.TimeoutExpired:
        return None
    if out.returncode != 0 or not out.stdout.strip():
        return None
    env_list = json.loads(out.stdout.strip())
    result: dict[str, str] = {}
    for entry in env_list:
        if "=" in entry:
            k, v = entry.split("=", 1)
            result[k] = v
    return result


def _mask(value: str) -> str:
    """Mask a secret value, last 4 chars only. Matches render_envs convention."""
    if not value:
        return "<empty>"
    if len(value) <= 4:
        return "****"
    return "*" * (len(value) - 4) + value[-4:]


# Verdict legend (also used in --json output):
#   OK             = master matches running container
#   DRIFT          = master != container (rotation needed OR container not
#                    restarted yet -- operator must ``docker compose restart``)
#   NOT_RUNNING    = container is down; nothing to compare (informational,
#                    does NOT trigger exit 1 -- a sleeping service cannot drift)
#   MASTER_MISSING = master.env has no value for this key (informational;
#                    e.g. per-instance password like COMFYUI_BEARER_TOKEN
#                    that's intentionally non-centralized -- not an error)
#   NO_AUTH_VAR    = compose has no $-reference for centralized auth vars
#                    (service likely does not need auth, e.g. an internal UI)
_CONTAINER_NOT_RUNNING_ROW = {
    "master_key": "",
    "container_var": "",
    "result": "container_not_running",
    "master_masked": "<n/a>",
    "container_masked": "<n/a>",
}


def audit_service(
    service_dir: Path, master: dict[str, str]
) -> tuple[str, list[dict[str, str]]]:
    """Audit one service. Returns (status, details) where status is one of:
    OK, DRIFT, NOT_RUNNING, NO_AUTH_VAR, COMPOSE_MISSING.
    """
    compose = service_dir / "docker-compose.yml"
    if not compose.exists():
        return "COMPOSE_MISSING", []
    auth_vars = _detect_auth_vars(compose)
    if not auth_vars:
        return "NO_AUTH_VAR", []
    # Convention: container_name == service_dir.name (verified across the
    # 13 service dirs in this repo).
    container = service_dir.name
    env = _container_env(container)
    if env is None:
        # One summary row; downstream printer skips per-var masking here.
        return "NOT_RUNNING", [{
            **_CONTAINER_NOT_RUNNING_ROW,
            "master_key": f"{len(auth_vars)} auth var(s) declared",
            "container_var": "(not running)",
        }]
    details: list[dict[str, str]] = []
    has_drift = False
    for master_key, container_var in auth_vars.items():
        master_val = master.get(master_key, "")
        container_val = env.get(container_var, "<missing>")
        if master_val == "":
            # Master doesn't carry this key -- informational only.
            # COMFYUI_BEARER_TOKEN is the canonical case (per-instance,
            # not centralized per secrets-hygiene.md). Not a drift.
            details.append({
                "master_key": master_key,
                "container_var": container_var,
                "result": "MASTER_MISSING",
                "master_masked": "<not-centralized>",
                "container_masked": _mask(container_val),
            })
            continue
        if container_val == "<missing>":
            details.append({
                "master_key": master_key,
                "container_var": container_var,
                "result": "CONTAINER_MISSING",
                "master_masked": _mask(master_val),
                "container_masked": "<missing>",
            })
            has_drift = True
            continue
        if master_val == container_val:
            details.append({
                "master_key": master_key,
                "container_var": container_var,
                "result": "OK",
                "master_masked": _mask(master_val),
                "container_masked": _mask(container_val),
            })
        else:
            details.append({
                "master_key": master_key,
                "container_var": container_var,
                "result": "DRIFT",
                "master_masked": _mask(master_val),
                "container_masked": _mask(container_val),
            })
            has_drift = True
    return ("DRIFT" if has_drift else "OK"), details


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--service",
        help="Audit only this service dir name (e.g. whisper-api). Default: all.",
    )
    parser.add_argument(
        "--json", action="store_true",
        help="Emit machine-readable JSON instead of the human-readable table.",
    )
    args = parser.parse_args()

    master = _read_master_env()
    if not master:
        print("ERROR: master.env not found or empty at", MASTER_ENV, file=sys.stderr)
        return 2

    services = sorted(
        d for d in SERVICES_ROOT.iterdir()
        if d.is_dir() and (args.service is None or d.name == args.service)
    )
    if not services:
        print(f"ERROR: no service dir matches --service={args.service}", file=sys.stderr)
        return 2

    rows: list[dict[str, object]] = []
    for svc in services:
        status, details = audit_service(svc, master)
        rows.append({"service": svc.name, "status": status, "vars": details})

    if args.json:
        print(json.dumps(rows, indent=2))
    else:
        for row in rows:
            print(f"[{row['status']:14}] {row['service']}")
            for var in row["vars"]:  # type: ignore[index]
                print(
                    f"    {var['master_key']} -> {var['container_var']}: "
                    f"{var['result']} master={var['master_masked']} "
                    f"container={var['container_masked']}"
                )

    has_drift = any(r["status"] == "DRIFT" for r in rows)
    return 1 if has_drift else 0


if __name__ == "__main__":
    sys.exit(main())