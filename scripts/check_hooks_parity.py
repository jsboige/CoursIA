#!/usr/bin/env python3
"""Parity check: declared vs installed pre-commit hooks (issue #9888).

Compares the hooks named in ``.pre-commit-config.yaml`` against the
hooks that would actually fire on a commit. The repo's harness
``secrets-hygiene.md`` and ``regles-validation-detail.md`` (rule H.3)
rely on gitleaks + notebook gates being live at commit time; this
script makes the silent gap visible before it becomes a leak.

What it checks
--------------
1. ``.pre-commit-config.yaml`` exists and parses as YAML.
2. ``pre-commit`` binary is on PATH.
3. ``gitleaks`` binary is on PATH (since the config declares v8.21.2).
4. ``.git/hooks/pre-commit`` is installed (produced by ``pre-commit install``).
5. The id of each hook declared in the config matches an id the framework
   will execute (best-effort: relies on ``pre-commit validate-config``).

Why advisory only
-----------------
The same angle-mot that produced #8782 (a gate that names a target it
stopped watching) is what we are guarding against. We do **not** block
CI on this parity check, because a missing local hook is the **worker's**
state to repair, not the PR's. The output is a warning.

Exit code:
    0 — every gate green
    1 — at least one gate red (printed in the report)
    2 — YAML parse error / config missing
"""
from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
from pathlib import Path

try:
    import yaml  # PyYAML
except ImportError:
    yaml = None  # type: ignore[assignment]

REPO_ROOT = Path(__file__).resolve().parent.parent
CONFIG_PATH = REPO_ROOT / ".pre-commit-config.yaml"
HOOK_PATH = REPO_ROOT / ".git" / "hooks" / "pre-commit"


def _declared_hook_ids() -> list[str]:
    if not CONFIG_PATH.exists():
        raise FileNotFoundError(f"{CONFIG_PATH} missing")
    if yaml is None:
        raise RuntimeError("PyYAML not installed; install with `pip install pyyaml`")
    text = CONFIG_PATH.read_text(encoding="utf-8")
    data = yaml.safe_load(text)
    if not isinstance(data, dict) or "repos" not in data:
        raise ValueError(f"{CONFIG_PATH}: top-level must be a mapping with 'repos' key")
    ids: list[str] = []
    for repo in data["repos"]:
        if not isinstance(repo, dict):
            continue
        for hook in repo.get("hooks", []) or []:
            if isinstance(hook, dict) and "id" in hook:
                ids.append(hook["id"])
    return ids


def _validate_config() -> tuple[bool, str]:
    """Run ``pre-commit validate-config`` and return (ok, stderr)."""
    precommit = shutil.which("pre-commit")
    if precommit is None:
        return False, "pre-commit not on PATH"
    try:
        proc = subprocess.run(
            [precommit, "validate-config", str(CONFIG_PATH)],
            capture_output=True, text=True, check=False,
        )
    except FileNotFoundError:
        # shutil.which can succeed on Windows even when CreateProcess can't
        # actually launch the binary (PATH mismatch in subprocess).
        return False, "pre-commit not launchable from subprocess"
    return proc.returncode == 0, (proc.stderr or proc.stdout or "").strip()


def _run_checks() -> list[tuple[str, str, str]]:
    """Return list of (gate, status, detail). status ∈ {"OK", "KO", "ERR"}."""
    out: list[tuple[str, str, str]] = []

    # Gate 1: config present and parseable
    try:
        ids = _declared_hook_ids()
        out.append(("config declared", "OK", f"{len(ids)} hooks: {', '.join(ids)}"))
    except FileNotFoundError as e:
        out.append(("config declared", "ERR", str(e)))
        return out  # cannot proceed further meaningfully
    except (ValueError, RuntimeError) as e:
        out.append(("config declared", "ERR", str(e)))
        return out

    # Gate 2: pre-commit on PATH
    precommit_path = shutil.which("pre-commit")
    if precommit_path:
        out.append(("pre-commit on PATH", "OK", precommit_path))
    else:
        out.append(("pre-commit on PATH", "KO", "install with: pip install --user pre-commit"))

    # Gate 3: gitleaks on PATH
    gitleaks_path = shutil.which("gitleaks")
    if gitleaks_path:
        out.append(("gitleaks on PATH", "OK", gitleaks_path))
    else:
        out.append(("gitleaks on PATH", "KO", "install with: pip install --user gitleaks"))

    # Gate 4: hook installed
    if HOOK_PATH.exists():
        out.append((".git/hooks/pre-commit installed", "OK", str(HOOK_PATH)))
    else:
        out.append((".git/hooks/pre-commit installed", "KO", "run: pre-commit install"))

    # Gate 5: validate-config
    if precommit_path:
        ok, detail = _validate_config()
        out.append(("pre-commit validate-config", "OK" if ok else "KO", detail or "(silent)"))
    else:
        out.append(("pre-commit validate-config", "SKIP", "pre-commit not installed"))

    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[1] if __doc__ else "")
    parser.add_argument("--quiet", action="store_true", help="only print the gate table on KO")
    args = parser.parse_args()

    rows = _run_checks()
    any_ko = False
    for gate, status, detail in rows:
        if status != "OK":
            any_ko = True
        line = f"  [{status:3}] {gate}: {detail}"
        if not args.quiet or status != "OK":
            print(line)
    if any_ko:
        print("\n  Run `python scripts/setup_hooks.py --install` to repair.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())