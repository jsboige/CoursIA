#!/usr/bin/env python3
"""Parity check: declared vs installed pre-commit hooks (issue #9888, suite).

Compares the hooks named in ``.pre-commit-config.yaml`` against the
hooks that would actually fire on a commit, then walks the YAML
structure to pair each declared hook id with its entry script.

Why this script (vs the regex walker in ``scripts/setup_hooks.py``)
-------------------------------------------------------------------
The current ``--check-parity`` subcommand uses
``re.finditer(r"-\\s+id:\\s*(\\S+).*?entry:\\s*([^\\n]+)", text, re.S)``
to pair ``id -> entry``. The non-greedy ``.*?`` with ``re.S`` (DOTALL)
makes **each id match the FIRST entry that follows** instead of the
entry that actually belongs to it. The result, measured first-hand on
this machine:

    $ python scripts/setup_hooks.py --check-parity | grep gitleaks
      gitleaks                         -> scripts/notebook_tools/strip_probe_banner.py [EXISTS]

``gitleaks`` is an external hook (no ``entry`` field of its own); the
regex falsely attaches it to ``strip_probe_banner.py`` (the first
local entry that follows). The real first local hook (id
``strip-probeaddresses-banner``) is silently dropped from the pairing
report. This is the same shape of blind spot as #8782 -- a gate that
names a target it stopped watching.

The PyYAML-aware walker in this script reads the YAML structure
instead of line regexes, so the pairing is correct (gitleaks has no
entry, and the five local hooks are each paired with their own entry).

What it checks
--------------
1. ``.pre-commit-config.yaml`` exists and parses as YAML.
2. ``pre-commit`` binary is on PATH.
3. ``gitleaks`` binary is on PATH (since the config declares v8.21.2).
4. ``.git/hooks/pre-commit`` is installed (produced by ``pre-commit install``).
5. The id of each hook declared in the config matches an id the framework
   will execute (best-effort: relies on ``pre-commit validate-config``).
6. **NEW**: each local hook's ``entry`` script exists on disk (PyYAML pair).

Why advisory only
-----------------
The same angle-mot that produced #8782 (a gate that names a target it
stopped watching) is what we are guarding against. We do **not** block
CI on this parity check, because a missing local hook is the **worker's**
state to repair, not the PR's. The output is a warning. CI is configured
with ``continue-on-error: true`` and annotates ``::warning::`` on parity
fail so the worker can see it without it stopping the rest of the run.

Exit code:
    0 -- every gate green
    1 -- at least one gate red (printed in the report)
    2 -- YAML parse error / config missing
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


def _local_hook_pairs() -> list[tuple[str, str | None]]:
    """PyYAML walk: yield (id, entry_or_None) for each local hook.

    External hooks (e.g. gitleaks) have no ``entry`` -- the entry is
    inherited from the remote repo's plugin. We yield ``None`` for the
    entry in that case so the caller can report it cleanly instead of
    pairing the id with the *next* hook's entry (the regex bug).
    """
    if not CONFIG_PATH.exists():
        raise FileNotFoundError(f"{CONFIG_PATH} missing")
    if yaml is None:
        raise RuntimeError("PyYAML not installed; install with `pip install pyyaml`")
    text = CONFIG_PATH.read_text(encoding="utf-8")
    data = yaml.safe_load(text)
    if not isinstance(data, dict) or "repos" not in data:
        raise ValueError(f"{CONFIG_PATH}: top-level must be a mapping with 'repos' key")
    pairs: list[tuple[str, str | None]] = []
    for repo in data["repos"]:
        if not isinstance(repo, dict):
            continue
        # Only local hooks have an explicit entry we can verify.
        if repo.get("repo") != "local":
            for hook in repo.get("hooks", []) or []:
                if isinstance(hook, dict) and "id" in hook:
                    pairs.append((hook["id"], None))
            continue
        for hook in repo.get("hooks", []) or []:
            if not isinstance(hook, dict) or "id" not in hook:
                continue
            entry = hook.get("entry")
            pairs.append((hook["id"], entry))
    return pairs


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


def _entry_script(entry: str) -> str | None:
    """Extract the first ``*.py`` path from a hook entry string.

    Entry strings are like:
        "python scripts/notebook_tools/strip_probe_banner.py --apply"
        "python scripts/notebook_tools/check_null_exec.py"
    Returns the path component (or None if no .py found).
    """
    parts = entry.split()
    return next((p for p in parts if p.endswith(".py")), None)


def _run_checks() -> list[tuple[str, str, str]]:
    """Return list of (gate, status, detail). status in {"OK", "KO", "ERR"}."""
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

    # Gate 6: local hook entry scripts (NEW, PyYAML-correct pairing)
    try:
        pairs = _local_hook_pairs()
        # Filter to local hooks (entry is not None) for the script check.
        local = [(hid, entry) for hid, entry in pairs if entry is not None]
        missing = []
        for hid, entry in local:
            script = _entry_script(entry)
            if script is None:
                missing.append((hid, "no .py in entry"))
                continue
            if not (REPO_ROOT / script).exists():
                missing.append((hid, script))
        if missing:
            details = "; ".join(f"{h} -> {s}" for h, s in missing)
            out.append(("local hook entry scripts", "KO", details))
        else:
            out.append(("local hook entry scripts", "OK", f"{len(local)} local hooks wired"))
    except (ValueError, RuntimeError) as e:
        out.append(("local hook entry scripts", "ERR", str(e)))

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
