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
3. *(removed -- see "Gate 3" note in ``_run_checks``: gitleaks lives in
   pre-commit's own cache and never has to be on the system PATH.)*
4. ``.git/hooks/pre-commit`` is installed (produced by ``pre-commit install``).
5. The id of each hook declared in the config matches an id the framework
   will execute (best-effort: relies on ``pre-commit validate-config``).
6. each local hook's ``entry`` script exists on disk (PyYAML pair).
7. **NEW** (#10139): the gitleaks version pinned by the hook's ``rev`` equals
   the one pinned by ``GITLEAKS_VERSION`` in ``secret-scan.yml``. Measured
   need: on identical content, 8.21.2 reported 0 findings where 8.24.3
   reported 2, so a hook pinned to 8.21.2 could not reproduce -- nor warn
   about -- what CI rejected.
8. **NEW** (#10141): ``secret-scan.yml`` does not invoke the third-party
   wrapper ``gitleaks/gitleaks-action@v2``. The wrapper tag is the action's
   own version, not the gitleaks binary version; without an explicit
   ``GITLEAKS_VERSION`` AND a consumer that honors it, the wrapper falls
   back to a hard-coded default (``8.24.3``, src/index.js:138) -- an
   implicit pin owned by a third party and revisable by any ``@v2``
   release without a commit here. #10141 replaces the wrapper with an
   explicit ``docker pull`` + ``docker run`` on a tagged image, so the
   CI pin and the hook ``rev`` agree on a single, repo-owned value.

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
SECRET_SCAN_PATH = REPO_ROOT / ".github" / "workflows" / "secret-scan.yml"


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


def _pre_commit_launchable() -> list[str] | None:
    """Return the argv prefix that launches pre-commit, or ``None``.

    Tries (in order):
      1. ``pre-commit`` on PATH (the canonical install — most workers get it
         via ``pip install --user`` and put it on PATH).
      2. ``python -m pre_commit`` (the fallback — ``pre-commit install``
         writes a hook that calls ``INSTALL_PYTHON -mpre_commit`` first, so
         a machine where the module is installed but the binary is missing
         from PATH still has a working H.3 harness; this gate should not
         KO such a machine — incident ai-01 reproduit sur #9903).

    Returns a list suitable for ``subprocess.run([*prefix, ...], ...)``.
    Returns ``None`` only when neither path resolves to a working
    ``--version`` invocation (so a single ``--version`` probe distinguishes
    "pre-commit absent" from "pre-commit present but unlaunchable", the
    latter being a real env bug the worker must repair).
    """
    precommit = shutil.which("pre-commit")
    if precommit:
        try:
            subprocess.run(
                [precommit, "--version"], capture_output=True, text=True,
                check=False, timeout=10,
            )
            return [precommit]
        except (FileNotFoundError, subprocess.TimeoutExpired, OSError):
            pass  # shutil.which lied (Windows PATH mismatch) or hung; fall through
    try:
        proc = subprocess.run(
            [sys.executable, "-m", "pre_commit", "--version"],
            capture_output=True, text=True, check=False, timeout=10,
        )
        if proc.returncode == 0:
            return [sys.executable, "-m", "pre_commit"]
    except (FileNotFoundError, subprocess.TimeoutExpired, OSError):
        pass
    return None


def _validate_config(launch: list[str]) -> tuple[bool, str]:
    """Run ``<launch> validate-config`` and return (ok, stderr)."""
    try:
        proc = subprocess.run(
            [*launch, "validate-config", str(CONFIG_PATH)],
            capture_output=True, text=True, check=False,
        )
    except FileNotFoundError:
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


def _hook_gitleaks_version() -> str | None:
    """Version pinned by the gitleaks hook's ``rev``, ``v`` prefix stripped.

    Returns ``None`` when no gitleaks repo is declared at all.
    """
    if yaml is None:
        raise RuntimeError("PyYAML not installed; install with `pip install pyyaml`")
    data = yaml.safe_load(CONFIG_PATH.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"{CONFIG_PATH}: top-level must be a mapping")
    for repo in data.get("repos", []) or []:
        if not isinstance(repo, dict):
            continue
        url = str(repo.get("repo", ""))
        if "gitleaks" in url and repo.get("rev"):
            return str(repo["rev"]).lstrip("v")
    return None


def _ci_gitleaks_version() -> str | None:
    """Version pinned by ``GITLEAKS_VERSION`` in the Secret Scan workflow.

    Looks at both job-level ``env:`` and step-level ``env:`` (the new
    post-#10141 pattern keeps it at job level so the ``run:`` step
    expands it via shell interpolation; the old wrapper-style pattern
    put it at step level only).

    Returns ``None`` when the workflow exists but pins nothing -- which is a
    real finding, not an absence of information: unset, the action falls back
    to a version hard-coded in its own source, i.e. an implicit pin owned by a
    third party that any ``@v2`` release can revise without a commit here.
    """
    if yaml is None:
        raise RuntimeError("PyYAML not installed; install with `pip install pyyaml`")
    if not SECRET_SCAN_PATH.exists():
        raise FileNotFoundError(f"{SECRET_SCAN_PATH} missing")
    data = yaml.safe_load(SECRET_SCAN_PATH.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"{SECRET_SCAN_PATH}: top-level must be a mapping")
    for job in (data.get("jobs") or {}).values():
        if not isinstance(job, dict):
            continue
        # Job-level env (the #10141 pattern).
        job_env = job.get("env")
        if isinstance(job_env, dict) and job_env.get("GITLEAKS_VERSION"):
            return str(job_env["GITLEAKS_VERSION"]).lstrip("v")
        # Step-level env (the old gitleaks-action@v2 pattern, still legitimate).
        for step in job.get("steps", []) or []:
            if not isinstance(step, dict):
                continue
            env = step.get("env")
            if isinstance(env, dict) and env.get("GITLEAKS_VERSION"):
                return str(env["GITLEAKS_VERSION"]).lstrip("v")
    return None


def _ci_uses_third_party_gitleaks_action() -> bool:
    """True iff ``secret-scan.yml`` invokes the ``gitleaks/gitleaks-action@v2`` wrapper.

    The wrapper's tag is the GitHub Action version, not the gitleaks binary
    version. Without a tagged image and a ``run:`` step that consumes it
    explicitly (the pattern #10141 introduces), the binary is selected by
    ``GITLEAKS_VERSION`` from the action's environment with a hard-coded
    fallback -- an implicit pin revisable by any ``@v2`` release.
    """
    if yaml is None:
        raise RuntimeError("PyYAML not installed; install with `pip install pyyaml`")
    if not SECRET_SCAN_PATH.exists():
        raise FileNotFoundError(f"{SECRET_SCAN_PATH} missing")
    data = yaml.safe_load(SECRET_SCAN_PATH.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"{SECRET_SCAN_PATH}: top-level must be a mapping")
    for job in (data.get("jobs") or {}).values():
        if not isinstance(job, dict):
            continue
        for step in job.get("steps", []) or []:
            if not isinstance(step, dict):
                continue
            uses = str(step.get("uses", ""))
            if "gitleaks-action@v2" in uses:
                return True
    return False


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

    # Gate 2: pre-commit launchable (PATH or `python -m pre_commit`).
    # The previous gate did `shutil.which("pre-commit")` only, and KO'd
    # machines where the module is installed but the binary is missing
    # from PATH -- which is precisely the configuration the pre-commit
    # install hook produces (`INSTALL_PYTHON -mpre_commit`). Reported by
    # ai-01 against #9903: a worker can have H.3 wired and still trip
    # this gate, learning to ignore it.
    precommit_launch = _pre_commit_launchable()
    if precommit_launch:
        out.append((
            "pre-commit launchable",
            "OK",
            " ".join(precommit_launch),  # human-friendly join
        ))
    else:
        out.append((
            "pre-commit launchable",
            "KO",
            "install with: pip install --user pre-commit "
            "(or ensure `python -m pre_commit` works)",
        ))

    # Gate 3 (formerly "gitleaks on PATH") has been removed. gitleaks is
    # declared as an external hook (``repo: https://github.com/gitleaks/...``)
    # and pre-commit downloads it into its own cache on first run -- it
    # never has to be on the system PATH. The previous gate KO'd every
    # correctly-configured machine, with a hint (``pip install --user
    # gitleaks``) that does nothing because gitleaks is a Go binary, not
    # a PyPI package. An advisory gate that cries KO on a healthy state
    # is the worst kind: workers learn to ignore it. The real test of
    # gitleaks reachability is Gate 5 (``validate-config``) plus the
    # actual hook run on commit -- both of which go through pre-commit's
    # download path. See #9903 follow-up.

    # Gate 4: hook installed
    if HOOK_PATH.exists():
        out.append((".git/hooks/pre-commit installed", "OK", str(HOOK_PATH)))
    else:
        out.append((".git/hooks/pre-commit installed", "KO", "run: pre-commit install"))

    # Gate 5: validate-config
    if precommit_launch:
        ok, detail = _validate_config(precommit_launch)
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

    # Gate 7: gitleaks version parity between the hook and CI (#10139).
    #
    # Unlike every gate above, this one does not depend on the worker's machine
    # state -- it compares two files in the repo, so it reads the same on every
    # checkout. It is here for discoverability (a worker running this script
    # sees it), but the ENFORCING copy is the unit test in
    # scripts/tests/test_check_hooks_parity.py, which runs on PRs. This script
    # stays advisory by design (see "Why advisory only" above) and a divergence
    # must fail something blocking.
    #
    # Why it matters concretely: on the files that blocked 5 PRs, gitleaks
    # 8.21.2 reported 0 findings and 8.24.3 reported 2. While the hook pinned
    # 8.21.2 and CI resolved 8.24.3, a clean `git commit` was rejected in CI
    # with nothing in the repo to explain it.
    try:
        hook_v = _hook_gitleaks_version()
        ci_v = _ci_gitleaks_version()
        if hook_v is None:
            out.append(("gitleaks version parity", "KO", "no gitleaks repo in pre-commit config"))
        elif ci_v is None:
            out.append((
                "gitleaks version parity", "KO",
                f"hook pins {hook_v} but {SECRET_SCAN_PATH.name} sets no GITLEAKS_VERSION "
                "(CI would use the action's own hard-coded default)",
            ))
        elif hook_v != ci_v:
            out.append((
                "gitleaks version parity", "KO",
                f"hook rev v{hook_v} != CI GITLEAKS_VERSION {ci_v} -- "
                "a green pre-commit does not predict CI",
            ))
        else:
            out.append(("gitleaks version parity", "OK", f"hook and CI both pin {hook_v}"))
    except (FileNotFoundError, ValueError, RuntimeError) as e:
        out.append(("gitleaks version parity", "ERR", str(e)))

    # Gate 8: secret-scan.yml does not invoke the gitleaks-action wrapper
    # (#10141). The wrapper's tag is the Action version, not the gitleaks
    # binary version; the binary is selected by GITLEAKS_VERSION from the
    # action's environment with a hard-coded fallback (src/index.js:138),
    # i.e. an implicit pin owned by a third party that any @v2 release
    # can revise. #10141 removes the wrapper entirely in favor of an
    # explicit `docker pull` + `docker run` on a tagged image. This gate
    # locks that structural fix: a future PR that re-introduces the
    # wrapper would re-create the implicit third-party pin.
    try:
        uses_wrapper = _ci_uses_third_party_gitleaks_action()
        if uses_wrapper:
            out.append((
                "gitleaks wrapper not used", "KO",
                f"{SECRET_SCAN_PATH.name} invokes gitleaks/gitleaks-action@v2 -- "
                "that wrapper's binary version is an implicit third-party pin "
                "(see src/index.js:138, fallback \"8.24.3\"). Use an explicit "
                "`docker pull` + `docker run` on a tagged image instead.",
            ))
        else:
            out.append((
                "gitleaks wrapper not used", "OK",
                f"{SECRET_SCAN_PATH.name} invokes the docker image directly",
            ))
    except (FileNotFoundError, ValueError, RuntimeError) as e:
        out.append(("gitleaks wrapper not used", "ERR", str(e)))

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
