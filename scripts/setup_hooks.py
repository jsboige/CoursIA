#!/usr/bin/env python3
"""Idempotent installer for the CoursIA pre-commit harness.

The repo ships a ``.pre-commit-config.yaml`` (gitleaks secret scanner +
notebook hygiene/strip hooks + the H.3 null-exec guard), but nothing installs
it: on every worker machine measured (myia-ai-01, myia-po-2024) ``pre-commit``
is absent and ``.git/hooks/pre-commit`` does not exist, so the declared hooks
are **decorative** -- they never run. See #9888.

This script is the *organe d'installation* the issue asks for ("pas une
consigne"): it installs pre-commit, wires the hook into ``.git/hooks/``, warms
the gitleaks cache, and verifies -- idempotently (a second run is a no-op).

Usage:
    python scripts/setup_hooks.py              # install (idempotent)
    python scripts/setup_hooks.py --check      # machine state relevé (no changes)
    python scripts/setup_hooks.py --check-parity  # declared hooks vs executable
    python scripts/setup_hooks.py --self-test  # functional: stage fake secret, verify gitleaks detects

Design notes:
  - Invokes pre-commit as ``python -m pre_commit`` (no PATH dependency: pip
    installs the module, the -m flag finds it without refreshing the shell).
  - gitleaks is fetched by pre-commit into its own cache on first run; it is
    NOT placed on the system PATH (pre-commit's design). The hook works
    regardless -- the proof is that a fake secret is refused at commit, not
    that ``command -v gitleaks`` resolves. See acceptance #2 of #9888.
  - ``--check`` verifies STRUCTURE (hook file present, module installed);
    ``--self-test`` verifies FUNCTION (gitleaks actually detects a staged
    secret). The two differ: the config once shipped without
    ``[extend] useDefault = true``, so gitleaks matched NOTHING -- structurally
    "installed", functionally a silent no-op (the root defect of #9888).
    ``--self-test`` stages a probe, runs gitleaks on the staged content, expects
    a nonzero exit (leaks found), then cleans up. It is the regression guard
    for that exact bug class.
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
from pathlib import Path


def find_repo_root(start: Path | None = None) -> Path:
    """Walk upward from ``start`` (default: this file's parents) to the repo
    root -- the first directory containing a ``.git`` entry."""
    cwd = (start or Path(__file__).resolve()).resolve()
    for candidate in [cwd, *cwd.parents]:
        if (candidate / ".git").exists():
            return candidate
    raise SystemExit(
        "setup_hooks: could not locate repo root (.git not found upward "
        f"from {cwd}). Run from inside the CoursIA checkout."
    )


def _run(cmd: list[str], cwd: Path) -> tuple[int, str]:
    """Run ``cmd`` in ``cwd``, return (returncode, combined trimmed output)."""
    proc = subprocess.run(
        cmd,
        cwd=str(cwd),
        capture_output=True,
        text=True,
        shell=False,
    )
    out = (proc.stdout + proc.stderr).strip()
    return proc.returncode, out


def _hooks_dir(repo: Path) -> Path:
    """Resolve the hooks directory git actually uses.

    Honors ``core.hooksPath`` if set (this repo sets it, shared across all 38
    worktrees); otherwise falls back to ``git rev-parse --git-path hooks`` (which
    correctly resolves through a worktree's ``.git`` file to the main gitdir).
    Avoids the naive ``repo/.git/hooks`` that breaks under worktrees.
    """
    hp = subprocess.run(
        ["git", "config", "core.hooksPath"], cwd=str(repo),
        capture_output=True, text=True,
    ).stdout.strip()
    if hp:
        p = Path(hp)
        return p if p.is_absolute() else (repo / p)
    g = subprocess.run(
        ["git", "rev-parse", "--git-path", "hooks"], cwd=str(repo),
        capture_output=True, text=True,
    ).stdout.strip()
    return (repo / g).resolve() if g else repo / ".git" / "hooks"


def _pre_commit_available(python: str) -> bool:
    rc, _ = _run([python, "-m", "pre_commit", "--version"], Path.cwd())
    return rc == 0


def _install_pre_commit(python: str) -> bool:
    """pip install pre-commit (user site). Returns True on success."""
    print("setup_hooks: installing pre-commit (pip install --user) ...")
    rc, out = _run(
        [python, "-m", "pip", "install", "--user", "--quiet", "pre-commit"],
        Path.cwd(),
    )
    if rc != 0:
        print(f"setup_hooks: pip install failed (rc={rc}):\n{out}", file=sys.stderr)
        return False
    return _pre_commit_available(python)


def cmd_install(repo: Path, python: str) -> int:
    """Idempotent: ensure pre-commit installed, hook wired, gitleaks warmed."""
    steps_ok = True

    # Step 1: pre-commit module available.
    if _pre_commit_available(python):
        rc, ver = _run([python, "-m", "pre_commit", "--version"], repo)
        print(f"setup_hooks: pre-commit already available ({ver}).")
    else:
        if not _install_pre_commit(python):
            steps_ok = False
        else:
            rc, ver = _run([python, "-m", "pre_commit", "--version"], repo)
            print(f"setup_hooks: pre-commit installed ({ver}).")

    if not steps_ok:
        return 1

    # Step 2: wire the hook into the git hooks directory.
    # pre-commit refuses to install when core.hooksPath is set (a safety guard).
    # This repo sets core.hooksPath (redundantly == gitdir/hooks, shared across
    # worktrees). Handle it: capture where git LOOKS for hooks, temporarily
    # unset hooksPath so pre-commit cooperates, then ensure the generated hook
    # lands where git actually reads it. Restore hooksPath afterwards.
    target_hooks = _hooks_dir(repo)  # where git reads hooks (honors core.hooksPath)
    saved_hookspath = subprocess.run(
        ["git", "config", "core.hooksPath"], cwd=str(repo),
        capture_output=True, text=True,
    ).stdout.strip()
    hook_path = target_hooks / "pre-commit"
    if saved_hookspath:
        subprocess.run(
            ["git", "config", "--unset-all", "core.hooksPath"], cwd=str(repo),
            capture_output=True, text=True,
        )
    try:
        rc, out = _run([python, "-m", "pre_commit", "install"], repo)
    finally:
        if saved_hookspath:
            subprocess.run(
                ["git", "config", "core.hooksPath", saved_hookspath], cwd=str(repo),
                capture_output=True, text=True,
            )
    # pre-commit writes to gitdir/hooks (its resolved git-path hooks). If git
    # reads hooks from a different dir (core.hooksPath), mirror it there.
    gitdir_hooks_rel = subprocess.run(
        ["git", "rev-parse", "--git-path", "hooks"], cwd=str(repo),
        capture_output=True, text=True,
    ).stdout.strip()
    gitdir_precommit = (repo / gitdir_hooks_rel).resolve() / "pre-commit"
    if rc == 0:
        # If pre-commit wrote to gitdir/hooks but git reads target_hooks, copy.
        if gitdir_precommit != hook_path and gitdir_precommit.exists():
            target_hooks.mkdir(parents=True, exist_ok=True)
            hook_path.write_bytes(gitdir_precommit.read_bytes())
        if hook_path.exists():
            print(f"setup_hooks: hook wired -> {hook_path}")
        else:
            print(f"setup_hooks: pre-commit install rc=0 but {hook_path} missing")
            steps_ok = False
    else:
        if hook_path.exists():
            print(f"setup_hooks: hook already wired -> {hook_path}")
        else:
            print(f"setup_hooks: pre-commit install failed:\n{out}", file=sys.stderr)
            steps_ok = False

    # Step 3: warm the gitleaks cache (download the binary on a harmless file).
    rc, out = _run(
        [python, "-m", "pre_commit", "run", "gitleaks",
         "--files", ".pre-commit-config.yaml"],
        repo,
    )
    # gitleaks returns 0 when no secrets found; a nonzero here after a fresh
    # fetch usually means the binary downloaded fine but the probe file tripped
    # something unexpected -- surface it but do not fail install.
    if rc == 0:
        print("setup_hooks: gitleaks warmed (cache populated, probe clean).")
    else:
        print(
            f"setup_hooks: gitleaks warm-up rc={rc} (cache may still populate "
            f"on first real run):\n{out[:300]}",
            file=sys.stderr,
        )

    # Step 4: verify.
    if hook_path.exists() and _pre_commit_available(python):
        print("\nsetup_hooks: OK. pre-commit harness is active.")
        print("  Next: `git commit` now runs gitleaks + notebook hygiene + H.3.")
        print("  Manual: python -m pre_commit run --all-files")
        return 0
    return 1


def cmd_check(repo: Path, python: str) -> int:
    """Print machine-state relevé (no changes). For the per-lane report #9888."""
    print(f"# Pre-commit harness relevé — {repo.name}")
    pc = shutil.which("pre-commit")
    gl = shutil.which("gitleaks")
    pc_mod = _pre_commit_available(python)
    rc, ver = (None, None)
    if pc_mod:
        rc, ver = _run([python, "-m", "pre_commit", "--version"], repo)
    hook = _hooks_dir(repo) / "pre-commit"
    hooks_dir = _hooks_dir(repo)
    installed_hooks = (
        sorted(p.name for p in hooks_dir.iterdir() if not p.name.endswith(".sample"))
        if hooks_dir.exists() else []
    )
    print(f"pre-commit on PATH      : {pc or 'ABSENT'}")
    print(f"pre-commit module (-m)  : {'available' if pc_mod else 'ABSENT'}" + (f" ({ver})" if ver else ""))
    print(f"gitleaks on PATH        : {gl or 'ABSENT (pre-commit manages it in its cache)'}")
    print(f"core.hooksPath          : {subprocess.run(['git','config','core.hooksPath'], capture_output=True, text=True).stdout.strip() or '(unset → default .git/hooks)'}")
    print(f"git hooks/pre-commit    : {'EXISTS' if hook.exists() else 'MISSING (run setup_hooks.py)'}")
    print(f"hooks dir installed     : {', '.join(installed_hooks) or '(only samples)'}")
    # Exit 0 if harness active, 1 otherwise (useful for fleet audit scripting).
    return 0 if (pc_mod and hook.exists()) else 1


def cmd_check_parity(repo: Path, python: str) -> int:
    """Compare declared hooks (.pre-commit-config.yaml) vs executable state."""
    cfg = repo / ".pre-commit-config.yaml"
    if not cfg.exists():
        print(f"setup_hooks: {cfg} not found", file=sys.stderr)
        return 1
    text = cfg.read_text(encoding="utf-8")
    declared = re.findall(r"^\s*-\s+id:\s*(\S+)", text, re.MULTILINE)
    print(f"Declared hooks ({len(declared)}): {', '.join(declared)}")

    # validate-config: confirms the YAML parses and external repos fetch.
    rc, out = _run([python, "-m", "pre_commit", "validate-config", str(cfg)], repo)
    print(f"validate-config         : {'PASS (all declared hooks fetch/parse)' if rc == 0 else f'FAIL rc={rc}'}")
    if rc != 0:
        print(out[:500], file=sys.stderr)

    # Which local-hook entry scripts exist on disk?
    print("Local hook entry scripts:")
    for m in re.finditer(r"-\s+id:\s*(\S+).*?entry:\s*([^\n]+)", text, re.S):
        hid, entry = m.group(1), m.group(2).strip()
        # entry like "python scripts/notebook_tools/strip_probe_banner.py --apply"
        parts = entry.split()
        script = next((p for p in parts if p.endswith(".py")), None)
        if script:
            exists = (repo / script).exists()
            print(f"  {hid:32} -> {script} [{'EXISTS' if exists else 'MISSING'}]")
    return 0 if rc == 0 else 1


# Probe secret for --self-test. Assembled from parts so NO contiguous literal
# appears in source -- GitHub push protection blocks commits carrying a literal
# Stripe key pattern even when the value is fake (it cannot tell). The assembled
# value IS a valid stripe-key pattern that gitleaks flags once written to the
# probe file. NOT a canonical EXAMPLE key: those are allowlisted by gitleaks'
# defaults and would mask a silent no-op (the root defect of #9888).
_SELFTEST_SECRET = "sk_live_" + "51Hqk2l3f4g5h6j7k" + "8l9n0mN1o2pQ3r4s"


def cmd_self_test(repo: Path, python: str) -> int:
    """Functional verification: does gitleaks actually DETECT a staged secret?

    ``--check`` verifies STRUCTURE (hook file present, pre-commit installed)
    but not FUNCTION. The gitleaks config once shipped without
    ``[extend] useDefault = true``, so gitleaks matched NOTHING -- structurally
    "installed", functionally a silent no-op (the root defect of #9888). This
    mode stages a known-detectable secret, runs gitleaks against the staged
    content, and expects a nonzero exit (leaks found = detection works). It then
    cleans up (unstage + delete the probe). No commit is ever made.

    Exit 0 if gitleaks detected the staged secret (harness FUNCTIONAL); exit 1
    if it did not (silent no-op -- check ``.gitleaks.toml`` ``[extend]
    useDefault = true``).
    """
    if not _pre_commit_available(python):
        print("setup_hooks: pre-commit not available -- run `setup_hooks.py` first.",
              file=sys.stderr)
        return 1

    probe = repo / "_gitleaks_selftest_probe.py"
    secret = _SELFTEST_SECRET  # assembled at runtime (no literal in source)
    probe.write_text(
        f"# setup_hooks --self-test probe (auto-deleted, never committed)\n"
        f'token = "{secret}"\n',
        encoding="utf-8",
    )
    try:
        # gitleaks runs as `protect --staged` with pass_filenames:false, so it
        # scans STAGED content only. `pre-commit run gitleaks --files <x>` is
        # IGNORED (--files never reaches the hook) -- staging is the only path.
        _run(["git", "add", "--", str(probe)], repo)
        rc, out = _run([python, "-m", "pre_commit", "run", "gitleaks"], repo)
        leaks = out.count("RuleID:")
        if rc != 0 and leaks > 0:
            print(f"setup_hooks: SELF-TEST PASS -- gitleaks detected {leaks} staged leak(s).")
            print("  Harness is FUNCTIONAL (detection works, not just structure).")
            return 0
        print(
            f"setup_hooks: SELF-TEST FAIL -- gitleaks rc={rc}, {leaks} leak(s) reported.",
            file=sys.stderr,
        )
        print(
            "  A staged secret was NOT detected. Check .gitleaks.toml carries "
            "`[extend] useDefault = true` (without it gitleaks is a silent no-op, "
            "the root defect of #9888).",
            file=sys.stderr,
        )
        if out:
            print(f"  gitleaks output (truncated):\n{out[:400]}", file=sys.stderr)
        return 1
    finally:
        # Cleanup: unstage + delete probe. Never leave the secret staged/on disk.
        _run(["git", "reset", "-q", "--", str(probe)], repo)
        try:
            probe.unlink()
        except OSError:
            pass


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(
        description="Idempotent installer for the CoursIA pre-commit harness (#9888)."
    )
    p.add_argument("--install", action="store_true", default=True,
                   help="Install pre-commit + wire hook + warm gitleaks (default; idempotent).")
    p.add_argument("--check", action="store_true",
                   help="Print machine-state relevé (no changes). Exit 1 if harness inactive.")
    p.add_argument("--check-parity", action="store_true",
                   help="Compare declared hooks vs executable state.")
    p.add_argument("--self-test", action="store_true",
                   help="Functional check: stage a fake secret, verify gitleaks detects it, clean up.")
    # Allow a plain `--check`/`--check-parity`/`--self-test` without implying install.
    args = p.parse_args(argv)

    repo = find_repo_root()
    python = sys.executable

    if args.self_test:
        return cmd_self_test(repo, python)
    if args.check_parity:
        return cmd_check_parity(repo, python)
    if args.check:
        return cmd_check(repo, python)
    return cmd_install(repo, python)


if __name__ == "__main__":
    sys.exit(main())
