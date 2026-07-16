#!/usr/bin/env python3
"""po-2026 — local lake-build recovery recipe (script codification of #6771).

Source issue : #6771 (priority-high, owner po-2026, self-repair rule F).
Canonical recipe documented in : docs/lean/po2026-local-build-troubleshooting.md
(PR #6789 MERGED c.472, validated firsthand c.473 on knot_lean).

Background. ``lake build`` on po-2026 was unreliable for cold rebuilds of
Mathlib (~2900 modules, ~8 min timeout, OOM ``3221226505`` under rc1). The
recovery recipe B (cache-get + build) was empirically validated c.473 :
``http.postBuffer 524288000`` + shallow ``--depth 1`` clone + ``lake exe cache
get`` + ``lake build`` => ~1 min SUCCESS instead of ~8 min/OOM-timeout.

This script codifies that recipe so the next cold build on po-2026 doesn't
re-invent the wheel : run ``python scripts/lean/po2026_recover_build.py <lake>``
and the script takes care of postBuffer / shallow clone / cache-get / build.

Idempotent. Each phase is skipped if already satisfied. Safe to re-run after
partial failures. Phase headers + elapsed time printed for diagnostics.

Usage:
    python scripts/lean/po2026_recover_build.py <lake_dir>             # Full recipe
    python scripts/lean/po2026_recover_build.py <lake_dir> --check     # Dry-run
    python scripts/lean/po2026_recover_build.py <lake_dir> --target <Module>  # Build target
    python scripts/lean/po2026_recover_build.py <lake_dir> --no-build  # Stop at cache-get
    python scripts/lean/po2026_recover_build.py <lake_dir> --from <sibling_lake>  # Recipe D
"""

from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
import time
from pathlib import Path

# PostBuffer 500 MB eliminates ``invalid index-pack output`` on mathlib4 clone
# (mode d'échec 4, #6771 + c.472). Set globally; harmless for other repos.
HTTP_POSTBUFFER_BYTES = 524288000  # 500 MB

# Mathlib4 upstream (community fork — Leanprover-community/mathlib4, NOT
# leanprover/mathlib4 which is the Lean 3 archive).
MATHLIB4_URL = "https://github.com/leanprover-community/mathlib4.git"

# ``LAKE_JOBS=2`` dodge OOM (mode d'échec 2, #6771 + c.472). Lake's default is
# N_cpu, too aggressive for Mathlib cold-build on po-2026 hardware.
LAKE_JOBS = 2


def _elapsed(t_start: float) -> str:
    """Format elapsed seconds as ``42.3s`` or ``1m23s``."""
    secs = time.monotonic() - t_start
    if secs < 60:
        return f"{secs:.1f}s"
    return f"{int(secs // 60)}m{int(secs % 60)}s"


def _phase(title: str) -> None:
    """Print a phase header (matches the existing script style in scripts/lean/)."""
    print()
    print("=" * 60)
    print(title)
    print("=" * 60)


def _ok(msg: str) -> None:
    print(f"OK: {msg}")


def _warn(msg: str) -> None:
    print(f"WARN: {msg}", file=sys.stderr)


def _err(msg: str) -> None:
    print(f"ERROR: {msg}", file=sys.stderr)


def step_postbuffer(dry_run: bool) -> bool:
    """Step 1 — set ``http.postBuffer 524288000`` globally (mode 4 mitigation).

    Idempotent : ``git config --global`` is a no-op if the value already
    matches. Belt-and-suspenders ``get`` first, then ``set`` only on miss.
    """
    _phase("STEP 1/4 : http.postBuffer 524288000 (mode 4 mitigation)")
    if dry_run:
        print("[dry-run] would set http.postBuffer = 524288000")
        return True
    try:
        cur = subprocess.run(
            ["git", "config", "--global", "--get", "http.postBuffer"],
            capture_output=True, timeout=10,
        )
        if cur.returncode == 0 and cur.stdout.strip() == str(HTTP_POSTBUFFER_BYTES).encode():
            _ok(f"already set ({HTTP_POSTBUFFER_BYTES} bytes)")
            return True
        subprocess.run(
            ["git", "config", "--global", "http.postBuffer", str(HTTP_POSTBUFFER_BYTES)],
            check=True, timeout=10,
        )
        _ok(f"set http.postBuffer = {HTTP_POSTBUFFER_BYTES}")
        return True
    except Exception as exc:
        _err(f"failed to set http.postBuffer: {exc}")
        return False


def step_clone_mathlib(lake_dir: Path, dry_run: bool) -> bool:
    """Step 2 — shallow clone mathlib4 into ``.lake/packages/mathlib``.

    Idempotent : skip if directory exists (regardless of content — operator
    judgment whether to delete and re-clone if partial). ``--depth 1`` is
    the resilience trick : 4x less data, faster + less likely to hit a flaky
    segment.
    """
    _phase("STEP 2/4 : shallow clone mathlib4 (mode 4 mitigation)")
    mathlib_dir = lake_dir / ".lake" / "packages" / "mathlib"
    if mathlib_dir.exists() and (mathlib_dir / ".git").exists():
        _ok(f"already present at {mathlib_dir} (skip clone)")
        return True
    if dry_run:
        print(f"[dry-run] would clone {MATHLIB4_URL} -> {mathlib_dir}")
        return True
    mathlib_dir.parent.mkdir(parents=True, exist_ok=True)
    t = time.monotonic()
    print(f"Cloning {MATHLIB4_URL} -> {mathlib_dir} (depth 1)...")
    result = subprocess.run(
        ["git", "clone", "--depth", "1", MATHLIB4_URL, str(mathlib_dir)],
        timeout=600,  # 10 min ceiling; on flaky networks this can take a while
    )
    if result.returncode != 0:
        _err(f"git clone failed (exit {result.returncode}, elapsed {_elapsed(t)})")
        _warn("mode d'échec 4 not eliminated : réseau instable — re-run the script")
        return False
    _ok(f"cloned ({_elapsed(t)})")
    return True


def step_cache_get(lake_dir: Path, dry_run: bool) -> bool:
    """Step 3 — ``lake exe cache get`` : download precompiled Mathlib oleans.

    Idempotent : lake's cache is content-addressed; re-running is cheap (skips
    files already present). The c.473 measurement was ~40-60s on a warm
    network.
    """
    _phase("STEP 3/4 : lake exe cache get (Azure precompiled .olean)")
    if not (lake_dir / "lakefile.lean").exists() and not (lake_dir / "lakefile.toml").exists():
        _err(f"no lakefile.lean/.toml found at {lake_dir}")
        return False
    if dry_run:
        print(f"[dry-run] would run 'lake exe cache get' in {lake_dir}")
        return True
    t = time.monotonic()
    print(f"Running: lake exe cache get (cwd={lake_dir})")
    result = subprocess.run(
        ["lake", "exe", "cache", "get"],
        cwd=str(lake_dir), timeout=900,  # 15 min ceiling; cold network rare
    )
    if result.returncode != 0:
        _err(f"lake exe cache get failed (exit {result.returncode}, elapsed {_elapsed(t)})")
        return False
    _ok(f"cache populated ({_elapsed(t)})")
    return True


def step_build(lake_dir: Path, target: str | None, no_build: bool, dry_run: bool) -> bool:
    """Step 4 — ``lake build [target]`` with ``LAKE_JOBS=2`` OOM mitigation.

    With oleans pre-populated by step 3, this is ~60s for knot_lean (vs ~8 min
    cold rebuild). ``LAKE_JOBS=2`` is the empirical mitigation for mode 2
    (OOM ``3221226505``).
    """
    if no_build:
        _phase("STEP 4/4 : lake build — SKIPPED (--no-build)")
        _ok("cache warm; build deferred to caller")
        return True
    _phase("STEP 4/4 : lake build (LAKE_JOBS=2 = mode 2 mitigation)")
    cmd = ["lake", "build"]
    if target:
        cmd.append(target)
    print(f"Running: LAKE_JOBS={LAKE_JOBS} {' '.join(cmd)} (cwd={lake_dir})")
    if dry_run:
        print("[dry-run] would invoke the above")
        return True
    t = time.monotonic()
    env = {"LAKE_JOBS": str(LAKE_JOBS), "PATH": _safe_path_env()}
    result = subprocess.run(cmd, cwd=str(lake_dir), env=env, timeout=1800)  # 30 min ceiling
    if result.returncode != 0:
        _err(f"lake build failed (exit {result.returncode}, elapsed {_elapsed(t)})")
        return False
    _ok(f"build succeeded ({_elapsed(t)})")
    return True


def step_copy_lake(src_lake: Path, dst_lake: Path, dry_run: bool) -> bool:
    """Step D — copy ``.lake/`` from a sibling lake (mode 3 mitigation).

    Junction ``.lake`` (NTFS reparse point) is NOT trusted by lake DB → cold
    rebuild → OOM. Solution : copy the entire ``.lake/`` directory from a
    sibling lake that has the same toolchain (lean-toolchain pin must match).
    """
    _phase("STEP D : copy .lake/ from sibling lake (mode 3 mitigation)")
    if not (src_lake / ".lake").exists():
        _err(f"sibling lake {src_lake} has no .lake/ to copy from")
        return False
    src_toolchain = (src_lake / "lean-toolchain").read_text().strip() if (src_lake / "lean-toolchain").exists() else None
    dst_toolchain = (dst_lake / "lean-toolchain").read_text().strip() if (dst_lake / "lean-toolchain").exists() else None
    if src_toolchain and dst_toolchain and src_toolchain != dst_toolchain:
        _warn(f"toolchain mismatch: src={src_toolchain} dst={dst_toolchain} — copy may corrupt cache")
    target_lake = dst_lake / ".lake"
    if target_lake.exists():
        _warn(f"{target_lake} already exists — remove it manually if you want a fresh copy")
        return True
    if dry_run:
        print(f"[dry-run] would copy {src_lake}/.lake -> {target_lake}")
        return True
    t = time.monotonic()
    print(f"Copying {src_lake}/.lake -> {target_lake}...")
    shutil.copytree(src_lake / ".lake", target_lake)
    _ok(f"copied ({_elapsed(t)})")
    return True


def _safe_path_env() -> str:
    """Return ``PATH`` string for subprocess. Falls back to current PATH.

    Windows subprocess defaults to a minimal PATH that often excludes ``git``
    and ``lake`` (elan install paths). Append the common elan locations.
    """
    import os
    base = os.environ.get("PATH", "")
    extras = []
    home = Path.home()
    # elan default install paths on Windows
    for p in [
        home / ".elan" / "bin",
        home / ".cargo" / "bin",
        Path("C:/Program Files/Git/bin"),
        Path("C:/Program Files/Git/usr/bin"),
    ]:
        if p.exists() and str(p) not in base:
            extras.append(str(p))
    if extras:
        return ";".join(extras) + ";" + base
    return base


def main() -> int:
    parser = argparse.ArgumentParser(
        description="po-2026 lake-build recovery recipe (codification of #6771).",
        epilog="Canonical docs: docs/lean/po2026-local-build-troubleshooting.md",
    )
    parser.add_argument("lake_dir", type=Path, help="Path to the Lean lake directory (containing lakefile.lean)")
    parser.add_argument("--target", type=str, default=None, help="Build only this target module (e.g. Knots)")
    parser.add_argument("--no-build", action="store_true", help="Stop after cache-get; don't run lake build")
    parser.add_argument("--from", dest="src_lake", type=Path, default=None,
                        help="Step D: copy .lake/ from this sibling lake before running recipe")
    parser.add_argument("--check", action="store_true", help="Dry-run : print what would be done, don't execute")
    args = parser.parse_args()

    lake_dir = args.lake_dir.resolve()
    if not lake_dir.exists():
        _err(f"lake_dir does not exist: {lake_dir}")
        return 1
    if not (lake_dir / "lakefile.lean").exists() and not (lake_dir / "lakefile.toml").exists():
        _err(f"no lakefile.lean/.toml at {lake_dir} — wrong directory?")
        return 1

    print("po-2026 lake-build recovery recipe (#6771)")
    print(f"  lake_dir : {lake_dir}")
    if args.target:
        print(f"  target   : {args.target}")
    if args.no_build:
        print("  mode     : cache-get only (no build)")
    if args.check:
        print("  mode     : --check (dry-run)")
    if args.src_lake:
        print(f"  from     : {args.src_lake.resolve()} (Step D copy)")
    print(f"  http.postBuffer target : {HTTP_POSTBUFFER_BYTES}")
    print(f"  LAKE_JOBS : {LAKE_JOBS}")

    results: list[tuple[str, bool]] = []

    if args.src_lake:
        results.append(("copy .lake/ from sibling", step_copy_lake(args.src_lake.resolve(), lake_dir, args.check)))

    results.append(("http.postBuffer", step_postbuffer(args.check)))
    results.append(("clone mathlib4", step_clone_mathlib(lake_dir, args.check)))
    results.append(("lake exe cache get", step_cache_get(lake_dir, args.check)))
    results.append(("lake build", step_build(lake_dir, args.target, args.no_build, args.check)))

    print()
    print("=" * 60)
    print("RESULTS")
    print("=" * 60)
    for name, ok in results:
        status = "OK" if ok else "FAILED"
        print(f"  {name:30s} {status}")
    all_ok = all(ok for _, ok in results)
    print()
    if all_ok:
        print("Recipe completed successfully. See docs/lean/po2026-local-build-troubleshooting.md for details.")
        return 0
    print("Some steps failed. See output above. Re-run the script after fixing the underlying issue.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
