#!/usr/bin/env python3
"""Reproduction harness for the HopfProblem formalization (plby/HopfProblem).

Verifies and summarizes a LOCAL, PINNED checkout of the upstream repository
(git@github.com:plby/HopfProblem.git @ 9ac8a456b526527837d7082ff775213ca8bc9809)
that reproduces the S^6 complex-structure proof on this machine:

    elan toolchain install leanprover/lean4:v4.33.0
    lake update
    lake exe cache get          # Mathlib v4.33.0 oleans
    lake build lean4export
    lake build Challenge        # 8707 jobs
    lake build Solution         # 248,818-line monolith (single file)
    lake exe comparator comparator/config.json   # Lean + nanoda kernels

The notebook Lean-30-Complex-Structure-S6.ipynb consumes the JSON emitted by
`check` so that every committed output traces back to a real artifact on disk
(build.log, comparator.log written by the actual runs -- never hand-edited).

Usage:
    python hopf_s6_reproduction.py check          # verify artifacts, emit JSON
    python hopf_s6_reproduction.py full --dry-run # print the full protocol
    python hopf_s6_reproduction.py full           # EXECUTE the full protocol
                                                  # (clone+build+comparator,
                                                  #  ~35 min + toolchains)

The checkout lives in WSL (ext4) because lake cache-get stalls on /mnt drvfs.
"""
import argparse
import json
import re
import subprocess
import sys

PINNED_SHA = "9ac8a456b526527837d7082ff775213ca8bc9809"
HOPF_DIR = "/home/jesse/HopfProblem"
TOOLCHAIN = "leanprover/lean4:v4.33.0"
PERMITTED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]

FULL_PROTOCOL = [
    f"git clone https://github.com/plby/HopfProblem.git {HOPF_DIR}",
    f"git -C {HOPF_DIR} checkout {PINNED_SHA}",
    f"elan toolchain install {TOOLCHAIN}",
    f"cd {HOPF_DIR} && lake update",
    f"cd {HOPF_DIR} && lake exe cache get",
    f"cd {HOPF_DIR} && lake build lean4export",
    f"cd {HOPF_DIR} && lake build Challenge",
    f"cd {HOPF_DIR} && lake build Solution",
    ("cd {d} && COMPARATOR_LANDRUN=$HOME/bin/landrun "
     "COMPARATOR_LEAN4EXPORT=$d/.lake/packages/lean4export/.lake/build/bin/lean4export "
     "COMPARATOR_NANODA=$HOME/nanoda_lib/target/release/nanoda_bin "
     "lake exe comparator comparator/config.json").format(d=HOPF_DIR),
]


def wsl(cmd: str, timeout: int = 120) -> str:
    """Run a command inside the WSL distro (login shell for elan PATH)."""
    proc = subprocess.run(
        ["wsl", "-e", "bash", "-lc", cmd],
        capture_output=True, text=True, timeout=timeout, encoding="utf-8", errors="replace",
    )
    if proc.returncode != 0:
        raise RuntimeError(f"WSL command failed (rc={proc.returncode}): {cmd}\n{proc.stderr}")
    return proc.stdout.strip()


def sh(cmd: str, default: str = "") -> str:
    """WSL command that may legitimately fail (grep no-match) -> default."""
    try:
        return wsl(cmd)
    except (RuntimeError, subprocess.TimeoutExpired):
        return default


def parse_build_log(log: str) -> dict:
    info = {"jobs_counts": None, "solution_seconds": None, "axioms_line": None}
    counts = [int(m.group(1)) for m in
              re.finditer(r"Build completed successfully \((\d+) jobs?\)", log)]
    info["jobs_counts"] = counts
    m = re.search(r"Built Solution \((\d+)s\)", log)
    if m:
        info["solution_seconds"] = int(m.group(1))
    m = re.search(r"^info: Solution\.lean:\d+:\d+: (.+depends on axioms.+)$",
                  log, re.MULTILINE)
    if m:
        info["axioms_line"] = m.group(1)
    return info


def parse_comparator_log(log: str) -> dict:
    info = {"real_seconds": None, "nanoda": None, "lean_kernel": None, "verdict": None}
    m = re.search(r"real\s+(\d+)m([\d.]+)s", log)
    if m:
        info["real_seconds"] = round(int(m.group(1)) * 60 + float(m.group(2)), 1)
    if "Nanoda kernel accepts the solution" in log:
        info["nanoda"] = "accepts"
    if "Lean default kernel accepts the solution" in log:
        info["lean_kernel"] = "accepts"
    if "Your solution is okay!" in log:
        info["verdict"] = "Your solution is okay!"
    return info


def cmd_check() -> dict:
    out = {
        "pinned_sha": PINN_SHA if (PINN_SHA := sh(f"git -C {HOPF_DIR} rev-parse HEAD")) else None,
        "sha_matches_pin": sh(f"git -C {HOPF_DIR} rev-parse HEAD") == PINNED_SHA,
        "toolchain": sh(f"cat {HOPF_DIR}/lean-toolchain", default=""),
        "solution_lines": int(sh(f"wc -l < {HOPF_DIR}/Solution.lean", default="0")),
        "solution_olean_bytes": int(sh(f"stat -c %s {HOPF_DIR}/.lake/build/lib/lean/Solution.olean",
                                       default="0")),
        "sorry_proof_count": int(sh(
            rf"grep -cE '^\s*sorry\s*$' {HOPF_DIR}/Solution.lean", default="0")),
        "sorry_word_count": int(sh(
            rf"grep -cw sorry {HOPF_DIR}/Solution.lean", default="0")),
        "axiom_decl_count": int(sh(
            rf"grep -cE '^\s*axiom\s' {HOPF_DIR}/Solution.lean", default="0")),
        "native_decide_count": int(sh(
            rf"grep -cw native_decide {HOPF_DIR}/Solution.lean", default="0")),
        "license": sh(f"head -1 {HOPF_DIR}/LICENSE", default=""),
    }
    build_log = sh(f"cat {HOPF_DIR}/build.log", default="")
    comp_log = sh(f"cat {HOPF_DIR}/comparator.log", default="")
    out["build"] = parse_build_log(build_log) if build_log else None
    out["comparator"] = parse_comparator_log(comp_log) if comp_log else None
    out["build_log_present"] = bool(build_log)
    out["comparator_log_present"] = bool(comp_log)

    ax = out.get("build", {}).get("axioms_line") if out.get("build") else None
    out["axioms_within_permitted"] = (
        sorted(re.findall(r"\w+(?:\.\w+)*", ax.split(":", 1)[-1]))
        == sorted(PERMITTED_AXIOMS)
        if ax else False
    )
    print(json.dumps(out, indent=2, ensure_ascii=False))
    return 0


def cmd_full(dry_run: bool) -> int:
    print("Full reproduction protocol (see docstring for hardware notes):")
    for step in FULL_PROTOCOL:
        print(f"  $ {step}")
    if dry_run:
        print("\n(dry-run: nothing executed)")
        return 0
    print("\nExecuting... (this takes ~35 min of build + 11 min of comparator)")
    for step in FULL_PROTOCOL:
        print(f"\n$ {step}")
        subprocess.run(["wsl", "-e", "bash", "-lc", step], check=False)
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("check", help="verify artifacts and emit JSON summary")
    full = sub.add_parser("full", help="run or print the full protocol")
    full.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()
    if args.cmd == "check":
        return cmd_check()
    return cmd_full(args.dry_run)


if __name__ == "__main__":
    sys.exit(main())
