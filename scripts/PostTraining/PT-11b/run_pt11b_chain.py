"""Chain-run PT-11b across all 4 seeds sequentially.

Each seed writes its own output notebook (pt11b_seed_<s>_output.ipynb) and appends
to pt11b_multiseed_output/pt11b_per_seed_metrics.jsonl.

Usage: python run_pt11b_chain.py [seeds]
       (defaults to 0 1 7 42)
"""

import subprocess
import sys
import time
from pathlib import Path

# Repo root: scripts/PostTraining/PT-11b/run_pt11b_chain.py -> <root>/scripts/PostTraining/PT-11b
WORK_DIR = Path(__file__).resolve().parents[3]

SEEDS = [int(s) for s in sys.argv[1:]] or [0, 1, 7, 42]
# run_pt11b.py lives NEXT TO this chain runner (scripts/PostTraining/PT-11b/),
# not at the repo root. WORK_DIR / "run_pt11b.py" was a path bug (rc=2, file not found).
RUNNER = Path(__file__).resolve().parent / "run_pt11b.py"


def run_seed(seed: int) -> tuple[int, float]:
    print(f"\n{'=' * 70}\n SEED {seed}\n{'=' * 70}")
    t_start = time.perf_counter()
    # use sys.executable (conda env python), NOT literal "python" which resolves to
    # system Python and fails (rc=2, no trl/torch). Inherit full env so CUDA + conda
    # paths propagate.
    import os as _os
    _env = dict(_os.environ)
    _env["PYTHONUNBUFFERED"] = "1"
    rc = subprocess.call(
        [sys.executable, str(RUNNER), str(seed)],
        cwd=str(WORK_DIR),
        env=_env,
    )
    elapsed = time.perf_counter() - t_start
    return rc, elapsed


def main():
    print(f"Chaining PT-11b across seeds: {SEEDS}")
    print(f"Work dir: {WORK_DIR}")
    print(f"Runner: {RUNNER}")

    t_global = time.perf_counter()
    for seed in SEEDS:
        rc, elapsed = run_seed(seed)
        print(f"\n[chain] seed={seed} rc={rc} elapsed={elapsed:.1f}s ({elapsed/60:.1f} min)")
        if rc != 0:
            print(f"[chain] FAIL at seed={seed}. Aborting chain.")
            sys.exit(rc)

    total = time.perf_counter() - t_global
    print(f"\n[chain] All {len(SEEDS)} seeds completed in {total:.1f}s ({total/60:.1f} min)")


if __name__ == "__main__":
    main()