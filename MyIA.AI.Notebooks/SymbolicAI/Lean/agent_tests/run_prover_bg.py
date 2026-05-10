"""Background-runnable harness for the multi-agent prover.

Usage:
    python -u run_prover_bg.py <demo_id> [--provider local|zai] [--max-iter N] \
                               [--workflow-timeout S]

Designed to be launched via Bash run_in_background. Writes structured
progress + final verdict to stdout (use -u so it streams) and reads/writes
files in-place — the next iteration picks up wherever the file ended.

Output format (parseable by harvest scripts):
    [BG] iter=<n> sorry=<count> action=<text>
    [BG] FINAL ok=<bool> sorry=<final> elapsed=<s>
    [BG] OTEL_PATH=<absolute path>
    [BG] TRACE_PATH=<absolute path>
"""

from __future__ import annotations

import argparse
import asyncio
import os
import sys
import time
from pathlib import Path

PROVER_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(PROVER_DIR))

# Force LEAN_PROJECT before importing prover modules so they see it.
DEFAULT_LEAN_PROJECT = (
    PROVER_DIR.parent.parent.parent / "GameTheory" / "social_choice_lean"
).resolve()
os.environ.setdefault("LEAN_PROJECT", str(DEFAULT_LEAN_PROJECT))

from prover.config import DEMOS  # noqa: E402
from prover.provers import MultiAgentSorryProver  # noqa: E402
from prover.trace import TraceLogger  # noqa: E402


def _bg(line: str) -> None:
    """Print a parseable [BG] line, flushing immediately."""
    print(f"[BG] {line}", flush=True)


def _peek_sorry_count(filepath: str) -> int:
    try:
        return Path(filepath).read_text(encoding="utf-8").count("sorry")
    except OSError:
        return -1


async def main(args: argparse.Namespace) -> int:
    demo = DEMOS.get(args.demo_id)
    if demo is None:
        _bg(f"ERROR demo_id={args.demo_id} not in DEMOS")
        return 2

    file_target = demo.get("file") or "(no file — synthetic theorem demo)"
    _bg(f"START demo_id={args.demo_id} name={demo['name']}")
    _bg(f"FILE  {file_target}")
    _bg(f"LINE  {demo.get('line')}")
    _bg(f"DIFF  {demo.get('difficulty')}")
    _bg(
        f"PROVIDER reasoning={args.provider} fast={args.local_provider} "
        f"max_iter={args.max_iter} workflow_timeout={args.workflow_timeout}s"
    )

    pre_sorry = _peek_sorry_count(file_target) if demo.get("file") else None
    if pre_sorry is not None:
        _bg(f"PRE_FILE_SORRY_COUNT {pre_sorry}")

    trace_dir = PROVER_DIR / "prover" / "baselines" / "traces"
    trace_dir.mkdir(parents=True, exist_ok=True)
    tr = TraceLogger(output_dir=str(trace_dir))

    prover = MultiAgentSorryProver(
        trace=tr,
        provider=args.provider,
        local_provider=args.local_provider,
    )

    t0 = time.time()
    try:
        result = await prover.prove_sorry(
            demo,
            max_iterations=args.max_iter,
            workflow_timeout_s=args.workflow_timeout,
        )
    except Exception as exc:
        elapsed = time.time() - t0
        _bg(f"EXCEPTION {type(exc).__name__}: {exc}")
        _bg(f"FINAL ok=False sorry=? elapsed={elapsed:.1f}")
        raise

    elapsed = time.time() - t0
    post_sorry = _peek_sorry_count(file_target) if demo.get("file") else None

    if post_sorry is not None:
        _bg(f"POST_FILE_SORRY_COUNT {post_sorry}")
        if pre_sorry is not None:
            _bg(f"DELTA {pre_sorry - post_sorry}")

    _bg(f"RESULT_KEYS {sorted(result.keys())}")
    _bg(f"RESULT_SUCCESS {result.get('success')}")
    _bg(f"RESULT_BEST_SORRY {result.get('best_sorry')}")
    _bg(f"RESULT_ITERATIONS {result.get('iterations')}")
    _bg(f"RESULT_ATTEMPTS {result.get('attempts')}")
    _bg(f"RESULT_SORRY_EVOLUTION {result.get('sorry_evolution')}")
    if result.get("skipped"):
        _bg(f"RESULT_SKIPPED reason={result.get('reason')} detail={result.get('detail')}")

    _bg(
        f"FINAL ok={bool(result.get('success'))} "
        f"sorry_after={post_sorry if post_sorry is not None else 'n/a'} "
        f"elapsed={elapsed:.1f}"
    )
    return 0


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("demo_id", type=int, help="Index in DEMOS dict (e.g. 9 for L325)")
    p.add_argument("--provider", default="local",
                   help="reasoning provider (local|zai|openai)")
    p.add_argument("--local-provider", default="local",
                   help="fast provider (default: local for SearchAgent)")
    p.add_argument("--max-iter", type=int, default=15,
                   help="max workflow iterations")
    p.add_argument("--workflow-timeout", type=int, default=1800,
                   help="wall-clock cap (seconds)")
    return p.parse_args()


if __name__ == "__main__":
    sys.exit(asyncio.run(main(parse_args())))
