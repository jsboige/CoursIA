"""Run the v4 FishAudio S2-Pro audiobook pipeline.

Usage:
    python -m v4.run_pipeline --phase all
    python -m v4.run_pipeline --phase p0
    python -m v4.run_pipeline --phase p0,p1,p2
    python -m v4.run_pipeline --phase p5 --force
"""
from __future__ import annotations

import argparse
import sys
import time
from pathlib import Path

from dotenv import load_dotenv

PHASES = ["p0", "p1", "p2", "p3", "p4", "p5", "p6", "p7"]

PHASE_NAMES = {
    "p0": "Narrative Research",
    "p1": "Voice Cloning + Casting",
    "p2": "Segmentation",
    "p3": "Dramatic Context",
    "p4": "Prosody Annotation",
    "p5": "TTS Generation",
    "p6": "MP3 Compilation",
    "p7": "Quality Verification",
}


def run_phase(phase: str, force: bool = False) -> Path:
    """Run a single pipeline phase."""
    if phase == "p0":
        from .p0_narrative_research import run
    elif phase == "p1":
        from .p1_voice_cloning import run
    elif phase == "p2":
        from .p2_segmentation import run
    elif phase == "p3":
        from .p3_dramatic_context import run
    elif phase == "p4":
        from .p4_annotation import run
    elif phase == "p5":
        from .p5_tts import run
    elif phase == "p6":
        from .p6_compile import run
    elif phase == "p7":
        from .p7_verify import run
    else:
        raise ValueError(f"Unknown phase: {phase}")

    return run(force=force)


def main():
    load_dotenv(Path(__file__).resolve().parent.parent.parent.parent / ".env")

    parser = argparse.ArgumentParser(
        description="v4 FishAudio S2-Pro audiobook pipeline"
    )
    parser.add_argument(
        "--phase",
        type=str,
        default="all",
        help=f"Phase(s) to run: {', '.join(PHASES)}, or 'all'",
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="Force re-run (ignore cached outputs)",
    )
    args = parser.parse_args()

    if args.phase == "all":
        phases = PHASES
    else:
        phases = [p.strip() for p in args.phase.split(",")]

    invalid = [p for p in phases if p not in PHASES]
    if invalid:
        print(f"ERROR: Invalid phases: {invalid}")
        print(f"Valid phases: {PHASES}")
        sys.exit(1)

    print("=" * 60)
    print("v4 FishAudio S2-Pro Audiobook Pipeline")
    print("=" * 60)
    print(f"Phases: {phases}")
    print(f"Force:  {args.force}")
    print()

    total_start = time.time()

    for phase in phases:
        print(f"\n{'─' * 60}")
        print(f"  {phase.upper()} — {PHASE_NAMES[phase]}")
        print(f"{'─' * 60}")

        start = time.time()
        try:
            output = run_phase(phase, force=args.force)
            elapsed = time.time() - start
            print(f"\n  {phase.upper()} completed in {elapsed:.1f}s")
            print(f"  Output: {output}")
        except Exception as e:
            elapsed = time.time() - start
            print(f"\n  {phase.upper()} FAILED after {elapsed:.1f}s: {e}")
            if "--force" not in sys.argv:
                print("  Use --force to retry, or fix the issue and re-run.")
            sys.exit(1)

    total_elapsed = time.time() - total_start
    print(f"\n{'═' * 60}")
    print(f"Pipeline complete in {total_elapsed:.1f}s ({total_elapsed/60:.1f}min)")
    print(f"{'═' * 60}")


if __name__ == "__main__":
    main()
