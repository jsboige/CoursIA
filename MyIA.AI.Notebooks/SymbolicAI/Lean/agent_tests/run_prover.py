"""Quick prover runner for Voting.lean sorry targets."""
import sys
import json
import traceback
from pathlib import Path

sys.stdout.reconfigure(line_buffering=True)

from prover.config import DEMOS
from prover.trace import TraceLogger
from prover.provers import AutonomousProver
from prover.lean_utils import count_real_sorries, stub_theorem_proof


def _run_demo(demo: dict, max_iters: int, timeout: int, provider: str) -> dict:
    """Run one demo, exposing approved calibration proofs as temporary sorries."""
    calibration_target = None
    if (
        demo.get("sorry_type") == "sorry_replacement"
        and demo.get("file")
        and demo.get("theorem_name")
    ):
        target_path = Path(demo["file"])
        original = target_path.read_bytes()
        if count_real_sorries(original.decode("utf-8")) == 0:
            stubbed = stub_theorem_proof(
                original.decode("utf-8"), demo["theorem_name"]
            )
            target_path.write_bytes(stubbed.encode("utf-8"))
            calibration_target = (target_path, original)
            print(
                f"[CALIBRATION_STUB] theorem={demo['theorem_name']} "
                f"line={demo.get('line')} - approved proof stubbed to sorry, "
                "original restored on exit",
                flush=True,
            )

    try:
        trace = TraceLogger(output_dir=f"traces/{demo['name']}")
        try:
            prover = AutonomousProver(trace, provider=provider, hitl_enabled=False)
            return prover.prove_sorry(
                demo,
                max_iterations=max_iters,
                agent_timeout_s=timeout,
            )
        finally:
            trace.save(demo["name"])
    finally:
        if calibration_target is not None:
            calibration_target[0].write_bytes(calibration_target[1])
            print(
                "[CALIBRATION_RESTORE] approved proof restored", flush=True
            )


if __name__ == "__main__":
    demo_id = int(sys.argv[1]) if len(sys.argv) > 1 else 13
    max_iters = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    timeout = int(sys.argv[3]) if len(sys.argv) > 3 else 180
    provider = sys.argv[4] if len(sys.argv) > 4 else "zai"

    demo = DEMOS[demo_id].copy()

    print(f"Running: {demo['name']} (line {demo['line']}, max {max_iters} iters, timeout {timeout}s)", flush=True)
    print(f"Provider: {provider}", flush=True)
    if demo.get("proof_scaffolding"):
        print(f"  [Scaffold] {len(demo['proof_scaffolding'].splitlines())} lines of scaffolding provided", flush=True)

    try:
        result = _run_demo(demo, max_iters, timeout, provider)
        print(f"\nRESULT: {json.dumps(result, indent=2)}", flush=True)
    except Exception as e:
        print(f"\nCRASH: {e}", flush=True)
        traceback.print_exc()
        sys.exit(1)

    print("Done.", flush=True)
