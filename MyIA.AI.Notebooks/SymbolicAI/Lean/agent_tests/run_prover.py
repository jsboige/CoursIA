"""Quick prover runner for Voting.lean sorry targets."""
import sys
import json
import traceback

sys.stdout.reconfigure(line_buffering=True)

from prover.config import DEMOS
from prover.trace import TraceLogger
from prover.provers import AutonomousProver

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

    trace = TraceLogger(output_dir=f"traces/{demo['name']}")
    prover = AutonomousProver(trace, provider=provider, hitl_enabled=False)

    try:
        result = prover.prove_sorry(demo, max_iterations=max_iters,
                                    agent_timeout_s=timeout)
        print(f"\nRESULT: {json.dumps(result, indent=2)}", flush=True)
    except Exception as e:
        print(f"\nCRASH: {e}", flush=True)
        traceback.print_exc()

    trace.save(demo["name"])
    print("Done.", flush=True)
