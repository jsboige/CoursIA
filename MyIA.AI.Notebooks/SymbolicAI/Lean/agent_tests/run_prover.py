"""Quick prover runner for Voting.lean sorry targets."""
import sys
import json
import traceback

sys.stdout.reconfigure(line_buffering=True)

from prover.config import VOTING_FILE, VOTING_IMPORTS
from prover.trace import TraceLogger
from prover.provers import AutonomousProver

DEMOS = [
    {
        "name": "VOTING_BANKS_SET_CONDORCET",
        "line": 437,
        "theorem_name": "banks_set_condorcet",
        "description": (
            "Prove banks_set_condorcet: if x is a Condorcet winner in S, "
            "then x belongs to the Banks set. "
            "Strategy: singleton chain {x} is a banks_chain when x beats everyone in S. "
            "Available: condorcet_winner, banks_set, banks_winner, banks_chain, margin_pos"
        ),
    },
]

if __name__ == "__main__":
    demo_idx = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    max_iters = int(sys.argv[2]) if len(sys.argv) > 2 else 6

    demo = DEMOS[demo_idx].copy()
    demo["file"] = str(VOTING_FILE)
    demo["imports"] = VOTING_IMPORTS
    demo["sorry_type"] = "full_proof"
    demo["theorem"] = demo["theorem_name"]

    print(f"Running: {demo['name']} (line {demo['line']}, max {max_iters} iters)", flush=True)

    trace = TraceLogger(output_dir=f"traces/{demo['name']}")
    prover = AutonomousProver(trace, provider="zai", hitl_enabled=False)

    try:
        result = prover.prove_sorry(demo, max_iterations=max_iters,
                                    agent_timeout_s=120)
        print(f"\nRESULT: {json.dumps(result, indent=2)}", flush=True)
    except Exception as e:
        print(f"\nCRASH: {e}", flush=True)
        traceback.print_exc()

    trace.save(demo["name"])
    print("Done.", flush=True)
