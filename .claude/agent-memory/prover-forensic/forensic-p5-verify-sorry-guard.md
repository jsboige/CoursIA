---
name: forensic-p5-verify-sorry-guard
description: Forensic P5 analysis of verify_sorry_replacement target-mismatch guard (2026-05-26)
metadata:
  type: project
---

## P5 verify_sorry_replacement Forensic (2026-05-26)

### Key Finding
P5 nearest-sorry relocation in `verify_sorry_replacement` (lean_utils.py:656-669) is **dead code in production** -- 0 triggers across 52 traces. The VerifyExecutor latch (workflow.py:724-802) catches the "target already proved" case before P5 is reached.

### Latent Bug in P5 Code
If ever triggered, P5 has 3 bugs: (1) no target-validation (relocates to ANY sorry), (2) global unbounded search (comment says +-20 but code scans all lines), (3) stale indentation from original line. Severity: WARNING (not yet triggered, but would be CRITICAL if triggered on multi-sorry files like Lattice.lean with 4 sorries).

### LOST_PROGRESS Pattern (3 cases, ~4,416s)
`best_sorry < original` but `final == original` -- agent found proof but build-check reverted. The `best_content` snapshot only updates on build_check=True+pass. Key cases: GALESHAPLEY_MAN_OPTIMAL (best=0, final=1, 3462s), LATTICE_MEET_ANTI_COMPL (best=1, final=3, 459s), Lattice_L145 (best=3, final=4, 495s).

### Macro-Signal
52 traces: 42% delta=0 (25.4h wall-clock), 58% successful (19.4h). No confirmed target-mismatch (wrong sorry replaced) in any trace.

### How to apply
- When reviewing P5 fixes, the code at lean_utils.py:656-669 needs bounded search + target validation
- LOST_PROGRESS suggests saving best_content on sorry decrease even without build pass
- The latch mechanism is multi-agent only -- autonomous path has no equivalent guard
