"""One-shot fix: swap `breakdown: projects=48, Python=48` → `breakdown: Python=48, projects=48`
in MyIA.AI.Notebooks/QuantConnect/README.md, preserving CRLF/LF unchanged.

Used to unblock UNSTABLE PRs whose CI fails on `Notebook catalog drift` due to
non-deterministic Counter.most_common() tie-break (Windows vs Linux sort order).

Usage: python scripts/notebook_tools/fix_catalog_drift.py
"""
from pathlib import Path

OLD = b"breakdown: projects=48, Python=48, ML-Training-Pipeline=1"
NEW = b"breakdown: Python=48, projects=48, ML-Training-Pipeline=1"

p = Path("MyIA.AI.Notebooks/QuantConnect/README.md")
data = p.read_bytes()
if OLD in data:
    p.write_bytes(data.replace(OLD, NEW, 1))
    print(f"OK patched {p}")
elif NEW in data:
    print(f"already-fixed {p}")
else:
    raise SystemExit(f"FAIL pattern not found in {p}")
