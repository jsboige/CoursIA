"""One-shot fix: swap `breakdown: projects=48, Python=48` → `breakdown: Python=48, projects=48`
in MyIA.AI.Notebooks/QuantConnect/README.md, preserving CRLF/LF unchanged.

Historique : ecrit pour debloquer des PRs rendues UNSTABLE par le check
`Notebook catalog drift`, a l'epoque ou `PR gate` le comptait comme un check
requis. Ce check est **advisory** depuis #15998 -- un drift ne bloque plus
aucune PR, puisque le catalogue est regenere par catalog-cron.yml sur main
(#2632/#2744). Le script reste utile comme reparation locale d'un drift de
tie-break Counter.most_common() non deterministe (tri Windows vs Linux).

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
