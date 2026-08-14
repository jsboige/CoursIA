"""c.8257 verifier: post-enrichment invariants for Lean-18-Search-AStar-Optimality.ipynb."""
import json
import sys
from pathlib import Path

NB_PATH = Path("MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-18-Search-AStar-Optimality.ipynb")
nb = json.loads(NB_PATH.read_text(encoding="utf-8"))

print(f"Total cells: {len(nb['cells'])}")
md_n = sum(1 for c in nb["cells"] if c["cell_type"] == "markdown")
code_n = sum(1 for c in nb["cells"] if c["cell_type"] == "code")
print(f"MD: {md_n}, Code: {code_n}")
md_chars = sum(len("".join(c["source"])) for c in nb["cells"] if c["cell_type"] == "markdown")
print(f"MD chars: {md_chars}, density: {md_chars/code_n:.0f} chars/code-cell")
ids = [c.get("id") for c in nb["cells"]]
print(f"Unique IDs: {len(set(ids))} (should={len(ids)})")
print(f"nbformat: {nb['nbformat']}.{nb['nbformat_minor']}")
raw = NB_PATH.read_bytes()
crlf = raw.count(b"\r\n")
cr_only = raw.count(b"\r") - crlf
lf = raw.count(b"\n")
print(f"CRLF: {crlf}, CR alone: {cr_only}, LF only: {lf}")
sys.exit(0 if (md_chars / code_n) >= 1200 else 1)
