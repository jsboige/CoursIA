"""c.8259 verifier: post-reorder invariants for App-8-MiniZinc-Csharp.ipynb."""
import json

NB_PATH = r"MyIA.AI.Notebooks/Search/Applications/CSP/App-8-MiniZinc-Csharp.ipynb"
BEFORE = r"C:\Users\jsboi\c8259_minizinc_before.json"

nb_before = json.load(open(BEFORE, encoding="utf-8"))
nb_after = json.load(open(NB_PATH, encoding="utf-8"))

# Multiset equality on (source, cell_type)
before_set = sorted(("".join(c["source"]), c["cell_type"]) for c in nb_before["cells"])
after_set = sorted(("".join(c["source"]), c["cell_type"]) for c in nb_after["cells"])
print(f"Multiset equality (source, type): {before_set == after_set}")
print(f"Before: {len(before_set)} cells, After: {len(after_set)} cells")

# IDs (filter None for sort)
ids_before = sorted([c.get("id") for c in nb_before["cells"] if c.get("id")])
ids_after = sorted([c.get("id") for c in nb_after["cells"] if c.get("id")])
print(f"IDs multiset (excluding None): {ids_before == ids_after}")

# Outputs preserved
out_before = sorted(repr(c.get("outputs")) for c in nb_before["cells"])
out_after = sorted(repr(c.get("outputs")) for c in nb_after["cells"])
print(f"Outputs multiset: {out_before == out_after}")

# Exec count preserved (handle None)
def safe_exec(c):
    v = c.get("execution_count")
    return v if v is not None else -1
ec_before = sorted([safe_exec(c) for c in nb_before["cells"]])
ec_after = sorted([safe_exec(c) for c in nb_after["cells"]])
print(f"Exec count multiset: {ec_before == ec_after}")

# CRLF check
raw_after = open(NB_PATH, "rb").read()
crlf = raw_after.count(b"\r\n")
cr_only = raw_after.count(b"\r") - crlf
lf = raw_after.count(b"\n")
print(f"CRLF: {crlf}, CR alone: {cr_only}, LF only: {lf}")

print(f"nbformat: {nb_after['nbformat']}.{nb_after['nbformat_minor']}")
