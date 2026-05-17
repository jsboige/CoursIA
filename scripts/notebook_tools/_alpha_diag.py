"""Diagnostic: pour un notebook, liste les cellules 'effective' sans output (celles qui le bloquent en ALPHA)."""
import ast, json, sys

def is_papermill_injected(cell):
    return "injected-parameters" in cell.get("metadata", {}).get("tags", [])

def is_outputless_by_design(cell):
    source = "".join(cell.get("source", []))
    if not source.strip():
        return True
    lines = [l.strip() for l in source.split("\n") if l.strip()]
    if all(l.startswith("#") for l in lines):
        return True
    try:
        tree = ast.parse(source)
        outputless = (ast.Assign, ast.AnnAssign, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
        return all(isinstance(node, outputless) for node in ast.iter_child_nodes(tree))
    except SyntaxError:
        return False

def count_todos(nb):
    c = 0
    for cell in nb.get("cells", []):
        if cell["cell_type"] == "code":
            c += "".join(cell.get("source", [])).upper().count("# TODO")
    return c

for path in sys.argv[1:]:
    nb = json.load(open(path, encoding="utf-8"))
    code = [c for c in nb["cells"] if c["cell_type"] == "code"]
    todos = count_todos(nb)
    print(f"\n=== {path}")
    print(f"todos={todos}  raw_code_cells={len(code)}")
    eff_noout = []
    for i, c in enumerate(nb["cells"]):
        if c["cell_type"] != "code":
            continue
        if is_papermill_injected(c) or is_outputless_by_design(c):
            continue
        if not c.get("outputs"):
            eff_noout.append(i)
    print(f"effective cells WITHOUT output (block ALPHA): {eff_noout}")
    for i in eff_noout:
        src = "".join(nb["cells"][i]["source"])
        print(f"  --- cell {i} (exec={nb['cells'][i].get('execution_count')}) ---")
        print("  " + src[:400].replace("\n", "\n  "))
