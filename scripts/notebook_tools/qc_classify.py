"""Quick sub-classifier of QC notebooks: QUANTBOOK / LOCAL_PY / ALGORITHM / OTHER.

Helps re-align T17 dispatch — many notebooks under QuantConnect/projects/ are local
Python research (yfinance) and don't need QC Cloud at all.
"""
import json
from pathlib import Path
import collections


def classify(nb):
    code = [c for c in nb["cells"] if c["cell_type"] == "code"]
    if not code:
        return "NO_CODE"
    sources = " | ".join("".join(c.get("source", "")).lower() for c in code)
    if (
        "quantbook()" in sources
        or "qb = quantbook" in sources
        or "qcalgorithm" in sources
        or "from algorithmimports" in sources
    ):
        return "QUANTBOOK"
    if (
        "yfinance" in sources
        or "pandas_datareader" in sources
        or "binance.client" in sources
    ):
        return "LOCAL_PY"
    return "OTHER"


def category(nb):
    code = [c for c in nb["cells"] if c["cell_type"] == "code"]
    if not code:
        return "NO_CODE"
    n_exec = sum(1 for c in code if c.get("execution_count") is not None)
    n_err = sum(
        1
        for c in code
        if any(o.get("output_type") == "error" for o in c.get("outputs", []))
    )
    if n_err > 0:
        return "D"
    if n_exec == 0:
        return "C"
    if n_exec == len(code):
        return "A"
    return "B"


def main():
    root = Path("MyIA.AI.Notebooks/QuantConnect")
    results = collections.defaultdict(list)

    for nb_path in sorted(root.rglob("*.ipynb")):
        if any(
            p.startswith("_") or p.lower() in ("trashbin", ".ipynb_checkpoints", "node_modules")
            for p in nb_path.parts
        ):
            continue
        try:
            with open(nb_path, encoding="utf-8") as f:
                nb = json.load(f)
        except (json.JSONDecodeError, OSError):
            continue
        c = category(nb)
        cls = classify(nb)
        rel = str(nb_path.relative_to(root)).replace("\\", "/")
        results[c].append((cls, rel))

    print("=== QC notebooks by category x classification ===")
    for c in ["A", "B", "C", "D", "NO_CODE"]:
        items = results[c]
        if not items:
            continue
        by_cls = collections.Counter(cls for cls, _ in items)
        print(f"\n  Cat {c} (total {len(items)}):")
        for cls, n in by_cls.most_common():
            print(f"    {cls:12s} {n}")
            if c in ("C", "D") and n <= 25:
                for ccls, p in items:
                    if ccls == cls:
                        print(f"        {p}")


if __name__ == "__main__":
    main()
