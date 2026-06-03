"""Quick sub-classifier of QC notebooks: QUANTBOOK_REAL / QUANTBOOK_SHALLOW
/ QUANTBOOK_STUB / QUANTBOOK_REFERENCE / LOCAL_PY / OTHER.

Helps re-align T17 dispatch — four QC sub-buckets matter:
  - REFERENCE = self-marked non-executable ([REFERENCE QC] in markdown)
  - STUB      = default QC template research.ipynb (<=2 cells, "QuantBook Analysis Tool" header,
                qb=QuantBook(); add_equity("SPY"); history; one indicator demo). MUST be
                TRANSFORMED into a real research notebook tied to its main.py algo, not just executed.
  - SHALLOW   = pseudo-research (<=5 code cells AND <=3000 source chars), often narrative
                "expected results" with placeholder prints — needs transformation, not execution.
  - REAL      = actual research with custom logic, ready to execute via Docker recipe
"""
import json
from pathlib import Path
import collections


STUB_MARKERS = (
    "quantbook analysis tool",
    "for more information see",
)


def _is_quantbook(sources_lower: str) -> bool:
    return (
        "quantbook()" in sources_lower
        or "qb = quantbook" in sources_lower
        or "qcalgorithm" in sources_lower
        or "from algorithmimports" in sources_lower
    )


def _is_reference(nb) -> bool:
    md_blob = " ".join(
        "".join(c.get("source", "")).lower()
        for c in nb["cells"]
        if c["cell_type"] == "markdown"
    )
    return "[reference qc]" in md_blob or "document de reference" in md_blob


def _is_stub(code_cells, sources_concat: str) -> bool:
    if len(code_cells) > 2:
        return False
    total_chars = sum(len("".join(c.get("source", "")).strip()) for c in code_cells)
    if total_chars > 600:
        return False
    sl = sources_concat.lower()
    if any(m in sl for m in STUB_MARKERS):
        return True
    has_qb_init = "qb = quantbook()" in sl
    has_spy_or_aapl = 'add_equity("spy"' in sl or "add_equity('spy'" in sl or 'add_equity("aapl"' in sl
    has_demo_history = "qb.history(" in sl
    return has_qb_init and (has_spy_or_aapl or has_demo_history) and total_chars < 400


def _is_shallow(code_cells) -> bool:
    if len(code_cells) > 5:
        return False
    total = sum(len("".join(c.get("source", "")).strip()) for c in code_cells)
    return total <= 3000


def classify(nb):
    code = [c for c in nb["cells"] if c["cell_type"] == "code"]
    if not code:
        return "NO_CODE"
    sources = " | ".join("".join(c.get("source", "")) for c in code)
    sources_lower = sources.lower()
    if _is_quantbook(sources_lower):
        if _is_reference(nb):
            return "QUANTBOOK_REFERENCE"
        if _is_stub(code, sources):
            return "QUANTBOOK_STUB"
        if _is_shallow(code):
            return "QUANTBOOK_SHALLOW"
        return "QUANTBOOK_REAL"
    if (
        "yfinance" in sources_lower
        or "pandas_datareader" in sources_lower
        or "binance.client" in sources_lower
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
