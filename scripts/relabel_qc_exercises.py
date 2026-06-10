#!/usr/bin/env python3
"""Relabel exercise headers in QuantConnect notebooks to ascending order.

Same approach as relabel_exercises.py but for QC notebooks.

Usage:
    python scripts/relabel_qc_exercises.py --dry-run
    python scripts/relabel_qc_exercises.py
    python scripts/relabel_qc_exercises.py --verify
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# Only truly scrambled notebooks (excluding per-section duplicates [1,1,2,2,3,3])
RELABEL_MAP = {
    "MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-28-Market-Regime-Detection.ipynb": [
        (7, 3, 1), (11, 1, 3), (16, 3, 4), (24, 2, 5), (32, 1, 6),
    ],
    "MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-35-RL-Portfolio-Construction.ipynb": [
        (6, 2, 1), (8, 1, 2), (14, 2, 4),
    ],
    "MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-40-PaperTrading-Binance.ipynb": [
        (14, 3, 1), (17, 1, 2),
    ],
    "MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-02-SectorRotation-Momentum.ipynb": [
        (5, 2, 1), (8, 3, 2), (10, 1, 3),
    ],
    "MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-03-Risk-Parity.ipynb": [
        (6, 2, 1), (8, 1, 2),
    ],
    "MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-04-RL-DQN-Trading.ipynb": [
        (10, 3, 2), (12, 2, 3),
    ],
    "MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-07-TemporalCNN.ipynb": [
        (2, 2, 1), (4, 1, 2),
    ],
}

EXERCICE_PAT = re.compile(
    r"(###\s+(?:Exercice|Exemple\s+guide)\s+)\d+",
    re.IGNORECASE,
)


def _to_text(source) -> str:
    return source if isinstance(source, str) else "".join(source)


def get_exercice_num(cell_source) -> int | None:
    m = EXERCICE_PAT.search(_to_text(cell_source))
    return int(m.group(0).split()[-1]) if m else None


def _replace_in_source(source, old_n: int, new_n: int):
    ph = f"__RL_{new_n}__"
    prefixes = ["Exercice", "Exemple guide"]

    if isinstance(source, str):
        text = source
        for pf in prefixes:
            text = text.replace(f"{pf} {old_n}", f"{pf} {ph}")
        for pf in prefixes:
            text = text.replace(f"{pf} {ph}", f"{pf} {new_n}")
        return text
    else:
        result = []
        for line in source:
            for pf in prefixes:
                line = line.replace(f"{pf} {old_n}", f"{pf} {ph}")
            for pf in prefixes:
                line = line.replace(f"{pf} {ph}", f"{pf} {new_n}")
            result.append(line)
        return result


def audit_qc():
    qc_dir = Path("MyIA.AI.Notebooks/QuantConnect")
    all_nbs = sorted(qc_dir.glob("**/*.ipynb"))
    scrambled = 0

    for nb_path in all_nbs:
        with open(nb_path, encoding="utf-8") as f:
            nb = json.load(f)
        findings = []
        for i, cell in enumerate(nb["cells"]):
            if cell.get("cell_type") != "markdown":
                continue
            num = get_exercice_num(cell["source"])
            if num is not None:
                findings.append((i, num))
        if not findings:
            continue
        nums = [f[1] for f in findings]
        is_ok = nums == sorted(nums) and len(nums) == len(set(nums))
        status = "OK" if is_ok else f"SCRAMBLED {nums}"
        if not is_ok:
            scrambled += 1
        print(f"{'!!' if not is_ok else '  '} {nb_path.relative_to(REPO)}: {status}")

    print(f"\n{scrambled} scrambled QC notebooks total")


def relabel_notebook(nb_path: Path, cell_mappings: list[tuple], dry_run: bool) -> bool:
    with open(nb_path, "r", encoding="utf-8") as f:
        nb = json.load(f)

    changed = False
    for cell_idx, old_num, new_num in cell_mappings:
        if cell_idx >= len(nb["cells"]):
            print(f"  WARN: cell {cell_idx} OOB ({len(nb['cells'])} cells)")
            continue
        cell = nb["cells"][cell_idx]
        if cell.get("cell_type") != "markdown":
            print(f"  WARN: cell {cell_idx} not markdown")
            continue

        current = get_exercice_num(cell["source"])
        if current is None:
            print(f"  WARN: cell {cell_idx} no exercise label")
            continue
        if current == new_num:
            print(f"  cell {cell_idx}: already {new_num}, skip")
            continue

        tag = "[DRY-RUN]" if dry_run else "[APPLY]"
        old_t = _to_text(cell["source"])[:50].strip()
        new_src = _replace_in_source(cell["source"], old_num, new_num)
        new_t = _to_text(new_src)[:50].strip()
        print(f"  {tag} cell {cell_idx}: '{old_t}' -> '{new_t}'")

        if not dry_run:
            nb["cells"][cell_idx]["source"] = new_src
        changed = True

    if changed and not dry_run:
        with open(nb_path, "w", encoding="utf-8", newline="") as f:
            json.dump(nb, f, ensure_ascii=False, indent=1)
            f.write("\n")
    return changed


def main():
    args = set(sys.argv[1:])
    dry_run = "--dry-run" in args
    verify_only = "--verify" in args

    if verify_only:
        audit_qc()
        return

    mode = "DRY-RUN" if dry_run else "APPLYING"
    print(f"=== {mode} ===\n")

    total = 0
    for rel_path, cell_mappings in sorted(RELABEL_MAP.items()):
        nb_path = REPO / rel_path
        if not nb_path.exists():
            print(f"MISSING: {rel_path}")
            continue
        print(f"\n{rel_path}:")
        if relabel_notebook(nb_path, cell_mappings, dry_run):
            total += 1

    print(f"\n{total} notebook(s) {'would be ' if dry_run else ''}changed")


if __name__ == "__main__":
    main()
