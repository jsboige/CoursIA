#!/usr/bin/env python3
"""Relabel exercise headers in GenAI notebooks to ascending order.

Uses per-cell replacement in parsed JSON with json.dump roundtrip.
Preserves indent=1 formatting (Jupyter standard).

Usage:
    python scripts/relabel_exercises.py --dry-run   # preview changes
    python scripts/relabel_exercises.py             # apply changes
    python scripts/relabel_exercises.py --verify    # audit all GenAI
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# (cell_idx, current_num, target_num)
# NOTE: 11_Quantization excluded — per-section numbering (body [1,2,3] + practicals [1..5])
# is NOT scrambled, just separate exercise blocks within the same notebook.
RELABEL_MAP = {
    "MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/01-4-Whisper-Local.ipynb": [
        (16, 3, 1), (26, 4, 3),
    ],
    "MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/01-5-Kokoro-TTS-Local.ipynb": [
        (19, 3, 1),
    ],
    "MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-1-Chatterbox-TTS.ipynb": [
        (16, 3, 1),
    ],
    "MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-2-XTTS-Voice-Cloning.ipynb": [
        (16, 2, 1),
    ],
    "MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-4-Demucs-Source-Separation.ipynb": [
        (20, 3, 1),
    ],
    "MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-5-Multi-Model-TTS-Gateway.ipynb": [
        (10, 3, 1), (19, 1, 2), (26, 2, 3), (28, 3, 4), (30, 2, 5),
    ],
    "MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-6-MIDI-Generation.ipynb": [
        (22, 3, 1), (24, 4, 2), (32, 2, 3),
    ],
    "MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-7-Song-Generation.ipynb": [
        (20, 3, 1), (36, 1, 3),
    ],
    "MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-8-Expressive-TTS.ipynb": [
        (24, 3, 1), (41, 1, 3),
    ],
    "MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-9-AceStep-Music-Generation.ipynb": [
        (17, 3, 1), (30, 1, 3),
    ],
    "MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/notebooks/01-Claude-CLI-Bases.ipynb": [
        (26, 6, 1), (29, 5, 2),
    ],
    "MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/notebooks/05-Claude-CLI-Automatisation.ipynb": [
        (21, 6, 1), (33, 5, 3), (35, 3, 4), (37, 4, 5),
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
    """Replace exercise number in cell source using placeholder approach."""
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
        # list[str]
        result = []
        for line in source:
            for pf in prefixes:
                line = line.replace(f"{pf} {old_n}", f"{pf} {ph}")
            for pf in prefixes:
                line = line.replace(f"{pf} {ph}", f"{pf} {new_n}")
            result.append(line)
        return result


def audit_all():
    dirs = [
        Path("MyIA.AI.Notebooks/GenAI/Texte"),
        Path("MyIA.AI.Notebooks/GenAI/Audio/01-Foundation"),
        Path("MyIA.AI.Notebooks/GenAI/Audio/02-Advanced"),
        Path("MyIA.AI.Notebooks/GenAI/Vibe-Coding"),
    ]
    all_nbs = []
    for d in dirs:
        if d.exists():
            all_nbs.extend(sorted(d.glob("**/[0-9]*.ipynb")))

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
        print(f"{'!!' if not is_ok else '  '} {nb_path}: {status}")

    print(f"\n{scrambled} scrambled notebooks total")


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
        audit_all()
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
