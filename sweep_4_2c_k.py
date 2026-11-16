#!/usr/bin/env python3
"""Sweep 4.2[c-k] obsoletes in 04-Vision + cross-refs 03-DeepLearning.

Mapping (longest-first to avoid collision 4.2i/4.2j):
  4.2k -> 4.6b
  4.2j -> 4.5d
  4.2i -> 4.6
  4.2h -> 4.5c
  4.2g -> 4.5b
  4.2f -> 4.5
  4.2e -> 4.4c
  4.2d -> 4.4b
  4.2c -> 4.4

Replacements only in markdown cell source. Code cells and outputs preserved byte-identical.
nbformat.write preserves the JSON compact form.
"""
import re
import sys
import nbformat
from pathlib import Path

# Mapping (longest-first to avoid 4.2i/4.2j collision)
MAPPING = [
    (r"\b4\.2k\b", "4.6b"),
    (r"\b4\.2j\b", "4.5d"),
    (r"\b4\.2i\b", "4.6"),
    (r"\b4\.2h\b", "4.5c"),
    (r"\b4\.2g\b", "4.5b"),
    (r"\b4\.2f\b", "4.5"),
    (r"\b4\.2e\b", "4.4c"),
    (r"\b4\.2d\b", "4.4b"),
    (r"\b4\.2c\b", "4.4"),
]

# Files to sweep
NOTEBOOKS = [
    "MyIA.AI.Notebooks/ML/DataScienceWithAgents/04-Vision/4.4b-Detection-AnchorFree-From-Scratch.ipynb",
    "MyIA.AI.Notebooks/ML/DataScienceWithAgents/04-Vision/4.5b-Detection-SOTA-Ultralytics.ipynb",
    "MyIA.AI.Notebooks/ML/DataScienceWithAgents/04-Vision/4.5d-Detection-SOTA-LibreYOLO.ipynb",
    "MyIA.AI.Notebooks/ML/DataScienceWithAgents/04-Vision/4.6-Detection-Ultralytics-Difficult-Scenes.ipynb",
    "MyIA.AI.Notebooks/ML/DataScienceWithAgents/04-Vision/4.5c-YOLOv5-Bench-Ultralytics.ipynb",
    "MyIA.AI.Notebooks/ML/DataScienceWithAgents/04-Vision/4.5-Detection-SOTA-Torchvision.ipynb",
    "MyIA.AI.Notebooks/ML/DataScienceWithAgents/04-Vision/4.6b-Detection-Adversarial-Camouflage.ipynb",
    "MyIA.AI.Notebooks/ML/DataScienceWithAgents/04-Vision/4.4c-Detection-FocalLoss-From-Scratch.ipynb",
    "MyIA.AI.Notebooks/ML/DataScienceWithAgents/04-Vision/4.4-Detection-Anchor-From-Scratch.ipynb",
    "MyIA.AI.Notebooks/ML/DataScienceWithAgents/03-DeepLearning/3.4c-MoE-from-scratch.ipynb",
    "MyIA.AI.Notebooks/ML/DataScienceWithAgents/03-DeepLearning/3.6-Modeles-Generatifs.ipynb",
    "MyIA.AI.Notebooks/ML/DataScienceWithAgents/03-DeepLearning/3.6d-Modeles-Generatifs-Score-SDE-from-scratch.ipynb",
]

TEXT_FILES = [
    "MyIA.AI.Notebooks/ML/DataScienceWithAgents/04-Vision/requirements.txt",
    "MyIA.AI.Notebooks/ML/DataScienceWithAgents/04-Vision/README.md",
]


def sweep_notebook(path: Path) -> tuple[int, int]:
    """Sweep a notebook. Returns (md_subs, code_subs_skipped)."""
    nb = nbformat.read(path, as_version=4)
    md_subs = 0
    code_subs_skipped = 0
    for cell in nb.cells:
        src = cell.source
        if cell.cell_type == "markdown":
            new_src = src
            for pat, repl in MAPPING:
                new_src, n = re.subn(pat, repl, new_src)
                md_subs += n
            if new_src != src:
                cell.source = new_src
        elif cell.cell_type == "code":
            for pat, repl in MAPPING:
                matches = re.findall(pat, src)
                code_subs_skipped += len(matches)
    if md_subs > 0:
        nbformat.write(nb, path)
    return md_subs, code_subs_skipped


def sweep_text(path: Path) -> int:
    """Sweep a text file. Returns substitutions made."""
    content = path.read_text(encoding="utf-8")
    new_content = content
    total = 0
    for pat, repl in MAPPING:
        new_content, n = re.subn(pat, repl, new_content)
        total += n
    if total > 0:
        path.write_text(new_content, encoding="utf-8", newline="\n")  # LF
    return total


def main():
    root = Path(".").resolve()
    total_md = 0
    total_code = 0
    total_text = 0
    for rel in NOTEBOOKS:
        path = root / rel
        if not path.exists():
            print(f"  MISSING: {rel}")
            continue
        md, code = sweep_notebook(path)
        total_md += md
        total_code += code
        if md > 0:
            print(f"  {rel}: {md} md subs, {code} code matches left untouched")
    for rel in TEXT_FILES:
        path = root / rel
        if not path.exists():
            print(f"  MISSING: {rel}")
            continue
        n = sweep_text(path)
        total_text += n
        if n > 0:
            print(f"  {rel}: {n} text subs")
    print(f"\nTOTAL: {total_md} md subs + {total_text} text subs = {total_md + total_text} substitutions")
    print(f"SKIPPED: {total_code} code matches left untouched (per C.2 byte-identity)")


if __name__ == "__main__":
    main()
