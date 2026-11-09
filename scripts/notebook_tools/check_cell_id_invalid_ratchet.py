#!/usr/bin/env python3
"""Bloque toute hausse des identifiants de cellule invalides par carnet."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

ID_RE = re.compile(r"^[A-Za-z0-9_-]{1,64}$")


def invalid_count(text: str) -> int | None:
    """Compte les défauts d'id; None signifie que le format ne les exige pas."""
    doc = json.loads(text)
    version = (doc.get("nbformat", 0), doc.get("nbformat_minor", 0))
    if version < (4, 5):
        return None
    cells = doc.get("cells")
    if not isinstance(cells, list):
        raise ValueError("propriété cells absente ou invalide")
    count = 0
    seen: set[str] = set()
    for cell in cells:
        value = cell.get("id") if isinstance(cell, dict) else None
        if not isinstance(value, str) or not ID_RE.fullmatch(value):
            count += 1
        elif value in seen:
            count += 1
        else:
            seen.add(value)
    return count


def changed_notebooks(base: str) -> list[str]:
    result = subprocess.run(
        ["git", "diff", "--name-only", "--diff-filter=ACMR", f"{base}...HEAD", "--", "*.ipynb"],
        capture_output=True, text=True, encoding="utf-8",
    )
    if result.returncode:
        raise RuntimeError(result.stderr.strip())
    return result.stdout.splitlines()


def compare(base_count: int | None, head_count: int | None) -> bool:
    """Autorise les carnets legacy inchangés, jamais un downgrade depuis 4.5+."""
    if base_count is None:
        return head_count is None or head_count == 0
    if head_count is None:
        return False
    return head_count <= base_count


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("base", help="ref de base de la PR, par exemple origin/main")
    args = parser.parse_args(argv)
    try:
        paths = changed_notebooks(args.base)
        failures = []
        print("Ratchet des ids de cellules (comptes par carnet)")
        for path in paths:
            base_blob = subprocess.run(
                ["git", "show", f"{args.base}:{path}"], capture_output=True,
                text=True, encoding="utf-8",
            )
            base_count = invalid_count(base_blob.stdout) if base_blob.returncode == 0 else 0
            head_count = invalid_count(Path(path).read_text(encoding="utf-8"))
            state = "OK" if compare(base_count, head_count) else "ÉCHEC"
            print(f"{state} {path}: {base_count} -> {head_count}")
            if not compare(base_count, head_count):
                failures.append(path)
        if failures:
            print("Hausse d'identifiants invalides détectée:", file=sys.stderr)
            for path in failures:
                print(f"  {path}", file=sys.stderr)
            return 1
        print(f"Aucune hausse sur {len(paths)} carnet(s) modifié(s).")
        return 0
    except (OSError, ValueError, RuntimeError) as exc:
        print(f"Erreur: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
