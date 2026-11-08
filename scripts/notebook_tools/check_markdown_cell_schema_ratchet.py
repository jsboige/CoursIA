#!/usr/bin/env python3
"""Compare markdown-cell schema defects on changed notebooks (issue #24090)."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

from fix_markdown_cell_schema import find_defects

REPO_ROOT = Path(__file__).resolve().parents[2]


def defects_from_bytes(data: bytes, path: str) -> list:
    try:
        notebook = json.loads(data.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"JSON notebook illisible: {exc}") from exc
    if not isinstance(notebook, dict):
        raise ValueError("racine JSON non objet")
    return find_defects(notebook)


def git_blob(ref: str, path: str) -> bytes | None:
    proc = subprocess.run(
        ["git", "show", f"{ref}:{path}"], capture_output=True,
        cwd=REPO_ROOT,
    )
    if proc.returncode == 0:
        return proc.stdout
    listed = subprocess.run(
        ["git", "ls-tree", "-r", "--name-only", ref, "--", path],
        capture_output=True, cwd=REPO_ROOT,
    )
    if listed.returncode:
        raise RuntimeError(f"impossible de lire le chemin {path} dans {ref}")
    if not listed.stdout.strip():
        return None
    raise RuntimeError(f"blob illisible dans {ref}: {path}")


def check(base_ref: str, paths: list[str]) -> int:
    resolved = subprocess.run(
        ["git", "rev-parse", "--verify", f"{base_ref}^{{commit}}"],
        capture_output=True, cwd=REPO_ROOT,
    )
    if resolved.returncode:
        print(f"::error::base PR illisible: {base_ref}")
        return 2
    failed = False
    for path in paths:
        try:
            base_data = git_blob(base_ref, path)
        except RuntimeError as exc:
            print(f"::error file={path}::base {base_ref}: {exc}")
            return 2
        if base_data is None:
            base_defects = []
        else:
            try:
                base_defects = defects_from_bytes(base_data, path)
            except ValueError as exc:
                print(f"::error file={path}::base {base_ref}: {exc}")
                return 2
        try:
            head_data = (REPO_ROOT / path).read_bytes()
        except FileNotFoundError:
            # Un checkout sparse peut omettre un carnet encore present dans
            # HEAD. Seule l'absence dans l'arbre Git prouve une suppression.
            try:
                head_data = git_blob("HEAD", path)
            except RuntimeError as exc:
                print(f"::error file={path}::HEAD: {exc}")
                return 2
            if head_data is None:
                print(f"OK {path}: carnet supprime dans HEAD")
                continue
        except OSError as exc:
            print(f"::error file={path}::lecture HEAD: {exc}")
            return 2
        try:
            head_defects = defects_from_bytes(head_data, path)
        except (OSError, ValueError) as exc:
            print(f"::error file={path}::HEAD: {exc}")
            return 2

        increase = len(head_defects) - len(base_defects)
        if increase > 0:
            failed = True
            cells = ", ".join(f"{d.index} ({'/'.join(d.keys)})" for d in head_defects)
            print(
                f"::error file={path}::classe cellule markdown execution_count/outputs: "
                f"{len(base_defects)} -> {len(head_defects)}; cellules fautives: {cells}"
            )
        else:
            print(
                f"OK {path}: {len(base_defects)} -> {len(head_defects)} "
                "cellule(s) markdown fautive(s)"
            )
    return 1 if failed else 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base-ref", required=True)
    parser.add_argument("paths", nargs="+")
    args = parser.parse_args(argv)
    return check(args.base_ref, args.paths)


if __name__ == "__main__":
    sys.exit(main())
