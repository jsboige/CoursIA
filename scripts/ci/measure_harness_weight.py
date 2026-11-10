#!/usr/bin/env python3
"""Mesure du poids du harnais auto-charge par session (issue #15204).

Rend le total auto-charge en octets ET en tokens (ratio calibre 2,25 o/token
sur MEMORY.md, mesure ai-01 du 2026-09-08), avec le detail par fichier.

Surfaces mesurees (celles de la mesure fondatrice de #15204) :
  - `.claude/rules/*.md` SANS frontmatter `paths:` (auto-chargees) ;
  - `CLAUDE.md` a la racine du depot ;
  - `~/.claude/CLAUDE.md` (global machine) ;
  - `MEMORY.md` de la machine pour CE depot (auto-detecte via
    `git rev-parse --git-common-dir`, robuste depuis un worktree).

Cible : < 157 500 o (~70k tokens). Par defaut informatif (exit 0) ;
`--check` sort 1 si la cible est depassee (gate). `--json` pour la machine.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

# Ratio calibre sur MEMORY.md (24 705 o -> 11,1k tokens), #15204.
BYTES_PER_TOKEN = 2.25
# Cible du mandat user : < 70k tokens au ratio calibre.
TARGET_BYTES = 157_500
TARGET_TOKENS = 70_000


def repo_root() -> Path:
    """Racine du depot (tolere un worktree : la regle est portee par le repo)."""
    out = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        capture_output=True, check=True,
        encoding="utf-8", errors="replace",
    ).stdout.strip()
    return Path(out).resolve()


def has_paths_gate(rule: Path) -> bool:
    """Vrai si la rule porte un frontmatter `paths:` (non auto-chargee)."""
    try:
        text = rule.read_text(encoding="utf-8")
    except OSError:
        return False
    if not text.startswith("---"):
        return False
    match = re.match(r"^---\s*\n(.*?)\n---\s*\n", text, re.DOTALL)
    if not match:
        return False
    return re.search(r"^paths\s*:", match.group(1), re.MULTILINE) is not None


def memory_slug_candidates(main_checkout: Path) -> list[str]:
    """Slugs candidats du chemin du checkout principal (convention projets/).

    `D:\\dev\\CoursIA` -> `d--dev-CoursIA` (separateurs et `:` en `-`).
    """
    raw = str(main_checkout)
    # Chaque separateur (`:` de lecteur, `\`, `/`) vaut UN tiret : ne pas
    # collapser -- `D:\dev\CoursIA` -> `D--dev-CoursIA`, pas `D-dev-CoursIA`.
    slug = re.sub(r"[^0-9A-Za-z]", "-", raw)
    cands = [slug]
    if len(slug) > 1 and slug[0].isupper():
        cands.append(slug[0].lower() + slug[1:])
    return cands


def find_memory_md(main_checkout: Path) -> Path | None:
    """MEMORY.md de la machine pour ce depot ; None si introuvable (fail-open)."""
    base = Path.home() / ".claude" / "projects"
    for slug in memory_slug_candidates(main_checkout):
        candidate = base / slug / "memory" / "MEMORY.md"
        if candidate.is_file():
            return candidate
    return None


def collect(root: Path) -> list[dict[str, object]]:
    """Une entree par surface auto-chargee, triee par poids decroissant."""
    entries: list[dict[str, object]] = []

    rules_dir = root / ".claude" / "rules"
    if rules_dir.is_dir():
        for rule in sorted(rules_dir.glob("*.md")):
            if not has_paths_gate(rule):
                entries.append({"surface": "rule", "path": str(rule.relative_to(root)), "bytes": rule.stat().st_size})

    for surface, path in (
        ("project", root / "CLAUDE.md"),
        ("global", Path.home() / ".claude" / "CLAUDE.md"),
    ):
        if path.is_file():
            entries.append({
                "surface": surface,
                "path": str(path),
                "bytes": path.stat().st_size,
            })

    # Racine du checkout principal (pas du worktree courant).
    common = subprocess.run(
        ["git", "rev-parse", "--git-common-dir"],
        capture_output=True, check=True, cwd=root,
        encoding="utf-8", errors="replace",
    ).stdout.strip()
    main_checkout = Path(common).resolve().parent
    memory = find_memory_md(main_checkout)
    if memory is not None:
        entries.append({"surface": "memory", "path": str(memory), "bytes": memory.stat().st_size})

    for entry in entries:
        entry["tokens"] = round(entry["bytes"] / BYTES_PER_TOKEN)  # type: ignore[index]
    entries.sort(key=lambda e: e["bytes"], reverse=True)  # type: ignore[arg-type,return-value]
    return entries


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true",
                        help="sort 1 si le total auto-charge depasse la cible (gate)")
    parser.add_argument("--json", action="store_true", dest="as_json",
                        help="sortie machine (JSON)")
    args = parser.parse_args()

    entries = collect(repo_root())
    total_bytes = sum(e["bytes"] for e in entries)  # type: ignore[misc]
    total_tokens = round(total_bytes / BYTES_PER_TOKEN)
    over = total_bytes >= TARGET_BYTES

    if args.as_json:
        print(json.dumps({
            "bytes_per_token": BYTES_PER_TOKEN,
            "target_bytes": TARGET_BYTES,
            "target_tokens": TARGET_TOKENS,
            "total_bytes": total_bytes,
            "total_tokens": total_tokens,
            "over_target": over,
            "files": entries,
        }, ensure_ascii=False, indent=2))
    else:
        print(f"{'surface':<8} {'octets':>9} {'~tokens':>9}  chemin")
        print("-" * 100)
        for e in entries:
            print(f"{e['surface']:<8} {e['bytes']:>9} {e['tokens']:>9}  {e['path']}")  # type: ignore[index]
        print("-" * 100)
        print(f"TOTAL auto-charge : {total_bytes} octets ~ {total_tokens} tokens "
              f"(cible < {TARGET_BYTES} o / {TARGET_TOKENS} tok)")
        print("VERDICT: OVER" if over else "VERDICT: UNDER")

    if args.check and over:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
