#!/usr/bin/env python3
"""Vérifie les motifs contents des listings Quarto suivis par Git.

Les chemins sont résolus depuis le répertoire du document. Les formes prises
 en charge sont les chaînes et listes de chaînes positives ; toute autre forme
 est signalée pour éviter de déclarer une couverture inexistante.
"""
from __future__ import annotations

import glob
import subprocess
import sys
from pathlib import Path

import yaml


def check_document(path: Path) -> list[str]:
    """Retourne les erreurs de motifs pour un document à front matter YAML."""
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    if not lines or lines[0].strip() != "---":
        return []
    try:
        end = lines.index("---", 1)
    except ValueError:
        return []
    front = "\n".join(lines[1:end])
    if not any(line.startswith("listing:") for line in lines[1:end]):
        return []
    try:
        metadata = yaml.safe_load(front)
    except yaml.YAMLError as exc:
        return [f"{path}: YAML invalide : {exc}"]
    listings = metadata.get("listing")
    if isinstance(listings, dict):
        listings = [listings]
    if not isinstance(listings, list):
        return [f"{path}: listing non pris en charge"]
    errors = []
    for listing in listings:
        if not isinstance(listing, dict):
            errors.append(f"{path}: entrée listing non prise en charge")
            continue
        name = listing.get("id", "sans id")
        contents = listing.get("contents")
        patterns = [contents] if isinstance(contents, str) else contents
        if not isinstance(patterns, list) or not patterns:
            errors.append(f"{path}: listing {name}: contents non pris en charge")
            continue
        for pattern in patterns:
            if not isinstance(pattern, str) or not pattern or pattern.startswith("!"):
                errors.append(f"{path}: listing {name}: motif non pris en charge : {pattern!r}")
            elif not any(Path(p).is_file() for p in glob.iglob(str(path.parent / pattern), recursive=True)):
                errors.append(f"{path}: listing {name}: aucun fichier pour {pattern!r}")
    return errors


def main() -> int:
    files = subprocess.check_output(
        ["git", "ls-files", "-z", "--", "*.qmd", "*.md"]
    ).decode("utf-8").split("\0")
    errors = []
    for name in filter(None, files):
        errors.extend(check_document(Path(name)))
    for error in errors:
        print(error, file=sys.stderr)
    print(f"Listings Quarto : {len(errors)} erreur(s)")
    return bool(errors)


if __name__ == "__main__":
    sys.exit(main())
