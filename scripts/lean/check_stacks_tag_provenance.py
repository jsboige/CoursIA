#!/usr/bin/env python3
"""Vérifie les repères Stacks cités par le README de l'îlot GROTH.

Le contrôle parse l'extrait source Axiom épinglé, vérifie que chaque tag et
symbole cité y figure, puis vérifie que les symboles GROTH existent dans leurs
modules suivis. Pour les déclarations locales, il réutilise
``DECLARATION_RE`` de ``lean_material_map.py`` ; les ``def`` sont normalisés
vers la forme ``theorem`` reconnue par cet index, sans modifier son contrat.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

from lean_material_map import DECLARATION_RE


REPO_ROOT = Path(__file__).resolve().parents[2]
LAKE_ROOT = REPO_ROOT / "MyIA.AI.Notebooks/SymbolicAI/Lean/GROTH/grothendieck_lean"
README = REPO_ROOT / "MyIA.AI.Notebooks/SymbolicAI/Lean/GROTH/README.md"
FIXTURE = REPO_ROOT / "scripts/lean/fixtures/stacks_adjoint_tags_excerpt.txt"
UPSTREAM_ENTRY_RE = re.compile(
    r"^\s*add_to_stacks\s+(?P<tag>[A-Z0-9]{4})\s+"
    r"(?:\"[^\"]*\")?(?:\s+(?P<symbol>[A-Za-z][A-Za-z0-9_'.]*))?\s*$"
)
UPSTREAM_SYMBOL_RE = re.compile(r"^\s+(?P<symbol>[A-Za-z][A-Za-z0-9_'.]*)\s*$")
PIN_RE = re.compile(r"Commit:\s*([0-9a-f]{40})")
README_PIN_RE = re.compile(r"épinglée au commit\s+`([0-9a-f]{40})`", re.IGNORECASE)
ROW_RE = re.compile(r"^\|\s*(?P<tag>[A-Z0-9]{4})\s*\|(?P<body>.*)\|\s*$")


def parse_upstream_excerpt(text: str) -> tuple[dict[str, set[str]], str | None]:
    """Indexe les ``add_to_stacks`` littéraux par tag et extrait l'épingle."""
    index: dict[str, set[str]] = {}
    pending_tag: str | None = None
    for line in text.splitlines():
        match = UPSTREAM_ENTRY_RE.match(line)
        if match:
            symbol = match.group("symbol")
            if symbol:
                index.setdefault(match.group("tag"), set()).add(symbol)
                pending_tag = None
            else:
                pending_tag = match.group("tag")
            continue
        if pending_tag:
            continuation = UPSTREAM_SYMBOL_RE.match(line)
            if continuation:
                index.setdefault(pending_tag, set()).add(continuation.group("symbol"))
            pending_tag = None
    pin = PIN_RE.search(text)
    return index, pin.group(1) if pin else None


def _declared_names(source: str) -> set[str]:
    """Noms theorem/lemma/def selon le parseur de l'index Lean partagé."""
    names: set[str] = set()
    for line in source.splitlines():
        match = DECLARATION_RE.match(line)
        if match:
            names.add(match.group(1))
            continue
        normalized = re.sub(r"\bdef\b", "theorem", line, count=1)
        match = DECLARATION_RE.match(normalized)
        if match and normalized != line:
            names.add(match.group(1))
    return names


def _validate_provenance(readme_text: str, excerpt_text: str, lake_root: Path) -> tuple[list[str], set[str]]:
    """Retourne les écarts et les tags rencontrés dans les deux sources."""
    errors: list[str] = []
    upstream, fixture_pin = parse_upstream_excerpt(excerpt_text)
    readme_pin_match = README_PIN_RE.search(readme_text)
    readme_pin = readme_pin_match.group(1) if readme_pin_match else None
    if not fixture_pin:
        errors.append("l'extrait ne porte pas de commit source")
    if not readme_pin:
        errors.append("le README ne porte pas de commit source")
    elif fixture_pin and readme_pin != fixture_pin:
        errors.append("le commit du README diffère de celui de l'extrait")

    section_start = readme_text.find("## Deux repères de provenance Stacks")
    if section_start < 0:
        return errors + ["section de provenance absente du README GROTH"], set()
    section = readme_text[section_start:]
    rows = [m for line in section.splitlines() if (m := ROW_RE.match(line))]
    seen_tags: set[str] = set()
    witness_count = 0
    for row in rows:
        tag = row.group("tag")
        cells = [cell.strip() for cell in row.group("body").split("|")]
        if len(cells) < 3:
            errors.append(f"ligne {tag}: table incomplète")
            continue
        # Les symboles amont sont dans la deuxième cellule du tableau.
        upstream_symbols = [
            token for token in re.findall(r"`([^`]+)`", cells[0])
            if "." in token and not token.endswith(".lean")
        ]
        local_tokens = re.findall(r"`([^`]+)`", cells[1])
        local_links = re.findall(r"\[`([^`]+\.lean)`\]\(([^)]+)\)", cells[1])
        local_files = [label for label, _url in local_links]
        local_symbols = [token for token in local_tokens if not token.endswith(".lean")]
        if not upstream_symbols:
            errors.append(f"ligne {tag}: aucun symbole Axiom cité")
        for symbol in upstream_symbols:
            if symbol not in upstream.get(tag, set()):
                errors.append(f"ligne {tag}: {symbol} absent de l'extrait amont")
        if not local_files or not local_symbols:
            errors.append(f"ligne {tag}: fichier ou symbole GROTH absent")
            continue
        if tag not in upstream:
            errors.append(f"ligne {tag}: tag absent de l'extrait amont")
        else:
            seen_tags.add(tag)
        for relative_file in local_files:
            file_path = (lake_root / relative_file).resolve()
            if not file_path.is_relative_to(lake_root.resolve()) or not file_path.is_file():
                errors.append(f"ligne {tag}: module local introuvable: {relative_file}")
                continue
            link_target = (README.parent / dict(local_links)[relative_file]).resolve()
            if link_target != file_path:
                errors.append(f"ligne {tag}: lien local incorrect: {relative_file}")
            names = _declared_names(file_path.read_text(encoding="utf-8"))
            for symbol in local_symbols:
                if symbol not in names:
                    errors.append(f"ligne {tag}: déclaration locale introuvable: {relative_file}:{symbol}")
                    continue
                witness_count += 1
    if len(seen_tags) < 2:
        errors.append(f"au moins deux tags réels sont requis; trouvés: {sorted(seen_tags)}")
    if witness_count < 2:
        errors.append(f"au moins deux témoins locaux sont requis; trouvés: {witness_count}")
    if "Apache-2.0" not in section:
        errors.append("la licence de l'extrait n'est pas citée")
    return errors, seen_tags


def validate_provenance(readme_text: str, excerpt_text: str, lake_root: Path) -> list[str]:
    """Retourne les écarts entre le README, la source épinglée et le lake."""
    errors, _ = _validate_provenance(readme_text, excerpt_text, lake_root)
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--json", action="store_true", help="sortie JSON")
    parser.add_argument("--readme", type=Path, default=README)
    parser.add_argument("--excerpt", type=Path, default=FIXTURE)
    parser.add_argument("--lake", type=Path, default=LAKE_ROOT)
    args = parser.parse_args()
    errors, tags = _validate_provenance(
        args.readme.read_text(encoding="utf-8"),
        args.excerpt.read_text(encoding="utf-8"),
        args.lake,
    )
    result = {"ok": not errors, "tags": sorted(tags), "errors": errors}
    if args.json:
        print(json.dumps(result, ensure_ascii=False, indent=2))
    elif errors:
        print("Écarts de provenance Stacks :")
        for error in errors:
            print(f"- {error}")
    else:
        print(f"Provenance Stacks valide : tags {', '.join(sorted(tags))}.")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
