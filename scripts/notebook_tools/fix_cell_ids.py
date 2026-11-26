#!/usr/bin/env python3
"""Répare les identifiants nbformat sans réécrire le JSON du carnet."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ID_RE = re.compile(r"^[A-Za-z0-9_-]{1,64}$")
DECODER = json.JSONDecoder()


def _space(text: str, pos: int) -> int:
    while pos < len(text) and text[pos] in " \t\r\n":
        pos += 1
    return pos


def _members(text: str, start: int) -> dict[str, tuple[int, int]]:
    """Offsets des valeurs des propriétés directes d'un objet JSON."""
    pos = _space(text, start + 1)
    result = {}
    while pos < len(text) and text[pos] != "}":
        key, end = DECODER.raw_decode(text, pos)
        if not isinstance(key, str):
            raise ValueError("clé JSON non textuelle")
        pos = _space(text, end)
        if text[pos] != ":":
            raise ValueError("objet JSON mal formé")
        value_start = _space(text, pos + 1)
        _, value_end = DECODER.raw_decode(text, value_start)
        result[key] = (value_start, value_end)
        pos = _space(text, value_end)
        if text[pos] == ",":
            pos = _space(text, pos + 1)
        elif text[pos] != "}":
            raise ValueError("objet JSON mal formé")
    return result


def _cell_ranges(text: str) -> list[tuple[int, int]]:
    root = json.loads(text)
    if not isinstance(root, dict) or not isinstance(root.get("cells"), list):
        raise ValueError("carnet sans tableau cells")
    # Les offsets viennent des propriétés directes de l'objet racine. Une
    # métadonnée imbriquée peut elle aussi s'appeler "cells".
    root_start = _space(text, 0)
    members = _members(text, root_start)
    cells_span = members.get("cells")
    if not cells_span:
        raise ValueError("propriété cells introuvable")
    pos = cells_span[0]
    if text[pos] != "[":
        raise ValueError("cells n'est pas un tableau")
    pos += 1
    ranges = []
    while True:
        pos = _space(text, pos)
        if text[pos] == "]":
            break
        start = pos
        _, end = DECODER.raw_decode(text, start)
        if text[start] != "{":
            raise ValueError("une cellule n'est pas un objet")
        ranges.append((start, end))
        pos = _space(text, end)
        if text[pos] == ",":
            pos += 1
    if len(ranges) != len(root["cells"]):
        raise ValueError("nombre de cellules incohérent")
    return ranges


def _external_references(cell_id: str, notebook: Path) -> list[str]:
    root_result = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"], capture_output=True,
        text=True, encoding="utf-8",
    )
    if root_result.returncode:
        raise RuntimeError(root_result.stderr.strip() or "racine git introuvable")
    root = Path(root_result.stdout.strip()).resolve()
    try:
        notebook_relative = notebook.resolve().relative_to(root).as_posix()
    except ValueError:
        notebook_relative = None
    result = subprocess.run(
        ["git", "grep", "-n", "-F", "--", cell_id],
        capture_output=True, text=True, encoding="utf-8", cwd=root,
    )
    if result.returncode not in (0, 1):
        raise RuntimeError(result.stderr.strip() or "git grep a échoué")
    return [line for line in result.stdout.splitlines()
            if notebook_relative is None or line.split(":", 1)[0] != notebook_relative]


def repair_text(text: str, path: Path) -> str:
    document = json.loads(text)
    cells = document["cells"]
    ranges = _cell_ranges(text)
    ids = [cell.get("id") for cell in cells]
    seen: set[str] = set()
    reserved = {value for value in ids if isinstance(value, str) and ID_RE.fullmatch(value)}
    edits: list[tuple[int, int, str]] = []

    def fresh(index: int, old: object) -> str:
        counter = 0
        while True:
            material = f"{path.as_posix()}\0{index}\0{old!r}\0{counter}".encode()
            candidate = hashlib.sha256(material).hexdigest()[:8]
            if candidate not in reserved and candidate not in seen:
                seen.add(candidate)
                return candidate
            counter += 1

    for index, (cell, (start, end)) in enumerate(zip(cells, ranges)):
        value = cell.get("id")
        valid = isinstance(value, str) and bool(ID_RE.fullmatch(value))
        duplicate = valid and value in seen
        if valid and not duplicate:
            seen.add(value)
            continue
        if isinstance(value, str) and value:
            refs = _external_references(value, path)
            if refs:
                raise ValueError(
                    f"id existant {value!r} référencé hors du carnet; réparation refusée: "
                    + "; ".join(refs[:5])
                )
        new_id = fresh(index, value)
        members = _members(text, start)
        encoded = json.dumps(new_id, ensure_ascii=False)
        if "id" in members:
            value_start, value_end = members["id"]
            edits.append((value_start, value_end, encoded))
        else:
            cell_type = members.get("cell_type")
            if cell_type is None:
                raise ValueError(f"cellule {index}: propriété cell_type absente")
            key_start = text.rfind('"cell_type"', start, cell_type[0])
            line_start = text.rfind("\n", start, key_start) + 1
            newline = "\r\n" if "\r\n" in text else "\n"
            if "\n" not in text[start:key_start] and "\r" not in text[start:key_start]:
                # JSON compact : insérer inline juste après l'accolade de cellule.
                edits.append((start + 1, start + 1, f'"id": {encoded},'))
            else:
                indent = text[line_start:key_start]
                edits.append((line_start, line_start, f'{indent}"id": {encoded},{newline}'))

    for start, end, replacement in reversed(edits):
        text = text[:start] + replacement + text[end:]
    # Vérifier le résultat brut sans que nbformat ne répare rien en mémoire.
    checked = json.loads(text)
    check_ids = [cell.get("id") for cell in checked["cells"]]
    if any(not isinstance(value, str) or not ID_RE.fullmatch(value) for value in check_ids):
        raise AssertionError("la réparation a laissé un id invalide")
    if len(check_ids) != len(set(check_ids)):
        raise AssertionError("la réparation a laissé un doublon")
    return text


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("notebooks", nargs="+", type=Path)
    args = parser.parse_args(argv)
    try:
        for path in args.notebooks:
            with path.open("r", encoding="utf-8", newline="") as handle:
                original = handle.read()
            fixed = repair_text(original, path)
            if fixed != original:
                with path.open("w", encoding="utf-8", newline="") as handle:
                    handle.write(fixed)
                print(f"{path}: ids réparés")
            else:
                print(f"{path}: aucun changement")
    except (OSError, ValueError, RuntimeError) as exc:
        print(f"Erreur: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
