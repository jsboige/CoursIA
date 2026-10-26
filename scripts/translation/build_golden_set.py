#!/usr/bin/env python3
"""Construit le golden set des paires FR/EN du depot (EPIC #1650, sequence 4).

Le golden set indexe les paires deja produites par le defrichissement manuel
et les rendus `_en` livres par le cluster : notebooks, README.en.md et
siblings Lean `_en`. Chaque paire porte des empreintes de contenu (sha1 sur
le fichier, sources seules pour les notebooks) pour etalonner la Phase 4 --
modele du registre twin-parity (#19118) : une paire est un fait mesure, pas
une declaration.

Sortie : translations/translation_golden_set.json
    pairs       : paires FR/EN avec empreintes des deux cotes
    orphans_en  : fichiers _en sans contrepartie FR visible (a trier)

Usage : python scripts/translation/build_golden_set.py [--check | --check-structure]
    --check : exit 1 si le JSON commite differe du JSON regenere (drift),
              empreintes comprises. Jambe ADVISORY de la garde (#22216) : la
              derive d'empreintes se signale, elle ne bloque pas.
    --check-structure : exit 1 seulement si les PAIRES (kind, fr, en) du JSON
              commite ne correspondent plus a l'arbre. Jambe BLOQUANTE : une
              PR qui edite un fichier apparie sans ajouter ni retirer de paire
              ne rougit pas -- la regeneration du JSON n'est plus due a chaque
              edition (arbitrage review #22216, alternative structure-seule).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
OUTPUT = REPO_ROOT / "translations" / "translation_golden_set.json"

# Prefixes exclus : vendores tiers et caches de build (memes exemptions que
# count_code_sorry.py / l'inventaire i18n cycle 38).
EXCLUDE_PARTS = {".lake", "_peters", "node_modules", ".git", "__pycache__"}
EXCLUDE_PREFIXES = ("MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentum/",)

KIND_NOTEBOOK = "notebook"
KIND_README = "readme"
KIND_LEAN = "lean"


def _sha1(path: Path) -> str:
    h = hashlib.sha1()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()


def _iter_files() -> list[Path]:
    out = []
    for p in REPO_ROOT.rglob("*"):
        try:
            if not p.is_file():
                continue
        except OSError:
            # Symlink casse (venv de conteneur Linux montee sur Windows) : ignorer.
            continue
        rel = p.relative_to(REPO_ROOT).as_posix()
        if any(part in EXCLUDE_PARTS for part in p.parts):
            continue
        if rel.startswith(EXCLUDE_PREFIXES):
            continue
        out.append(p)
    return out


def _notebook_source_sha1(path: Path) -> str:
    """Empreinte des sources d'un notebook (cellules source uniquement).

    Les outputs et execution_count bougent a chaque re-execution sans que la
    substance traduise change ; l'empreinte de pair se veut stable.
    """
    nb = json.loads(path.read_text(encoding="utf-8"))
    h = hashlib.sha1()
    for cell in nb.get("cells", []):
        src = cell.get("source", [])
        text = src if isinstance(src, str) else "".join(src)
        h.update(cell.get("cell_type", "?").encode())
        h.update(b"\x00")
        h.update(text.encode())
        h.update(b"\x00")
    return h.hexdigest()


def _fr_for_en(en_rel: str) -> str | None:
    """Chemin FR attendu pour un fichier _en (convention suffixe)."""
    if en_rel.endswith("_en.ipynb"):
        return en_rel[: -len("_en.ipynb")] + ".ipynb"
    if en_rel.endswith("_en.lean"):
        return en_rel[: -len("_en.lean")] + ".lean"
    if en_rel.endswith(".en.md"):
        return en_rel[: -len(".en.md")] + ".md"
    return None


def collect() -> dict:
    files = _iter_files()
    by_rel = {p.relative_to(REPO_ROOT).as_posix(): p for p in files}

    pairs: list[dict] = []
    orphans_en: list[str] = []

    for rel, p in sorted(by_rel.items()):
        kind = None
        if rel.endswith("_en.ipynb"):
            kind = KIND_NOTEBOOK
        elif rel.endswith("_en.lean"):
            kind = KIND_LEAN
        elif rel.endswith(".en.md"):
            kind = KIND_README
        if kind is None:
            continue
        fr_rel = _fr_for_en(rel)
        fr_path = by_rel.get(fr_rel) if fr_rel else None
        if fr_path is None:
            orphans_en.append(rel)
            continue
        entry = {
            "kind": kind,
            "fr": fr_rel,
            "en": rel,
            "sha1_fr": _sha1(fr_path),
            "sha1_en": _sha1(p),
        }
        if kind == KIND_NOTEBOOK:
            entry["sources_sha1_fr"] = _notebook_source_sha1(fr_path)
            entry["sources_sha1_en"] = _notebook_source_sha1(p)
        pairs.append(entry)

    return {
        "pairs": pairs,
        "counts": {k: sum(1 for e in pairs if e["kind"] == k)
                   for k in (KIND_NOTEBOOK, KIND_README, KIND_LEAN)},
        "orphans_en": sorted(orphans_en),
    }


def structure_of(data: dict) -> list:
    """Structure du golden set : couples (kind, fr, en) des paires, sans empreintes.

    C'est la partie dont la derive signale qu'une paire a ete AJOUTEE ou
    RETIREE de l'arbre. Les empreintes (sha1_fr, sha1_en, sources_sha1_*)
    derivent des qu'un fichier apparie est edite, sans changement de paire :
    elles vivent dans la jambe advisory (`--check`), pas dans la bloquante
    (arbitrage #22216). Les orphelins _en suivent les empreintes : ajouter un
    `_en` sans contrepartie FR n'est pas ajouter une paire, la jambe
    bloquante ne le voit pas.
    """
    return [[e.get("kind"), e.get("fr"), e.get("en")]
            for e in data.get("pairs", [])]


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true",
                    help="verifie que le JSON commite est a jour (pas de drift)")
    ap.add_argument("--check-structure", action="store_true",
                    help="verifie seulement les paires (kind, fr, en) -- la "
                         "derive d'empreintes ne fait pas echouer ce mode")
    args = ap.parse_args(argv)

    data = collect()

    if args.check or args.check_structure:
        if not OUTPUT.exists():
            print("GOLDEN-SET MISSING: translations/translation_golden_set.json absent")
            return 1
        current = json.loads(OUTPUT.read_text(encoding="utf-8"))
        if args.check and current != data:
            print("GOLDEN-SET DRIFT: le JSON commite ne correspond plus a l'arbre")
            print("  (jambe advisory : empreintes et orphelins compris)")
            print("  Regenérer : python scripts/translation/build_golden_set.py")
            return 1
        if structure_of(current) != structure_of(data):
            print("GOLDEN-SET STRUCTURE DRIFT: les paires du JSON commite "
                  "ne correspondent plus a l'arbre")
            print("  Regenérer : python scripts/translation/build_golden_set.py")
            return 1
        if args.check:
            print(f"GOLDEN-SET OK: {len(data['pairs'])} paires a jour")
        else:
            print(f"GOLDEN-SET STRUCTURE OK: {len(data['pairs'])} paires a jour "
                  "(empreintes non comparees dans ce mode)")
        return 0

    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(data, ensure_ascii=False, indent=1) + "\n",
                      encoding="utf-8", newline="\n")
    c = data["counts"]
    print(f"golden set: {len(data['pairs'])} paires "
          f"(notebooks={c[KIND_NOTEBOOK]}, readme={c[KIND_README]}, lean={c[KIND_LEAN]}), "
          f"{len(data['orphans_en'])} orphelins _en")
    return 0


if __name__ == "__main__":
    sys.exit(main())
