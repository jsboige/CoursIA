#!/usr/bin/env python3
"""Detecteur de duplication d'organe (#16776, fille de #13564).

Sert la regle .claude/rules/organ-first-implementation.md (merge #16778) :
avant de reimplementer une semantique qu'une autre serie possede deja,
une PR doit nommer l'organe (5 questions) ou declarer une copie
pedagogique dans son body.

Scan un diff (mode --patch ou --base) et repere les symboles def/class
AJOUTES qui collisionnent avec l'index des organes
(scripts/audit/organ_api_index.yaml), dans un fichier hors de la serie
proprietaire de l'organe. Une phrase de copie declaree dans le body de
la PR blanchit les collisions (la porte de sortie vit dans le body).

Sortie : une ligne par collision au format
  COLLISION <serie demandeuse|?> (<fichier>) -> <serie organe> (<symbole>)
--check : exit 1 si au moins une collision non declaree.
"""

import argparse
import re
import subprocess
import sys
from pathlib import Path

try:
    import yaml
except ImportError:  # pragma: no cover
    print("ERROR: PyYAML requis (pip install pyyaml)", file=sys.stderr)
    sys.exit(2)

DEFAULT_INDEX = Path(__file__).resolve().parent / "organ_api_index.yaml"

DEF_RE = re.compile(r"(?:^|[\s\"'(])(?:def|class)\s+([A-Za-z_][A-Za-z0-9_]*)")
DIFF_FILE_RE = re.compile(r"^diff --git a/(.+?) b/(.+?)(?:\s|$)")

# Formes acceptees pour la declaration : « copie pedagogique declarée »
# (forme canonique de la regle) et « copie fidèle » (forme retroactive du
# cas Greffe2, PR #13802). Les accents sont normalises avant matching.
DECLARATION_RE = re.compile(
    r"\bcopie\s+(?:pedagogique\s+)?(?:declaree|fidele)\b", re.IGNORECASE
)


def strip_accents(text: str) -> str:
    import unicodedata
    nfd = unicodedata.normalize("NFD", text)
    return "".join(c for c in nfd if not unicodedata.combining(c))


def is_declared(body: str) -> bool:
    if not body:
        return False
    return bool(DECLARATION_RE.search(strip_accents(body)))


def load_index(path: Path):
    data = yaml.safe_load(path.read_text(encoding="utf-8"))
    series = data.get("series") or {}
    if not isinstance(series, dict) or not series:
        raise SystemExit(f"ERROR: index {path} sans section 'series' exploitable")
    symbol_owners = {}
    owners = {}
    for name, entry in series.items():
        owner_path = str(entry.get("owner_path", "")).rstrip("/")
        owners[name] = owner_path
        for sym in entry.get("symbols") or []:
            symbol_owners.setdefault(str(sym), name)
    return owners, symbol_owners


def resolve_series(path: str, owners: dict):
    """Serie propriétaire du fichier = owner_path le plus long prefix du chemin.

    Fallback hors index : composant racine sous MyIA.AI.Notebooks (label
    informatif ~, pas une serie indexee).
    """
    best, best_len = None, -1
    for name, owner_path in owners.items():
        if owner_path and (path + "/").startswith(owner_path + "/") and len(owner_path) > best_len:
            best, best_len = name, len(owner_path)
    if best is None:
        parts = path.split("/")
        if len(parts) >= 2 and parts[0] == "MyIA.AI.Notebooks":
            return "~" + parts[1]
    return best


def parse_patch(patch_text: str, owners: dict, symbol_owners: dict):
    """Retourne [(file, series, symbol)] pour chaque def/class ajoute en collision."""
    collisions = []
    current_file = None
    for line in patch_text.splitlines():
        m = DIFF_FILE_RE.match(line)
        if m:
            current_file = m.group(2)
            continue
        if current_file is None or not line.startswith("+") or line.startswith("+++"):
            continue
        content = line[1:].lstrip()
        if content.startswith("#"):
            continue
        for sym_m in DEF_RE.finditer(line[1:]):
            sym = sym_m.group(1)
            owner = symbol_owners.get(sym)
            if owner is None:
                continue
            file_series = resolve_series(current_file, owners)
            if file_series == owner:
                continue
            collisions.append((current_file, file_series, owner, sym))
    return collisions


def git_diff(base: str, head: str, cwd: Path) -> str:
    result = subprocess.run(
        ["git", "diff", f"{base}...{head}", "--unified=0"],
        capture_output=True, text=True, cwd=str(cwd), check=True,
    )
    return result.stdout


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--patch", help="fichier diff unifie a scanner (mode hors git)")
    parser.add_argument("--base", help="ref de base pour git diff (defaut origin/main)")
    parser.add_argument("--head", default="HEAD", help="ref de tete (defaut HEAD)")
    parser.add_argument("--body-file", help="fichier contenant le body de la PR")
    parser.add_argument("--body", help="body de la PR en ligne")
    parser.add_argument("--index", type=Path, default=DEFAULT_INDEX)
    parser.add_argument("--check", action="store_true",
                        help="exit 1 si collision non declaree")
    parser.add_argument("--cwd", type=Path, default=None)
    args = parser.parse_args(argv)

    if not args.patch and not args.base:
        args.base = "origin/main"

    owners, symbol_owners = load_index(args.index)

    if args.patch:
        patch_text = Path(args.patch).read_text(encoding="utf-8", errors="replace")
    else:
        patch_text = git_diff(args.base, args.head, args.cwd or Path.cwd())

    body = args.body if args.body is not None else (
        Path(args.body_file).read_text(encoding="utf-8", errors="replace")
        if args.body_file else ""
    )
    declared = is_declared(body)

    collisions = parse_patch(patch_text, owners, symbol_owners)

    undeclared = []
    for file, file_series, owner, sym in collisions:
        origin = file_series if file_series else "?"
        if declared:
            print(f"EXEMPTED {origin} ({file}) -> {owner} ({sym}) [copie declaree]")
        else:
            print(f"COLLISION {origin} ({file}) -> {owner} ({sym})")
            undeclared.append((file, owner, sym))

    status = "EXEMPTED" if declared and collisions else (
        "BLOCKED" if undeclared else "CLEAN"
    )
    print(f"{status}  {len(collisions)} collision(s), {len(undeclared)} non declaree(s), "
          f"{len(owners)} series dans l'index")

    if args.check and undeclared:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
