#!/usr/bin/env python3
"""Genere la requete `#print axioms` d'un contenu Lean externe (enveloppe DarkSnail).

Le script ne depend d'aucun outil du depot : il lit des fichiers `.lean` et
ecrit un fichier de requetes que `lake env lean <fichier>` execute. Il permet a
un tiers de rejouer la passe d'axiomes sur un clone amont, sans avoir a
rederiver la liste des theoremes a la main.

Usage :
    python scripts/lean/dsnail_axioms_query.py \
        --out Axioms.query \
        Formalization/OcclusionTriad.lean Formalization/BlockBridge.lean

Les imports sont deduits du chemin des sources (`Formalization/X.lean` ->
`import Formalization.X`) ; `--import` ajoute un import supplementaire.

Les theoremes sont qualifies par la pile de `namespace` courante ; les
declarations hors namespace sont emises sans prefixe.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

NAMESPACE_RE = re.compile(r"^namespace\s+(\S+)\s*$")
END_RE = re.compile(r"^end\s+(\S+)\s*$")
DECL_RE = re.compile(r"^\s*(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)")


def extract(path: Path) -> list[str]:
    """Rend les noms qualifies des theoremes/lemmas declares dans `path`."""
    stack: list[str] = []
    names: list[str] = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        ns = NAMESPACE_RE.match(raw)
        if ns:
            stack.append(ns.group(1))
            continue
        end = END_RE.match(raw)
        if end and stack and stack[-1] == end.group(1):
            stack.pop()
            continue
        decl = DECL_RE.match(raw)
        if decl:
            name = decl.group(2)
            names.append(".".join(stack + [name]) if stack else name)
    return names


def module_of(path: Path, root: Path) -> str:
    """Rend le nom de module Lean d'un fichier source (`Formalization/X.lean` -> `Formalization.X`).

    Le chemin est rendu relatif a `root` (la racine du projet lake) : un chemin
    absolu ne doit jamais produire un nom de module (le `/` initial produirait
    un nom invalide).
    """
    try:
        rel = path.resolve().relative_to(root.resolve())
    except ValueError:
        rel = Path(path.name)
    return rel.with_suffix("").as_posix().replace("/", ".")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("sources", nargs="+", type=Path, help="fichiers .lean a inspecter")
    parser.add_argument("--out", required=True, type=Path, help="fichier de requetes a ecrire")
    parser.add_argument(
        "--import",
        action="append",
        default=[],
        dest="imports",
        help="import supplementaire a prependre (repete)",
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path.cwd(),
        help="racine du projet lake (les modules sont nommes relativement a elle)",
    )
    args = parser.parse_args(argv)

    names: list[str] = []
    imports: list[str] = list(args.imports)
    for src in args.sources:
        if not src.is_file():
            print(f"[query] source absente : {src}", file=sys.stderr)
            return 2
        found = extract(src)
        print(f"[query] {src.name} : {len(found)} theoremes/lemmas")
        names.extend(found)
        imports.append(module_of(src, args.root))

    seen: set[str] = set()
    unique = [n for n in names if not (n in seen or seen.add(n))]
    unique_imports = [m for m in imports if not (m in seen or seen.add(m))]

    body = [f"import {m}" for m in unique_imports]
    body += [f"#print axioms {n}" for n in unique]
    args.out.write_text("".join(line + "\n" for line in body), encoding="utf-8", newline="\n")
    print(f"[query] ecrit : {args.out} ({len(unique)} requetes, {len(unique_imports)} imports)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
