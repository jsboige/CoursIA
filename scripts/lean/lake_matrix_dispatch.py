#!/usr/bin/env python3
"""Dispatch des lakes Lean vers la matrice CI (#13751, sous-item workflows).

Consomme le manifeste ``scripts/lean/ci_lakes.json`` et la liste des
fichiers changes d'un evenement push/pull_request, et rend l'ensemble
``include`` de la matrice a executer :

  - un fichier qui matche les ``paths`` d'un lake -> ce lake ;
  - un fichier de GATE_SELF_COVER (le workflow lui-meme, le reusable
    lean-build.yml, le composite, ce script, le manifeste) -> TOUS les
    lakes : un changement du gate doit lancer le gate (lecon #8712 --
    les workflows definissant la CI sont les seuls fichiers qu'elle ne
    verifiait jamais ; la forme matricielle herite de l'obligation).

Sortie : JSON ``{"any": bool, "include": [entrees de manifeste]}`` sur
stdout, ou ecriture directe du fichier outputs GitHub via
``--outputs-file`` (cles ``any`` et ``lake-set``). Pur et testable :
aucun acces reseau, aucun appel gh, fnmatch uniquement.
"""

from __future__ import annotations

import argparse
import fnmatch
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_MANIFEST = REPO_ROOT / "scripts" / "lean" / "ci_lakes.json"

# Un changement du gate lance le gate pour TOUS les lakes du manifeste
# (self-cover, lecon #8712 : le dispatcher supprime `lean-<lake>.yml`
# de la liste -- c'est ce fichier qui le remplace).
GATE_SELF_COVER = [
    ".github/workflows/lean-ci-matrix.yml",
    ".github/workflows/lean-build.yml",
    ".github/actions/lean-build/action.yml",
    "scripts/lean/ci_lakes.json",
    "scripts/lean/lake_matrix_dispatch.py",
    "scripts/ci/check_lake_matrix_paths.py",
]


def changed_lakes(changed: list[str], manifest: dict) -> list[dict]:
    lakes = manifest["lakes"]
    if any(f in GATE_SELF_COVER for f in changed):
        return list(lakes)
    selected: dict[str, dict] = {}
    for entry in lakes:
        for pattern in entry["paths"]:
            if any(fnmatch.fnmatch(f, pattern) for f in changed):
                selected[entry["lake"]] = entry
                break
    # Ordre stable = ordre du manifeste (determinisme des check-runs).
    return [e for e in lakes if e["lake"] in selected]


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    ap.add_argument("--changed-file", type=Path, default=None,
                    help="fichier contenant un chemin change par ligne "
                         "(defaut : stdin)")
    ap.add_argument("--outputs-file", type=Path, default=None,
                    help="ecrire les outputs GitHub (any, lake-set) dans "
                         "ce fichier au lieu du JSON stdout")
    args = ap.parse_args(argv)

    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    if args.changed_file is not None:
        changed = [l.strip() for l in
                   args.changed_file.read_text(encoding="utf-8").splitlines()
                   if l.strip()]
    else:
        changed = [l.strip() for l in sys.stdin if l.strip()]

    include = changed_lakes(changed, manifest)
    result = {"any": bool(include), "include": include}

    if args.outputs_file is not None:
        lines = [
            f"any={'true' if result['any'] else 'false'}",
            "lake-set=" + json.dumps({"include": include}, separators=(",", ":")),
        ]
        args.outputs_file.write_text("\n".join(lines) + "\n", encoding="utf-8")
    else:
        json.dump(result, sys.stdout, indent=1, ensure_ascii=False)
        sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
