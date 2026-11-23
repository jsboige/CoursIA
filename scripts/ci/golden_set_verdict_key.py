#!/usr/bin/env python3
"""Cle de verdict du golden-set (tranche 1 de #22468, levier 6 de #22461).

Un verdict vert du golden-set est une PREUVE : les carnets pinces executent de
bout en bout et produisent leur sortie. Rejouer la suite alors que rien de ce
qui influe sur ce verdict n'a bouge ne produit aucune preuve supplementaire --
la mesure de #22468 releve 19 runs redondants sur 21.

Cette cle couvre tout ce qui influe sur le verdict :

  - le manifeste (liste des carnets, timeouts, ``python_pin``) ;
  - le lockfile pinne (les dependances installees) ;
  - l'implementation de l'executeur (``notebook_tools.py``) ;
  - la version de Python demandee par l'appelant ;
  - le workflow qui appelle cette cle et gouverne la reutilisation du verdict ;
  - le contenu OCTET POUR OCTET de chaque carnet execute.

Le workflow complet entre dans la cle : une modification de ses commandes,
conditions ou mecanismes de cache ne doit jamais reutiliser un verdict produit
sous un autre contrat. Cela inclut aussi les changements de commentaire ou de
routage, qui peuvent invalider la reutilisation sans rendre le cache perime.

Sortie (JSON, sur stdout ou dans ``--out``) :

    {"key": "<16 hex>", "components": {...}, "notebooks": [...]}

Le script ne depend que de la bibliotheque standard : dans le workflow, il
tourne AVANT l'installation du lockfile, precisement pour qu'un verdict
reutilise ne paie pas l'installation.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

_KEY_BYTES = 8  # 16 caracteres hexadecimaux
_ENTRY = re.compile(r"^\s*-\s*path:\s*(\S.*?)\s*$", re.MULTILINE)


def _sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def manifest_notebooks(manifest_text: str) -> list[str]:
    """Chemins des carnets declares par le manifeste, dans l'ordre du fichier."""
    return [m.group(1).strip("'\"") for m in _ENTRY.finditer(manifest_text)]


def compute_key(
    repo_root: Path,
    manifest: Path,
    lockfile: Path,
    implementation: Path,
    workflow: Path,
    python_version: str,
) -> dict:
    """Empreinte du verdict : identite des entrees + contenu des carnets."""
    manifest_text = _read_text(manifest)
    notebooks = manifest_notebooks(manifest_text)

    per_notebook = []
    missing = []
    for rel in notebooks:
        path = repo_root / rel
        if path.is_file():
            per_notebook.append({"path": rel, "sha256": _sha256_file(path)})
        else:
            missing.append(rel)

    components = {
        "python_version": python_version,
        "manifest": _sha256_file(manifest),
        "lockfile": _sha256_file(lockfile),
        "implementation": _sha256_file(implementation),
        "workflow": _sha256_file(workflow),
        "notebooks": per_notebook,
        "manifest_notebook_order": notebooks,
    }
    canonical = json.dumps(components, sort_keys=True, separators=(",", ":"))
    key = hashlib.sha256(canonical.encode("utf-8")).hexdigest()[:_KEY_BYTES * 2]
    return {
        "key": key,
        "components": {
            "python_version": python_version,
            "manifest_sha256": components["manifest"],
            "lockfile_sha256": components["lockfile"],
            "implementation_sha256": components["implementation"],
            "workflow_sha256": components["workflow"],
            "notebook_count": len(per_notebook),
        },
        "notebooks": per_notebook,
        "missing_notebooks": missing,
    }


def main(argv: list[str] | None = None) -> int:
    here = Path(__file__).resolve()
    repo_root = here.parent.parent.parent
    tools = repo_root / "scripts" / "notebook_tools"

    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--repo-root", type=Path, default=repo_root)
    ap.add_argument("--manifest", type=Path, default=tools / "golden_set.yml")
    ap.add_argument("--lockfile", type=Path, default=tools / "golden_set.lock.txt")
    ap.add_argument("--implementation", type=Path, default=tools / "notebook_tools.py")
    ap.add_argument(
        "--workflow",
        type=Path,
        default=repo_root / ".github" / "workflows" / "notebook-execution-required.yml",
    )
    ap.add_argument("--python-version", default="3.12")
    ap.add_argument("--out", type=Path, default=None)
    args = ap.parse_args(argv)

    result = compute_key(
        args.repo_root,
        args.manifest,
        args.lockfile,
        args.implementation,
        args.workflow,
        args.python_version,
    )
    for rel in result["missing_notebooks"]:
        print(f"::warning::carnet declare au manifeste mais absent : {rel}", file=sys.stderr)

    payload = json.dumps(result, indent=2, sort_keys=True)
    if args.out:
        args.out.write_text(payload + "\n", encoding="utf-8")
    else:
        print(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
