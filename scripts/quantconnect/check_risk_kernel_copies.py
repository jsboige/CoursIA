#!/usr/bin/env python3
"""Garde des copies du noyau de risque deterministe (QuantConnect) - issue #24698.

**Pourquoi des copies.** Le noyau de risque (plafond d'exposition, stop a
2 ATR, coupe-circuit) vit dans une source canonique,
`projects/RiskKernel/risk_kernel.py`. QuantConnect n'importe que les
fichiers du projet : chaque projet qui l'utilise en porte donc une copie
`risk_kernel.py`, a cote de son `main.py`.

**Ce que la garde refuse.**

- `COPY_DRIFT` : une copie differe de la source canonique. Un correctif pose
  sur une copie ne se propage pas ; on modifie la source canonique, puis on
  recopie.
- `COPY_MISSING` : un projet importe `risk_kernel` sans en porter la copie.
  Sur QC Cloud, l'echec n'apparait pas a la compilation mais au lancement
  du backtest, dans `Initialize()`.
- `CANONICAL_MISSING` : la source canonique est absente.

Les copies sont decouvertes, pas declarees : tout `risk_kernel.py` sous
`projects/` hors de la source canonique est compare. Une nouvelle strategie
qui adopte le noyau est couverte sans editer la garde.

**Empreinte.** `sha256` du texte normalise (fins de ligne ramenees a `\n`),
pour qu'un checkout Windows (`core.autocrlf`) et un checkout Linux donnent
la meme empreinte.

**Hors perimetre.** `projects/DeterministicRiskKernel-QC` garde son portage
du carnet, sous un autre nom de fichier : il n'est pas une copie.

Usage :
    python scripts/quantconnect/check_risk_kernel_copies.py
    python scripts/quantconnect/check_risk_kernel_copies.py --json
    python scripts/quantconnect/check_risk_kernel_copies.py --root <checkout>
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
PROJECTS = "MyIA.AI.Notebooks/QuantConnect/projects"
CANONICAL_REL = f"{PROJECTS}/RiskKernel/risk_kernel.py"
MODULE_FILE = "risk_kernel.py"
IMPORT_RE = re.compile(r"^\s*(?:from\s+risk_kernel\s+import|import\s+risk_kernel\b)", re.MULTILINE)

CODES = {
    "CANONICAL_MISSING": "La source canonique du noyau de risque est absente.",
    "COPY_DRIFT": "Une copie du noyau differe de la source canonique : recopier depuis RiskKernel/.",
    "COPY_MISSING": "Un projet importe risk_kernel sans en porter la copie (echec a Initialize() sur QC).",
}


def normalized_sha256(path: Path) -> str:
    text = path.read_bytes().replace(b"\r\n", b"\n")
    return hashlib.sha256(text).hexdigest()


def analyse(root: Path) -> dict:
    """Verdict de la garde sur l'arbre `root`."""
    projects = root / PROJECTS
    canonical = root / CANONICAL_REL
    findings: list[dict] = []
    copies: list[str] = []
    canonical_sha = None
    if not canonical.is_file():
        findings.append({"code": "CANONICAL_MISSING", "path": CANONICAL_REL})
    else:
        canonical_sha = normalized_sha256(canonical)
    if projects.is_dir():
        for copy in sorted(projects.rglob(MODULE_FILE)):
            rel = copy.relative_to(root).as_posix()
            if rel == CANONICAL_REL:
                continue
            copies.append(rel)
            if canonical_sha is not None and normalized_sha256(copy) != canonical_sha:
                findings.append({"code": "COPY_DRIFT", "path": rel})
        for source in sorted(projects.rglob("*.py")):
            rel = source.relative_to(root).as_posix()
            if source.name == MODULE_FILE:
                continue
            try:
                text = source.read_text(encoding="utf-8")
            except UnicodeDecodeError:
                continue
            if IMPORT_RE.search(text) and not (source.parent / MODULE_FILE).is_file():
                findings.append({"code": "COPY_MISSING", "path": rel})
    return {
        "canonical": CANONICAL_REL,
        "canonical_sha256": canonical_sha,
        "copies": copies,
        "findings": findings,
        "ok": not findings,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", type=Path, default=REPO_ROOT, help="racine du checkout")
    parser.add_argument("--json", action="store_true", help="verdict machine")
    args = parser.parse_args(argv)
    result = analyse(args.root.resolve())
    if args.json:
        print(json.dumps(result, ensure_ascii=False, indent=2))
    else:
        print(f"source canonique : {result['canonical']}")
        print(f"copies comparees : {len(result['copies'])}")
        for rel in result["copies"]:
            print(f"  - {rel}")
        for finding in result["findings"]:
            print(f"[{finding['code']}] {finding['path']} : {CODES[finding['code']]}")
        print("verdict : OK" if result["ok"] else "verdict : ROUGE")
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
