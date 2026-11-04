#!/usr/bin/env python3
"""Garde de source unique du PCM par poches (QuantConnect) — issue #20188, critère 2.

**Ce que le défaut était.** Le modèle de construction de portefeuille par
poches (`MultiStrategyPCM`) existait en neuf copies sous
`MyIA.AI.Notebooks/QuantConnect/`, en six variantes, et le correctif
`additive` (#19740) n'était présent que dans trois d'entre elles. Un
correctif posé sur une copie ne se propageait pas : rien ne signalait qu'une
nouvelle composite avait pris une variante sans le correctif.

**Ce que l'extraction a laissé.** `projects/SharedPCM/pouches_pcm.py` est
devenue la source canonique (`MultiStrategyPouchesPCM`) ; les composites
composites l'importent (`from SharedPCM.pouches_pcm import ...`). Deux
copies subsistent, pour deux raisons qui ne se corrigent pas par un
copier-coller :

- le kit pédagogique `03-Framework-Composite` est **autonome** (le code est
  copié dans `main.py` par l'apprenant, sans bibliothèque QC attachée) ;
- `projects/TrendWeatherPointInTime` est **gelé** : le registre de l'ombre
  (`ML-Training-Pipeline/shadow/registry.json`, entrée `tw-pit`) épingle
  l'empreinte de ses trois fichiers, et l'extraction ne touche pas une
  entrée gelée.

**Ce que fait cette garde.** Elle refuse qu'une **nouvelle** copie du modèle
apparaisse sans déclaration, et elle refuse qu'une copie **déclarée** soit
modifiée sans re-déclaration. Le manifeste
(`scripts/quantconnect/pcm_single_source.json`) porte la source canonique,
les copies déclarées et la raison de chaque déclaration.

**Contrôle positif.** Une copie volontairement modifiée fait rougir la
garde : c'est le cas `DECLARATION_STALE` du corps de tests
(`scripts/quantconnect/tests/test_check_pcm_single_source.py`), qui crée un
arbre temporaire où une copie déclarée diffère de son empreinte et exige un
verdict rouge. Le cas nominal (arbre du dépôt) doit rester vert.

**Empreinte.** `sha256` du texte normalisé (fins de ligne ramenées à `\n`),
afin que l'empreinte soit la même sur un checkout Windows (`core.autocrlf`)
et sur un checkout Linux.

Usage :
    python scripts/quantconnect/check_pcm_single_source.py
    python scripts/quantconnect/check_pcm_single_source.py --json
    python scripts/quantconnect/check_pcm_single_source.py --root <checkout>
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_MANIFEST = REPO_ROOT / "scripts" / "quantconnect" / "pcm_single_source.json"
SCAN_SUBTREE = "MyIA.AI.Notebooks/QuantConnect"

# Famille du PCM par poches : le nom de classe suffit a designer le modele.
# `RiskParityPCM`, `MeanVariancePCM` ou `CappedPouchesPCM` sont d'autres
# modeles (ou une specialisation du canonique) : ils ne sont pas concernes.
CLASS_RE = re.compile(r"^class\s+(MultiStrategy\w*PCM)\s*\(([^)]*)\)", re.MULTILINE)

# Codes de verdict : `blocking` = la garde rougit, `info` = signale sans
# bloquer (les carnets de reference recopient le code a copier).
CODES = {
    "CANONICAL_MISSING": "La source canonique du PCM par poches est absente du depot.",
    "CANONICAL_DRIFT": "La source canonique a change : le manifeste doit etre re-declare.",
    "UNDECLARED_COPY": "Une copie du PCM par poches existe hors de la source canonique, sans declaration.",
    "DECLARATION_STALE": "Une copie declaree a ete modifiee sans re-declaration.",
    "DECLARED_COPY_MISSING": "Une copie declaree n'existe plus : declaration a retirer.",
    "CLASS_MISMATCH": "Les classes declarees ne correspondent pas au contenu du fichier.",
}


def normalized_sha256(path: Path) -> str:
    """sha256 du texte normalise (fins de ligne LF) — insensible a l'OS."""
    data = path.read_bytes()
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError:
        text = data.decode("utf-8", errors="replace")
    text = text.replace("\r\n", "\n").replace("\r", "\n")
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def find_definitions(path: Path) -> list[dict]:
    """Classes de la famille definies dans un fichier .py."""
    text = path.read_text(encoding="utf-8", errors="replace")
    found = []
    for match in CLASS_RE.finditer(text):
        name = match.group(1)
        bases = match.group(2)
        found.append(
            {
                "class": name,
                "line": text[: match.start()].count("\n") + 1,
                "inherits_canonical": name != "MultiStrategyPouchesPCM"
                and "MultiStrategyPouchesPCM" in bases,
            }
        )
    return found


def scan_copies(root: Path) -> list[dict]:
    """Tous les sites de definition de la famille, sous l'arborescence QC."""
    sites = []
    base = root / SCAN_SUBTREE
    if not base.is_dir():
        return sites
    for path in sorted(base.rglob("*.py")):
        if any(part.endswith(".lake") for part in path.parts):
            continue
        for definition in find_definitions(path):
            rel = path.relative_to(root).as_posix()
            sites.append({"path": rel, **definition})
    return sites


def scan_notebook_copies(root: Path) -> list[str]:
    """Copies recopiées dans des carnets (informatif : le code est a copier).

    Un carnet porte le code sous forme de JSON : les sources sont donc
    concatenees cellule par cellule avant d'appliquer le motif de classe.
    """
    base = root / SCAN_SUBTREE
    hits = []
    if not base.is_dir():
        return hits
    for path in sorted(base.rglob("*.ipynb")):
        try:
            notebook = json.loads(path.read_text(encoding="utf-8", errors="replace"))
        except (OSError, ValueError):
            continue
        chunks = []
        for cell in notebook.get("cells", []):
            source = cell.get("source", "")
            chunks.append("".join(source) if isinstance(source, list) else str(source))
        if CLASS_RE.search("\n".join(chunks)):
            hits.append(path.relative_to(root).as_posix())
    return hits


def analyse(root: Path, manifest_path: Path) -> dict:
    findings = []
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        return {
            "verdict": "ERROR",
            "findings": [
                {
                    "code": "MANIFEST_UNREADABLE",
                    "path": manifest_path.as_posix(),
                    "detail": str(exc),
                }
            ],
            "canonical": None,
            "declared_copies": [],
            "notebook_copies": [],
        }

    canonical = manifest.get("canonical", {})
    canonical_rel = canonical.get("path", "")
    declared = {entry["path"]: entry for entry in manifest.get("declared_copies", [])}

    sites = scan_copies(root)
    notebook_copies = scan_notebook_copies(root)

    # 1. La source canonique est presente, unique, et conforme a son empreinte.
    canonical_path = root / canonical_rel if canonical_rel else None
    canonical_sites = [s for s in sites if s["path"] == canonical_rel]
    if not canonical_path or not canonical_path.is_file():
        findings.append(
            {
                "code": "CANONICAL_MISSING",
                "path": canonical_rel,
                "detail": "fichier absent du checkout",
            }
        )
    else:
        if len(canonical_sites) != 1:
            findings.append(
                {
                    "code": "CANONICAL_MISSING",
                    "path": canonical_rel,
                    "detail": "%d definitions de la famille dans le fichier canonique" % len(canonical_sites),
                }
            )
        digest = normalized_sha256(canonical_path)
        if canonical.get("sha256") and digest != canonical["sha256"]:
            findings.append(
                {
                    "code": "CANONICAL_DRIFT",
                    "path": canonical_rel,
                    "detail": "empreinte actuelle %s, empreinte declaree %s"
                    % (digest[:12], canonical["sha256"][:12]),
                }
            )
        declared_classes = set(canonical.get("classes", []))
        found_classes = {s["class"] for s in canonical_sites}
        if declared_classes and found_classes != declared_classes:
            findings.append(
                {
                    "code": "CLASS_MISMATCH",
                    "path": canonical_rel,
                    "detail": "declare %s, trouve %s"
                    % (sorted(declared_classes), sorted(found_classes)),
                }
            )

    # 2. Chaque copie declaree existe, declare les bonnes classes, et son
    #    contenu est celui que la declaration decrit.
    for rel, entry in sorted(declared.items()):
        path = root / rel
        if not path.is_file():
            findings.append(
                {
                    "code": "DECLARED_COPY_MISSING",
                    "path": rel,
                    "detail": "declaration a retirer du manifeste",
                }
            )
            continue
        digest = normalized_sha256(path)
        if entry.get("sha256") and digest != entry["sha256"]:
            findings.append(
                {
                    "code": "DECLARATION_STALE",
                    "path": rel,
                    "detail": "empreinte actuelle %s, empreinte declaree %s"
                    % (digest[:12], entry["sha256"][:12]),
                }
            )
        found_classes = {s["class"] for s in sites if s["path"] == rel}
        declared_classes = set(entry.get("classes", []))
        if declared_classes and found_classes != declared_classes:
            findings.append(
                {
                    "code": "CLASS_MISMATCH",
                    "path": rel,
                    "detail": "declare %s, trouve %s"
                    % (sorted(declared_classes), sorted(found_classes)),
                }
            )

    # 3. Aucune copie non declaree.
    for site in sites:
        rel = site["path"]
        if rel == canonical_rel or rel in declared:
            continue
        if site.get("inherits_canonical"):
            # Une specialisation du canonique n'est pas une copie.
            continue
        findings.append(
            {
                "code": "UNDECLARED_COPY",
                "path": rel,
                "detail": "class %s (ligne %d) — declarer la copie ou importer le canonique"
                % (site["class"], site["line"]),
            }
        )

    blocking = [f for f in findings if f["code"] != "INFO"]
    return {
        "verdict": "OK" if not blocking else "FAIL",
        "findings": findings,
        "canonical": canonical_rel,
        "declared_copies": sorted(declared),
        "notebook_copies": notebook_copies,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--root",
        default=str(REPO_ROOT),
        help="racine du depot (contient MyIA.AI.Notebooks/...)",
    )
    parser.add_argument(
        "--manifest",
        default=str(DEFAULT_MANIFEST),
        help="manifeste des declarations",
    )
    parser.add_argument("--json", action="store_true", help="sortie structuree")
    args = parser.parse_args(argv)

    root = Path(args.root).resolve()
    manifest_path = Path(args.manifest).resolve()
    report = analyse(root, manifest_path)

    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        print("Garde de source unique du PCM par poches — #20188 critere 2")
        print("Source canonique : %s" % (report["canonical"] or "(absente)"))
        print("Copies declarees  : %d" % len(report["declared_copies"]))
        if report["notebook_copies"]:
            print(
                "Copies dans des carnets (informatif, code a copier) : %d"
                % len(report["notebook_copies"])
            )
        if report["verdict"] == "OK":
            print("VERDICT: OK — aucune copie non declaree, aucune declaration perimee.")
        elif report["verdict"] == "ERROR":
            print("VERDICT: ERROR — le manifeste est illisible : la garde ne peut pas statuer.")
        else:
            print("VERDICT: FAIL")
            for finding in report["findings"]:
                print(
                    "  [%s] %s — %s (%s)"
                    % (
                        finding["code"],
                        finding["path"],
                        finding.get("detail", ""),
                        CODES.get(finding["code"], ""),
                    )
                )

    if report["verdict"] == "ERROR":
        return 2
    return 0 if report["verdict"] == "OK" else 1


if __name__ == "__main__":
    sys.exit(main())
