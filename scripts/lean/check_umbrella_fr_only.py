#!/usr/bin/env python3
"""Check that a Lean lake's root aggregator (umbrella) is FR-only.

Background
----------
Issue #16154 (EPIC #16048) : l'umbrella ``grothendieck_lean/Grothendieck.lean``
avait dérivé à ``18 _en imports / 73 _en sur disque`` — un quart seulement
des siblings EN étaient importés, et **rien ne le tenait**. Un lecteur ouvrant
l'umbrella et y voyant ``CoversAtomicArrow_en`` et ``PlusConstruction_en``
conclurait à tort que l'inclusion des EN est la règle ; elle ne l'est que pour
les familles ajoutées récemment.

Convention ratifiée ``docs/lean/i18n-inventory-cycle-38.md`` (cf
``.claude/rules/code-style.md`` §Lean i18n) : les **root aggregators**
(umbrellas imports-only, 0 déclaration) sont **FR-only by design**. Les
siblings ``_en`` (namespace ``<Lib>_en``) sont auto-découverts par le
``globs := #[`<Lib>.*]`` du ``lakefile.lean`` et restent construits ; ils sont
vérifiés en byte-identity par ``check_i18n_siblings.py``. Importer un ``_en``
dans l'umbrella en ferait un doublon bilingue — anti-pattern qui gaspille
l'index humain sans rien apporter au build.

Drift classes (all block CI on ``--strict``) :

1. ``EN_IMPORT_PRESENT`` — l'umbrella importe un sibling ``_en``. Le défaut à
   corriger : retirer la ligne ``import Grothendieck.<Foo>_en`` (cf #16154).
2. ``MISSING_FR_LEAF`` — un module ``<Foo>.lean`` du répertoire n'est pas
   importé par l'umbrella. Le défaut à corriger : ajouter
   ``import Grothendieck.<Foo>`` (cf #16068, fermé 7/72 → 72/72 sur FR).
3. ``ORPHAN_FR_IMPORT`` — un import FR de l'umbrella pointe vers un fichier
   absent du répertoire. À distinguer du cas légitime ``SheafCohomology``
   (parent d'un sous-module, listé en plus) — advisory par défaut.

Usage
-----
    python scripts/lean/check_umbrella_fr_only.py <lake_root>
    python scripts/lean/check_umbrella_fr_only.py --json <lake_root>
    python scripts/lean/check_umbrella_fr_only.py --strict <lake_root>

Exit code ``0`` when the invariant holds (or only advisory findings remain),
``1`` on any blocking drift, ``2`` on usage error.

Examples
--------
    python scripts/lean/check_umbrella_fr_only.py \\
        MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean \\
        --strict
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import List

IMPORT_RE = re.compile(r"^\s*import\s+(?P<ns>[A-Za-z][A-Za-z0-9_]*)"
                       r"(?:\.(?P<mod>[A-Za-z][A-Za-z0-9_]*)?)?")


@dataclass(frozen=True)
class Finding:
    kind: str            # EN_IMPORT_PRESENT | MISSING_FR_LEAF | ORPHAN_FR_IMPORT | INFO
    module: str          # e.g. "Grothendieck.CoversAtomicArrow_en"
    detail: str          # human-readable explanation

    def to_dict(self) -> dict:
        return asdict(self)


def collect_disk_modules(lake_root: Path) -> tuple[set[str], set[str]]:
    """Return ``(fr_modules, en_modules)`` of leaf module basenames under ``<lake>/<Namespace>/``.

    The umbrella is conventionally ``<lake>/<Namespace>.lean`` and imports
    children of ``<lake>/<Namespace>/<Foo>.lean`` via ``import <Namespace>.<Foo>``.
    """
    umbrella_path = next(lake_root.glob("*.lean"), None)
    if umbrella_path is None:
        raise FileNotFoundError(f"no umbrella .lean found under {lake_root}")
    namespace = umbrella_path.stem  # e.g. "Grothendieck"
    sub_dir = lake_root / namespace
    if not sub_dir.is_dir():
        raise FileNotFoundError(f"sub-directory {sub_dir} does not exist")

    fr: set[str] = set()
    en: set[str] = set()
    for f in sub_dir.glob("*.lean"):
        stem = f.stem
        if stem.endswith("_en"):
            en.add(stem)
        else:
            fr.add(stem)
    return fr, en


def collect_umbrella_imports(umbrella: Path, namespace: str) -> tuple[set[str], set[str]]:
    """Return ``(fr_imports, en_imports)`` of bare ``import <Namespace>.<Foo>`` lines."""
    fr: set[str] = set()
    en: set[str] = set()
    for line in umbrella.read_text(encoding="utf-8").splitlines():
        m = IMPORT_RE.match(line)
        if not m:
            continue
        ns = m.group("ns")
        mod = m.group("mod")
        if ns != namespace or not mod:
            continue
        if mod.endswith("_en"):
            en.add(mod)
        else:
            fr.add(mod)
    return fr, en


def check_lake(lake_root: Path) -> List[Finding]:
    """Return the list of findings for ``lake_root``."""
    findings: List[Finding] = []
    umbrella_path = next(lake_root.glob("*.lean"), None)
    if umbrella_path is None:
        findings.append(Finding("INFO", "<umbrella>",
                                f"no umbrella .lean found under {lake_root}"))
        return findings
    namespace = umbrella_path.stem

    fr_disk, en_disk = collect_disk_modules(lake_root)
    fr_imp, en_imp = collect_umbrella_imports(umbrella_path, namespace)

    # 1. EN_IMPORT_PRESENT — umbrella imports an _en
    for mod in sorted(en_imp):
        findings.append(Finding(
            kind="EN_IMPORT_PRESENT",
            module=f"{namespace}.{mod}",
            detail=(
                f"umbrella imports the EN sibling; convention i18n "
                f"(EPIC #4980, root aggregator = FR-only by design) "
                f"requires removing this import"
            ),
        ))

    # 2. MISSING_FR_LEAF — FR leaf on disk but not imported by umbrella
    for mod in sorted(fr_disk - fr_imp):
        findings.append(Finding(
            kind="MISSING_FR_LEAF",
            module=f"{namespace}.{mod}",
            detail=(
                f"FR leaf present on disk but not imported by umbrella "
                f"(add `import {namespace}.{mod}`)"
            ),
        ))

    # 3. ORPHAN_FR_IMPORT — umbrella imports a FR module not on disk
    for mod in sorted(fr_imp - fr_disk):
        # ``SheafCohomology`` (parent of ``SheafCohomology.Basic`` etc.) is
        # legitimate — it has no leaf file because it's a parent aggregator.
        # We mark it advisory (not strict) by emitting INFO not ORPHAN_FR_IMPORT.
        findings.append(Finding(
            kind="INFO",
            module=f"{namespace}.{mod}",
            detail=(
                f"FR import of umbrella has no leaf file on disk — likely "
                f"a parent aggregator (e.g. ``SheafCohomology``) that names "
                f"a sub-directory rather than a .lean file"
            ),
        ))

    return findings


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Verify that a Lean lake's root aggregator (umbrella) "
                    "is FR-only (EPIC #4980, convention root aggregator)."
    )
    parser.add_argument(
        "lake_root",
        type=Path,
        help="Path to the lake root, e.g. "
             "MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Treat any drift (including advisory) as a non-zero exit.",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Emit machine-readable JSON instead of human-readable text.",
    )
    args = parser.parse_args(argv)

    if not args.lake_root.is_dir():
        print(f"error: {args.lake_root} is not a directory", file=sys.stderr)
        return 2

    findings = check_lake(args.lake_root)
    blocking = [f for f in findings if f.kind in ("EN_IMPORT_PRESENT", "MISSING_FR_LEAF")]
    advisory = [f for f in findings if f.kind == "ORPHAN_FR_IMPORT"]

    if args.json:
        payload = {
            "lake_root": str(args.lake_root),
            "findings": [f.to_dict() for f in findings],
            "blocking_count": len(blocking),
            "advisory_count": len(advisory),
            "exit_code": 1 if (blocking or (args.strict and advisory)) else 0,
        }
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        if not findings:
            print(f"OK: {args.lake_root} umbrella is FR-only "
                  f"(0 EN imports, 0 missing FR leaves)")
        else:
            for f in findings:
                tag = "BLOCKING" if f.kind in ("EN_IMPORT_PRESENT", "MISSING_FR_LEAF") else "advisory"
                print(f"[{tag}] {f.kind}: {f.module} — {f.detail}")

    if blocking:
        return 1
    if args.strict and advisory:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
