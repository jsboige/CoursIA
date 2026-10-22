#!/usr/bin/env python3
"""check_memory_index_coverage.py -- organe de couverture du MEMORY.md per-machine.

Implémente l'acceptance de #17885 (consolider MEMORY.md en grappes, 0 orphelin,
0 lien mort) :

  - 0 orphelin : tout fichier .md du dossier memory/ (hors MEMORY.md lui-même)
                 est référencé au moins une fois par MEMORY.md.
  - 0 lien mort : tout lien markdown explicite vers un .md local pointe sur un
                  fichier existant.
  - Couverture : referenced / total (sortie diagnostique).
  - Taille : rapport en octets, ligne count. Plafond par défaut 24 400 octets
             (truncation-at-load de Claude Code) ; alerte NON bloquante à 90 %
             (21 960 octets). Aligné sur roo-extensions #4204.

Usage :

    python scripts/coordination/check_memory_index_coverage.py \\
        --memory-dir C:/Users/Jesse/.claude/projects/<hash>/memory \\
        [--json] [--max-bytes N] [--no-max-bytes]

Exit 0 si 0 orphelin ET 0 lien mort ET taille <= plafond ; exit 1 sinon.
L'alerte 90 % est un avertissement, pas un échec.

L'organe n'écrit rien : il mesure. Sans --no-max-bytes, la taille est bornée
par le plafond aligné #4204 (24 400 o) ; --max-bytes N le surcharge ;
--no-max-bytes rend le verdict binaire seul (comportement pré-#4204).

Origine : #17885 (arbitrage user Q10 du 2026-09-26 : « complétude et
consolidation en grappes »). Avant cet organe, la couverture était vérifiée à
l'œil dans le cycle c.874. Seuils de taille alignés le 2026-10-16 sur
roo-extensions #4204 (plafond 24,4 Ko, alerte 21 960 o, budget <= 63 o/entrée).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# Alignement #4204 : 24 400 o = plafond de truncation-at-load de Claude Code,
# alerte à 90 % (21 960 o). Le budget par entrée (<= 63 o) relève du contenu,
# pas de cet organe.
DEFAULT_MAX_BYTES = 24_400
ALERT_RATIO = 0.90


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument(
        "--memory-dir",
        required=True,
        type=Path,
        help="chemin du dossier memory/ (contient MEMORY.md + fichiers de Tells)",
    )
    p.add_argument("--json", action="store_true", help="sortie JSON")
    p.add_argument(
        "--max-bytes",
        type=int,
        default=DEFAULT_MAX_BYTES,
        help=f"exit 1 si MEMORY.md dépasse cette taille (octets) ; défaut {DEFAULT_MAX_BYTES} (#4204)",
    )
    p.add_argument(
        "--no-max-bytes",
        action="store_true",
        help="désactive le plafond de taille (verdict binaire seul, comportement pré-#4204)",
    )
    args = p.parse_args()

    mem_dir: Path = args.memory_dir
    mem_file = mem_dir / "MEMORY.md"

    if not mem_file.is_file():
        print(f"FATAL: {mem_file} introuvable", file=sys.stderr)
        return 2

    # Lire MEMORY.md
    mem_text = mem_file.read_text(encoding="utf-8")

    # Tous les fichiers .md dans memory/ sauf MEMORY.md lui-même
    all_files = sorted([p.name for p in mem_dir.glob("*.md") if p.stem != "MEMORY"])

    # Liens markdown explicites [text](path) où path finit par .md et n'est pas http(s)
    md_links = re.findall(r"\[([^\]]+)\]\(([^\)]+)\)", mem_text)
    md_local_links = [(t, u) for t, u in md_links if u.endswith(".md") and not u.startswith("http")]

    # Référencés (par nom de fichier)
    referenced = set()
    for _, u in md_local_links:
        referenced.add(Path(u).name)

    # Orphelins = fichiers non référencés
    orphans = sorted([f for f in all_files if f not in referenced])

    # Liens cassés = liens pointant vers un fichier qui n'existe pas
    existing_files = set(all_files) | {"MEMORY.md"}
    broken_links = sorted(
        [(t, u) for t, u in set(md_local_links) if Path(u).name not in existing_files]
    )

    size_bytes = mem_file.stat().st_size
    line_count = mem_text.count("\n") + (1 if mem_text and not mem_text.endswith("\n") else 0)

    coverage_pct = (100.0 * len(referenced) / len(all_files)) if all_files else 100.0

    max_bytes = None if args.no_max_bytes else args.max_bytes
    alert_bytes = int(max_bytes * ALERT_RATIO) if max_bytes is not None else None
    size_alert = alert_bytes is not None and size_bytes > alert_bytes

    report = {
        "memory_file": str(mem_file),
        "size_bytes": size_bytes,
        "line_count": line_count,
        "total_files": len(all_files),
        "referenced_files": len(referenced),
        "orphan_files": orphans,
        "orphan_count": len(orphans),
        "broken_links": broken_links,
        "broken_link_count": len(broken_links),
        "coverage_pct": coverage_pct,
        "max_bytes": max_bytes,
        "alert_bytes": alert_bytes,
        "size_alert": size_alert,
        "verdict": "OK" if not orphans and not broken_links else "FAIL",
    }

    if max_bytes is not None and size_bytes > max_bytes:
        report["verdict"] = "FAIL_OVERSIZE"

    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
    else:
        print(f"MEMORY.md: {mem_file}")
        print(f"  taille: {size_bytes} octets, {line_count} lignes")
        if max_bytes is not None:
            print(f"  plafond: {max_bytes} octets, alerte 90%: {alert_bytes} octets")
        print(f"  couverture: {len(referenced)}/{len(all_files)} = {coverage_pct:.1f}%")
        print(f"  orphelins: {len(orphans)}")
        if orphans:
            for f in orphans[:5]:
                print(f"    - {f}")
            if len(orphans) > 5:
                print(f"    ... ({len(orphans) - 5} de plus)")
        print(f"  liens cassés: {len(broken_links)}")
        if broken_links:
            for t, u in broken_links[:5]:
                print(f"    - [{t}]({u})")
        if size_alert:
            print(
                f"  ATTENTION taille: {size_bytes} > {alert_bytes} octets "
                "(90 % du plafond #4204) -- consolider avant le durcissement"
            )
        print(f"  verdict: {report['verdict']}")

    return 0 if report["verdict"] == "OK" else 1


if __name__ == "__main__":
    sys.exit(main())
