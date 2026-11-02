#!/usr/bin/env python3
"""check_memory_index_coverage.py -- organe de couverture du MEMORY.md per-machine.

Implémente l'acceptance de #17885 (consolider MEMORY.md en grappes, 0 orphelin,
0 lien mort) :

  - 0 orphelin : tout fichier .md du dossier memory/ (hors MEMORY.md lui-même)
                 est atteignable depuis MEMORY.md.
  - 0 lien mort : tout lien local vers un .md pointe sur un fichier existant.
  - Couverture : referenced / total (sortie diagnostique).
  - Taille : rapport en octets, ligne count. Plafond par défaut 24 400 octets
             (truncation-at-load de Claude Code) ; alerte NON bloquante à 90 %
             (21 960 octets). Aligné sur roo-extensions #4204.

Trois surfaces de référencement (une fiche invisible par la mauvaise surface
n'est pas une fiche perdue) :

  - lien markdown local ``[texte](chemin.md)`` : un lien. Non résolu = lien mort.
  - wikilink ``[[nom]]`` : un lien (convention de lane). Non résolu = lien mort.
  - chemin en backticks ``annexes/xxx.md`` : un POINTEUR. Résolu, il ouvre une
    grappe ; non résolu, il est ignoré (une prose peut citer un .md du dépôt).

Un index **compacté** ne référence pas ses fiches une par une : il pointe vers
des **grappes** (annexes) qui les listent. L'acceptance Q10 du 2026-09-26 dit
explicitement « complétude et consolidation en grappes » : une fiche listée dans
une grappe joignable depuis l'index n'est pas orpheline. D'où la couverture à
deux niveaux :

  - direct      : résolu depuis MEMORY.md ;
  - via grappe  : résolu depuis une grappe joignable depuis MEMORY.md (un seul
                   saut -- `--cluster-depth` permet d'aller plus loin).

Le rapport **décompose** les deux niveaux : la couverture reste auditable, et
le verdict continue de tomber sur un vrai orphelin. Les liens morts **dans**
les grappes sont listés à part et **bloquent** aussi le verdict (0 lien mort),
mais sous une raison distincte (`fail_reasons`), jamais masqués derrière la
couverture.

Usage :

    python scripts/coordination/check_memory_index_coverage.py \\
        --memory-dir C:/Users/Jesse/.claude/projects/<hash>/memory \\
        [--json] [--max-bytes N] [--no-max-bytes] [--cluster-depth N]

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

# Les trois surfaces de référencement. Une référence qui ne résout pas est un
# lien mort pour "markdown" et "wikilink" ; pour "backtick" c'est une prose
# (le .md cité peut être celui du dépôt, hors memory/).
MD_LINK_RE = re.compile(r"\[([^\]]+)\]\(([^)]+)\)")
WIKILINK_RE = re.compile(r"\[\[([^\[\]|]+?)(?:\|[^\[\]]*)?\]\]")
BACKTICK_PATH_RE = re.compile(r"`([^`\n]*?\.md(?:#[^`\n]*)?)`")

SURFACES_LIENS = ("markdown", "wikilink")


def extract_references(text: str) -> list[tuple[str, str, str]]:
    """Références d'un document : (surface, libellé, cible brute)."""
    refs: list[tuple[str, str, str]] = []
    for label, url in MD_LINK_RE.findall(text):
        url = url.strip()
        if url.endswith(".md") and not url.startswith(("http://", "https://")):
            refs.append(("markdown", label.strip(), url))
    for name in WIKILINK_RE.findall(text):
        refs.append(("wikilink", name.strip(), name.strip()))
    for path in BACKTICK_PATH_RE.findall(text):
        refs.append(("backtick", path.strip(), path.strip()))
    return refs


class Resolver:
    """Résout une cible brute vers un fichier du dossier memory/."""

    def __init__(self, mem_dir: Path, files: list[Path]) -> None:
        self.mem_dir = mem_dir
        self.by_stem: dict[str, list[Path]] = {}
        for path in files:
            self.by_stem.setdefault(path.stem, []).append(path)

    def resolve(self, raw: str, base: Path | None = None) -> Path | None:
        """Résout une cible. `base` = dossier du document qui référence (un lien
        relatif se résout depuis son propre dossier)."""
        cible = raw.strip().split("#")[0].strip()
        if not cible or any(c in cible for c in "*?"):
            return None  # ancre seule, ou motif glob : rien à résoudre
        if "/" in cible or "\\" in cible:
            candidat = (base or self.mem_dir) / cible.replace("\\", "/")
            if candidat.is_file():
                return candidat.resolve()
            return None
        for racine in (base, self.mem_dir):
            if racine is None:
                continue
            for candidat in (racine / cible, racine / (cible + ".md")):
                if candidat.is_file():
                    return candidat.resolve()
        stem = cible[:-3] if cible.endswith(".md") else cible
        hits = self.by_stem.get(stem, [])
        if len(hits) == 1:
            return hits[0].resolve()
        return None


def _collect(
    texte: str, resolver: Resolver, mem_dir: Path, base: Path | None = None
) -> tuple[set[str], set[Path], list[tuple[str, str, str]]]:
    """Références d'un document : (fiches directes, grappes, liens morts)."""
    fiches: set[str] = set()
    grappes: set[Path] = set()
    morts: list[tuple[str, str, str]] = []
    for surface, libelle, cible in extract_references(texte):
        resolu = resolver.resolve(cible, base)
        if resolu is None:
            if surface in SURFACES_LIENS:
                morts.append((surface, libelle, cible))
            continue
        if resolu.parent == mem_dir:
            fiches.add(resolu.name)
        else:
            grappes.add(resolu)
    return fiches, grappes, morts


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
    p.add_argument(
        "--cluster-depth",
        type=int,
        default=1,
        help="profondeur de résolution depuis une grappe joignable (défaut 1 = un seul saut)",
    )
    p.add_argument(
        "--strict-direct",
        action="store_true",
        help=(
            "n'accepte que le référencement DIRECT (sémantique d'origine : chaque "
            "fiche doit être citée par MEMORY.md elle-même). Les grappes ne "
            "couvrent plus rien — le critère n'est pas relâché, il est mesuré "
            "dans les deux modes."
        ),
    )
    args = p.parse_args()

    mem_dir: Path = args.memory_dir.resolve()
    mem_file = mem_dir / "MEMORY.md"

    if not mem_file.is_file():
        print(f"FATAL: {mem_file} introuvable", file=sys.stderr)
        return 2

    mem_text = mem_file.read_text(encoding="utf-8")

    # Les fiches sont les .md à la racine du dossier memory/ ; les .md rangés
    # dans un sous-dossier sont des GRAPPES (annexes, digests) : ce sont des
    # conteneurs, pas des unités de connaissance.
    all_files = sorted(p for p in mem_dir.glob("*.md") if p.stem != "MEMORY")
    cluster_files = sorted(p for p in mem_dir.rglob("*.md") if p.parent != mem_dir and p.stem != "MEMORY")
    resolver = Resolver(mem_dir, all_files + cluster_files)

    # Niveau 1 : ce que MEMORY.md atteint lui-même.
    direct_fiches, grappes_niveau1, morts_index = _collect(mem_text, resolver, mem_dir)

    # Niveau 2 : ce qu'atteignent les grappes joignables (un saut par défaut).
    via_fiches: set[str] = set()
    morts_clusters: list[tuple[str, str, str, str]] = []
    grappes_atteignables: set[Path] = set(grappes_niveau1)
    frontiere = set(grappes_niveau1)
    for _ in range(max(0, args.cluster_depth)):
        if not frontiere:
            break
        suivants: set[Path] = set()
        for grappe in sorted(frontiere):
            fiches, sous_grappes, morts = _collect(
                grappe.read_text(encoding="utf-8"), resolver, mem_dir, base=grappe.parent
            )
            via_fiches |= fiches
            morts_clusters.extend((grappe.name, *m) for m in morts)
            suivants |= sous_grappes - grappes_atteignables
        grappes_atteignables |= suivants
        frontiere = suivants

    covered = direct_fiches | via_fiches
    # Mode strict : seule la référence directe vaut couverture (sémantique
    # d'origine de l'organe). Par défaut, une fiche listée dans une grappe
    # joignable est couverte — c'est la forme que l'arbitrage Q10 autorise.
    effectif = direct_fiches if args.strict_direct else covered
    orphan_files = sorted(f.name for f in all_files if f.name not in effectif)

    cluster_names = {p.name for p in cluster_files}
    cluster_reachable = {p.name for p in grappes_atteignables}
    clusters_unreachable = sorted(cluster_names - cluster_reachable)

    size_bytes = mem_file.stat().st_size
    line_count = mem_text.count("\n") + (1 if mem_text and not mem_text.endswith("\n") else 0)

    coverage_pct = (100.0 * len(effectif) / len(all_files)) if all_files else 100.0
    grappe_coverage_pct = (100.0 * len(covered) / len(all_files)) if all_files else 100.0

    max_bytes = None if args.no_max_bytes else args.max_bytes
    alert_bytes = int(max_bytes * ALERT_RATIO) if max_bytes is not None else None
    size_alert = alert_bytes is not None and size_bytes > alert_bytes

    fail_reasons: list[str] = []
    if orphan_files:
        fail_reasons.append("orphelins")
    if morts_index:
        fail_reasons.append("liens_morts_index")
    if morts_clusters:
        fail_reasons.append("liens_morts_grappes")

    report = {
        "memory_file": str(mem_file),
        "size_bytes": size_bytes,
        "line_count": line_count,
        "total_files": len(all_files),
        "referenced_files": len(effectif),
        "direct_referenced_files": len(direct_fiches),
        "via_cluster_referenced_files": len(via_fiches - direct_fiches),
        "cluster_referenced_files": len(covered),
        "strict_direct": args.strict_direct,
        "grappe_coverage_pct": grappe_coverage_pct,
        "orphan_files": orphan_files,
        "orphan_count": len(orphan_files),
        "broken_links": [(lab, tgt) for (_surf, lab, tgt) in morts_index],
        "broken_link_count": len(morts_index),
        "broken_link_details": [
            {"surface": surf, "label": lab, "target": tgt} for (surf, lab, tgt) in morts_index
        ],
        "cluster_broken_links": [(lab, tgt) for (_src, _surf, lab, tgt) in morts_clusters],
        "cluster_broken_link_count": len(morts_clusters),
        "cluster_broken_link_details": [
            {"source": src, "surface": surf, "label": lab, "target": tgt}
            for (src, surf, lab, tgt) in morts_clusters
        ],
        "cluster_files_present": len(cluster_names),
        "cluster_files_reachable": len(cluster_reachable),
        "cluster_files_unreachable": clusters_unreachable,
        "cluster_depth": args.cluster_depth,
        "coverage_pct": coverage_pct,
        "max_bytes": max_bytes,
        "alert_bytes": alert_bytes,
        "size_alert": size_alert,
        "fail_reasons": fail_reasons,
        "verdict": "OK" if not fail_reasons else "FAIL",
    }

    if max_bytes is not None and size_bytes > max_bytes:
        report["verdict"] = "FAIL_OVERSIZE"
        report["fail_reasons"] = ["taille"] + fail_reasons

    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
    else:
        print(f"MEMORY.md: {mem_file}")
        print(f"  taille: {size_bytes} octets, {line_count} lignes")
        if max_bytes is not None:
            print(f"  plafond: {max_bytes} octets, alerte 90%: {alert_bytes} octets")
        mode = "strict direct" if args.strict_direct else "grappes acceptées"
        print(
            f"  couverture: {len(effectif)}/{len(all_files)} = {coverage_pct:.1f}%"
            f" (direct {len(direct_fiches)}, via grappes {len(via_fiches - direct_fiches)})"
            f" — mode: {mode}"
        )
        print(
            f"  grappes: {len(cluster_reachable)}/{len(cluster_names)} joignables"
            f" (profondeur {args.cluster_depth})"
        )
        print(f"  orphelins: {len(orphan_files)}")
        if orphan_files:
            for f in orphan_files[:5]:
                print(f"    - {f}")
            if len(orphan_files) > 5:
                print(f"    ... ({len(orphan_files) - 5} de plus)")
        print(f"  liens cassés (index): {len(morts_index)}")
        for surf, libelle, cible in morts_index[:5]:
            print(f"    - [{surf}] {libelle} -> {cible}")
        if len(morts_index) > 5:
            print(f"    ... ({len(morts_index) - 5} de plus)")
        print(f"  liens cassés (grappes): {len(morts_clusters)}")
        for src, surf, libelle, cible in morts_clusters[:5]:
            print(f"    - [{src}] [{surf}] {libelle} -> {cible}")
        if len(morts_clusters) > 5:
            print(f"    ... ({len(morts_clusters) - 5} de plus)")
        if clusters_unreachable:
            print(f"  grappes non joignables: {len(clusters_unreachable)}")
            for nom in clusters_unreachable[:5]:
                print(f"    - {nom}")
            if len(clusters_unreachable) > 5:
                print(f"    ... ({len(clusters_unreachable) - 5} de plus)")
        if size_alert:
            print(
                f"  ATTENTION taille: {size_bytes} > {alert_bytes} octets "
                "(90 % du plafond #4204) -- consolider avant le durcissement"
            )
        print(f"  verdict: {report['verdict']}")
        if report["fail_reasons"]:
            print(f"  raisons: {', '.join(report['fail_reasons'])}")

    return 0 if report["verdict"] == "OK" else 1


if __name__ == "__main__":
    sys.exit(main())
