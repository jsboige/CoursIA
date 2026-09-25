#!/usr/bin/env python3
"""detect_granular_cadrage.py -- issue #15573

Instrument de detection des issues dont le cadrage prescrit un grain
unitaire (par fichier / notebook / lake / entree / serie). Sortie:
liste structuree (number, motif, extrait) pour signal de couverture
futur dans le picker, et table de recension pour le ledger.

Pas une introspection semantique : regex explicites sur titre+body,
avec marge d'erreur documentee.

Usage :
    python scripts/audit/detect_granular_cadrage.py [--limit N] [--json]
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class GranularHit:
    number: int
    pattern: str
    title: str
    excerpt: str


# Motifs nominaux (mesure du 2026-09-22 sur 400 issues : 32 hits).
# Chaque motif cite la phrase du cadrage qu'il detecte. Un meme issue
# peut etre touche par plusieurs motifs : on garde le premier match
# pour eviter le double-comptage.
PATTERNS: tuple[tuple[str, str], ...] = (
    # Cadrage explicite par item unitaire
    (r"une PR par (fichier|notebook|lake|entree|dossier|serie|cas|note|sous[\-_ ]grain|etape|domaine)", "cadrage-par-item"),
    (r"une note par", "cadrage-par-item"),
    (r"pour chaque (fichier|notebook|lake|entree|serie|domaine)", "pour-chaque"),
    (r"par item", "par-item"),
    (r"one PR per (file|notebook|lake|item)", "one-pr-per"),
    # Liste qui se lit comme une liste de PRs
    (r"liste de PRs?", "liste-de-prs"),
    # Demande explicite de decoupage
    (r"couper en (\d+|plusieurs) PR", "couper-en-N"),
    # Tranches specifiques (deaccent, mermaid, etc.) avec compte explicite
    (r"sweep .* (\d+) fichiers", "sweep-N-fichiers"),
)


def fetch_open_issues(limit: int) -> list[dict]:
    """Recupere les issues ouvertes via gh CLI."""
    cmd = [
        "gh", "issue", "list",
        "--state", "open",
        "--limit", str(limit),
        "--json", "number,title,body",
    ]
    out = subprocess.check_output(cmd, text=True, encoding="utf-8", errors="replace")
    return json.loads(out)


def detect(text: str) -> tuple[str, str] | None:
    """Renvoie (motif, extrait) si un motif correspond, sinon None."""
    for pattern, label in PATTERNS:
        m = re.search(pattern, text, re.IGNORECASE)
        if m:
            # extrait : 80 chars autour du match
            start = max(0, m.start() - 20)
            end = min(len(text), m.end() + 60)
            excerpt = text[start:end].replace("\n", " ").strip()
            return label, excerpt
    return None


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("--")[0].strip())
    p.add_argument("--limit", type=int, default=400, help="Nombre max d issues a scanner (defaut 400)")
    p.add_argument("--json", action="store_true", help="Sortie JSON structuree")
    p.add_argument("--sample", type=int, default=10, help="Taille echantillon en mode texte (defaut 10)")
    args = p.parse_args(argv)

    issues = fetch_open_issues(args.limit)
    hits: list[GranularHit] = []
    for issue in issues:
        text = (issue.get("title") or "") + "\n" + (issue.get("body") or "")
        result = detect(text)
        if result is None:
            continue
        label, excerpt = result
        hits.append(GranularHit(
            number=issue["number"],
            pattern=label,
            title=(issue.get("title") or "")[:100],
            excerpt=excerpt[:120],
        ))

    if args.json:
        print(json.dumps({
            "scanned": len(issues),
            "hits": len(hits),
            "taux": round(len(hits) / max(1, len(issues)), 4),
            "issues": [asdict(h) for h in hits],
        }, ensure_ascii=False, indent=2))
        return 0

    print(f"# detect_granular_cadrage -- {len(hits)} hits / {len(issues)} scanned ({100 * len(hits) / max(1, len(issues)):.1f}%)")
    print()
    for h in hits[:args.sample]:
        print(f"  #{h.number} [{h.pattern}] {h.title}")
        print(f"      {h.excerpt}")
    if len(hits) > args.sample:
        print(f"  ... +{len(hits) - args.sample} autres (utiliser --json ou --sample N)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
