#!/usr/bin/env python3
"""La PRISE EN CHARGE d'un grain : qualifier avant d'agir.

Le tirage propose un ordre sur toutes les issues ouvertes ; ce module est le
temps d'ACTION : la lane qualifie le grain qu'elle engage a prendre -- son
corps, son fil complet, et la re-decision des neuf regles d'ecart -- avant de
le reclamer.

Usage :

    python scripts/coordination/tapis_prise_en_charge.py --issue 17397
    python scripts/coordination/tapis_prise_en_charge.py --issues 17397 27241

Sortie : un rapport JSON (`servis`, `ecartees` avec code et motif, appels,
secondes). Une exclusion n'est jamais silencieuse.
"""
from __future__ import annotations

import sys
import time
from datetime import UTC, datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import gh_bulk, gh_selection, tapis_qualification as tq
from coordination.tapis_marqueurs import _iso


def main(argv: list[str] | None = None, run=gh_bulk.run_defaut,
         maintenant: datetime | None = None) -> int:
    """La qualification de la prise en charge : un ou plusieurs issues."""
    import argparse
    import json

    p = argparse.ArgumentParser(
        description="Qualifie un grain pris en charge : corps, fil complet, decision.")
    p.add_argument("--issue", type=int, action="append", default=[],
                   help="numero d'issue a qualifier (repetable)")
    p.add_argument("--issues", type=int, nargs="*", default=[],
                   help="liste d'issues a qualifier, dans l'ordre")
    p.add_argument("--lane", default="", help="machine:workspace (pour les regles)")
    p.add_argument("--jours", type=int, default=45)
    p.add_argument("--budget-s", type=float, default=gh_selection.MUR_GLOBAL_S)
    p.add_argument("--json", action="store_true")
    args = p.parse_args(argv)
    candidats = list(args.issue) + list(args.issues)
    if not candidats:
        print("Aucun issue a qualifier (--issue N).", file=sys.stderr)
        return 2
    depot = Path(__file__).resolve().parents[2]
    maintenant = maintenant or datetime.now(UTC)
    debut = time.monotonic()
    citations = gh_bulk.lire_citations_mergees(depot, args.jours, run)
    prs = gh_bulk.lire_prs_ouvertes(run)
    servis, ecartees, echecs, arrete, appels = tq.qualifier(
        candidats, args.lane, maintenant, args.jours, prs, citations, run,
        debut + args.budget_s)
    rapport = {
        "lane": args.lane, "maintenant": _iso(maintenant),
        "qualifies": len(candidats), "servis": len(servis),
        "rejets": len(ecartees), "illisibles": echecs,
        "appels": appels, "secondes": round(time.monotonic() - debut, 1),
        "budget_epuise": arrete,
        "grains": [{"numero": e.numero, "titre": e.titre,
                    "visites": e.visites, "consolidation": e.consolidation,
                    "conteneur": e.conteneur, "notes": e.notes}
                   for e in servis],
        "ecartees": list(ecartees.values()),
    }
    out = json.dumps(rapport, ensure_ascii=False, indent=1)
    sys.stdout.buffer.write((out + "\n").encode("utf-8"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
