#!/usr/bin/env python3
"""remeasure_bad_pending.py -- issue #12389 acceptance #2.

Re-mesure le plateau des PRs ouvertes : bad (checks rouges après dedupe),
pending (checks pas encore verdict), et PR sans defaut (zero bad). Appelle
`pr_gate.classify()` directement (acceptance #3), ne ré-implémente PAS ses
règles (c'est l'omission qui a produit le faux chiffre 83/171 c.833).

Usage:
    python scripts/remeasure_bad_pending.py [--json] [--limit N]

Output:
    Tableau récapitulatif + liste des PR sans defaut.
"""

import argparse
import json
import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(__file__))
from pr_gate import dedupe_latest, classify


def fetch_check_runs(pr_number: int, head_sha: str) -> list:
    """Récupère les check-runs d'un PR via gh CLI (pas d'auth requise)."""
    result = subprocess.run(
        ["gh", "api", f"repos/jsboige/CoursIA/commits/{head_sha}/check-runs",
         "--paginate", "--jq", ".check_runs[]"],
        capture_output=True, text=True, encoding='utf-8', errors='replace', check=True,
    )
    runs = []
    for line in result.stdout.strip().split("\n"):
        if not line.strip():
            continue
        try:
            d = json.loads(line)
        except json.JSONDecodeError:
            continue
        # dedupe_latest lit `name`, `status`, `conclusion`, et utilise des
        # methodes `.get()` -> on garde un dict minimal, pas un objet.
        runs.append({
            "name": d.get("name", ""),
            "status": d.get("status", "completed"),
            "conclusion": d.get("conclusion", ""),
        })
    return runs


def list_open_prs(limit: int = 200) -> list:
    """Liste les PRs ouvertes avec head sha."""
    result = subprocess.run(
        ["gh", "pr", "list", "--state", "open", "--limit", str(limit),
         "--json", "number,headRefOid,headRefName,title"],
        capture_output=True, text=True, encoding='utf-8', errors='replace', check=True,
    )
    return json.loads(result.stdout)


def main():
    parser = argparse.ArgumentParser(description="Re-mesure plateau PRs ouvertes (#12389)")
    parser.add_argument("--json", action="store_true", help="Output JSON")
    parser.add_argument("--limit", type=int, default=200, help="Limite PRs à scanner")
    args = parser.parse_args()

    prs = list_open_prs(args.limit)
    if not args.json:
        print(f"PR ouvertes scannées: {len(prs)}")

    total_bad = 0
    total_pending = 0
    total_advisory = 0
    prs_sans_defaut = []
    par_check = {}
    par_pr = {}

    for pr in prs:
        head_sha = pr["headRefOid"]
        pr_number = pr["number"]
        try:
            runs = fetch_check_runs(pr_number, head_sha)
        except subprocess.CalledProcessError:
            continue
        latest = dedupe_latest(runs)
        pending, bad, ok, advisory = classify(latest, self_name="PR gate")
        # Ignorer les checks en pending (jamais rendu)
        bad_count = len(bad)
        advisory_count = len(advisory)
        if bad_count == 0:
            prs_sans_defaut.append({
                "number": pr_number,
                "headRefName": pr["headRefName"],
                "title": pr["title"],
            })
        total_bad += bad_count
        total_pending += len(pending)
        total_advisory += advisory_count
        par_pr[pr_number] = bad_count
        for b in bad:
            par_check[b] = par_check.get(b, 0) + 1

    if args.json:
        print(json.dumps({
            "prs_total": len(prs),
            "bad_total": total_bad,
            "pending_total": total_pending,
            "advisory_total": total_advisory,
            "prs_sans_defaut_count": len(prs_sans_defaut),
            "prs_sans_defaut": prs_sans_defaut,
            "par_check": par_check,
            "par_pr": par_pr,
        }, indent=2, ensure_ascii=False))
        return

    print()
    print(f"PRs scannées              : {len(prs)}")
    print(f"checks bad (post-dedupe)  : {total_bad}")
    print(f"checks pending            : {total_pending}")
    print(f"checks advisory (non-bloquants) : {total_advisory}")
    print(f"PRs sans aucun défaut     : {len(prs_sans_defaut)} / {len(prs)} ({len(prs_sans_defaut) * 100 // max(len(prs), 1)}%)")
    print()
    print("Top 10 checks bad (par nom):")
    for name, n in sorted(par_check.items(), key=lambda x: -x[1])[:10]:
        print(f"  {n:3d}  {name}")
    print()
    print(f"Liste des {len(prs_sans_defaut)} PRs sans défaut :")
    for pr in prs_sans_defaut[:30]:
        print(f"  #{pr['number']:5d}  {pr['headRefName']}")
    if len(prs_sans_defaut) > 30:
        print(f"  ... +{len(prs_sans_defaut) - 30} autres")


if __name__ == "__main__":
    main()