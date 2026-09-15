#!/usr/bin/env python3
"""
scan_z3linq_upstream.py -- scan structuré des PRs endjin/Z3.Linq vs fork MyIntelligenceAgency/Z3.Linq.

Sortie : tableau JSON par PR avec verdict préliminaire + chemins de fichiers touchés
(fork vs amont). Le verdict definitif (REDONDANT/DIVERGENT/NOUVEAU-POUR-NOUS) demande
une lecture du diff et du code fork -- ce script NE LE FAIT PAS, il produit le
squelette de comparaison que G1-bis remplira.

EPIC parent : #14169 (Z3.Linq amont se remet en mouvement)
Sous-grain   : #16050 (G1 mesurer le recouvrement)
Lane         : myia-po-2027:CoursIA-2

Usage :
    python scripts/smt/scan_z3linq_upstream.py --prs 44,45,47,...,99 --out JSON
    python scripts/smt/scan_z3linq_upstream.py --pr-list 28prs.txt --out JSON

Rapport G1 depose sur le dashboard RooSync workspace CoursIA (cf PR body), pas dans le repo (harness-hygiene).
"""
import argparse
import json
import subprocess
import sys
from pathlib import Path


# Bloc 1 -- Modernisation build (#44/#45/#47/#94)
# Bloc 2 -- Runtime Z3 (#61)
# Bloc 3 -- Suite de tests (#48/#59/#65/#67/#69/#71) -- SONT des PRs de test, exclues de G1
# Bloc 4 -- Marshalling et sortes (#73/#74/#77/#79/#80/#81/#84/#88/#90/#91/#92/#93/#95)
# Bloc 5 -- Sémantique de résolution (#86/#96/#98/#99)

DEFAULT_PRS = [
    44, 45, 47, 94, 61,
    # 48, 59, 65, 67, 69, 71 -- test-only, excluded per EPIC body
    73, 74, 77, 79, 80, 81, 84, 88, 90, 91, 92, 93, 95,
    86, 96, 98, 99,
]


def gh_api(path: str) -> dict:
    """gh api <path> --jq renvoie du JSON. Wrapper."""
    out = subprocess.check_output(
        ["gh", "api", f"repos/endjin/Z3.Linq/{path}"],
        stderr=subprocess.DEVNULL,
    )
    return json.loads(out.decode("utf-8", errors="replace"))


def fetch_pr(number: int) -> dict:
    """Métadonnées + fichiers touchés."""
    meta = gh_api(f"pulls/{number}")
    files = gh_api(f"pulls/{number}/files")
    return {
        "number": number,
        "title": meta.get("title", ""),
        "state": meta.get("state", "?"),
        "merged_at": meta.get("merged_at"),
        "files": [f["filename"] for f in files],
        "files_count": len(files),
    }


def classify_block(pr: int) -> str:
    """Bloc EPIC d'appartenance."""
    if pr in (44, 45, 47, 94):
        return "modernisation-build"
    if pr == 61:
        return "runtime-z3"
    if pr in (48, 59, 65, 67, 69, 71):
        return "tests-only-exclu"
    if pr in (73, 74, 77, 79, 80, 81, 84, 88, 90, 91, 92, 93, 95):
        return "marshalling-sortes"
    if pr in (86, 96, 98, 99):
        return "resolution-semantique"
    return "unknown"


def is_test_only(files: list[str]) -> bool:
    """Heuristique : PR dont TOUS les fichiers sont des tests."""
    if not files:
        return False
    return all(
        "Z3.Linq.Tests/" in f
        or f.startswith("tests/")
        or "/tests/" in f
        for f in files
    )


def touches_capability(files: list[str]) -> bool:
    """Heuristique : PR qui touche du code applicatif (Theorem.cs, ExpressionVisitor.cs, etc.)."""
    capability_paths = (
        "Z3.Linq/Theorem.cs",
        "Z3.Linq/Theorem{T}.cs",
        "Z3.Linq/ExpressionVisitor.cs",
        "Z3.Linq/Optimization.cs",
        "Z3.Linq/Environment.cs",
        "Z3.Linq/ISolveable{T}.cs",
        "Z3.Linq/SolveableExtensions.cs",
        "Z3.Linq/TheoremUndecidedException.cs",
        "Z3.Linq/Z3Context.cs",
    )
    return any(any(p in f for p in capability_paths) for f in files)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument(
        "--prs",
        type=str,
        default=",".join(str(n) for n in DEFAULT_PRS),
        help=f"PR numbers, comma-separated (default: {len(DEFAULT_PRS)} PRs du body EPIC #14169)",
    )
    ap.add_argument("--out", type=Path, default=None, help="Output JSON path (default: stdout)")
    args = ap.parse_args()

    prs = [int(x) for x in args.prs.split(",") if x.strip()]

    rows = []
    for n in prs:
        try:
            data = fetch_pr(n)
        except subprocess.CalledProcessError as exc:
            print(f"# PR #{n} : gh api failed: {exc}", file=sys.stderr)
            rows.append({"number": n, "error": "gh_api_failed"})
            continue

        row = {
            "number": data["number"],
            "title": data["title"],
            "state": data["state"],
            "block": classify_block(data["number"]),
            "files": data["files"],
            "files_count": data["files_count"],
            "test_only": is_test_only(data["files"]),
            "touches_capability": touches_capability(data["files"]),
            # Verdict préliminaire : à compléter par lecture de code (G1-bis)
            "verdict_preliminary": "TBD",
            "fork_equivalent": "TBD",
            "notes": "",
        }
        if row["test_only"]:
            row["verdict_preliminary"] = "EXCLU-TESTS"
            row["notes"] = "PR ajoute des tests, pas de capacité -- exclu de G1 per body EPIC"
        elif not row["touches_capability"]:
            row["verdict_preliminary"] = "INFRA"
            row["notes"] = "PR d'infrastructure (build/packaging/doc), pas de code de capacité"
        # Si touches_capability sans test_only, verdict_preliminary reste TBD
        # (à compléter G1-bis par lecture du diff + du code fork).
        rows.append(row)

    out = {
        "epic": "#14169",
        "sub_grain": "#16050 (G1)",
        "fork_pinned": "MyIntelligenceAgency/Z3.Linq @ e09dae6",
        "prs_total": len(rows),
        "verdict_summary": {
            "EXCLU-TESTS": sum(1 for r in rows if r.get("verdict_preliminary") == "EXCLU-TESTS"),
            "INFRA": sum(1 for r in rows if r.get("verdict_preliminary") == "INFRA"),
            "TBD": sum(1 for r in rows if r.get("verdict_preliminary") == "TBD"),
        },
        "rows": rows,
    }

    if args.out:
        args.out.write_text(json.dumps(out, indent=2))
        print(f"Wrote {len(rows)} rows to {args.out}", file=sys.stderr)
    else:
        print(json.dumps(out, indent=2))

    return 0


if __name__ == "__main__":
    sys.exit(main())
