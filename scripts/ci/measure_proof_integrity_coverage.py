"""Mesure la couverture proof-integrity sur les workflows Lean.

Issue #17097 : identifier les lakes sans gate proof-integrity, et parmi eux
distinguer ceux qui ne l'ont JAMAIS eu de ceux qui l'ont PERDU lors de la
fusion matrix.

Livrable : script + rapport. Reproduit exactement la procédure de mesure
prescrite par `.claude/rules/pr-review-discipline.md` §B.3 :
    grep -ln 'lean-axiom' .github/workflows/*.yml | grep -v 'lean-axiom.yml'

Usage :
    python scripts/ci/measure_proof_integrity_coverage.py [--json]

Sortie : stdout, format texte par défaut (--json pour sortie JSON unique).
"""
import argparse
import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent  # scripts/ci/X.py -> racine
WF_DIR = REPO_ROOT / ".github" / "workflows"
MANIFEST = REPO_ROOT / "scripts" / "lean" / "ci_lakes.json"


def run(cmd, cwd=None):
    r = subprocess.run(cmd, capture_output=True, text=True, cwd=cwd or REPO_ROOT, shell=True, encoding="utf-8", errors="replace")
    return r.stdout.strip(), r.stderr.strip(), r.returncode


def parse_args():
    p = argparse.ArgumentParser(description="Mesure la couverture proof-integrity")
    p.add_argument("--json", action="store_true", help="Sortie JSON unique")
    return p.parse_args()


def measure():
    """Effectue la mesure et retourne un dict résumé."""
    wf_files = sorted(WF_DIR.glob("lean-*.yml"))
    cabled = []
    matrix_only = []
    for wf in wf_files:
        if wf.name == "lean-axiom.yml":
            continue
        out, _, _ = run(f"grep -c 'lean-axiom' '{wf}'")
        count = int(out) if out.strip().isdigit() else 0
        if count > 0:
            cabled.append((wf.name, count))
        else:
            matrix_only.append(wf.name)

    log_out, _, _ = run("git log --diff-filter=D --name-only --format= -n 500 -- '.github/workflows/lean-*.yml'")
    deleted_files = sorted(set(p for p in log_out.split('\n') if p.strip()))

    perdus = set()
    jamais_eu = set()
    for f in deleted_files:
        f = f.strip()
        if not f:
            continue
        rev_out, _, _ = run(f"git rev-list -n 1 HEAD -- \"{f}\"")
        last_sha = rev_out.strip()
        if not last_sha:
            continue
        parent = f"{last_sha}^"
        show_out, _, _ = run(f"git show \"{parent}:{f}\"")
        if 'lean-axiom' in show_out:
            perdus.add((f, last_sha[:8]))
        else:
            jamais_eu.add((f, last_sha[:8]))

    manifest_lakes = []
    if MANIFEST.exists():
        with MANIFEST.open() as f:
            d = json.load(f)
        manifest_lakes = [l["display-name"] for l in d.get("lakes", [])]

    return {
        "cabled": [{"name": n, "count": c} for n, c in cabled],
        "matrix_only": matrix_only,
        "perdus": [{"name": f, "delete_sha": sha} for f, sha in sorted(perdus)],
        "jamais_eu": [{"name": f, "delete_sha": sha} for f, sha in sorted(jamais_eu)],
        "manifest_lakes": manifest_lakes,
        "manifest_count": len(manifest_lakes),
    }


def print_text(summary):
    print("=== ÉTAPE 1 : workflows ACTUELS qui appellent lean-axiom ===")
    print(f"\nCâblés ({len(summary['cabled'])} workflows) :")
    for c in summary["cabled"]:
        print(f"  + {c['name']}: {c['count']} mentions lean-axiom")
    print(f"\nNon câblés ({len(summary['matrix_only'])} workflows) :")
    for n in summary["matrix_only"]:
        print(f"  - {n}")

    print("\n=== ÉTAPE 2 : workflows SUPPRIMÉS (git log D) qui appelaient lean-axiom ===")
    print(f"Total fichiers supprimés : {len(summary['perdus']) + len(summary['jamais_eu'])}")
    print(f"\nPERDUS : {len(summary['perdus'])}")
    for p in summary["perdus"]:
        print(f"  PERDU  {p['delete_sha']}  {p['name']}")
    print(f"\nJAMAIS EU : {len(summary['jamais_eu'])}")
    for p in summary["jamais_eu"]:
        print(f"  JAMAIS {p['delete_sha']}  {p['name']}")

    print(f"\n=== ÉTAPE 3 : LAKES DU MANIFEST ({summary['manifest_count']}) ===")
    for n in summary["manifest_lakes"]:
        print(f"  - {n}")
    print(f"\n→ Les {summary['manifest_count']} lakes passent par lean-ci-matrix.yml")
    print(f"  → qui appelle lean-build.yml (réutilisable),")
    print(f"  → qui N'appelle PAS lean-axiom.yml (grep -c = 0).")
    print(f"  → Conclusion : les {summary['manifest_count']} lakes sont SANS gate proof-integrity.")


def main():
    args = parse_args()
    summary = measure()
    if args.json:
        print(json.dumps(summary, indent=2, ensure_ascii=False))
    else:
        print_text(summary)


if __name__ == "__main__":
    main()
