#!/usr/bin/env python3
"""Couverture proof-integrity (B.3) des lakes de la matrice lean CI.

Rend la couverture du gate d'axiomes LISIBLE par un reviewer en une commande,
pour trancher B.3 (« non applicable » vs « applicable ») sans enquete :
quels lakes portent `axiom-target-modules` dans le manifeste
`scripts/lean/ci_lakes.json` (le gate tourne pour eux), lesquels sont nus,
et — pour les listes explicites — si chaque module nomme existe reellement
sous le chemin du lake (ferme le cas #8782 : un vert dont les
target-modules n'atteignent aucun module reellement modifie).

Sortie : table alignée + comptes. `--json` pour dossier/CI. Exit 0 en
lecture ; `--require-covered` durcit en gate (exit 1 si un lake est nu) —
a n'activer que lorsque le cablage progressif (#18038) est termine.

Verdicts B.3 par lake :
- WIRED      : cle presente, modules verifies sur disque (ou passe-partout)
- WIRED-DEAD : cle presente mais au moins un module nomme introuvable
               (le vert du gate ne dit alors rien des modules reels)
- BARE       : pas de cle — le step Proof integrity ne tourne pas,
               B.3 se lit « non applicable » (#8677 cas a)
"""
import argparse
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
MANIFEST = REPO_ROOT / "scripts" / "lean" / "ci_lakes.json"


def _modules_on_disk(project_path: Path) -> set:
    """Noms de modules `.lean` du lake en notation pointee (SocialChoice.Arrow),
    relative au chemin du lake — la convention du manifeste."""
    if not project_path.is_dir():
        return set()
    root = project_path
    return {
        str(p.relative_to(root).with_suffix("")).replace("\\", "/").replace("/", ".")
        for p in root.rglob("*.lean")
        if ".lake" not in p.parts
    }


def coverage_report(verify_modules: bool = True) -> dict:
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    lakes = []
    for entry in manifest["lakes"]:
        targets = (entry.get("axiom-target-modules") or "").strip()
        row = {
            "lake": entry["lake"],
            "display-name": entry.get("display-name", entry["lake"]),
            "project-path": entry.get("project-path", ""),
            "axiom-target-modules": targets or None,
            "axiom-fail-on-sorry": entry.get("axiom-fail-on-sorry"),
            "verdict": "BARE",
            "dead_modules": [],
        }
        if targets:
            row["verdict"] = "WIRED"
            if targets == "*":
                row["wildcard"] = True
            elif verify_modules:
                on_disk = _modules_on_disk(REPO_ROOT / entry["project-path"])
                dead = [m for m in targets.split(",") if m not in on_disk]
                if dead:
                    row["verdict"] = "WIRED-DEAD"
                    row["dead_modules"] = sorted(dead)
        lakes.append(row)
    counts = {}
    for row in lakes:
        counts[row["verdict"]] = counts.get(row["verdict"], 0) + 1
    return {"total": len(lakes), "counts": counts, "lakes": lakes}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--json", action="store_true", help="Sortie JSON machine-readable")
    parser.add_argument("--no-verify", action="store_true",
                        help="Sauter la verification d'existence des modules explicites")
    parser.add_argument("--require-covered", action="store_true",
                        help="Gate : exit 1 si un lake est BARE (cablage #18038 non termine)")
    args = parser.parse_args(argv)

    report = coverage_report(verify_modules=not args.no_verify)

    if args.json:
        json.dump(report, sys.stdout, ensure_ascii=False, indent=1)
        print()
        return 1 if (args.require_covered and report["counts"].get("BARE")) else 0

    counts = report["counts"]
    print(f"proof-integrity coverage — {report['total']} lakes du manifeste : "
          f"{counts.get('WIRED', 0)} wired, {counts.get('WIRED-DEAD', 0)} wired-dead, "
          f"{counts.get('BARE', 0)} bare")
    print()
    name_w = max(len(r["display-name"]) for r in report["lakes"])
    for row in report["lakes"]:
        mods = row["axiom-target-modules"]
        mod_str = ("*" if row.get("wildcard") else mods) if mods else "-"
        if len(mod_str) > 48:
            mod_str = mod_str[:45] + f"... ({len(mods.split(','))} modules)"
        print(f"  {row['verdict']:<10} {row['display-name']:<{name_w}}  {mod_str}")
        for dead in row["dead_modules"]:
            print(f"             ! module introuvable: {dead}")
    if counts.get("WIRED-DEAD"):
        print("\nWIRED-DEAD : un module nomme n'existe pas sous le chemin du lake —")
        print("le vert du gate n'atteint pas ce module (cf #8782). Corriger la cle.")
    if args.require_covered and counts.get("BARE"):
        print(f"\nFAIL: {counts['BARE']} lake(s) BARE (cablage #18038 non termine)")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
