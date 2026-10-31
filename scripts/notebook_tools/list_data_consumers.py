#!/usr/bin/env python3
"""Liste les carnets qui lisent une donnee vendoree modifiee, et signale ceux
qui ne font pas partie du meme changement.

Une resynchronisation de taxonomie (OWL/CSV vendoree) ne declenche aucun
carnet : les sorties commitees continuent de decrire les donnees d'avant,
et la prose qui les commente aussi (#20628, cas mesure Obs-04).

Modes :
  (defaut)        fichiers indexes (`git diff --cached --name-only`)
  --base REF      fichiers du changement depuis REF (`git diff REF...HEAD`)
  --advisory      toujours rc 0 : affiche la liste sans bloquer
  --json          sortie machine
  --self-test     controle positif + negatif

rc 1 quand un carnet consommateur d'une donnee modifiee n'est pas lui-meme
dans le changement. En mode pre-commit, le hook tourne en --advisory : la
liste est imprimee, aucun commit legitime n'est bloque (penurie de runners
CI, #13097 -- le hook ne consomme aucun emplacement de file).
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

# Donnees vendorees dont la mise a jour doit propager une re-execution.
DATA_PATTERNS = (
    re.compile(r"^MyIA\.AI\.Notebooks/SymbolicAI/Argument_Analysis/ontologies/.*\.owl$"),
    re.compile(r"^MyIA\.AI\.Notebooks/SymbolicAI/Argument_Analysis/data/.*taxonomy.*\.csv$"),
)
# Un carnet de traduction ou archive ne se re-execute pas avec la source.
EXCLUDED_CONSUMER = re.compile(r"(^|/)_archive/|-EN\.ipynb$")


def git(*args: str, cwd: Path | None = None) -> str:
    proc = subprocess.run(
        ["git", *args],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        cwd=str(cwd) if cwd else None,
    )
    if proc.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)}: {proc.stderr.strip()}")
    return proc.stdout


def changed_files(base: str | None, cwd: Path | None = None) -> list[str]:
    if base:
        raw = git("diff", "--name-only", "--diff-filter=ACMR", f"{base}...HEAD", cwd=cwd)
    else:
        raw = git("diff", "--cached", "--name-only", "--diff-filter=ACMR", cwd=cwd)
    return [line.strip() for line in raw.splitlines() if line.strip()]


def is_vendored_data(path: str) -> bool:
    return any(p.match(path) for p in DATA_PATTERNS)


def consumers_of(basename: str, cwd: Path | None = None) -> list[str]:
    """Carnets dont le source cite ce nom de fichier (index git, pas le disque)."""
    try:
        raw = git("grep", "-l", "-F", basename, "--", "*.ipynb", cwd=cwd)
    except RuntimeError:
        return []  # aucun consommateur : git grep rend 1 sur zero resultat
    out = []
    for line in raw.splitlines():
        path = line.split(":", 1)[1] if ":" in line else line
        path = path.strip()
        if path and not EXCLUDED_CONSUMER.search(path):
            out.append(path)
    return sorted(set(out))


def analyse(files: list[str], cwd: Path | None = None) -> dict:
    data = [f for f in files if is_vendored_data(f)]
    changed = set(files)
    report = {"data_files": [], "missing": []}
    for path in data:
        basename = Path(path).name
        cons = consumers_of(basename, cwd=cwd)
        entries = [{"notebook": c, "in_change": c in changed} for c in cons]
        report["data_files"].append({"data": path, "consumers": entries})
        report["missing"].extend(e["notebook"] for e in entries if not e["in_change"])
    report["missing"] = sorted(set(report["missing"]))
    return report


def render(report: dict) -> str:
    if not report["data_files"]:
        return ""
    lines = ["Donnee vendoree modifiee -- carnets consommateurs :"]
    for entry in report["data_files"]:
        lines.append(f"  {entry['data']}")
        if not entry["consumers"]:
            lines.append("    (aucun carnet ne la lit)")
        for c in entry["consumers"]:
            flag = "dans le changement" if c["in_change"] else "A RE-EXECUTER"
            lines.append(f"    [{flag}] {c['notebook']}")
    if report["missing"]:
        lines.append(
            "  -> re-executer les carnets marques A RE-EXECUTER dans le meme changement, "
            "ou ouvrir une issue nommee qui les liste."
        )
    return "\n".join(lines)


def self_test(cwd: Path | None = None) -> int:
    ok = True
    positive = analyse(
        ["MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/ontologies/argumentum_fallacies.owl"],
        cwd=cwd,
    )
    found = [c["notebook"] for e in positive["data_files"] for c in e["consumers"]]
    if not found:
        print("[self-test] ECHEC : aucun consommateur pour l'OWL des sophismes")
        ok = False
    else:
        print(f"[self-test] controle positif : {len(found)} consommateur(s)")
    if not positive["missing"]:
        print("[self-test] ECHEC : le controle positif ne signale aucun carnet manquant")
        ok = False
    negative = analyse(["docs/reference/common-commands.md"], cwd=cwd)
    if negative["data_files"] or negative["missing"]:
        print("[self-test] ECHEC : un fichier non vendore a produit un rapport")
        ok = False
    else:
        print("[self-test] controle negatif : aucune donnee vendoree, rc 0")
    # Deduplication : le meme carnet citant deux donnees ne compte qu'une fois.
    both = analyse(
        [
            "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/ontologies/argumentum_fallacies.owl",
            "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/data/argumentum_fallacies_taxonomy.csv",
        ],
        cwd=cwd,
    )
    if len(both["missing"]) != len(set(both["missing"])):
        print("[self-test] ECHEC : doublon dans la liste des carnets manquants")
        ok = False
    print("[self-test] " + ("OK" if ok else "ECHEC"))
    return 0 if ok else 1


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--base", default=None, help="Ref de base (defaut : fichiers indexes)")
    parser.add_argument("--advisory", action="store_true", help="Toujours rc 0 (mode hook)")
    parser.add_argument("--json", action="store_true", help="Sortie machine")
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--repo", default=None, help="Racine du depot (defaut : cwd)")
    args = parser.parse_args(argv)

    cwd = Path(args.repo) if args.repo else None
    if args.self_test:
        return self_test(cwd=cwd)

    report = analyse(changed_files(args.base, cwd=cwd), cwd=cwd)
    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
    else:
        text = render(report)
        if text:
            print(text)
    if not report["missing"]:
        return 0
    return 0 if args.advisory else 1


if __name__ == "__main__":
    sys.exit(main())
