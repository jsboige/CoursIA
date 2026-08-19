#!/usr/bin/env python3
"""Mesure de la classe #11725 : chemins machine dans les SORTIES commitees.

`D:\\Dev\\...`, `C:\\Users\\...` imprimés par un notebook (env_path absolu,
`Path.cwd()`, `os.path.abspath`, `__file__`, chemin de modele local,
`FileNotFoundError`...) leake le layout disque de l'auteur. Le pre-commit
`strip_machine_paths.py` n'attrape que le nom d'utilisateur .NET ;
`detect_papermill_path_leak.py` ne lit que la metadata papermill. Aucun
organe ne mesurait la classe dans les outputs eux-memes -- le compte de
l'issue etait a re-mesurer a la main au lieu d'etre rejoue.

Ce scanner rend le compte reproductible (acceptance #1 de #11725). Il lit
EXCLUSIVEMENT les outputs (`text`, `data['text/*']`, `traceback`) -- jamais
les sources : un chemin dans une source est un choix d'auteur, dans une
sortie c'est un residu d'execution.

Advisory par defaut (exit 0) : l'issue pose une decroissance **par
attrition** au fil des re-executions faites pour d'autres motifs, pas un
rollout frontal. `--check` existe pour un futur gate CI.

Usage
-----

    # Mesure par defaut (GenAI, racine de l'issue)
    python scan_machine_path_outputs.py

    # Chemin arbitraire
    python scan_machine_path_outputs.py MyIA.AI.Notebooks/GenAI/Audio

    # JSON structure pour tooling en aval
    python scan_machine_path_outputs.py --json

    # CI dry-run (exit 1 si non-nul)
    python scan_machine_path_outputs.py --check

Acceptance (#11725)
- [x] Le scan devient reproductible (ce script, sortie JSON + compacte)
- [x] Le compte se re-mesure au lieu de se recopier
"""
import argparse
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

# Drive letter + antislash + racine layout-auteur. Equivalent au pattern de
# reproduction de l'issue (`[A-Za-z]:` + chr(92)*2 + `(?:Dev|dev|Users|MyIA)`
# avec re.I) : deux antislashs en regex = un antislash litteral dans le texte
# parse du notebook.
MACHINE_PATH_RE = re.compile(r"[A-Za-z]:\\(?:Dev|dev|Users|MyIA)", re.IGNORECASE)

SKIP_DIRS = {".ipynb_checkpoints", ".lake", "_archives", "node_modules"}


def iter_output_texts(outputs):
    """Genere chaque chaine de sortie d'une liste d'outputs ipynb.

    Couvre les trois surfaces portees par l'issue : `text` (stream/error
    implicite via execute_result texte brut), `data['text/*']`, `traceback`.
    Les outputs binaires (images...) n'ont pas de texte a fuiter.
    """
    for out in outputs:
        if not isinstance(out, dict):
            continue
        text = out.get("text")
        if isinstance(text, str):
            yield text
        elif isinstance(text, list):
            for piece in text:
                if isinstance(piece, str):
                    yield piece
        data = out.get("data")
        if isinstance(data, dict):
            for key, value in data.items():
                if not key.startswith("text/"):
                    continue
                if isinstance(value, str):
                    yield value
                elif isinstance(value, list):
                    for piece in value:
                        if isinstance(piece, str):
                            yield piece
        tb = out.get("traceback")
        if isinstance(tb, list):
            for piece in tb:
                if isinstance(piece, str):
                    yield piece


def scan_notebook(nb_path: Path):
    """Retourne la liste des occurrences (prefix, snippet) d'un notebook."""
    hits = []
    try:
        nb = json.loads(nb_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError, OSError):
        return hits
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        for text in iter_output_texts(cell.get("outputs", [])):
            for m in MACHINE_PATH_RE.finditer(text):
                start = max(0, m.start() - 30)
                end = min(len(text), m.end() + 40)
                snippet = text[start:end].replace("\n", " ")
                hits.append({
                    "prefix": m.group(0).upper(),
                    "snippet": snippet,
                })
    return hits


def scan_tree(root: Path):
    """Scanne les .ipynb d'une racine. Retourne l'inventaire structure."""
    notebooks = {}
    scanned = 0
    for nb_path in sorted(root.rglob("*.ipynb")):
        if any(part in SKIP_DIRS for part in nb_path.parts):
            continue
        scanned += 1
        hits = scan_notebook(nb_path)
        if hits:
            # Chemin relatif a la racine : sortie portable (independante du
            # worktree/clone qui execute le scan) et famille derivable.
            notebooks[str(nb_path.relative_to(root)).replace("\\", "/")] = hits
    by_prefix = Counter()
    by_family = defaultdict(Counter)
    for nb, hits in notebooks.items():
        for hit in hits:
            by_prefix[hit["prefix"]] += 1
            family = "/".join(nb.split("/")[:-1]) or "(racine)"
            by_family[family][nb] += 1
    return {
        "root": str(root),
        "scanned": scanned,
        "notebooks_with_hits": len(notebooks),
        "occurrences": sum(len(h) for h in notebooks.values()),
        "by_prefix": dict(by_prefix.most_common()),
        "by_family": {
            fam: {"notebooks": len(counts), "occurrences": sum(counts.values())}
            for fam, counts in sorted(
                by_family.items(),
                key=lambda kv: -sum(kv[1].values()),
            )
        },
        "notebooks": notebooks,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--json", action="store_true", help="Sortie JSON structuree")
    parser.add_argument("--check", action="store_true",
                        help="Exit 1 si occurrences > 0 (futur CI bloquant)")
    parser.add_argument("paths", nargs="*",
                        help="Racines a scanner (defaut: MyIA.AI.Notebooks/GenAI)")
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[2]
    roots = [repo_root / p for p in args.paths] if args.paths else [
        repo_root / "MyIA.AI.Notebooks" / "GenAI"
    ]
    inventories = [scan_tree(root) for root in roots]
    combined = {
        "scanned": sum(inv["scanned"] for inv in inventories),
        "notebooks_with_hits": sum(inv["notebooks_with_hits"] for inv in inventories),
        "occurrences": sum(inv["occurrences"] for inv in inventories),
        "by_prefix": dict(sum((Counter(inv["by_prefix"]) for inv in inventories),
                              Counter()).most_common()),
        "trees": inventories,
    }

    if args.json:
        print(json.dumps(combined, indent=2, ensure_ascii=False))
    else:
        print(f"scanned={combined['scanned']} "
              f"notebooks_with_hits={combined['notebooks_with_hits']} "
              f"occurrences={combined['occurrences']}")
        for prefix, count in combined["by_prefix"].items():
            print(f"  {prefix}: {count}")
        for tree in combined["trees"]:
            for fam, stats in list(tree["by_family"].items())[:10]:
                print(f"  {fam}: {stats['notebooks']} notebooks, "
                      f"{stats['occurrences']} occurrences")

    if args.check and combined["occurrences"] > 0:
        print(f"FAIL: {combined['occurrences']} machine-path occurrences "
              f"remain (#11725)", file=sys.stderr)
        sys.exit(1)
    sys.exit(0)


if __name__ == "__main__":
    main()
