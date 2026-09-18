#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Garde d'ancrage des cellules de densite.

Une cellule markdown qui **lit un resultat** (« Lecture du resultat »,
« Interpretation », « On observe que... ») doit etre ancree sur une cellule de
code qui porte un **output reel**. Une lecture posee sur un stub d'exercice non
rempli est doublement fautive : elle commente un resultat qui n'existe pas, et
elle divulgue la reponse a l'etudiant qui n'a pas encore fait l'exercice.

Aucun organe ne verifiait ca : `validate_pr_notebooks.py` mesure
`execution_count` et les outputs d'erreur, pas le **rattachement** d'une prose a
son ancre. La regle `cell-interpretation-ordering` decrit le geste, ce script le
mesure.

Usage :

    # sur des fichiers locaux
    python scripts/notebook_tools/check_density_anchor.py notebook.ipynb ...

    # sur le diff d'une PR (compare head vs base, ne juge que les AJOUTS)
    python scripts/notebook_tools/check_density_anchor.py --pr 16492

    # sortie machine
    python scripts/notebook_tools/check_density_anchor.py --pr 16492 --json

Code de sortie : 0 si aucun defaut, 1 si au moins une lecture est mal ancree,
2 en cas d'erreur d'invocation.
"""
from __future__ import annotations

import argparse
import base64
import json
import os
import re
import subprocess
import sys

# Une cellule markdown est une « lecture » si elle annonce qu'elle commente un
# resultat. Volontairement large : un faux positif coute une relecture, un faux
# negatif laisse passer une divulgation.
LECTURE = re.compile(
    r"(lecture du r|interpr[ée]tation|ce que (montre|dit|nous apprend)"
    r"|r[ée]sultat\s*:|on (lit|observe|constate|voit)|attendu\s*:)",
    re.I,
)

# Marqueurs d'une cellule de code laissee a l'etudiant.
STUB = re.compile(
    r"(#\s*TODO|Exercice a completer|Exercice à compléter|#\s*Indice"
    r"|votre code ici|your code here|#\s*Etape \d)",
    re.I,
)

# En dessous de ce volume, un output est considere comme un vestige (un prompt,
# une ligne de bruit), pas comme un resultat qu'on peut commenter.
MIN_OUTPUT_BYTES = 200


def output_size(cell: dict) -> int:
    """Volume total de sortie d'une cellule, texte et donnees riches confondus."""
    total = 0
    for out in cell.get("outputs", []):
        total += len("".join(out.get("text", [])))
        total += len(json.dumps(out.get("data", {}), ensure_ascii=False))
    return total


def _run(args: list[str]) -> str:
    proc = subprocess.run(args, capture_output=True, text=True,
                          encoding="utf-8", errors="replace")
    if proc.returncode != 0:
        raise RuntimeError((proc.stderr or "").strip()[:200])
    return proc.stdout


def cells_at_ref(repo: str, path: str, ref: str) -> list[dict] | None:
    """Cellules d'un notebook a une reference donnee, via l'API contents."""
    try:
        encoded = _run(["gh", "api",
                        "repos/%s/contents/%s?ref=%s" % (repo, path, ref),
                        "--jq", ".content"])
    except RuntimeError:
        return None
    raw = base64.b64decode(encoded.strip()).decode("utf-8", "replace")
    return json.loads(raw)["cells"]


def audit(head_cells: list[dict], base_cells: list[dict] | None) -> list[dict]:
    """Defauts d'ancrage parmi les cellules de lecture AJOUTEES.

    `base_cells` a None fait auditer toutes les lectures du notebook (mode
    fichier local) ; sinon seules les cellules absentes de la base sont jugees,
    ce qui borne le verdict au diff.
    """
    known = set()
    if base_cells is not None:
        known = {"".join(c["source"]) for c in base_cells}

    findings = []
    for i, cell in enumerate(head_cells):
        if cell["cell_type"] != "markdown":
            continue
        source = "".join(cell["source"])
        if source in known or not LECTURE.search(source):
            continue

        # L'ancre est la cellule de code immediatement precedente.
        j = i - 1
        while j >= 0 and head_cells[j]["cell_type"] != "code":
            j -= 1
        if j < 0:
            findings.append({"cell": i, "anchor": None,
                             "reason": "lecture sans aucune cellule de code en amont"})
            continue

        anchor = head_cells[j]
        size = output_size(anchor)
        is_stub = bool(STUB.search("".join(anchor["source"])))
        if size == 0:
            findings.append({
                "cell": i, "anchor": j, "output_bytes": 0, "stub": is_stub,
                "reason": "ancre sans aucun output" + (" (stub d'exercice)" if is_stub else ""),
            })
        elif is_stub and size < MIN_OUTPUT_BYTES:
            findings.append({
                "cell": i, "anchor": j, "output_bytes": size, "stub": True,
                "reason": "ancre = stub d'exercice, output residuel de %d octets" % size,
            })
    return findings


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("notebooks", nargs="*", help="fichiers .ipynb locaux")
    parser.add_argument("--pr", type=int, help="numero de PR : n'audite que les cellules ajoutees")
    parser.add_argument("--repo", default="jsboige/CoursIA")
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args(argv)

    if not args.notebooks and args.pr is None:
        parser.error("donner des notebooks ou --pr")

    results = []

    if args.pr is not None:
        meta = json.loads(_run(["gh", "pr", "view", str(args.pr), "-R", args.repo,
                                "--json", "headRefOid,baseRefOid,files"]))
        paths = [f["path"] for f in meta["files"] if f["path"].endswith(".ipynb")]
        for path in paths:
            head = cells_at_ref(args.repo, path, meta["headRefOid"])
            if head is None:
                results.append({"path": path, "error": "notebook illisible au head"})
                continue
            base = cells_at_ref(args.repo, path, meta["baseRefOid"]) or []
            results.append({"path": path, "findings": audit(head, base)})

    for path in args.notebooks:
        with open(path, encoding="utf-8") as handle:
            results.append({"path": path,
                            "findings": audit(json.load(handle)["cells"], None)})

    failed = any(r.get("findings") for r in results)

    if args.as_json:
        print(json.dumps({"ok": not failed, "results": results},
                         ensure_ascii=False, indent=2))
    else:
        for result in results:
            name = os.path.basename(result["path"])
            if "error" in result:
                print("??  %s : %s" % (name, result["error"]))
            elif not result["findings"]:
                print("OK  %s" % name)
            else:
                print("!!  %s" % name)
                for f in result["findings"]:
                    anchor = "c%s" % f["anchor"] if f["anchor"] is not None else "-"
                    print("      cellule %-4s ancre %-5s %s" % (f["cell"], anchor, f["reason"]))
        if failed:
            print("\nUne cellule de lecture doit suivre une cellule de code qui a REELLEMENT produit\n"
                  "le resultat commente. Sur un stub d'exercice, elle divulgue la reponse.")

    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
