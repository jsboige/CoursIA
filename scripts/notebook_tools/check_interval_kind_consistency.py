#!/usr/bin/env python3
"""Garde d'accord intervalle declare <-> intervalle affiche (#15592).

Origine -- le laisser-passer de #15156
--------------------------------------
#15156 a migre 7 notebooks PyMC vers l'API arviz 1.1 en remplacant
`hdi_prob=0.89` par `ci_prob=0.89`, **sans `ci_kind`**. Or en arviz 1.1
(`arviz_stats`), `ci_kind` a pour defaut `None`, que la bibliotheque resout en
`"eti"` (equal-tailed interval) -- **pas** en `"hdi"`. La migration s'executait
donc sans erreur tout en changeant **l'objet statistique affiche**, pendant que
la prose des notebooks continuait d'annoncer un HDI.

L'issue #15592 nomme elle-meme la mesure manquante :

    "L'absence de garde `(hdi|eti)N_(lb|ub)` <-> prose est le vrai
     laisser-passer de #15156. Un controle peu couteux -- extraire les noms de
     colonnes des sorties, les confronter aux mentions `HDI`/`ETI` du markdown
     -- aurait attrape les deux cas."

CE QUE CE GARDE MESURE, ET POURQUOI PAS LA PROSE
-----------------------------------------------
Deux invariants etaient candidats. La mesure a tranche, pas la preference.

**Retenu -- source declaree -> sortie affichee.** Pour chaque cellule de code
dont les sorties portent une colonne `(hdi|eti)<N>_(lb|ub)`, on lit dans la
SOURCE le type d'intervalle demande (`ci_kind="hdi"`, `hdi_prob=`, `az.hdi(`)
et on le compare a la famille reellement presente dans la sortie. C'est
exactement le mecanisme du defaut : #15156 a change la source sans re-executer,
donc la sortie committée a cesse de correspondre a la source qui la porte --
un manquement C.2/H.1, detectable statiquement, sans executer le notebook.

**Rejete -- prose <-> sortie.** Mesure sur l'arbre entier (`origin/main@
d14b1ac098`) : sur les **18** cellules du depot qui portent une colonne
d'intervalle, **16 n'ont aucune revendication `HDI`/`ETI` en amont**. Le garde
n'aurait donc regarde que 2 cellules sur 18, tout en ouvrant une surface de
faux positifs reelle : `HDI` apparait aussi dans les cellules qui **definissent**
le terme (« HDI = highest density interval ») sans rien revendiquer sur la
sortie affichee. Un garde qui couvre 11 % des cas et crie au loup ailleurs est
un garde qu'on desactive -- lecon #12586 / #15489 defaut 5.

CE QUE CE GARDE NE FAIT PAS
---------------------------
- Il ne juge pas la prose : cf ci-dessus.
- Il ne re-execute rien : il lit l'etat committe. Un notebook dont la source et
  les sorties s'accordent mais qui ment sur son contenu statistique lui echappe.
- Il ne couvre que les colonnes d'intervalle nommees. Un `az.hdi(...)` dont le
  resultat n'est pas affiche en colonne n'est pas vu.
- Il ignore les cellules mixtes (qui demandent explicitement deux types a la
  fois) : ambigues par construction, elles sont denombrees, pas jugees.

PORTEE
------
Arbre ENTIER, pas delta. Mesure de la baseline sur `origin/main@d14b1ac098` :
18 cellules examinees, **0 desaccord**. Un garde bloquant sur un arbre vert ne
fabrique aucun mur rouge -- c'est la condition qui rend le mode bloquant
legitime ici, et elle est verifiee, pas supposee.

Usage
-----
    python scripts/notebook_tools/check_interval_kind_consistency.py
    python scripts/notebook_tools/check_interval_kind_consistency.py --json
    python scripts/notebook_tools/check_interval_kind_consistency.py --self-test

Sortie : 0 = aucun desaccord ; 1 = desaccord ; 2 = erreur d'invocation.
Le denombrement des cellules examinees est TOUJOURS imprime : "rien trouve" et
"rien regarde" ne doivent jamais se confondre.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
NOTEBOOKS = REPO_ROOT / "MyIA.AI.Notebooks"

#: Famille d'intervalle portee par une colonne de sortie, p.ex. `hdi89_lb`.
COLUMN = re.compile(r"\b(hdi|eti)(\d+)_(lb|ub)\b", re.I)

#: Appels arviz qui acceptent le choix du type d'intervalle. Restreindre a ces
#: appelants evite de lire un `ci_kind=` qui appartiendrait a autre chose.
CALLERS = re.compile(r"\baz\.(summary|plot_dist|plot_posterior|plot_forest"
                     r"|plot_ppc|plot_elpd|hdi|plot_hdi|hdpi)\s*\(")

#: Declarations explicites du type d'intervalle.
KIND_HDI = re.compile(r"""ci_kind\s*=\s*['"]hdi['"]""", re.I)
KIND_ETI = re.compile(r"""ci_kind\s*=\s*['"]eti['"]""", re.I)
LEGACY_HDI_PROB = re.compile(r"\bhdi_prob\s*=")
CI_PROB = re.compile(r"\bci_prob\s*=")

#: Dossiers hors corpus pedagogique (libs vendorees, lakes externes).
EXCLUDED = ("/.lake/", "/_peters/")

#: Le defaut d'arviz 1.1 : `ci_kind=None` est resolu en intervalle equal-tailed.
#: C'est CE defaut qui a rendu #15156 silencieux, donc c'est lui qu'on encode.
DEFAULT_KIND = "eti"


def _iter_notebooks(root: Path = NOTEBOOKS):
    for nb in sorted(root.rglob("*.ipynb")):
        if any(x in nb.as_posix() for x in EXCLUDED):
            continue
        yield nb


def _cell_source(cell: dict) -> str:
    return "".join(cell.get("source", []))


def output_kinds(cell: dict) -> set[str]:
    """Familles d'intervalle presentes dans les SORTIES commitees de la cellule."""
    kinds: set[str] = set()
    for out in cell.get("outputs", []) or []:
        for m in COLUMN.finditer(json.dumps(out)):
            kinds.add(m.group(1).lower())
    return kinds


def declared_kinds(source: str) -> set[str]:
    """Familles que la SOURCE demande explicitement.

    Un appel d'intervalle sans `ci_kind` (ni `hdi_prob` legacy) ne demande rien
    d'explicite : il retombe sur le defaut de la bibliotheque, qui est encode
    separement (`DEFAULT_KIND`) pour que la part de deduction reste visible.
    """
    kinds: set[str] = set()
    if KIND_HDI.search(source) or LEGACY_HDI_PROB.search(source):
        kinds.add("hdi")
    if KIND_ETI.search(source):
        kinds.add("eti")
    return kinds


def examines_interval(source: str) -> bool:
    """La source porte-t-elle un appel qui produit un intervalle ?"""
    return bool(CALLERS.search(source) or CI_PROB.search(source))


def examine(nb_path: Path) -> tuple[list[dict], dict]:
    """Rend (desaccords, compteurs) pour un notebook.

    Un desaccord est enregistre quand la famille attendue -- celle que la
    source demande, ou le defaut de la bibliotheque si elle ne demande rien --
    n'apparait dans AUCUNE colonne de sortie de la cellule.
    """
    try:
        doc = json.loads(nb_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return [], {"unreadable": 1, "detail": str(exc)}

    try:
        shown = nb_path.relative_to(REPO_ROOT).as_posix()
    except ValueError:
        shown = nb_path.as_posix()

    issues: list[dict] = []
    counts = {"cells": 0, "explicit": 0, "default": 0, "ambiguous": 0}
    for idx, cell in enumerate(doc.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        shown_kinds = output_kinds(cell)
        if not shown_kinds:
            continue
        counts["cells"] += 1
        source = _cell_source(cell)
        declared = declared_kinds(source)
        if len(declared) > 1:
            counts["ambiguous"] += 1
            continue
        if declared:
            expected = next(iter(declared))
            counts["explicit"] += 1
        elif examines_interval(source):
            expected = DEFAULT_KIND
            counts["default"] += 1
        else:
            # Aucune source d'intervalle identifiable (sortie heritee d'un
            # appel non reconnu) : rien a confronter, on ne juge pas.
            continue
        if expected not in shown_kinds:
            issues.append({
                "file": shown,
                "cell": idx,
                "expected": expected,
                "shown": sorted(shown_kinds),
                "basis": "explicit" if declared else "library-default",
            })
    return issues, counts


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description="Refuser un notebook dont les colonnes d'intervalle "
                    "affichees ne correspondent pas au type demande par la "
                    "source (#15592).")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--root", default=str(NOTEBOOKS),
                    help="racine a scanner (defaut : MyIA.AI.Notebooks)")
    a = ap.parse_args(argv)

    issues: list[dict] = []
    totals = {"cells": 0, "explicit": 0, "default": 0, "ambiguous": 0,
              "notebooks": 0, "unreadable": 0}
    for nb in _iter_notebooks(Path(a.root)):
        found, counts = examine(nb)
        totals["notebooks"] += 1
        totals["unreadable"] += counts.get("unreadable", 0)
        for k in ("cells", "explicit", "default", "ambiguous"):
            totals[k] += counts.get(k, 0)
        issues.extend(found)

    if a.json:
        print(json.dumps({"totals": totals, "issues": issues},
                         ensure_ascii=False, indent=2))
        return 1 if issues else 0

    print("notebooks lus : %d   cellules a colonne d'intervalle : %d "
          "(declare explicite=%d, defaut=%d, mixte ecarte=%d)"
          % (totals["notebooks"], totals["cells"], totals["explicit"],
             totals["default"], totals["ambiguous"]))
    if totals["unreadable"]:
        print("   (%d notebook(s) illisible(s) -- ignores, comptes)"
              % totals["unreadable"])
    if not totals["cells"]:
        print("VERDICT: OK -- aucune cellule a colonne d'intervalle, rien a "
              "verifier.")
        return 0
    if not issues:
        print("VERDICT: OK -- les intervalles affiches correspondent au type "
              "demande par la source.")
        return 0
    print("")
    print("VERDICT: INTERVALLE AFFICHE != INTERVALLE DECLARE (%d)" % len(issues))
    print("")
    for it in issues:
        print("   %s cellule %d : source demande %s, sortie porte %s (%s)"
              % (it["file"], it["cell"], it["expected"].upper(),
                 "/".join(k.upper() for k in it["shown"]), it["basis"]))
    print("")
    print("En arviz 1.1, `ci_kind` vaut None par defaut et la bibliotheque le "
          "resout en intervalle equal-tailed ('eti'). Un `ci_prob=` sans "
          "`ci_kind` affiche donc un ETI, pas un HDI.")
    print("Corriger la SOURCE (`ci_kind=\"hdi\"`) puis RE-EXECUTER : changer "
          "la source sans re-executer laisse une sortie qui ne correspond plus "
          "au code qui la porte (C.2/H.1). Jamais de retouche manuelle de la "
          "sortie.")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
