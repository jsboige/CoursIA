#!/usr/bin/env python3
"""Garde d'ancrage : toute cellule markdown AJOUTEE qui LIT un resultat doit
etre ancre sur une cellule de code qui porte un OUTPUT REEL (#16695).

Le danger
---------
Deux formes de fuite pedagogique qu'aucun organe existant ne couvre :

1. **Lecture sans ancre** -- la prose commente un resultat qu'aucune sortie du
   notebook ne porte (valeurs citees absentes des outputs).
2. **Lecture sur un stub d'exercice** -- forme aggravee : la prose DIVULGUE le
   resultat d'un exercice que l'etudiant n'a pas rempli. Le notebook s'execute
   (C.1 respectee : `pass` + `print("Exercice a completer")`), tous les organes
   sont verts, et le spoiler passe. Incident fondateur : P0 #16590 (9 cellules
   « Lire la sortie d'un exercice non rempli » retirees dans #16599/#16600/#16601).

Pourquoi les gardes voisins sont muets dessus (verifie, docstrings lus) :
- `check_markdown_claims_output.py`    : il faut une valeur DANS l'output pour
                                          la contredire ; output vide = rien a comparer.
- `check_prose_quantitative_claims.py`  : compteurs d'artefacts du depot figes en
                                          prose -- autre genre, pas une lecture de sortie.
- `check_interp_positioning.py`         : arbitre QUELLE cellule de code l'interp
                                          suit ; il suppose que les outputs existent.

Regle
-----
Une cellule markdown ajoutee par la PR est examinee si elle matche un motif de
lecture (LECTURE_RE) et n'est PAS EXEMPTEE. Elle doit alors etre ancoree sur la
cellule de code immediatement precedente, et cette ancre doit porter un output
 reel : refus si `outlen == 0`, ou si l'ancre est un stub avec moins de
STUB_MIN_OUTPUT_BYTES octets de sortie.

EXEMPTION de cloture/transition -- le coeur du calibrage (#16695) : une
`## Conclusion`, une `## Synthese`, un bilan, un en-resume, un pour-aller-plus-
loin ou une OUVERTURE DE SECTION (premiere ligne = titre de section, pas un
titre de lecture) ne « lit » pas sa cellule amont. Sans cette exemption, le
garde tire sur tous les notebooks qui se terminent proprement par un exercice
-- soit, par construction pedagogique, la majorite. Controle negatif mesure :
#16619 c32 (`## Conclusion` de cloture suivant un stub, 23 o de sortie) doit
rendre OK.

Hors scope (v1) :
- Lien SEMANTIQUE lecture <-> output (NLP) : fragile, cf voisin.
- Les cellules NON ajoutees par la PR (dette historique) : en mode --pr on ne
  regarde que le diff ; en mode local (chemins), on scanne tout -- documente.

Usage
-----
    python scripts/notebook_tools/check_lecture_anchor.py --pr 16619          # 1 PR (ajoutees seulement)
    python scripts/notebook_tools/check_lecture_anchor.py --pr 16619 --pr 16455
    python scripts/notebook_tools/check_lecture_anchor.py MonNotebook.ipynb   # scan local (toutes cellules)
    python scripts/notebook_tools/check_lecture_anchor.py --pr 16619 --check  # exit 1 sur finding
"""
from __future__ import annotations

import argparse
import base64
import json
import re
import subprocess
import sys
from pathlib import Path

REPO = "jsboige/CoursIA"

# Motifs de lecture d'un resultat. En tête de cellule OU dans le corps -- mais
# la cellule n'est examinee QUE si elle n'est pas une cloture/transition.
LECTURE_RE = re.compile(
    r"(lecture du r|lecture de la sortie|interpr[ée]tation du r|ce que (montre|dit|nous apprend)"
    r"|r[ée]sultat\s*:|on (lit|observe|constate))",
    re.I,
)

# Clotures / syntheses : la cellule RESUME le notebook ou une partie, elle ne
# lit pas la cellule amont. Numerotee (`## 7. Conclusion`) ou non. La forme
# GRAS (`**Remarque** : ...`) est couverte : mesure firsthand Pyro_RSA_Hyperbole
# cell#39 -- remarque d'extension citee (Kao & Goodman 2015), pas une lecture.
CLOSURE_RE = re.compile(
    r"^(?:#{1,4}\s*(?:\d+[.\s]+)?|\*\*\s*)(conclusion|synth[èe]se|bilan|en r[ée]sum[ée]"
    r"|r[ée]capitulatif|remarque|pour aller plus loin|prochaines [ée]tapes|ouverture"
    r"|transition)(?:\s*\*\*)?\b",
    re.I,
)

# Titre de lecture reconnu (la cellule SE DECLARE lecture) -- niveau 3+ typique.
LECTURE_HEADER_RE = re.compile(r"^#{1,6}\s*(lecture|interpr[ée]tation)", re.I)

# Detecteur de stub d'exercice (cf regle C.1 -- patterns de stub autorises).
STUB_RE = re.compile(
    r"(TODO|Exercice a completer|Exercice à compléter|# Indice|votre code|your code|\bpass\b\s*$)",
    re.I | re.S,
)

STUB_MIN_OUTPUT_BYTES = 200  # un stub avec >=200 o de sortie n'est plus un stub muet


def _outlen(cell: dict) -> int:
    """Taille texte totale des outputs d'une cellule de code (0 si aucun)."""
    total = 0
    for out in cell.get("outputs") or []:
        data = out.get("data") or {}
        if "text/plain" in data:
            t = data["text/plain"]
            total += len("".join(t) if isinstance(t, list) else t)
        elif "text" in out:
            t = out["text"]
            total += len("".join(t) if isinstance(t, list) else t)
    return total


# Enonce d'exercice : la cellule INSTRUIT l'exercice (elle peut relire le
# contexte amont sans lire une sortie). Pin FP : PyMC-17 c16.
EXERCISE_HEADER_RE = re.compile(
    r"^#{1,6}\s*(?:\d+[.\s]+)?(exercice|exercise|probl[èe]me|activit[ée]|travail pratique|tp)\b",
    re.I,
)


def _first_line(source) -> str:
    s = "".join(source) if isinstance(source, list) else (source or "")
    # sauter regles horizontales et lignes vides de tete (pin FP Infer-4 c17 :
    # `***` puis `### Vers l'inference...` = transition, pas lecture)
    for line in s.lstrip().split("\n"):
        line = line.strip()
        if line and not re.match(r"^(\*\*\*|---|___)\s*$", line):
            return line
    return ""


def is_exempt(cell: dict) -> bool:
    """Cloture/synthese, enonce d'exercice, OU ouverture de section (titre de
    section en premiere ligne utile qui n'est pas un titre de lecture)."""
    first = _first_line(cell.get("source"))
    if CLOSURE_RE.match(first) or EXERCISE_HEADER_RE.match(first):
        return True
    if re.match(r"^#{1,4}\s", first) and not LECTURE_HEADER_RE.match(first):
        return True  # ouverture de section / transition : ne lit pas l'amont
    return False


def scan_cells(cells: list, added_indices=None) -> list:
    """Retourne les findings [{cell_index, rule, evidence}].

    added_indices : ensemble d'indices a examiner (mode PR). None = tout
    (mode local, dette historique incluse).
    """
    findings = []
    for i, cell in enumerate(cells):
        if cell.get("cell_type") != "markdown":
            continue
        if added_indices is not None and i not in added_indices:
            continue
        src = "".join(cell.get("source") or [])
        if not LECTURE_RE.search(src):
            continue
        if is_exempt(cell):
            continue
        # ancre = cellule de code immediatement precedente
        j = i - 1
        while j >= 0 and cells[j].get("cell_type") != "code":
            j -= 1
        if j < 0:
            findings.append({"cell_index": i, "rule": "no_anchor",
                             "evidence": "lecture sans cellule de code amont"})
            continue
        anchor = cells[j]
        ol, asrc = _outlen(anchor), "".join(anchor.get("source") or [])
        stub = bool(STUB_RE.search(asrc))
        if ol == 0:
            findings.append({"cell_index": i, "rule": "anchor_no_output",
                             "evidence": "ancre c%d sans output" % j})
        elif stub and ol < STUB_MIN_OUTPUT_BYTES:
            findings.append({"cell_index": i, "rule": "anchor_stub_output",
                             "evidence": "ancre c%d = stub, output %do" % (j, ol)})
    return findings


# ---------------------------------------------------------------- PR mode --
def _fetch_cells(ref: str, path: str):
    """Cellules d'un notebook a un ref donne, via l'API GitHub (raw)."""
    r = subprocess.run(
        ["gh", "api", "-H", "Accept: application/vnd.github.raw",
         "repos/%s/contents/%s?ref=%s" % (REPO, path, ref)],
        capture_output=True, text=True, encoding="utf-8",
    )
    if r.returncode != 0:
        return None
    try:
        nb = json.loads(r.stdout)
    except json.JSONDecodeError:
        return None
    return nb.get("cells")


def _srckey(cell: dict) -> str:
    return json.dumps(cell.get("source"), ensure_ascii=False)


def scan_pr(pr: int) -> dict:
    """Scanne les cellules markdown AJOUTEES par une PR (diff base->head)."""
    info = subprocess.run(
        ["gh", "pr", "view", str(pr), "--json", "baseRefOid,headRefOid,files",
         "--repo", REPO],
        capture_output=True, text=True, encoding="utf-8",
    )
    if info.returncode != 0:
        return {"pr": pr, "error": "gh pr view failed: " + info.stderr.strip()[:200]}
    data = json.loads(info.stdout)
    base, head = data["baseRefOid"], data["headRefOid"]
    results = []
    for f in data.get("files", []):
        path = f["path"]
        if not path.endswith(".ipynb"):
            continue
        head_cells = _fetch_cells(head, path)
        if head_cells is None:
            continue
        base_cells = _fetch_cells(base, path)
        if base_cells is None:  # nouveau notebook : tout est ajoute
            added = set(range(len(head_cells)))
        else:
            base_keys = {_srckey(c) for c in base_cells}
            added = {i for i, c in enumerate(head_cells) if _srckey(c) not in base_keys}
        findings = scan_cells(head_cells, added)
        if findings:
            results.append({"file": path, "added_markdown": len(added), "findings": findings})
    return {"pr": pr, "flagged_files": results,
            "total": sum(len(r["findings"]) for r in results)}


# -------------------------------------------------------------------- CLI --
def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("paths", nargs="*", help="notebooks locaux (scan complet)")
    ap.add_argument("--pr", type=int, action="append", default=[],
                    help="numero de PR (repeatable) : cellules AJOUTEES seulement")
    ap.add_argument("--check", action="store_true",
                    help="exit 1 si un finding (CI-ready)")
    ap.add_argument("--json", action="store_true", help="sortie machine")
    args = ap.parse_args(argv)

    all_findings = []
    pr_reports = []
    for pr in args.pr:
        rep = scan_pr(pr)
        pr_reports.append(rep)
        for rf in rep.get("flagged_files", []):
            for f in rf["findings"]:
                all_findings.append({"pr": pr, "file": rf["file"], **f})

    for p in args.paths:
        path = Path(p)
        if not path.exists():
            print("error: not found: %s" % p, file=sys.stderr)
            return 2
        targets = sorted(path.rglob("*.ipynb")) if path.is_dir() else [path]
        for tp in targets:
            nb = json.loads(tp.read_text(encoding="utf-8"))
            for f in scan_cells(nb.get("cells")):
                all_findings.append({"file": str(tp), **f})

    if args.json:
        print(json.dumps({"total": len(all_findings),
                          "prs": pr_reports, "findings": all_findings},
                         indent=2, ensure_ascii=False))
    else:
        for rep in pr_reports:
            print("#%s  %s" % (rep["pr"], "OK" if rep.get("total", 0) == 0
                               else "!! %d finding(s)" % rep["total"]))
        for f in all_findings:
            print("  %s cell#%d [%s] %s" % (f.get("file"), f["cell_index"],
                                            f["rule"], f["evidence"]))

    if args.check and all_findings:
        print("FAIL: %d lecture(s) mal ancoree(s)." % len(all_findings), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
