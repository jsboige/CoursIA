#!/usr/bin/env python3
"""Refuser une cellule markdown de LECTURE ajoutee, ancoree sur du code sans sortie reelle.

Origine -- #16695 (prototype ai-01, cycle du 2026-09-18). Une cellule markdown
**ajoutee par la PR** qui lit un resultat (``### Lecture du resultat``, ``on
observe``, ``ce que montre...``) doit etre ancoree sur une cellule de code qui
porte un OUTPUT REEL. Deux formes de defaut :

1. **Lecture sans ancre** -- la prose commente un resultat qu'aucune sortie du
   notebook ne porte. Instance mesuree : #16619 citait trois fois un
   « phi moyen conditionnel » dont deux valeurs n'existaient dans aucun output.
2. **Lecture sur un stub d'exercice** -- forme aggravee : la prose DIVULGUE le
   resultat d'un exercice que l'etudiant n'a pas rempli. Le notebook s'execute
   (C.1 respectee : ``pass`` + ``print("Exercice a completer")``), donc les
   organes d'execution restent verts et le spoiler passe.

CE QUE CE GARDE MESURE, ET CE QU'IL NE MESURE PAS
-------------------------------------------------
Il mesure l'ANCRAGE STRUCTUREL d'une cellule de lecture ajoutee : la cellule de
code amont la plus proche porte-t-elle une sortie reelle ? Il ne mesure NI la
veracite des valeurs citees, NI le placement relatif de plusieurs cellules
d'interpretation. Trois gardes voisins couvrent ces autres axes et restent muets
sur le notre (verifie en lisant leurs docstrings, cf #16695) :

- ``scripts/check_markdown_claims_output.py`` : prose citant une valeur qui
  CONTREDIT l'output -- il lui faut une valeur dans l'output pour la comparer ;
  output vide = rien a contredire.
- ``scripts/notebook_tools/check_prose_quantitative_claims.py`` : compteurs
  d'artefacts du depot figes dans la prose -- autre genre (mesure de depot), pas
  une lecture de sortie.
- ``scripts/notebook_tools/check_interp_positioning.py`` : interpretation posee
  apres la MAUVAISE cellule -- il suppose que les outputs existent ; il arbitre
  laquelle est l'ancre, pas s'il y en a une.

EXEMPTION DE CLOTURE / TRANSITION (le FP fondateur du prototype)
----------------------------------------------------------------
L'heuristique « ancre = cellule de code precedente » tire sur toute synthese de
cloture qui suit la derniere cellule de code, fut-elle un stub : mesure du
prototype sur 4 PRs de densite (16619, 16413, 16455, 16441) = 1 touche, FAUSSE
(#16619 c32, une ``## Conclusion`` legitime). Une cellule dont l'en-tete est une
cloture (Conclusion, Synthese, Resume, Bilan...), un rappel, ou l'introduction
d'une section SUIVANTE (Exercice, Partie, Section, Etape, Annexe...) n'est pas
une lecture de sa cellule amont : elle clot ou elle introduit, elle ne commente
pas. Ces en-tetes sont exemptes. Le garde reste arme sur toute lecture sans
en-tete exempte -- c'est le controle negatif #16619 c32 du self-test.

Portee : **uniquement les cellules markdown AJOUTEES** par la revision (source
absente de la base), pour ne pas rougir sur la dette heritee. Advisory
(blocking=False, #15327) tant que la mesure de FP sur un lot reel n'est pas a
zero.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

LECTURE = re.compile(
    r"(lecture du r|interpr|ce que (montre|dit|nous apprend)"
    r"|r[ée]sultat\s*:|on (lit|observe|constate)|attendu)",
    re.I,
)
STUB = re.compile(
    r"(TODO|Exercice a completer|Exercice à compléter|# Indice|votre code"
    r"|your code|\bpass\b\s*$)",
    re.I,
)
# En-tetes de cloture / rappel / introduction de section SUIVANTE : la cellule
# ne commente pas son amont (exemption du FP #16619 c32, cf docstring).
EXEMPT_HEADING = re.compile(
    r"^#{1,4}\s*"
    r"("
    r"conclusion|synth[èe]se|r[ée]sum[ée]|bilan|summary|recap"
    r"|ce qu'il faut retenir|l'essentiel|pour aller plus loin|rappels?"
    r"|exercice|partie|section|[ée]tape|annexe|appendix|introduction"
    r"|prologue|pr[ée]ambule|sommaire|plan du notebook"
    r")\b",
    re.I,
)
STUB_OUTPUT_MAX = 200  # octets : un stub executé rend ~25o ; une vraie lecture s'ancre sur plus
# Zone d'ouverture : une cellule markdown situee AVANT la premiere cellule de code
# du notebook (titre, navigation, epigraphe, presentation du companion). Mesure
# #16695 sur 18 PRs : les 4 seules touches de la classe « lecture sans ancre
# amont » etaient toutes des cellules d'ouverture de PRs Lean (#16656) referencant
# un notebook COMPANION externe -- 0 vrai positif. Le defaut vise est l'ancre
# SANS output, pas l'absence d'ancre : la classe est retiree.


def cell_source(c: dict) -> str:
    src = c.get("source", "")
    return "".join(src) if isinstance(src, list) else src


def outlen(c: dict) -> int:
    n = 0
    for o in c.get("outputs", []):
        t = o.get("text", "")
        n += len("".join(t) if isinstance(t, list) else t)
        n += len(json.dumps(o.get("data", {}), ensure_ascii=False))
    return n


def is_exempt(md_src: str) -> bool:
    for line in md_src.splitlines():
        if line.strip():
            return bool(EXEMPT_HEADING.match(line.strip()))
    return True  # cellule vide : rien a lire, rien a ancrer


def analyze(head_cells: list, base_cells: list | None) -> list[dict]:
    """Coeur du garde : cellules de lecture AJOUTEES vs leur ancre de code amont."""
    base_src = {cell_source(c) for c in (base_cells or [])}
    findings = []
    for i, c in enumerate(head_cells):
        if c.get("cell_type") != "markdown":
            continue
        src = cell_source(c)
        if src in base_src:  # pas une cellule ajoutee
            continue
        if not LECTURE.search(src):
            continue
        if is_exempt(src):
            continue
        j = i - 1
        while j >= 0 and head_cells[j].get("cell_type") != "code":
            j -= 1
        if j < 0:
            continue  # zone d'ouverture : avant tout code, rien a ancrer (cf docstring)
        anchor = head_cells[j]
        a_src, ol = cell_source(anchor), outlen(anchor)
        if ol == 0:
            findings.append({
                "cell": i, "anchor": j, "kind": "ANCRE_SANS_OUTPUT",
                "detail": "ancre c%d sans output%s" % (
                    j, " (STUB : divulgation probable)" if STUB.search(a_src) else ""),
            })
        elif STUB.search(a_src) and ol < STUB_OUTPUT_MAX:
            findings.append({
                "cell": i, "anchor": j, "kind": "ANCRE_STUB",
                "detail": "ancre c%d = stub d'exercice, output %do < %do" % (
                    j, ol, STUB_OUTPUT_MAX),
            })
    return findings


def load_cells(ref: str, path: str) -> list | None:
    """Cellules d'un notebook a un ref git quelconque (None = introuvable)."""
    r = subprocess.run(["git", "show", "%s:%s" % (ref, path)],
                       capture_output=True, text=True, encoding="utf-8",
                       errors="replace", cwd=REPO_ROOT)
    if r.returncode != 0:
        return None
    try:
        return json.loads(r.stdout)["cells"]
    except (json.JSONDecodeError, KeyError):
        return None


def changed_notebooks(base: str, head: str) -> list[str]:
    r = subprocess.run(
        ["git", "diff", "--name-only", "%s...%s" % (base, head), "--", "*.ipynb"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        cwd=REPO_ROOT)
    return [l for l in r.stdout.splitlines() if l.strip()]


def self_test() -> int:
    def code(src, outputs=None, exec_count=None):
        return {"cell_type": "code", "metadata": {}, "execution_count": exec_count,
                "outputs": outputs or [], "source": src}

    def md(src):
        return {"cell_type": "markdown", "metadata": {}, "source": src}

    def out(text):
        return {"output_type": "stream", "name": "stdout", "text": text}

    ok = True

    def check(label, cond):
        nonlocal ok
        print("  [%s] %s" % ("OK " if cond else "ERR", label))
        ok = ok and cond

    # Controle positif 1 : lecture sur ancre sans output -- doit REFUSER.
    head = [code("# calcul\nmoyenne = sum(valeurs) / len(valeurs)\n"),
            md("### Lecture du resultat\n\nOn observe que la moyenne vaut 42.")]
    f = analyze(head, [])
    check("positif : lecture sur code sans output -> 1 finding ANCRE_SANS_OUTPUT",
          len(f) == 1 and f[0]["kind"] == "ANCRE_SANS_OUTPUT")

    # Controle positif 2 : lecture sur STUB executé (spoiler) -- doit REFUSER.
    stub = code("# TODO etudiant\npass\n", outputs=[out("Exercice a completer\n")], exec_count=1)
    head = [stub, md("On constate que le resultat attendu est 0.75 pour le jeu A.")]
    f = analyze(head, [])
    check("positif : lecture sur stub executé -> 1 finding ANCRE_STUB",
          len(f) == 1 and f[0]["kind"] == "ANCRE_STUB")

    # Controle negatif #16656 : cellule d'ouverture (avant TOUT code, motif de
    # lecture sur un companion externe) -- zone d'ouverture, doit PASSER.
    head = [md("# Lean-12b -- companion formel\n\nCe notebook est le companion du "
               "notebook Python ; on observe la preuve formelle dans le lake.")]
    f = analyze(head, [])
    check("negatif #16656 : ouverture avant tout code -> 0 finding", not f)

    # Controle negatif fondateur #16619 c32 : Conclusion apres stub -- doit PASSER.
    stub31 = code("# Exercice : votre code\npass\n", outputs=[out("Exercice a completer")], exec_count=7)
    c32 = ("## Conclusion\n\nCe qu'il faut retenir : on observe trois familles "
           "d'attribution, et le resultat de chacune merite une lecture attentive.")
    f = analyze([stub31, md(c32)], [])
    check("negatif #16619 c32 : Conclusion apres stub -> 0 finding", not f)

    # Controle negatif : lecture ancoree sur un VRAI output -- doit PASSER.
    real = code("print(summary_table)", outputs=[out("phi_moyen_conditionnel = 0.62\n")], exec_count=3)
    head = [real, md("Lecture du resultat : on lit un phi moyen conditionnel de 0.62.")]
    f = analyze(head, [])
    check("negatif : lecture sur output reel -> 0 finding", not f)

    # Controle negatif : cellule NON ajoutee (deja dans la base) -- ignoree.
    f = analyze(head, head)
    check("negatif : cellule heritee (non ajoutee) -> 0 finding", not f)

    print("\nself-test:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--base", help="ref git de la base (ex. origin/main)")
    ap.add_argument("--head", default="HEAD", help="ref git de la tete (defaut HEAD)")
    ap.add_argument("--fail", action="store_true", help="sortie 1 si au moins un defaut")
    ap.add_argument("--json", action="store_true", help="sortie JSON")
    ap.add_argument("--self-test", action="store_true",
                    help="controles positifs/negatifs (lecon #11685)")
    args = ap.parse_args(argv)

    if args.self_test:
        return self_test()
    if not args.base:
        ap.error("--base est requis (mode PR) ; utiliser --self-test pour les controles")

    findings, scanned = {}, 0
    for nb in changed_notebooks(args.base, args.head):
        head_cells = load_cells(args.head, nb)
        if head_cells is None:
            findings[nb] = [{"kind": "UNREADABLE", "detail": "notebook illisible au head"}]
            continue
        base_cells = load_cells(args.base, nb) or []
        scanned += 1
        f = analyze(head_cells, base_cells)
        if f:
            findings[nb] = f

    if args.json:
        print(json.dumps({"scanned": scanned, "findings": findings},
                         indent=2, ensure_ascii=False))
    else:
        print("Notebooks examines : %d" % scanned)
        n = sum(len(v) for v in findings.values())
        print("Defauts d'ancrage de lecture : %d" % n)
        for nb, fs in findings.items():
            for f in fs:
                print("  %s c%s : %s %s" % (nb, f.get("cell", "?"), f["kind"], f["detail"]))
    return 1 if (args.fail and any(findings.values())) else 0


if __name__ == "__main__":
    sys.exit(main())
