#!/usr/bin/env python3
"""Detecte les liens dont le LIBELLE nomme un notebook different de la CIBLE.

Pourquoi cet outil existe
-------------------------
Incident fondateur #13645. Le renommage `ICT-15d-NerveDiscriminant.ipynb` ->
`ICT-15j-NerveDiscriminant.ipynb` (commit `641be890a4`, refactor(notebooks,#12375))
a mis a jour le **href** et laisse le **texte affiche** a l'ancien identifiant :

    [ICT-15d](../../IIT/ICT-Series/ICT-15j-NerveDiscriminant.ipynb)

Un lecteur qui suit « ICT-15d » atterrit sur ICT-15j. Le defaut a ete trouve a
l'oeil, dans un notebook Lean qui n'etait meme pas dans le perimetre du renommage.

Pourquoi les quatre gardes existants ne le voient pas
----------------------------------------------------
Tous verifient que la CIBLE existe ; ici elle existe.

- `check_docs_links.py`          : 404 sur .md, ne scanne pas les .ipynb.
- `check_notebook_navlinks.py`   : 404 sur les cibles dans les cellules markdown.
- `detect_link_target_regression.py` : regressions d'ACCENTS dans les cibles.
- `check_notebook_link_render.py`: rendu .html vs .ipynb brut.

Aucun ne compare le libelle a la cible. C'est le predicat ajoute ici, et rien
d'autre : cet outil ne remplace aucun des quatre, il comble leur angle mort commun.

Ce que l'outil signale
----------------------
Uniquement le cas non ambigu : le libelle contient un identifiant de notebook
**de la meme famille** que la cible, et il **differe**. Un libelle en prose
(« voir le notebook sur les faisceaux ») ne declenche rien : l'absence
d'identifiant n'est pas un desaccord.

Usage
-----
    python scripts/notebook_tools/check_link_label_agreement.py [--json] [--fail]
    python scripts/notebook_tools/check_link_label_agreement.py --self-test
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

SCAN_GLOBS = ("MyIA.AI.Notebooks/**/*.ipynb", "MyIA.AI.Notebooks/**/README.md", "docs/**/*.md")
EXCLUDE_PARTS = {".ipynb_checkpoints", "_archive", "_archives", ".lake", "node_modules", ".git"}

# [texte](cible) -- cible non-http, non-ancre
LINK_RE = re.compile(r"\[([^\]\n]{1,200})\]\(([^)\s]+?\.ipynb)(?:#[^)\s]*)?\)", re.I)
# <Prefixe>-<num><lettre?>- : la convention du depot (le tiret precede le titre)
ID_IN_NAME_RE = re.compile(r"^(?P<pre>.+?)[-_](?P<num>\d{1,3})(?P<let>[a-z])?[-_]", re.I)


def target_id(filename: str):
    """(prefixe, numero, lettre) depuis un nom de fichier notebook, ou None."""
    m = ID_IN_NAME_RE.match(Path(filename).name)
    if not m:
        return None
    return (m.group("pre").lower(), int(m.group("num")), (m.group("let") or "").lower())


def labels_in_text(text: str, prefix: str):
    """Identifiants de la meme famille cites dans le libelle."""
    pat = re.compile(rf"\b{re.escape(prefix)}[-_](\d{{1,3}})([a-z])?\b", re.I)
    return [(int(n), (l or "").lower()) for n, l in pat.findall(text)]


def check_text(source: str, path: str):
    out = []
    for label, target in LINK_RE.findall(source):
        tid = target_id(target)
        if not tid:
            continue
        prefix, tnum, tlet = tid
        for lnum, llet in labels_in_text(label, prefix):
            if (lnum, llet) != (tnum, tlet):
                out.append({
                    "file": path,
                    "label": label.strip()[:80],
                    "target": target,
                    "says": f"{prefix}-{lnum}{llet}",
                    "points_to": f"{prefix}-{tnum}{tlet}",
                })
                break
    return out


def cell_sources(nb_path: Path):
    try:
        nb = json.loads(nb_path.read_text(encoding="utf-8"))
    except Exception:
        return
    for cell in nb.get("cells", []):
        if cell.get("cell_type") == "markdown":
            src = cell.get("source", "")
            yield "".join(src) if isinstance(src, list) else src


SELF_TEST_CASES = [
    # (source, nb_findings_attendus, intitule)
    ("L'erreur du premier Cech affine ([ICT-15d](../../IIT/ICT-Series/ICT-15j-NerveDiscriminant.ipynb)) "
     "ne se corrige pas...", 1, "#13645 verbatim -- doit ROUGIR"),
    ("[ICT-15j](../../IIT/ICT-Series/ICT-15j-NerveDiscriminant.ipynb)", 0, "libelle exact -- doit passer"),
    ("[le notebook sur le nerf](ICT-15j-NerveDiscriminant.ipynb)", 0, "libelle en prose -- doit passer"),
    ("[ICT-15j -- Nerve Discriminant](ICT-15j-NerveDiscriminant.ipynb)", 0, "libelle titre complet -- doit passer"),
    ("[Lean-16](../Lean/Lean-16e-Something.ipynb)", 1, "lettre perdue au libelle -- doit ROUGIR"),
    ("[GameTheory-03e](GameTheory-03e-Chambers.ipynb)", 0, "accretion coherente -- doit passer"),
    ("[voir Search-9](Search-11c-Advanced.ipynb)", 1, "numero different -- doit ROUGIR"),
]


def self_test() -> int:
    ok = True
    for src, expected, title in SELF_TEST_CASES:
        got = len(check_text(src, "<self-test>"))
        status = "OK " if got == expected else "ECHEC"
        if got != expected:
            ok = False
        print(f"  [{status}] attendu={expected} obtenu={got}  {title}")
    print("\nself-test:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--json", action="store_true", help="sortie machine")
    ap.add_argument("--fail", action="store_true", help="sortie 1 si au moins un desaccord")
    ap.add_argument("--self-test", action="store_true", help="controle positif (#13645) et negatifs")
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    findings, scanned = [], 0
    seen = set()
    for glob in SCAN_GLOBS:
        for p in REPO_ROOT.glob(glob):
            if not p.is_file() or p in seen or EXCLUDE_PARTS & set(p.parts):
                continue
            seen.add(p)
            scanned += 1
            rel = p.relative_to(REPO_ROOT).as_posix()
            if p.suffix == ".ipynb":
                for src in cell_sources(p):
                    findings += check_text(src, rel)
            else:
                try:
                    findings += check_text(p.read_text(encoding="utf-8"), rel)
                except Exception:
                    pass

    if args.json:
        print(json.dumps({"scanned": scanned, "findings": findings}, indent=2, ensure_ascii=False))
    else:
        print(f"Fichiers scannes : {scanned}")
        print(f"Desaccords libelle/cible : {len(findings)}\n")
        for f in findings:
            print(f"  {f['file']}")
            print(f"    libelle dit  : {f['says']}   ([{f['label']}])")
            print(f"    cible pointe : {f['points_to']}   ({f['target']})")
    return 1 if (args.fail and findings) else 0


if __name__ == "__main__":
    sys.exit(main())
