#!/usr/bin/env python3
"""Detecte les liens dont le LIBELLE nomme un notebook different de la CIBLE.

Pourquoi cet outil existe
-------------------------
Incident fondateur #13645. Le renommage `ICT-15d-NerveDiscriminant.ipynb` ->
`ICT-15j-NerveDiscriminant-Python.ipynb` (commit `641be890a4`, refactor(notebooks,#12375))
a mis a jour le **href** et laisse le **texte affiche** a l'ancien identifiant :

    [ICT-15d](../../IIT/ICT-Series/ICT-15j-NerveDiscriminant-Python.ipynb)

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
dont l'ordinal ou le suffixe differe de la cible. La famille peut differer
apres un reclass (#23684) : `GameTheory-6c` -> `Dynamics-01` est signale, mais
`GameTheory-01` -> `Dynamics-01` reste muet. Un libelle en prose (« voir le
notebook sur les faisceaux ») ne declenche rien : l'absence d'identifiant
n'est pas un desaccord.

Usage
-----
    python scripts/notebook_tools/check_link_label_agreement.py [--json] [--fail]
    python scripts/notebook_tools/check_link_label_agreement.py --self-test

Portee
------
Notebooks, READMEs de serie, `docs/`, et les decks `slides/**/slides.md`
(#15867). Un deck cite ses notebooks par leur basename ; un renommage qui met a
jour le href en laissant le libelle derriere produit exactement le defaut
#13645. Le predicat n'a pas eu besoin d'etre assoupli pour la forme « basename
sans extension » : il compare un identifiant de famille extrait des DEUX cotes,
donc l'extension et la glose hors crochets ne le concernent pas.

Chemins illisibles
------------------
Un chemin que l'OS refuse de stat-er n'interrompt plus le balayage : il est
consigne, affiche sur `stderr`, et rendu dans `unreadable` en `--json`. Il ne
change pas le code de sortie -- ce n'est pas un desaccord, et `rc=1` appartient
a `--fail` (cf. `iter_scan_files` pour la mesure fondatrice : WinError 1920 sur
un paquet `.lake` sous Windows rendait l'organe muet, `rc=1` sans verdict).
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

# Decks (#15867). A deck cites its notebooks as `[Basename](../../MyIA.AI.Notebooks/...)`
# -- the label IS the basename, so a rename that updates the href and leaves the
# label behind is exactly the #13645 defect this organ exists for. Deck-only
# scope: `slides/**/*.md` would pull in the `analysis/` trees and the `.marp.md`
# siblings sourced from a different pipeline (see `scripts/check_docs_links.py`
# DECK_DIR for the measured cost of the wider scope).
DECK_DIR = "slides"
DECK_GLOB = "slides/**/slides.md"

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


def labels_in_text(text: str, prefix: str = ""):
    """Identifiants cites dans le libelle, toutes familles confondues (#23684).

    La famille seule ne peut pas discriminer un reclass : chercher les seuls
    identifiants de la famille de la cible rendait `GameTheory-6c` invisible
    derriere une cible `Dynamics-01`. On compare donc ordinal et suffixe, pas
    le nom de famille. ``prefix`` reste accepte pour compatibilite d'API.
    """
    pat = re.compile(r"\b(?P<prefix>[A-Za-z][A-Za-z0-9]*)[-_](?P<num>\d{1,3})(?P<let>[a-z])?(?=[-_]\w|\b)", re.I)
    return [(m.group("prefix").lower(), int(m.group("num")),
             (m.group("let") or "").lower()) for m in pat.finditer(text)]


def target_family_parts(source_path: str, target: str) -> set[str]:
    """Familles parentes de la cible, resolue contre le document source.

    Les liens entre carnets voisins portent souvent seulement un basename : les
    dossiers de la cible absents du href viennent alors du chemin du source.
    Un href deja relatif au depot reste utilisable depuis ``<self-test>``.
    """
    target_path = Path(target)
    resolved = target_path if target_path.is_absolute() else (
        Path(source_path).parent / target_path)
    return {part.lower() for part in resolved.parts[:-1]
            if part not in (".", "..")}


def check_text(source: str, path: str):
    out = []
    for label, target in LINK_RE.findall(source):
        tid = target_id(target)
        if not tid:
            continue
        prefix, tnum, tlet = tid
        for lprefix, lnum, llet in labels_in_text(label, prefix):
            if (lnum, llet) != (tnum, tlet) and lprefix == prefix:
                out.append({
                    "file": path,
                    "label": label.strip()[:80],
                    "target": target,
                    "says": f"{lprefix}-{lnum}{llet}",
                    "points_to": f"{prefix}-{tnum}{tlet}",
                })
                break

        # Reclass (#23684) : l'ancien identifiant n'est signale que s'il est
        # ENTIER, seul dans le libelle (ponctuation/whitespace admis). C'est
        # precisement la forme d'un titre repris par extract_title. Un
        # basename recopie ou une glose ne rougit pas : le controle de masse
        # a mesure 160 faux positifs sans cette restriction. Les references
        # historiques hors chemin de la cible restent muettes ; celles qui
        # subsistent dans ce chemin (Lean-17 -> KNOTS, Lean-21 -> MIMO, etc.)
        # sont les desaccords residuels exposes par le scan. La famille
        # ancienne doit etre un dossier parent de la cible et l'ordinal doit
        # differer.
        stripped = label.strip().strip("`*_ <>[]()")
        m = re.fullmatch(
            r"(?P<prefix>[A-Za-z][A-Za-z0-9]*)[-_](?P<num>\d{1,3})(?P<let>[a-z])?\b",
            stripped, re.I)
        if not m:
            continue
        lprefix = m.group("prefix").lower()
        lnum = int(m.group("num"))
        llet = (m.group("let") or "").lower()
        if lprefix == prefix or lprefix not in target_family_parts(path, target):
            continue
        if (lnum, llet) != (tnum, tlet):
            out.append({
                "file": path,
                "label": label.strip()[:80],
                "target": target,
                "says": f"{lprefix}-{lnum}{llet}",
                "points_to": f"{prefix}-{tnum}{tlet}",
            })
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


def iter_scan_files(root: Path, globs, unreadable: list):
    """Rend les fichiers a scanner. Un chemin illisible est consigne, jamais fatal.

    Pourquoi cette fonction existe (mesure du 2026-10-26, Windows). Le balayage
    testait `p.is_file()` **avant** `EXCLUDE_PARTS` : un chemin que la portee
    exclut -- `MyIA.AI.Notebooks/.../erc20_lean/.lake/packages/batteries/docs/
    README.md` -- levait `OSError: [WinError 1920]` et tuait la boucle entiere.
    L'organe rendait alors `rc=1` **sans aucun verdict** : indiscernable, pour
    une lane qui le lance avant de committer, d'un desaccord trouve par `--fail`.
    Un gate qui ne peut pas conclure n'est pas un gate.

    Deux corrections, dans cet ordre : l'exclusion est evaluee d'abord (elle est
    purement lexicale, donc gratuite, et elle evite de toucher un arbre qu'on
    n'a pas a lire), puis `is_file()` est protege. Un chemin illisible est
    **rendu a l'appelant** (`unreadable`), qui l'affiche : le silence sur une
    portee non lue serait un faux vert de plus (#15867).
    """
    seen = set()
    for glob in globs:
        for p in root.glob(glob):
            if p in seen or EXCLUDE_PARTS & set(p.parts):
                continue
            try:
                if not p.is_file():
                    continue
            except OSError as exc:
                unreadable.append({
                    "path": p.relative_to(root).as_posix(),
                    "error": str(exc),
                })
                continue
            seen.add(p)
            yield p


SELF_TEST_CASES = [
    # (source, nb_findings_attendus, intitule)
    ("L'erreur du premier Cech affine ([ICT-15d](../../IIT/ICT-Series/ICT-15j-NerveDiscriminant-Python.ipynb)) "
     "ne se corrige pas...", 1, "#13645 verbatim -- doit ROUGIR"),
    ("[ICT-15j](../../IIT/ICT-Series/ICT-15j-NerveDiscriminant-Python.ipynb)", 0, "libelle exact -- doit passer"),
    ("[le notebook sur le nerf](ICT-15j-NerveDiscriminant-Python.ipynb)", 0, "libelle en prose -- doit passer"),
    ("[ICT-15j -- Nerve Discriminant](ICT-15j-NerveDiscriminant-Python.ipynb)", 0, "libelle titre complet -- doit passer"),
    ("[Lean-16](../Lean/Lean-16e-Something.ipynb)", 1, "lettre perdue au libelle -- doit ROUGIR"),
    ("[GameTheory-03e](GameTheory-03e-Chambers.ipynb)", 0, "accretion coherente -- doit passer"),
    ("[voir Search-9](Search-11c-Advanced.ipynb)", 1, "numero different -- doit ROUGIR"),
    ("[GameTheory-6c](../../MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-01-Jeux-Repetes-Folk-Theorem-CSharp.ipynb)", 1,
     "#23684 reclass et ordinal different -- doit ROUGIR"),
    ("[GameTheory-01](../../MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-01-Jeux-Repetes-Folk-Theorem-CSharp.ipynb)", 0,
     "#23684 famille differente mais ordinal correct -- controle negatif"),
    ("[02-5 LTX-2](02-5-LTX-Video.ipynb)", 0,
     "glose de modele dans le titre -- controle negatif"),
    ("[Lean-17a](KNOTS/KNOTS-01-Conway-Proofs-Lean-Python.ipynb)", 0,
     "reference historique hors familles de la cible -- controle negatif"),
    ("[Argumentation-08d-Restitution-3-Actes-Python](Argumentation-08d-Restitution-3-Actes-Python.ipynb)", 0,
     "section numerotee du basename -- controle negatif"),
    ("[ANALYSE-06](ANALYSE-06b-Noyau.ipynb)", 1,
     "suffixe de noyau different -- non-regression"),
]

# Chemin source explicite : un href frere n'a aucun dossier, ses familles se
# derivent donc du document qui le contient. C'est le temoin reel Dynamics-03.
SELF_TEST_PATH_CASES = [
    ("MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-03-Sympathie-vs-Engagement-Python.ipynb",
     "[GameTheory-06c](Dynamics-01-Jeux-Repetes-Folk-Theorem-Python.ipynb)", 1,
     "#23684 lien frere resolu contre le chemin source -- doit ROUGIR"),
    ("MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-03-Sympathie-vs-Engagement-Python.ipynb",
     "[GameTheory-01](Dynamics-01-Jeux-Repetes-Folk-Theorem-Python.ipynb)", 0,
     "#23684 lien frere ordinal correct -- controle negatif"),
]


def self_test() -> int:
    ok = True
    for src, expected, title in SELF_TEST_CASES:
        got = len(check_text(src, "<self-test>"))
        status = "OK " if got == expected else "ECHEC"
        if got != expected:
            ok = False
        print(f"  [{status}] attendu={expected} obtenu={got}  {title}")
    for path, src, expected, title in SELF_TEST_PATH_CASES:
        got = len(check_text(src, path))
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

    findings, scanned, unreadable = [], 0, []
    for p in iter_scan_files(REPO_ROOT, SCAN_GLOBS + (DECK_GLOB,), unreadable):
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

    # Anti-silent-scan (#15867): `slides/` present but matching no deck would
    # render "0 desaccord" indistinguishable from a scope that scanned nothing.
    if (REPO_ROOT / DECK_DIR).is_dir() and not any(
        (REPO_ROOT / DECK_DIR).rglob("slides.md")
    ):
        print(f"ERREUR : {DECK_DIR}/ existe mais aucun {DECK_DIR}/**/slides.md "
              f"trouve -- refus de rendre un scan propre depuis une portee vide "
              f"(#15867).", file=sys.stderr)
        return 2

    # Un chemin illisible est signale, jamais tu : le scan a une portee non lue,
    # et le taire rendrait le verdict plus propre qu'il ne l'est. Il ne rougit
    # pas pour autant -- ce n'est pas un desaccord, et rc=1 y est deja pris par
    # `--fail` (c'est precisement la collision qui rendait le crash illisible).
    for u in unreadable[:20]:
        print(f"AVERTISSEMENT : chemin illisible, ignore -- {u['path']} ({u['error']})",
              file=sys.stderr)
    if len(unreadable) > 20:
        print(f"AVERTISSEMENT : {len(unreadable) - 20} autre(s) chemin(s) illisible(s) "
              f"non detailles -- relancer avec --json pour la liste complete.",
              file=sys.stderr)

    if args.json:
        print(json.dumps({"scanned": scanned, "unreadable": unreadable, "findings": findings},
                         indent=2, ensure_ascii=False))
    else:
        print(f"Fichiers scannes : {scanned}")
        if unreadable:
            print(f"Chemins illisibles (ignores) : {len(unreadable)}")
        print(f"Desaccords libelle/cible : {len(findings)}\n")
        for f in findings:
            print(f"  {f['file']}")
            print(f"    libelle dit  : {f['says']}   ([{f['label']}])")
            print(f"    cible pointe : {f['points_to']}   ({f['target']})")
    return 1 if (args.fail and findings) else 0


if __name__ == "__main__":
    sys.exit(main())
