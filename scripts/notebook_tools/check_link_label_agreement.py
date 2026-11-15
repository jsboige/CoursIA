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
Le cas non ambigu : le libelle porte un identifiant de notebook et il **differe**
de celui de la cible. Un libelle en prose (« voir le notebook sur les faisceaux »)
ne declenche rien : l'absence d'identifiant n'est pas un desaccord.

Deux chemins, depuis #23684 :

- **meme famille** que la cible : l'identifiant est cherche **partout** dans le
  libelle, et l'ordinal doit concorder (comportement d'origine, #13645) ;
- **famille differente** : c'est le cas du **reclass** -- un carnet change de
  famille, le href suit, le libelle reste a l'ancien nom (`GameTheory-6c` vers
  `Dynamics-01-...`). Deux bornes le rendent exploitable plutot que bruyant :
  la famille citee doit exister dans le corpus (`corpus_families`), et
  l'identifiant doit **ouvrir** le libelle (`leading_label_id`). Sans elles,
  le vocabulaire du domaine (standard `ERC-20`, modele `Qwen3.5-0.8B`,
  bibliotheque `DoWhy-2`) et les alias propres a un deck (`AA-1-informal`)
  entrent dans la comparaison : mesure du 2026-11-06, 169 findings en lecture
  libre contre 84 avec les deux bornes.

La population mesuree au 2026-11-06 sur `origin/main` est de **84** findings
(contre 1 avant l'elargissement) : la classe dominante est celle du reclass
(`Lean-17a`->`KNOTS-01`, `Lean-22`->`GALOIS-01`, `GameTheory-06x`->`Dynamics-0x`).
Le correctif de **contenu** de ces libelles ne releve pas de cet organe
(#22291, #20442) ; celui-ci ne fait que rendre le desaccord visible. Le
check-run CI est **advisory**, donc l'elargissement ne rougit aucune PR.

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
# <famille>-<num><lettre?> : identifiant cite DANS un libelle, quelle que soit
# la famille (#23684). La famille n'est pas ancree a celle de la cible : c'est
# ce qui rend visible un libelle qui nomme une AUTRE famille.
ID_IN_LABEL_RE = re.compile(
    r"\b(?P<fam>[A-Za-z][A-Za-z0-9]*(?:[._][A-Za-z0-9]+)*)[-_](?P<num>\d{1,3})(?P<let>[a-z])?\b",
    re.I,
)


def target_id(filename: str):
    """(prefixe, numero, lettre) depuis un nom de fichier notebook, ou None."""
    m = ID_IN_NAME_RE.match(Path(filename).name)
    if not m:
        return None
    return (m.group("pre").lower(), int(m.group("num")), (m.group("let") or "").lower())


def labels_in_text(text: str, families=None):
    """Identifiants `famille-NN[l]` cites dans le libelle.

    `families=None` n'impose aucune restriction (self-test, mesure) ; sinon seuls
    les prefixes presents dans le corpus sont retenus (#23684). La restriction
    n'est pas cosmetique : sans elle, une date (`2024-01`), une version ou un
    numero d'issue ressemblant a un identifiant entreraient dans la comparaison.
    """
    out = []
    for fam, n, l in ID_IN_LABEL_RE.findall(text):
        fam = fam.lower()
        if families is not None and fam not in families:
            continue
        out.append((fam, int(n), (l or "").lower()))
    return out


# Decoration de tete toleree devant un identifiant de libelle (nav, gras, citation).
LEAD_STRIP = " \t\r\n*_`\"'«»()[]|#>~-–—:,.←→↑↓<>/\\"


def leading_label_id(text: str, families=None):
    """Identifiant qui OUVRE le libelle, ou None (#23684).

    Le reclass se lit en tete : `<famille>-<NN>` puis un separateur puis le
    titre. Chercher l'identifiant n'importe ou dans le libelle ramene la
    prose -- une glose `(Qwen3.5-0.8B)`, un standard `(Solidity ERC-20)`, un
    nom de modele `Z-Image (Lumina-2)` -- et rougit 87 fois a tort sur le
    corpus mesure le 2026-11-06. La tete seule separe la citation d'identifiant
    du vocabulaire du domaine.
    """
    s = text.lstrip(LEAD_STRIP)
    m = ID_IN_LABEL_RE.match(s)
    if not m:
        return None
    fam = m.group("fam").lower()
    if families is not None and fam not in families:
        return None
    return (fam, int(m.group("num")), (m.group("let") or "").lower())


def check_text(source: str, path: str, families=None):
    out = []
    for label, target in LINK_RE.findall(source):
        tid = target_id(target)
        if not tid:
            continue
        prefix, tnum, tlet = tid
        lead = leading_label_id(label, families)
        for lfam, lnum, llet in labels_in_text(label, families):
            # Famille de la cible : comportement inchange (toute position).
            # Autre famille (#23684) : seule la tete du libelle compte, sinon
            # le vocabulaire du domaine rentre dans la comparaison.
            if lfam != prefix and (lfam, lnum, llet) != lead:
                continue
            if (lnum, llet) != (tnum, tlet):
                out.append({
                    "file": path,
                    "label": label.strip()[:80],
                    "target": target,
                    "says": f"{lfam}-{lnum}{llet}",
                    "points_to": f"{prefix}-{tnum}{tlet}",
                })
                break
    return out


def corpus_families(root: Path) -> set:
    """Prefixes de famille presents dans le corpus de notebooks (#23684)."""
    fams = set()
    for p in root.glob("MyIA.AI.Notebooks/**/*.ipynb"):
        if EXCLUDE_PARTS & set(p.parts):
            continue
        tid = target_id(p.name)
        if tid:
            fams.add(tid[0])
    return fams


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


# Univers de familles fige pour le self-test : il doit rendre le meme verdict
# quelle que soit la machine, y compris sur un corpus partiel (#23684).
SELF_TEST_FAMILIES = {"ict", "lean", "gametheory", "search", "dynamics", "analyse", "pt"}

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
    # #23684 -- le predicat comparait le libelle a la famille de la CIBLE, donc un
    # libelle nommant une AUTRE famille n'etait jamais lu (0 finding, quel que
    # soit l'ordinal affiche).
    ("[GameTheory-6c](../IIT/Dynamics/Dynamics-01-Bifurcations.ipynb)", 1,
     "#23684 controle POSITIF : famille differente + ordinal different -- doit ROUGIR"),
    ("[PT-06b](../Analyse/ANALYSE-06b-Etude.ipynb)", 0,
     "#23684 controle NEGATIF : famille differente + ordinal CORRECT -- doit passer"),
    ("[ANALYSE-06](../Analyse/ANALYSE-06b-Etude.ipynb)", 1,
     "#23684 meme famille, lettre perdue -- doit ROUGIR"),
]


def self_test() -> int:
    ok = True
    for src, expected, title in SELF_TEST_CASES:
        got = len(check_text(src, "<self-test>", SELF_TEST_FAMILIES))
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

    families = corpus_families(REPO_ROOT)

    findings, scanned, unreadable = [], 0, []
    for p in iter_scan_files(REPO_ROOT, SCAN_GLOBS + (DECK_GLOB,), unreadable):
        scanned += 1
        rel = p.relative_to(REPO_ROOT).as_posix()
        if p.suffix == ".ipynb":
            for src in cell_sources(p):
                findings += check_text(src, rel, families)
        else:
            try:
                findings += check_text(p.read_text(encoding="utf-8"), rel, families)
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
