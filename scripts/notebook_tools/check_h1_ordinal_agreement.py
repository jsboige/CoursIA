#!/usr/bin/env python3
"""Detecte les carnets dont le H1 nomme un ordinal different de leur nom de fichier.

Pourquoi cet outil existe
-------------------------
Issue #22291. Les evenements `renum()`/`reclass()` (cf
`docs/reference/notebook-renumbering-detail.md`) renumerotent le **nom de
fichier** ; le H1 interne, lui, n'est pas toujours suivi. Quand il reste en
arriere, le desaccord est invisible dans le depot mais **visible dans le
parcours genere** : `docs/curriculum/recherche.md` affiche comme libelle le
premier heading du carnet (`extract_title`, `scripts/notebook_tools/
generate_catalog.py:561`) et comme lien le chemin du fichier. Le lecteur voit
alors un libelle qui contredit sa cible.

Mesure fondatrice : 18 carnets en desaccord sur le catalogue du 2026-10-24,
repares a la main par #22357 / #22364 / #22365 puis #23230. Un mois plus tot,
le meme defaut avait deja produit des libelles « ICT-15d » pointant vers
ICT-15j (#13645) — c'etait la meme classe, vue par les liens plutot que par
les H1.

Pourquoi aucun garde existant ne le voit
----------------------------------------
Tous verifient qu'une cible EXISTE ; ici elle existe, c'est l'etiquette qui
ment.

- `check_docs_links.py` / `check_notebook_navlinks.py` : 404 sur les cibles.
- `check_link_label_agreement.py` : compare le libelle d'un **lien** a sa
  cible. Le H1 n'est pas un lien ; il devient un libelle par la generation.
- `h1_hygiene_scan.py` : hygiene de forme du H1 (markup inline, emoji, prefixe
  « Notebook: »), jamais l'ordinal.
- `generate_catalog.py` : lit fidelement les deux sources ; la faute est dans
  la metadonnee du carnet, pas dans le generateur.

Aucun ne compare le H1 au nom de fichier. C'est le predicat ajoute ici, et rien
d'autre.

Ce que l'outil signale
----------------------
Quatre classes, jamais mélangees — parce qu'elles n'appellent pas le meme
geste :

- `drift` : le H1 nomme une **autre identite** que le fichier — autre serie
  (`Dynamics-01-...` dont le H1 dit `GameTheory-6c`) ou autre ordinal
  (`GameTheory-03c-...` dont le H1 dit `GameTheory 3b`). C'est le defaut de
  #22291, et le seul que `--fail` compte.
- `generic` : le H1 porte le **bon ordinal** mais un mot de serie generique
  (`# Notebook 9: Resolution de Sudoku ...` sur `Sudoku-09-...`). Le libelle
  genere est juste, il est seulement **interchangeable** : « Notebook 9 »
  designe un carnet dans chaque serie du depot. C'est une decision de
  convention de nommage, pas une derive d'ordinal — d'ou le compte separe.
- `ambiguous` : le H1 porte un **chiffre nu <= 5** apres un mot de langage
  (`Lean 4 - Installation ...` sur `Lean-01-...`). Le « 4 » peut etre la
  version du langage et non un ordinal. Compte a part, jamais comme derive :
  c'est un cas a trancher par ecrit, ce que #22291 a fait pour `Lean-01`.
- `missing_h1` : le carnet n'a **aucun** heading de niveau 1. Ce n'est **pas**
  une lacune de libelle : `extract_title` accepte un heading de **n'importe
  quel niveau**, donc un carnet qui porte `## ICT-22b — ...` publie deja un
  libelle riche, et le repli sur le nom de fichier
  (`"title": title or nb_path.stem`, `generate_catalog.py:1301`) ne se
  declenche que sur un libelle **vide** — cas inexistant dans le corpus (1676
  carnets sur 1677 ont un libelle). Ce que la classe signale est donc une
  **incoherence de niveau** : un `## ` la ou la convention du depot attend
  `# `. Les cinq carnets concernes (`ICT-22b`, `ICT-35`, `ICT-35b`, `ICT-35c`,
  `ICT-35d`) en sont l'illustration exacte.

Un H1 en prose libre (« Capstone Geometry — l'escalier ... ») ne declenche
rien : l'absence d'identifiant n'est pas un desaccord. Le H1 est cherche dans
**toutes** les cellules markdown, pas seulement la premiere : la convention du
depot place le bloc de navigation avant le titre.

Ce que l'outil ne voit pas, et qu'il faut savoir avant de s'y fier
------------------------------------------------------------------
Deux restrictions deliberees, mesurees sur le corpus du 2026-10-29. Aucune ne
produit de faux verdict aujourd'hui, mais toutes deux cadrent la portee :

- **Le niveau 1 seulement, quand le catalogue lit tous les niveaux.** Un carnet
  dont le `## ` nomme une autre identite que le fichier passe ici pour
  `missing_h1` (ou pour rien si un `# ` correct le precede), alors que le
  libelle publie, lui, vient du `## `. Mesure : **0 cas vivant** sur les 1677
  carnets. La branche est ecrite pour le futur, et c'est le futur qui decidera
  s'il faut lire les headings comme `extract_title` le fait.
- **Les fences ne sont pas suivis** : un `# ` a l'interieur d'un bloc de code
  est pris pour un H1. `generate_catalog.py` a le meme angle mort, donc les
  deux ne divergent pas — fragilite commune, pas un desaccord a detecter.

**Denominateur et couverture.** Le balayage par defaut couvre **1677** carnets
sous `MyIA.AI.Notebooks/` (1689 fichiers `.ipynb` moins 12 sous un
`_archive/`). Sur ces 1677, **930 seulement** portent une identite de fichier
exploitable au sens de `FILE_ID_RE` : les 747 autres, dont **168** dont le
second segment est alphabetique (`QC-Py-01-…`, `Argumentation-Obs-03-…`,
`Probas-KLS-…`), sont hors perimetre **par construction** et ne peuvent
produire aucun verdict. Un carnet illisible (JSON tronque) sortait du
denominateur en silence ; la sortie `--json` porte desormais un compteur
`unreadable`, pour que ce silence soit mesurable.

Usage
-----
    python scripts/notebook_tools/check_h1_ordinal_agreement.py [--json] [--fail]
    python scripts/notebook_tools/check_h1_ordinal_agreement.py --paths a.ipynb b.ipynb
    python scripts/notebook_tools/check_h1_ordinal_agreement.py --self-test

`--fail` transforme la presence de `drift` en code de retour 1. Sans lui,
l'outil est advisory (code 0), comme `h1_hygiene_scan.py` et
`check_link_label_agreement.py`.

Portee
------
Les carnets de `MyIA.AI.Notebooks/` par defaut. Ne modifie rien : le correctif
est une edition markdown-only du H1, et les pages generees suivent au prochain
passage catalogue — jamais a la main (`catalog-pr-hygiene`).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
SCAN_GLOB = "MyIA.AI.Notebooks/**/*.ipynb"
EXCLUDE_PARTS = {".ipynb_checkpoints", "_archive", "_archives", ".lake", "node_modules", ".git"}

# `GameTheory-03c-Chambres-...` -> (gametheory, 3, c)
FILE_ID_RE = re.compile(r"^(?P<pre>[A-Za-z][A-Za-z0-9]*)-(?P<num>\d{1,2})(?P<let>[a-z])?-")
# `GameTheory-3b — ...` / `GameTheory 3c : ...` / `KNOTS-01 — ...`
H1_ID_RE = re.compile(
    r"^\s*#+\s*(?P<pre>[A-Za-z][A-Za-z0-9]*)[-\s]+(?P<num>\d{1,2})(?P<let>[a-z])?(?![A-Za-z0-9])"
)

# Mots apres lesquels un chiffre nu peut etre une VERSION et non un ordinal.
# Le seuil est celui de #22291 : « Lean 4 » designe la version du langage.
VERSIONISH_WORDS = {"lean", "python", "csharp", "dotnet", "fsharp", "java", "julia", "rust", "swift"}
VERSION_MAX = 5

# Mots qui nomment un carnet sans nommer sa serie : « Notebook 9 » designe un
# carnet dans chaque serie du depot. Le libelle reste juste, il est seulement
# interchangeable — classe separee, jamais comptee comme derive.
GENERIC_SERIES = {"notebook", "carnet", "lecon", "lesson", "chapitre", "partie", "module", "tutoriel", "tutorial"}


def ident(pre: str, num: str, let_: str | None):
    """Identite normalisee : (mot de serie en minuscules, entier, lettre).

    La normalisation est celle que #22291 a etablie : zero initial neutre
    (`04c` == `4c`), tiret et espace equivalents, casse neutre.
    """
    return (pre.lower(), int(num), (let_ or "").lower())


def file_identity(path: Path):
    m = FILE_ID_RE.match(path.name)
    return ident(m.group("pre"), m.group("num"), m.group("let")) if m else None


def h1_of(nb: dict):
    """Premier heading de niveau 1 du carnet, ou None."""
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "markdown":
            continue
        src = cell.get("source", "")
        text = "".join(src) if isinstance(src, list) else src
        for line in text.splitlines():
            if line.lstrip().startswith("# "):
                return line.strip()
    return None


def classify(path: Path, nb: dict):
    """Un dict de finding, `None` si le carnet est muet (pas d'identite file)."""
    fid = file_identity(path)
    if not fid:
        return None
    h1 = h1_of(nb)
    if h1 is None:
        return {"file": str(path), "kind": "missing_h1", "h1": None, "says": None, "file_says": f"{fid[0]}-{fid[1]}{fid[2]}"}
    m = H1_ID_RE.match(h1)
    if not m:
        return None  # H1 en prose libre : pas un desaccord, pas une lacune
    hid = ident(m.group("pre"), m.group("num"), m.group("let"))
    if hid == fid:
        return None
    record = {
        "file": str(path),
        "kind": "drift",
        "h1": h1[:100],
        "says": f"{hid[0]}-{hid[1]}{hid[2]}",
        "file_says": f"{fid[0]}-{fid[1]}{fid[2]}",
    }
    if hid[0] in GENERIC_SERIES and hid[1:] == fid[1:]:
        record["kind"] = "generic"
    elif hid[0] in VERSIONISH_WORDS and hid[1] <= VERSION_MAX and not hid[2]:
        record["kind"] = "ambiguous"
    return record


def iter_notebooks(paths):
    if paths:
        for p in paths:
            yield Path(p)
        return
    for p in sorted(REPO_ROOT.glob(SCAN_GLOB)):
        if EXCLUDE_PARTS & set(p.parts):
            continue
        yield p


def scan(paths=None):
    """Rend `(findings, unreadable)`.

    `unreadable` compte les carnets qui n'ont pas pu etre parses. Sans ce
    compteur, un JSON tronque disparaissait du denominateur **en silence** —
    exactement ce que `test_the_organ_scans_the_repository_at_all` interdit par
    ailleurs (« un resultat vide doit vouloir dire un arbre propre, pas un
    mauvais glob »). Mesure du 2026-10-29 : 0 echec sur 1677, aucun effet
    aujourd'hui ; le compteur rend le silence mesurable pour la suite.
    """
    findings = []
    unreadable = []
    for p in iter_notebooks(paths):
        try:
            nb = json.loads(p.read_text(encoding="utf-8"))
        except Exception as exc:
            unreadable.append({"file": str(p), "error": f"{type(exc).__name__}: {exc}"})
            continue
        rec = classify(p, nb)
        if rec:
            findings.append(rec)
    return findings, unreadable


def self_test() -> int:
    """Controles positif et negatifs, sans lire le depot."""
    cases = []

    def nb_with_h1(h1):
        return {"cells": [{"cell_type": "markdown", "source": [h1 + "\n", "suite"]}]}

    # positif : derive reelle, zero initial normalise
    cases.append(("GameTheory-03b-Chambres-Murs-Chemins-Lean-Python.ipynb", nb_with_h1("# GameTheory 3c : Chambres"), "drift"))
    # positif : derive de serie (reclass)
    cases.append(("Dynamics-01-Jeux-Repetes-Folk-Theorem-Python.ipynb", nb_with_h1("# GameTheory-6c : Jeux repetes"), "drift"))
    # negatif : zero initial et tiret/espace equivalents
    cases.append(("KNOTS-01-Conway-Proofs-Lean-Python.ipynb", nb_with_h1("# KNOTS-01 — Conway"), None))
    cases.append(("Search-09e-Komlos-Lean.ipynb", nb_with_h1("# Search 9e — Discrepance"), None))
    # negatif : H1 en prose libre (pas d'identifiant)
    cases.append(("Lean-38-Capstone-Geometry-Lean-Python.ipynb", nb_with_h1("# Capstone Geometry — l'escalier"), None))
    # ambigu : chiffre nu apres un mot de langage
    cases.append(("Lean-01-Setup-Lean-Python.ipynb", nb_with_h1("# Lean 4 - Installation et Configuration"), "ambiguous"))
    # negatif : le cas repare par #23230
    cases.append(("Lean-01-Setup-Lean-Python.ipynb", nb_with_h1("# Lean 01 - Installation et configuration de Lean 4"), None))
    # lacune : aucun H1
    cases.append(("Dynamics-01-Jeux-Repetes-Folk-Theorem-CSharp.ipynb", {"cells": [{"cell_type": "markdown", "source": ["## Sous-titre"]}]}, "missing_h1"))
    # negatif : un nom de fichier sans identite n'est pas un carnet de serie
    cases.append(("Diagnostic-Medical.ipynb", nb_with_h1("# CC1 - IA Exploratoire"), None))
    # generique : bon ordinal, mot de serie interchangeable
    cases.append(("Sudoku-09-GraphColoring-CSharp.ipynb", nb_with_h1("# Notebook 9: Resolution de Sudoku"), "generic"))
    cases.append(("RL-02-Wrappers-Sauvegarde-Callbacks-Python.ipynb", nb_with_h1("# Notebook 2 - Wrappers Gym"), "generic"))
    # negatif : un generique au MAUVAIS ordinal n'est pas generique, c'est une derive
    cases.append(("Sudoku-09-GraphColoring-CSharp.ipynb", nb_with_h1("# Notebook 11: Resolution de Sudoku"), "drift"))
    # negatif : le H1 peut suivre le bloc de navigation dans la meme cellule
    cases.append(("KNOTS-02-Invariants-Python.ipynb",
                  {"cells": [{"cell_type": "markdown", "source": ["**Navigation** : [Index](README.md)\n", "\n", "# KNOTS-02 — Invariants\n"]}]}, None))

    failures = 0
    with tempfile.TemporaryDirectory() as tmp:
        for name, nb, expected in cases:
            p = Path(tmp) / name
            p.write_text(json.dumps(nb), encoding="utf-8")
            got = classify(p, nb)
            got_kind = got["kind"] if got else None
            ok = got_kind == expected
            if not ok:
                failures += 1
            print(f"{'OK   ' if ok else 'ECHEC'} {name} -> {got_kind!r} (attendu {expected!r})")
    print(f"\nself-test : {len(cases) - failures}/{len(cases)}")
    return 1 if failures else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--json", action="store_true", help="sortie machine")
    ap.add_argument("--fail", action="store_true", help="code de retour 1 si une derive est trouvee")
    ap.add_argument("--paths", nargs="+", metavar="IPYNB", help="carnets a examiner (defaut : tout le depot)")
    ap.add_argument("--self-test", action="store_true", help="controles positif et negatifs, sans lire le depot")
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    findings, unreadable = scan(args.paths)
    drifts = [f for f in findings if f["kind"] == "drift"]
    generic = [f for f in findings if f["kind"] == "generic"]
    ambiguous = [f for f in findings if f["kind"] == "ambiguous"]
    missing = [f for f in findings if f["kind"] == "missing_h1"]

    if args.json:
        print(json.dumps(
            {"drift": drifts, "generic": generic, "ambiguous": ambiguous, "missing_h1": missing,
             "unreadable": unreadable,
             "counts": {"drift": len(drifts), "generic": len(generic),
                        "ambiguous": len(ambiguous), "missing_h1": len(missing),
                        "unreadable": len(unreadable)}},
            ensure_ascii=False, indent=2))
    else:
        print(f"derive d'identite (serie ou ordinal) : {len(drifts)}")
        for f in drifts:
            print(f"  {f['file']}\n      H1 dit {f['says']} -> fichier dit {f['file_says']} | {f['h1']}")
        print(f"mot de serie generique (bon ordinal) : {len(generic)}")
        for f in generic:
            print(f"  {f['file']}\n      H1 dit {f['says']} -> fichier dit {f['file_says']} | {f['h1']}")
        print(f"cas ambigus (chiffre nu, possible version) : {len(ambiguous)}")
        for f in ambiguous:
            print(f"  {f['file']}\n      H1 dit {f['says']} | {f['h1']}")
        print(f"carnets sans H1 : {len(missing)}")
        for f in missing:
            print(f"  {f['file']}")
        if unreadable:
            print(f"carnets illisibles (hors denominateur) : {len(unreadable)}")
            for f in unreadable:
                print(f"  {f['file']}\n      {f['error']}")

    if args.fail and drifts:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
