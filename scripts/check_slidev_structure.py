#!/usr/bin/env python3
"""Deux defauts de structure Slidev qu'aucun gate existant ne voit.

Contexte (#10950, rollout `two-cols` -> `image-overlay`, 2026-08-20) : trois PRs
d'affilee ont perdu du contenu de slide, et `slides-build-advisory` n'en a
attrape qu'une seule. Les deux autres construisaient **vert**.

DEFAUT 1 -- `::right::` orphelin (silencieux, build vert)
--------------------------------------------------------
Retirer `layout: two-cols` sans retirer le `::right::` apparie laisse un
marqueur sans emplacement. Slidev **jette tout ce qui suit** : le build reussit,
la slide perd sa moitie droite. Aucun grep de source ne le voit -- le texte est
toujours dans le markdown (`grep -c 'Jeu de dames'` rend 1 sur la version
cassee comme sur la saine) ; seul un rendu ou un parseur structurel le voit.

DEFAUT 2 -- separateur colle a un titre (build rouge, message trompeur)
----------------------------------------------------------------------
Un `---` immediatement suivi d'un `# Titre`, sans ligne vide, casse le build.
Le message d'erreur pointe un mot innocent de la prose, parfois vingt lignes
plus bas (`Unresolved alias: *Environnement`), parce que YAML lit le `*` d'un
`**gras**` comme un alias. Le vrai coupable est la ligne vide manquante.

Mesure repo-wide au moment de l'ecriture : **16 decks, 0 occurrence** des deux
motifs sur `main`. Le gate ne sur-accuse donc aucun deck existant. Cette mesure
est le controle qui manque le plus souvent aux detecteurs neufs -- une suite de
tests verte prouve ce que l'auteur a imagine, pas ce que l'outil fait sur le
depot reel (cf. #11668, ou 17 constats sur 1044 notebooks etaient 17 faux
positifs malgre 10 tests verts).

Usage
-----
    python scripts/check_slidev_structure.py slides/S3-acculturation/slides.md
    python scripts/check_slidev_structure.py --all        # tous les decks
    python scripts/check_slidev_structure.py --selftest    # controle positif

Sortie : une ligne par constat, exit 1 si au moins un constat.
"""

import argparse
import pathlib
import re
import sys
import tempfile

YAML_KEY = re.compile(r"^[A-Za-z_][A-Za-z0-9_-]*\s*:")
COL_MARKER = re.compile(r"^\s*::(right|left)::\s*$")


def parse_slides(lines):
    """Decoupe en slides. Rend [(ligne_debut_1based, frontmatter, corps), ...].

    Regle Slidev reproduite : un `---` seul ouvre une slide ; si la premiere
    ligne non vide qui suit ressemble a une cle YAML, c'est du frontmatter,
    ferme par le `---` suivant -- lequel n'ouvre PAS une nouvelle slide.
    """
    slides = []
    n = len(lines)
    i = 0

    # frontmatter racine : sauter le bloc ---...--- de tete
    if i < n and lines[i].strip() == "---":
        i += 1
        while i < n and lines[i].strip() != "---":
            i += 1
        i += 1

    start, fm, body, in_fm = i, [], [], False

    def flush(begin, fm_, body_):
        if fm_ or [b for b in body_ if b.strip()]:
            slides.append((begin + 1, fm_, body_))

    while i < n:
        line = lines[i]
        if line.strip() == "---":
            if in_fm:
                in_fm = False           # fermeture du frontmatter, pas une slide
                i += 1
                continue
            flush(start, fm, body)
            start, fm, body = i + 1, [], []
            j = i + 1
            while j < n and not lines[j].strip():
                j += 1
            if j < n and YAML_KEY.match(lines[j]) and not lines[j].lstrip().startswith("#"):
                in_fm = True
            i += 1
            continue
        (fm if in_fm else body).append(line)
        i += 1

    flush(start, fm, body)
    return slides


def scan(path):
    """Rend les constats STRUCTURES : [(path, ligne, code, message), ...].

    Structure et non chaine formatee, parce que l'appelant CI doit produire une
    annotation `file=,line=` : re-decouper une chaine formatee en shell casse
    des le premier chemin contenant un `:` (`C:/Users/...` -> fichier « C »,
    mesure firsthand). Le producteur a la donnee separee, il la rend separee.
    """
    lines = pathlib.Path(path).read_text(encoding="utf-8").splitlines()
    found = []

    # --- defaut 2 : separateur colle a un titre ---------------------------
    for idx, line in enumerate(lines):
        if line.strip() != "---":
            continue
        if idx + 1 < len(lines) and lines[idx + 1].lstrip().startswith("#"):
            found.append((
                path, idx + 2, "SEP_COLLE_AU_TITRE",
                "un `---` suivi sans ligne vide de `%s` -- le frontmatter ne se "
                "ferme pas et YAML avale la prose (le message d'erreur pointera "
                "un autre mot). Inserer une ligne vide."
                % lines[idx + 1].strip()[:40],
            ))

    # --- defaut 1 : marqueur de colonne orphelin --------------------------
    for begin, fm, body in parse_slides(lines):
        if any("two-cols" in f for f in fm if f.strip().startswith("layout:")):
            continue
        for off, line in enumerate(body):
            if COL_MARKER.match(line):
                found.append((
                    path, begin + len(fm) + off, "MARQUEUR_ORPHELIN",
                    "`%s` sans `layout: two-cols` (slide ouverte ligne %d) -- "
                    "Slidev construit VERT et jette tout ce qui suit ce marqueur."
                    % (line.strip(), begin),
                ))
    return found


def check(path):
    """Rend les constats rendus lisibles (une chaine par constat)."""
    return ["%s:%d  %s  %s" % c for c in scan(path)]


SELFTEST_ORPHAN = """---
theme: default
---

# Slide saine

du texte

---
layout: two-cols
---

# Slide two-cols legitime

colonne gauche

::right::

colonne droite -- legitime, ne doit PAS etre signalee

---

# Slide cassee

colonne gauche

::right::

colonne droite -- PERDUE au rendu, doit etre signalee
"""

SELFTEST_SEP = """---
theme: default
---

# Slide saine

texte
---
# Titre colle -- doit etre signale

prose avec **du gras**
"""


def _write_tmp(content):
    with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False,
                                     encoding="utf-8") as fh:
        fh.write(content)
        return fh.name


def selftest():
    """Controle positif ET negatif.

    Un detecteur dont le motif s'est casse rend "rien trouve" -- indiscernable
    d'un depot sain, en plus petit et plus propre que la verite. Le controle
    positif est ce qui separe les deux ; le controle negatif est ce qui empeche
    de "reussir" en signalant tout.
    """
    ok = True

    for name, content, motif in (
        ("orphelin", SELFTEST_ORPHAN, "MARQUEUR_ORPHELIN"),
        ("separateur", SELFTEST_SEP, "SEP_COLLE_AU_TITRE"),
    ):
        tmp = _write_tmp(content)
        hits = [h for h in check(tmp) if motif in h]
        pathlib.Path(tmp).unlink()
        if len(hits) != 1:
            print("CONTROLE POSITIF ECHOUE (%s) : %d constat(s) %s, 1 attendu"
                  % (name, len(hits), motif))
            ok = False
        else:
            print("controle positif OK (%s) : 1 constat %s" % (name, motif))

    tmp = _write_tmp(SELFTEST_ORPHAN)
    orphans = [h for h in check(tmp) if "MARQUEUR_ORPHELIN" in h]
    pathlib.Path(tmp).unlink()
    if len(orphans) != 1:
        print("CONTROLE NEGATIF ECHOUE : la slide two-cols legitime est signalee")
        ok = False
    else:
        print("controle negatif OK : la slide two-cols legitime reste muette")

    return ok


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("paths", nargs="*", help="fichiers slides.md")
    ap.add_argument("--all", action="store_true",
                    help="scanner tous les decks de slides/")
    ap.add_argument("--selftest", action="store_true",
                    help="controle positif + negatif, puis sortir")
    ap.add_argument("--github", action="store_true",
                    help="emettre des annotations GitHub Actions (::warning file=,line=)")
    args = ap.parse_args()

    if args.selftest:
        sys.exit(0 if selftest() else 1)

    paths = list(args.paths)
    if args.all:
        paths += [str(p) for p in sorted(pathlib.Path("slides").rglob("slides.md"))]
    if not paths:
        ap.error("aucun fichier : passer des chemins ou --all")

    paths = [p for p in paths if pathlib.Path(p).exists()]
    total = []
    for p in paths:
        total += scan(p)

    for path, line, code, msg in total:
        if args.github:
            # Le producteur rend `file=` et `line=` separement : aucune chaine
            # formatee n'est re-decoupee en aval.
            print("::warning file=%s,line=%d::%s %s" % (path, line, code, msg))
        else:
            print("%s:%d  %s  %s" % (path, line, code, msg))
    print()
    print("decks scannes : %d | constats : %d" % (len(paths), len(total)))
    sys.exit(1 if total else 0)


if __name__ == "__main__":
    main()
