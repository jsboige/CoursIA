#!/usr/bin/env python3
"""Refuser un notebook AJOUTE dont l'index de serie est deja pris dans son repertoire.

Origine -- #12753. Le 2026-08-24, la sous-serie `03-DeepLearning` a recu deux
notebooks `3.1` a vingt-neuf minutes d'intervalle : `3.1-Retropropagation.ipynb`
(#12736) puis `3.1-Retropropagation-From-Scratch.ipynb` (#12468). Meme lane, meme
issue, et les deux mergés par le coordinateur. La lane n'avait pas faute : elle avait
ouvert une branche fraiche pour sortir une PR d'une file saturee -- manoeuvre
recommandee -- et l'ancienne PR est devenue mergeable derriere.

Le defaut etait cote merge-gate. Les gardes verifiaient les nits, le perimetre,
l'execution des cellules, le tag de grain, le cap de variation. Aucun ne demandait si
le contenu ajoute existait deja sur `main` sous un autre nom de fichier. Aucune dose
de vigilance supplementaire ne ferme un angle mort de cette classe.

CE QUE CE GARDE MESURE, ET CE QU'IL NE MESURE PAS
-------------------------------------------------
Il compare des **index de position dans une serie**, pas du contenu. Deux notebooks
qui traitent le meme sujet sous des index differents ne le declenchent pas ; deux
notebooks sans rapport qui se disputent l'index `3.1` le declenchent. C'est
volontaire : l'index est ce qui rend une serie navigable, et c'est la grandeur qu'une
machine peut trancher sans se tromper. La redondance de CONTENU reste un jugement
humain, et ce garde ne la certifie pas -- un vert dit « aucun index en conflit », il
ne dit jamais « aucun doublon ».

Portee : **uniquement les fichiers AJOUTES** par la revision examinee, confrontes a
la base. Les collisions deja presentes sur `main` ne le font pas rougir -- sinon il
serait rouge des sa naissance et chaque PR echouerait sur une dette qu'elle n'a pas
creee. Il empeche la recurrence, il ne solde pas le passe. Les collisions existantes
se traitent par une issue (cf. #12753), pas par un gate qui bloque tout le monde.

DEUX FAUX POSITIFS QUE LE PREMIER JET PRODUISAIT
------------------------------------------------
Mesure repo-wide au moment d'ecrire ce fichier : 1116 notebooks sur `main`, un
prefixe numerique naif accusait **17** collisions dont **1** seule etait reelle.

1. Series a DEUX niveaux. `GenAI/Audio/04-Applications` porte `04-1-...` a
   `04-13-...` : le premier nombre est la **categorie**, le second l'**item**. La cle
   est `04-1`, pas `04`. Lire seulement le premier nombre transforme une serie bien
   formee de treize notebooks en treize collisions.
2. Paires de langue. `GameTheory/SocialChoice` porte
   `01-Arrow-Impossibility-Theorem.ipynb` et son frere `-Csharp`. Ce sont deux
   rendus du meme item, par convention du depot -- pas deux items en conflit. Idem
   pour les siblings `_en` de la convention i18n #4980.

Les deux sont couverts par des tests. Un motif de detection se valide par ses **faux
negatifs et ses faux positifs**, jamais par ses hits.

Usage
-----
    python scripts/notebook_tools/check_duplicate_notebook_index.py --base origin/main
    python scripts/notebook_tools/check_duplicate_notebook_index.py --base origin/main --json
    python scripts/notebook_tools/check_duplicate_notebook_index.py --self-test

Sortie : 0 = aucune collision introduite ; 1 = collision ; 2 = erreur d'invocation.
Le denombrement des fichiers examines est TOUJOURS imprime, y compris quand la
reponse est zero : « rien trouve » et « rien regarde » ne doivent jamais partager la
meme sortie.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys

# Suffixes marquant un rendu ALTERNATIF du meme item, pas un item concurrent.
# -Csharp / -Python : paires de langage (GameTheory/SocialChoice).
# _en / _fr         : siblings i18n (#4980).
LANG_SUFFIXES = ("-csharp", "-python", "_en", "-en", "_fr", "-fr")

# Index en tete de nom : un ou plusieurs nombres separes par . ou -, suivis d'un
# separateur puis du titre. On capture TOUS les niveaux : "04-1" et non "04".
#   3.1-Retropropagation      -> 3.1
#   04-13-Audiobook           -> 04-13
#   22_Evaluating             -> 22
#   MGS-26-Equilibrium        -> (prefixe alphabetique : aucun index, ignore)
#
# Le suffixe de lettre est CAPTURE separement et fait partie de l'index. La serie
# `02-ML-Cours` porte `2.3b`, `2.5b`, `2.8b`, `2.8c` : la lettre designe une variante
# inseree entre deux items numerotes, c'est un index a part entiere. Sans le groupe
# `[a-z]?`, le moteur retrograde par-dessus la lettre et rend `2` pour les quatre --
# quatre notebooks legitimes deviennent six collisions. Ce faux positif n'a PAS ete
# trouve par les tests unitaires mais par le balayage des 1116 notebooks de `main` :
# un jeu de cas ecrit a la main ne contient que les formes auxquelles on a pense.
_INDEX_RE = re.compile(r"^(\d+(?:[.\-]\d+)*)([a-z]?)[._\-\s]", re.I)


def index_key(filename):
    """Index de serie d'un nom de fichier, ou None s'il n'en porte pas."""
    stem = re.sub(r"\.ipynb$", "", filename, flags=re.I)
    m = _INDEX_RE.match(stem)
    if not m:
        return None
    # Normalise separateurs de niveau et zero-padding : 04-1 et 4.1 sont le meme
    # index. Sans cette normalisation, un zero-pad partiel ouvrirait une porte de
    # contournement silencieuse.
    parts = re.split(r"[.\-]", m.group(1))
    return ".".join(str(int(p)) for p in parts) + m.group(2).lower()


def strip_lang(filename):
    """Nom sans son suffixe de langue, pour apparier les rendus d'un meme item."""
    stem = re.sub(r"\.ipynb$", "", filename, flags=re.I)
    low = stem.lower()
    for suf in LANG_SUFFIXES:
        if low.endswith(suf):
            return stem[: -len(suf)]
    return stem


def _git(args):
    env = dict(os.environ, MSYS_NO_PATHCONV="1")
    r = subprocess.run(["git"] + args, capture_output=True, text=True,
                       encoding="utf-8", errors="replace", env=env)
    if r.returncode != 0:
        raise RuntimeError("git %s -> %s" % (" ".join(args), (r.stderr or "").strip()[:200]))
    return r.stdout


def added_notebooks(base, head):
    out = _git(["diff", "--diff-filter=A", "--name-only", "%s...%s" % (base, head)])
    return [l.strip() for l in out.splitlines() if l.strip().lower().endswith(".ipynb")]


def notebooks_at(ref):
    out = _git(["ls-tree", "-r", "--name-only", ref])
    return [l.strip() for l in out.splitlines() if l.strip().lower().endswith(".ipynb")]


def collisions(added, base_files):
    """Chaque fichier ajoute dont l'index est deja tenu dans SON repertoire."""
    by_dir = {}
    for p in base_files:
        d, b = os.path.split(p)
        by_dir.setdefault(d, []).append(b)

    found = []
    for p in added:
        d, b = os.path.split(p)
        key = index_key(b)
        if key is None:
            continue
        mine = strip_lang(b).lower()
        for other in by_dir.get(d, []):
            if other == b:
                continue
            if index_key(other) != key:
                continue
            if strip_lang(other).lower() == mine:
                continue  # rendu alternatif du meme item : legitime
            # Chemin de depot : separateur POSIX, jamais os.sep (backslash sous
            # Windows). La sortie est lue par des humains ET comparee a des chemins
            # git, qui n'utilisent que "/".
            found.append({"added": p, "index": key,
                          "conflicts_with": "%s/%s" % (d, other) if d else other})
    return found


# ---------------------------------------------------------------- self-test
_CASES = [
    ("3.1-Retropropagation.ipynb", "3.1"),
    ("3.1-Retropropagation-From-Scratch.ipynb", "3.1"),
    ("04-13-Audiobook-FishAudio-S2Pro.ipynb", "4.13"),
    ("04-1-Educational-Audio-Content.ipynb", "4.1"),
    ("22_Evaluating_Generated_Text.ipynb", "22"),
    ("22_TensorSharp_DotNet_Inference.ipynb", "22"),
    ("01-Arrow-Impossibility-Theorem.ipynb", "1"),
    # Variantes a suffixe de lettre (serie 02-ML-Cours). Trouvees par le balayage
    # repo-wide, pas par ce jeu de cas : c'est pourquoi le balayage existe.
    ("2.3b-Naive-Bayes-Generatif.ipynb", "2.3b"),
    ("2.8b-Theorie-PAC-Lean.ipynb", "2.8b"),
    ("2.8c-Borne-Temoin-Concentration.ipynb", "2.8c"),
    ("MGS-26-EquilibriumOptimizer-vs-Mealpy.ipynb", None),
    ("README-notes.ipynb", None),
]

_SCENARIOS = [
    ("VRAI POSITIF  index 3.1 deja pris",
     ["a/03-DL/3.1-Retropropagation-From-Scratch.ipynb"],
     ["a/03-DL/3.1-Retropropagation.ipynb"], 1),
    ("VRAI POSITIF  index 22 deja pris",
     ["g/Texte/22_TensorSharp_DotNet_Inference.ipynb"],
     ["g/Texte/22_Evaluating_Generated_Text.ipynb"], 1),
    ("FAUX POSITIF  serie a deux niveaux 04-1 vs 04-2",
     ["g/Audio/04-2-Transcription-Pipeline.ipynb"],
     ["g/Audio/04-1-Educational-Audio-Content.ipynb"], 0),
    ("FAUX POSITIF  paire de langue Csharp",
     ["s/01-Arrow-Impossibility-Theorem-Csharp.ipynb"],
     ["s/01-Arrow-Impossibility-Theorem.ipynb"], 0),
    ("FAUX POSITIF  sibling i18n _en",
     ["s/07-Shapley_en.ipynb"], ["s/07-Shapley.ipynb"], 0),
    ("FAUX POSITIF  meme index, repertoire different",
     ["x/3.1-Autre.ipynb"], ["y/3.1-Retropropagation.ipynb"], 0),
    ("FAUX POSITIF  prefixe alphabetique sans index",
     ["s/MGS-27-Forensic.ipynb"], ["s/MGS-26-Equilibrium.ipynb"], 0),
    ("FAUX POSITIF  variantes a lettre 2.8b vs 2.8c",
     ["m/02-ML/2.8c-Borne-Temoin-Concentration.ipynb"],
     ["m/02-ML/2.8b-Theorie-PAC-Lean.ipynb"], 0),
    ("FAUX POSITIF  variante a lettre vs numerique nu 2.3b vs 2.5b",
     ["m/02-ML/2.5b-Calibration-Probabilites.ipynb"],
     ["m/02-ML/2.3b-Naive-Bayes-Generatif.ipynb"], 0),
    ("VRAI POSITIF  meme lettre, meme index 2.8b",
     ["m/02-ML/2.8b-Autre-Sujet.ipynb"],
     ["m/02-ML/2.8b-Theorie-PAC-Lean.ipynb"], 1),
    ("NEGATIF       aucun ajout",
     [], ["a/03-DL/3.1-Retropropagation.ipynb"], 0),
]


def self_test():
    ko = 0
    print("--- extraction d'index (%d cas) ---" % len(_CASES))
    for name, want in _CASES:
        got = index_key(name)
        ok = got == want
        ko += 0 if ok else 1
        print("  %-4s %-46s -> %-6s (attendu %s)"
              % ("OK" if ok else "KO", name, got, want))

    print("")
    print("--- collisions (controles positifs ET negatifs) ---")
    for label, added, base, want in _SCENARIOS:
        got = len(collisions(added, base))
        ok = got == want
        ko += 0 if ok else 1
        print("  %-4s %-48s -> %d (attendu %d)"
              % ("OK" if ok else "KO", label, got, want))

    total = len(_CASES) + len(_SCENARIOS)
    print("")
    print("%s : %d cas, %d echec(s)" % ("ECHEC" if ko else "SUCCES", total, ko))
    return 1 if ko else 0


def main():
    ap = argparse.ArgumentParser(
        description="Refuser un notebook ajoute dont l'index de serie est deja pris.")
    ap.add_argument("--base", default="origin/main", help="revision de base (defaut: origin/main)")
    ap.add_argument("--head", default="HEAD", help="revision examinee (defaut: HEAD)")
    ap.add_argument("--json", action="store_true", help="sortie machine")
    ap.add_argument("--self-test", action="store_true", help="controles positifs et negatifs")
    a = ap.parse_args()

    if a.self_test:
        return self_test()

    try:
        added = added_notebooks(a.base, a.head)
        base_files = notebooks_at(a.base)
    except RuntimeError as e:
        print("ERREUR git : %s" % e, file=sys.stderr)
        return 2

    hits = collisions(added, base_files)

    if a.json:
        print(json.dumps({"base": a.base, "head": a.head,
                          "added_notebooks": len(added),
                          "base_notebooks": len(base_files),
                          "collisions": hits}, indent=2, ensure_ascii=False))
        return 1 if hits else 0

    # Le denominateur est imprime meme quand la reponse est zero : « rien trouve »
    # et « rien regarde » ne doivent jamais avoir la meme sortie.
    print("notebooks ajoutes examines : %d   (base %s : %d notebooks)"
          % (len(added), a.base, len(base_files)))
    if not added:
        print("VERDICT: OK -- aucun notebook ajoute, rien a verifier.")
        return 0
    for p in added:
        print("   + %s   index=%s" % (p, index_key(os.path.basename(p)) or "(aucun)"))
    if not hits:
        print("VERDICT: OK -- aucun index de serie en conflit.")
        return 0
    print("")
    print("VERDICT: COLLISION D'INDEX (%d)" % len(hits))
    for h in hits:
        print("   %s" % h["added"])
        print("      index %s deja tenu par %s" % (h["index"], h["conflicts_with"]))
    print("")
    print("Un index de serie designe une position, et deux notebooks ne peuvent pas")
    print("occuper la meme. Renommer l'ajout vers un index libre, OU -- si les deux")
    print("traitent le meme sujet -- les reconcilier en un seul avant de merger.")
    print("Ne PAS supprimer l'un des deux sans avoir absorbe ce qu'il porte en propre")
    print("(anti-regression : « Consolider != Archiver »).")
    return 1


if __name__ == "__main__":
    sys.exit(main())
