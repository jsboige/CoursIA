"""Canon de nommage des notebooks (#5081) — primitives partagees par les gardes.

Origine — W0 de #5081/#11840 (`guard(#5081): securiser les renames`). Les organes
de nommage se sont ecrits separement et ont chacun leur grammaire : le garde de
collision d'index lit un index multi-niveaux avec lettre d'accretion
(`^\\d+([.\\-]\\d+)*[a-z]?`), le garde de zero-pad lit un numero apres prefixe de
serie (`^GameTheory-(\\d)(?!\\d)`). Deux lectures du meme nom, deux verites
possibles. Ce module est la lecture unique : les deux organes l'importent au lieu
de redefinir leur motif.

PORTEE — ce que ce module certifie, et ce qu'il ne certifie pas
--------------------------------------------------------------
Il couvre les formes **reellement en service** dans le depot, telles que les deux
organes les traitent aujourd'hui :

    GameTheory-04c-NashExistence-Csharp.ipynb   serie + numero + accretion + langue
    04-1-Educational-Audio-Content.ipynb        index a deux niveaux (categorie.item)
    2.3b-Naive-Bayes-Generatif.ipynb            index decimal + lettre de variante
    22_Evaluating_Generated_Text.ipynb          index nu, separateur underscore
    MGS-26-EquilibriumOptimizer-vs-Mealpy.ipynb serie a prefixe alphabetique
    07-Shapley_en.ipynb                         sibling i18n

Il ne certifie **pas** : la casse canonique des suffixes de langue (`Python` /
`CSharp` / `Lean`), la reservation d'un slot contre les PR ouvertes, ni la
configuration par serie du zero-pad. Ce sont les points 3 a 5 de #15489, laisses
hors de cette tranche — les revendiquer ici sans les implementer ferait passer un
module partiel pour le canon entier. Le point 3 est depuis livre par
`check_kernel_suffix_canon.py`, qui lit `KERNEL_LANG_SUFFIXES` ci-dessous : le
canon fournit la LISTE des suffixes de noyau, le garde juge leur casse. Un
module ne peut pas juger la casse d'un nom qu'il vient de normaliser.

REGLE DE NON-REGRESSION — extraction a comportement constant
------------------------------------------------------------
Ce module a ete extrait des organes existants, il ne les reinterprete pas. La
preuve n'est pas un raisonnement mais leurs self-tests : `check_duplicate_notebook_index.py
--self-test` et `scripts/tests/test_check_series_zero_pad.py` doivent rester verts
sans qu'aucun de leurs cas ait ete modifie.
"""
from __future__ import annotations

import re
from dataclasses import dataclass

# Suffixes de NOYAU : ceux dont la mesure de l'arbre montre qu'ils NOMMENT le
# moteur qui execute le notebook. Sous-ensemble extrait de LANG_SUFFIXES pour que
# le garde de casse (#15489 defaut 3) ne juge que ceux-la -- `_en`/`_fr` sont des
# siblings i18n (#4980) et `-Lean` un marqueur de contenu ; leur imposer une
# "casse canonique de noyau" n'a pas de sens.
#
#   130 x -Csharp/-CSharp -> 130 x `.net-csharp`
#    44 x -Python         ->  41 x `python3`, 2 x `coursia-ml-training`,
#                              1 x `.net-csharp` (le defaut, cf le garde)
#
# `-Lean` est volontairement ABSENT : dans ce depot il marque le contenu, pas le
# moteur. Le pendant reellement Lean porte `-Native`
# (`Lean-16d-Conway-Game-of-Life-Lean-Native.ipynb` -> `lean4-wsl`) et 2 des 4
# `-Lean` tournent sous `python3`. Le declarer comme noyau ferait crier le garde
# a tort sur ~50 notebooks de `SymbolicAI/Lean`. `-FSharp` est absent aussi :
# aucun kernelspec F# n'existe dans l'arbre et `.net-csharp` est partage par les
# langages .NET. Exclusions mesurees, pas oublis.
KERNEL_LANG_SUFFIXES = ("-csharp", "-python")

# Suffixes marquant un rendu ALTERNATIF du meme item, pas un item concurrent.
# = les noyaux ci-dessus + le rendu Lean (sibling de contenu) + les siblings
# i18n (#4980). Ceux-la servent a APPARIER deux rendus (`strip_lang`), jamais a
# juger un moteur.
LANG_SUFFIXES = KERNEL_LANG_SUFFIXES + ("-lean", "_en", "-en", "_fr", "-fr")

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
INDEX_RE = re.compile(r"^(\d+(?:[.\-]\d+)*)([a-z]?)[._\-\s]", re.I)

# Numero d'un notebook a prefixe de serie alphabetique : `Prefixe-NN` (+ lettre
# d'accretion). Le `(?!\d)` distingue le premier chiffre d'un numero a deux
# chiffres (`GameTheory-26` : le `6` suit le `2`, pas de coupure) du chiffre
# unique (`GameTheory-3a` : le `a` suit le `3`, coupure).
SERIES_NUM_RE = re.compile(r"^(?P<prefix>[A-Za-z][A-Za-z0-9]*)-(?P<num>\d+)(?P<accr>[a-z])?(?!\d)")

_IPYNB_RE = re.compile(r"\.ipynb$", re.I)


@dataclass(frozen=True)
class NotebookName:
    """Lecture structuree d'un nom de notebook. Champs optionnels : `None` = absent.

    `number` et `index` ne repondent pas a la meme question et ne sont donc pas
    redondants : `number` est le numero tel qu'ecrit apres le prefixe de serie
    (`04`, `26`), `index` est la position de navigation normalisee, zero-pad et
    separateurs resorbes (`4.1`, `2.3b`). Un notebook sans prefixe de serie porte
    un `index` et pas de `number` ; un notebook a prefixe porte les deux quand son
    numero est en tete.
    """

    stem: str
    series: str | None
    number: str | None
    accr: str | None
    index: str | None
    lang: str | None
    title: str


def strip_lang(filename: str) -> str:
    """Nom sans son suffixe de langue, pour apparier les rendus d'un meme item."""
    stem = _IPYNB_RE.sub("", filename)
    low = stem.lower()
    for suf in LANG_SUFFIXES:
        if low.endswith(suf):
            return stem[: -len(suf)]
    return stem


def index_key(filename: str) -> str | None:
    """Index de serie d'un nom de fichier, ou None s'il n'en porte pas."""
    stem = _IPYNB_RE.sub("", filename)
    m = INDEX_RE.match(stem)
    if not m:
        return None
    # Normalise separateurs de niveau et zero-padding : 04-1 et 4.1 sont le meme
    # index. Sans cette normalisation, un zero-pad partiel ouvrirait une porte de
    # contournement silencieuse.
    parts = re.split(r"[.\-]", m.group(1))
    return ".".join(str(int(p)) for p in parts) + m.group(2).lower()


def lang_of(filename: str) -> str | None:
    """Suffixe de langue d'un nom, normalise sans son separateur, ou None."""
    stem = _IPYNB_RE.sub("", filename)
    low = stem.lower()
    for suf in LANG_SUFFIXES:
        if low.endswith(suf):
            return suf.lstrip("-_")
    return None


def parse_name(filename: str) -> NotebookName:
    """Lecture structuree d'un nom de notebook selon le canon #5081.

    La langue est retiree en premier : `01-Arrow-Csharp` doit livrer son index `1`
    et non un index faussé par le suffixe. Le prefixe de serie est ensuite teste
    sur le nom deja delangue, puis l'index en tete.
    """
    stem = _IPYNB_RE.sub("", filename)
    lang = lang_of(stem)
    base = strip_lang(stem) if lang else stem

    series = number = accr = None
    m = SERIES_NUM_RE.match(base)
    if m:
        series = m.group("prefix")
        number = m.group("num")
        accr = m.group("accr")

    idx = index_key(base)
    if m:
        title = base[m.end():].lstrip("-_ ")
    else:
        mm = INDEX_RE.match(base)
        title = base[mm.end():] if mm else base
    return NotebookName(stem=stem, series=series, number=number, accr=accr,
                        index=idx, lang=lang, title=title)
