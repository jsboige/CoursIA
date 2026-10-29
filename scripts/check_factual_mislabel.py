#!/usr/bin/env python3
"""Organe factual-mislabel (#18354 tranche 2, campagne #17073).

Détecte une cellule markdown qui énonce un compte d'entité CONTREDIT par
le stream text committé de la cellule code qu'elle décrit -- canon :
App-5-Timetabling énonce « 3 salles » et « (3 × 20)^8 » alors que le
stream committé imprime « Salles : 4 » et « (4 x 20)^8 = 1.68e+15 ».

Deux facettes, toutes deux des contradictions (un compte DIFFÉRENT du
stream) -- l'absence pure d'un nombre relève de l'organe stale-claim
(tranche 1) :

1. compte d'unité : « N <unit> » en markdown vs « <Unit> : M » dans le
   stream d'une cellule code adjacente (fenêtre +-2), même unité,
   N != M ;
2. formule-tuple : « (N × K)^P » en markdown vs « (M x K)^P » dans le
   stream, N != M.

Sortie : rc=0 propre, rc=1 au moins un finding, rc=2 erreur d'usage.
Advisory par construction (patron #11435) -- jamais bloquant seul.

#20035 : la portee du vocabulaire d'unites a ete etendue pour couvrir
les substantifs de comptage trouves sur les cotes hors-App-5 (carnet,
lemme, modele, ...). Le scope par defaut est `core` (les 14 unites
historiques d'App-5) ; `extended` est un **opt-in explicite**
(`--units extended`), depuis l'arbitrage du coordinateur du
2026-10-21 : un defaut qui rend 36 findings pour 0 vrai positif
n'est pas un defaut. Le test de regression documente en haut reste
vert dans les deux scopes (la garde SUBCOUNT_CONTEXT_RE filtre les
sous-comptes qui produiraient les FP).

MESURE CORPUS (exigence #20035, relevee le 2026-10-21 sur ai-01) --
corpus `MyIA.AI.Notebooks`, 1 603 carnets, organe execute sur les
deux scopes avant et apres la garde compte/valeur :

| scope | avant la garde | apres la garde |
|---|---|---|
| `core` | 13 | 13 (inchange) |
| `extended` | 43 | 36 |

(Une mesure anterieure sur un corpus de 1 553 carnets donnait 15 / 45 ->
38 : le delta de 7 est stable, seuls les compteurs absolus dependent du
corpus, qui grossit.)

Les 7 findings disparus etaient tous de la classe VALEUR lue comme
COMPTE (moyennes decimales). Sur les 36 restants, la lecture de la
source, classe par classe, donne **0 vrai positif** : separateur de
milliers par espace (2 : « 10 000 iterations » lu comme `000
iterations`), plages de valeurs (6 : « 1-2 iterations », « 12-18 »),
comptes partiels de split (2 : Train 382 + Test 164 pour 546),
sous-comptes par item (5 : « 16 slots a 1 seul », « A 2 agents »), et
quantites de nature differente (21 : horizon « 5 jours » vs 6 300
lignes, fonctions differentes dans la meme fenetre, carnet differente).

Aucun vrai positif ne subsiste : le cas fondateur App-5 (« 3 salles »
contre `Salles : 4`) a ete CORRIGE sur `main` par une autre lane -- la
prose y dit desormais « 4 salles » -- et l'organe ne le voit plus. Le
scope `core` (13 findings) est compose des memes classes de faux
positifs.

CONSEQUENCE : sur le corpus actuel, le scope `extended` rend 36
findings pour 0 vrai positif. L'organe reste ADVISORY (patron #11435,
jamais bloquant seul), donc ce taux ne bloque rien -- mais il produit
du bruit, et l'extension de portee est, en l'etat, un amplificateur de
bruit. L'arbitrage du coordinateur (dispatch c2205, 2026-10-21) tranche :
**`core` par defaut, `extended` en opt-in explicite**. Le defaut est
donc change -- dans une PR distincte de celle-ci, qui reste
dediee a la fermeture d'une classe de faux positifs et a la mesure.

MESURE CORPUS DES FORMES (2026-10-29, lane myia-po-2023) -- les deux
leviers de forme du cas fondateur #19918 (« 15 carnets dans Serre100/ »
contre « les huit carnets ») et la classe de collection associee,
mesures sur le meme corpus (1 694 carnets, base `e06daea2734`) :

| scope / formes | findings |
|---|---|
| `core` / `strict` | 13 |
| `core` / `broad` | 17 |
| `extended` / `strict` | 40 |
| `extended` / `broad` | 152 |

Lecture des 123 findings AJOUTES par `broad` en scope `extended` : les
25 formes « en toutes lettres » ont ete lues une a une -- **25 faux
positifs sur 25** (24 sous-comptes : « les deux modeles », « les trois
instances les plus longues », « Ces deux notebooks » ; 1 lecture de
docstring : « (1 axiome = 1 ligne de la definition mathematique) »
dans le listing d'un fichier Lean). Les 98 formes « en chiffres »
appartiennent a la meme famille : sous-comptes, quantites derivees
(« 64 strategies pures » pour 6 jeux d'information), experiences
differentes.

Le cas fondateur est, lui, attrape : sur la tete d'avant correction
(`6986f3f43b`), `--units extended --forms broad` rend 1 finding --
« huit carnets » contre `15 carnets dans Serre100/` -- la ou
`--units extended --forms strict` rend 0.

CONSEQUENCE : la COMPARAISON DE COMPTES est un mecanisme de
proximite, et a l'echelle du corpus deux comptes de la meme unite dans
des cellules voisines sont presque toujours deux grandeurs
differentes. La classe de counting units rend donc, au gate, du bruit
pour 0 vrai positif -- le meme arbitrage que celui du 2026-10-21 sur
`extended`, et pour la meme raison. `--forms broad` reste un
**instrument d'audit cible** (une serie, un dossier de domaine), jamais
un gate ; `--units core --forms strict` reste le defaut.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import unicodedata
from pathlib import Path

UNITS = (
    "salles?|cours|cre?neaux?|enseignants?|professeurs?|etudiants?|"
    "agents?|variables?|contraintes?|jours?|rooms?|courses?|slots?|teachers?"
)

# #20035 : la liste UNITS est mono-domaine (App-5 / emploi du temps).
# Le cas fondateur documente en #19918 est "15 carnets dans Serre100/"
# vs prose "les huit carnets" : le substantif `carnet` n'est pas dans
# la liste, l'organe est aveugle par construction. La voie "ajouter une
# unite a la fois" ne tient pas -- chaque instance trouve une autre
# (carnet, lemme, fichier, modele, ...). La voie choisie est une liste
# fermee, documentee, et couplee a la garde SUBCOUNT_CONTEXT_RE deja
# en place (chacun, par, au moins, ...) : les faux positifs mesures
# sur App-5 (3 FP tues) restent la base de reference. La liste est un
# **opt-in explicite** (`--units extended`) -- c'est elle qui rend l'organe
# utile aux cotes hors App-5 -- et le defaut reste `core`, c'est-a-dire la
# portee historique (la portee du test de regression documente en haut du
# fichier : 0 FP / 30 carnets sur le corpus de reference d'avant #20035),
# depuis l'arbitrage du coordinateur qui a mesure 0 vrai positif sur le
# scope etendu (36 findings sur le corpus).
UNITS_EXTENDED = (
    # Carnets / notebooks / pages / sections (Serre100, IIT, ICT, ML,
    # SymbolicAI) : substantifs que le stream peut enumerer directement
    # (print d'un listing ou d'un compteur).
    "carnets?|notebooks?|fichiers?|sections?|pages?|cellules?|"
    "modules?|bibliotheques?|paquets?|"
    # Preuves / theoremes / lemmes (Lean) : le stream d'une campagne
    # `lake envlean` rend `Build OK` (pas de compte) ; le compteur
    # apparait surtout dans les re-executions `print(N_theorems)`.
    "theoremes?|lemmes?|preuves?|corollaires?|propositions?|"
    "definitions?|axiomes?|hypotheses?|"
    # ML / training : modeles, predictions, echantillons.
    "modeles?|predictions?|echantillons?|hyperparametres?|"
    "parametres?|epochs?|iterations?|episodes?|"
    # Quantbooks : strategies, backtests.
    "strategies?|backtests?|"
    # Solveurs / moteurs : problemes, solutions, instances.
    "problemes?|solutions?|instances?|"
    # Tests : cas, scenarios, fixtures.
    "scenarios?|fixtures?|"
    # Genres d'objets code : classes, fonctions, methodes, lignes.
    "classes?|fonctions?|methodes?|lignes?|"
    # Datasets / fichiers de donnees.
    "datasets?|colonnes?|tableaux?|"
    # Pluriels courants en prose pedagogique : parties, etapes, chapitres.
    "parties?|etapes?|chapitres?|paragraphes?"
)

# ---------------------------------------------------------------------------
# #20035 (suite) : la CLASSE D'UNITES DE COMPTAGE.
#
# L'extension du vocabulaire ci-dessus est une liste de noms, pas une classe
# : elle mêle deux grandeurs de nature differente.
#   - une COLLECTION : un ensemble d'entites documentees, dont le total est
#     affichable par un listing ou un compteur (« 15 carnets dans
#     Serre100/ ») ;
#   - un PARAMETRE : une duree, une fenetre, un nombre d'iterations
#     (« sur 20 jours », « 30 iterations »), dont la valeur depend du
#     contexte et ne se contredit pas d'une cellule a l'autre.
#
# Mesure du 2026-10-29 (corpus `MyIA.AI.Notebooks`, 1 694 carnets) : les
# deux leviers de forme appliques a la liste etendue font passer le scope
# `extended` de 40 a 314 findings -- une amplification de 7,9 x, dont la
# quasi-totalite vient des unites-parametre (« jours », « iterations »,
# « instances », « colonnes »). Le meme verrou que l'arbitrage du
# coordinateur du 2026-10-21 sur le defaut `core` : elargir sans mesure
# viderait l'organe de son sens.
#
# D'ou la separation en deux listes. Le mode `strict` (defaut) garde le
# vocabulaire historique, scope par scope -- son perimetre mesure n'est pas
# touche. Le mode `broad` applique les deux leviers de forme a la seule
# CLASSE COLLECTION, ou un compte designe une totalite d'entites.
COLLECTION_CORE = (
    "salles?|cours|cre?neaux?|enseignants?|professeurs?|etudiants?|"
    "rooms?|courses?|slots?|teachers?"
)
COLLECTION_EXTENDED = (
    "carnets?|notebooks?|fichiers?|sections?|pages?|cellules?|"
    "modules?|bibliotheques?|paquets?|"
    "theoremes?|lemmes?|preuves?|corollaires?|propositions?|"
    "definitions?|axiomes?|hypotheses?|"
    "modeles?|predictions?|echantillons?|"
    "strategies?|backtests?|"
    "problemes?|solutions?|instances?|"
    "scenarios?|fixtures?|"
    "classes?|fonctions?|methodes?|"
    "datasets?|tableaux?|"
    "parties?|etapes?|chapitres?|paragraphes?"
)


def _collection_units(units_scope: str) -> str:
    """Vocabulaire de COLLECTION du scope demande.

    `core` : les collections App-5 (les durees, fenetres et dimensions de
    probleme — « jours », « variables », « contraintes » — sont exclues,
    ce sont des parametres) ;
    `extended` : les collections App-5 + les collections hors-App-5.
    """
    if units_scope == "core":
        return COLLECTION_CORE
    if units_scope == "extended":
        return COLLECTION_CORE + "|" + COLLECTION_EXTENDED
    raise ValueError(f"units_scope inconnu: {units_scope!r} (attendu 'core' ou 'extended')")

# Le pattern regex depend du scope d'unites (core vs extended). Compile
# une seule fois par appel de scan_notebook ; un cache par process
# suffirait, mais le scan est lui-meme le chemin chaud. Les regex sont
# par-fonction pour que le test puisse mocker les deux sans toucher au
# scope par defaut.
def _build_count_patterns(units: str) -> tuple[re.Pattern, re.Pattern]:
    """Compile les regexes MD/stream compte pour le scope d'unites.

    Le pattern stream utilise `[ \t]*` (et non `\\s*`) entre le nom
    d'unite et le separateur, et entre le separateur et le chiffre :
    `\\s*` absorbe le saut de ligne et lit le premier digit d'une
    liste numerotee comme un compte -- ex. `Etapes:\\n  1. Preparer`
    devient `etapes = 1` (faux positif, Hermes 2026-10-15 sur
    `GenAI/Texte/03_Structured_Outputs.ipynb` cellule md 19).
    `[ \t]*` preserve les separateurs en espace/tabulation sur la
    meme ligne et tue la classe FP sur les listes numerotees.

    Les deux motifs refusent un nombre suivi d'une partie decimale
    (garde `(?!\\d*[.,]\\d)`) : un nombre a virgule ou a point est une VALEUR, pas
    un compte. Sans cette garde, « Recompense moyenne sur 10 episodes:
    465.1 » donnait `episodes = 465` dans le stream, contredit par les « 10
    episodes » de la prose -- faux positif mesure sur
    `RL/RL-02-Wrappers-Sauvegarde-Callbacks-Python.ipynb` cellules md 12 et
    18 (signale par la lane adjointe, cycle c2204).

    La meme garde, seule, ne suffit pas : le lookahead arretait le match au
    bon nombre, mais le MOTEUR reprenait APRES le separateur. Sur « 465.1
    episodes » (cote prose), le `\b` entre « . » et « 1 » est une frontiere
    de mot : le motif MD relisait donc `(1, episodes)` -- un compte fabrique
    a partir de la partie decimale d'une valeur. Idem « 87,4 iterations » ->
    `(4, iterations)`. Mesure du 2026-10-21 (reserve du coordinateur,
    3 points sur #20956) :
        '465.1 episodes'   -> ('1', 'episodes')
        '87,4 iterations'  -> ('4', 'iterations')
    D'ou la **borne gauche** `(?<![\\d.,])` sur le motif MD : un match ne peut
    plus commencer sur un chiffre precede d'un chiffre, d'un point ou d'une
    virgule. Les deux gardes sont complementaires -- le lookahead refuse le
    nombre lui-meme, la borne gauche refuse la reprise apres separateur.

    LIMITE CONNUE, non couverte par cette garde : le separateur de
    milliers PAR ESPACE (« 10 000 iterations », « 6 912 variables »). Le
    motif MD lit alors le dernier groupe (« 000 iterations »), un
    compte faux -- classe distincte, mesuree a 2 findings sur le corpus
    (GameTheory-13 c16, SocialChoice-04 c16). Elle n'est pas traitee ici :
    la corriger exige de distinguer un groupe de milliers d'un compte,
    ce qui suppose une grammaire de nombre, pas une garde de lookahead.
    La faute la plus grave (une valeur lue comme un compte, donc une
    contradiction FABRIQUEE) est, elle, fermee.

    LIMITE CONNUE, cote stream : une enumeration sur la MEME LIGNE
    (« Etapes: 1) Re-SFT ») est encore lue comme un compte par le motif
    stream -- le separateur `[:=][ \t]*` autorise le chiffre qui suit
    directement « 1) ». Le cas « Etapes:\\n  1. Preparer » (liste sur la
    ligne suivante) est deja ecarte par le `[ \t]*` entre l'unite et le
    separateur. Traiter l' enumeration sur la meme ligne suppose une
    grammaire de liste, pas une garde de lookahead : c'est une suite, pas
    un correctif de ce cycle.
    """
    return (
        re.compile(rf"(?i)(?<![\d.,])\b(\d{{1,5}})(?!\d*[.,]\d)\s*({units})\b"),
        re.compile(rf"(?i)\b({units})[ \t]*[:=][ \t]*(\d{{1,5}})(?!\d*[.,]\d)\b"),
    )


# ---------------------------------------------------------------------------
# #20035 (suite) : les deux leviers que la seule extension du VOCABULAIRE
# ne couvre pas sur le cas fondateur #19918.
#
# La session cloud du mainteneur (13/10) a mesure les trois leviers du cas
# sur la tete d'avant correction (`6986f3f43b`) :
#   - vocabulaire seul ..................... 0 finding
#   - les trois leviers ensemble ........... 3 findings (1 vrai, 2 FP)
#
# Les deux leviers manquants ne sont pas des questions de vocabulaire :
#   1. la FORME DU STREAM « N unites » (« 15 carnets dans Serre100/ ») --
#      l'organe ne lisait que « Unite : M » ;
#   2. les NOMBRES EN TOUTES LETTRES de la prose (« les huit carnets ») --
#      MD_COUNT_RE n'accepte que des chiffres.
#
# Les deux sont derriere `--forms broad` (opt-in explicite). Le defaut
# `strict` conserve exactement le comportement mesure (le perimetre n'est
# pas change : ni le vocabulaire, ni les formes).
NUMBER_WORDS = {
    # FR : l'indefini (« un », « une ») est exclus -- ce n'est pas un compte
    # (« une salle » n'oppose rien a « Salles : 4 »). La liste s'arrete a 60 :
    # au-dela, les grandeurs rondes (« cent », « mille ») sont trop ambiguës
    # en prose pour etre opposees au stream.
    "deux": 2, "trois": 3, "quatre": 4, "cinq": 5, "six": 6, "sept": 7,
    "huit": 8, "neuf": 9, "dix": 10, "onze": 11, "douze": 12, "treize": 13,
    "quatorze": 14, "quinze": 15, "seize": 16, "vingt": 20, "trente": 30,
    "quarante": 40, "cinquante": 50, "soixante": 60,
    # EN : memes valeurs, memes exclusions.
    "two": 2, "three": 3, "four": 4, "five": 5, "seven": 7, "eight": 8,
    "nine": 9, "ten": 10, "eleven": 11, "twelve": 12, "thirteen": 13,
    "fourteen": 14, "fifteen": 15, "sixteen": 16, "twenty": 20, "thirty": 30,
    "forty": 40, "fifty": 50, "sixty": 60,
}
# « six » est commun aux deux langues : meme cle, meme valeur.

# Ratio « X sur Y » : X est un SOUS-compte (« sept carnets sur huit »),
# pas le total que le stream affiche. Le denominateur Y reste un compte
# valide. Garde propre au mode `broad` : le mode `strict` ne change pas.
RATIO_SUFFIX_RE = re.compile(r"\s*sur\b")

# Enumeration d'identifiants (« deux carnets, 05 et 06 ») : le nombre en
# toutes lettres designe les items listes, pas le total de la serie.
# Meme classe que le ratio : garde propre au mode `broad`.
ENUM_SUFFIX_RE = re.compile(r"\s*,\s*\d+\s*(?:et|and)\b")

# Determinant defini exige devant un nombre en toutes lettres. Un total se
# dit « LES huit carnets » ; un sous-compte se dit « DEUX carnets n'ont pas
# de cellule Python » (constate sur le carnet fondateur lui-meme, tete
# `6986f3f43b` : le mode `broad` y rendait 2 findings, dont 1 faux
# positif). Le determinant defini est la marque du total.
DETERMINERS = (
    r"(?:les|ces|l'ensemble des|the|these|those)"
)


def _build_broad_patterns(units: str) -> tuple[re.Pattern, re.Pattern]:
    """Compile les deux motifs du mode `broad`.

    - motif prose : un nombre en toutes lettres, **precede d'un determinant
      defini**, suivi de l'unite (« les huit carnets ») ;
    - motif stream : la forme « N unite » (« 15 carnets dans Serre100/ »),
      que la forme « Unite : M » ne voit pas.

    Le mot est exige avec au moins une espace devant l'unite, et le nombre
    doit etre precede d'une frontiere non numerique : « dix-huit carnets »
    ne peut pas etre lu « huit carnets », « quatre-vingts carnets » ni
    « deuxieme carnet » (le `\b` apres le mot ne trouve pas de frontiere
    dans « deuxieme »).

    La borne gauche est `(?<![\\w.,-])` — elle refuse une reprise apres un
    tiret. Deux classes sont fermees par la :
      - les nombres composes (« dix-huit », « quatre-vingts ») : le mot
        de queue (« huit », « vingt ») ne peut pas etre lu seul ;
      - les plages de valeurs (« 12-18 creneaux ») : la borne haute ne
        peut pas etre lue comme un compte (classe de faux positifs
        measurée sur le corpus en scope `strict`, 6 findings).
    Elle ne s'applique qu'au mode `broad` : le perimetre mesure de
    `strict` reste inchange.
    """
    words = "|".join(sorted(NUMBER_WORDS, key=len, reverse=True))
    return (
        re.compile(rf"(?i)(?<![\w.,-]){DETERMINERS}\s+({words})\s+({units})\b"),
        re.compile(rf"(?i)(?<![\w.,-])(\d{{1,5}})(?!\d*[.,]\d)\s+({units})\b"),
    )


MD_TUPLE_RE = re.compile(r"\(\s*(\d{1,5})\s*(?:[x×]|\\times\s*)\s*(\d{1,5})\s*\)\s*\^")
STREAM_TUPLE_RE = re.compile(r"\(\s*(\d{1,5})\s*x\s*(\d{1,5})\s*\)\s*\^")

# Sous-comptes par entite (« Dupont enseigne 2 cours », « chacun 2 cours »,
# « par jour », bornes « au moins/au plus ») : le total du stream ne les
# contredit pas -- mesure sur App-5 (md c.6 : 3 faux « 2 cours » vs
# stream « Cours : 8 »).
SUBCOUNT_CONTEXT_RE = re.compile(
    r"(?i)(enseign\w*|chacun\w*|par\s+\w+|au\s+(?:moins|plus)|maximum|minimum|"
    r"environ|centaines?|dizaines?)"
)

WINDOW = 3


def _unaccent(s: str) -> str:
    return "".join(
        c for c in unicodedata.normalize("NFD", s) if unicodedata.category(c) != "Mn"
    )


def _output_text(cell: dict) -> str:
    parts: list[str] = []
    for o in cell.get("outputs", []):
        t = o.get("text", "")
        parts.append("".join(t) if isinstance(t, list) else (t if isinstance(t, str) else ""))
        data = o.get("data", {}) if isinstance(o.get("data"), dict) else {}
        for key in ("text/plain", "text/html"):
            v = data.get(key, "")
            parts.append("".join(v) if isinstance(v, list) else (v if isinstance(v, str) else ""))
    return "\n".join(parts)


def _nearby_streams(cells: list[dict], idx: int) -> str:
    lo = max(0, idx - WINDOW)
    hi = min(len(cells), idx + WINDOW + 1)
    parts = [
        _output_text(c)
        for c in cells[lo:hi]
        if c["cell_type"] == "code" and _output_text(c).strip()
    ]
    return "\n".join(parts)


def _singular(unit: str) -> str:
    return unit.rstrip("s").lower()


def scan_notebook(path: Path, *, units_scope: str = "core", forms: str = "strict") -> list[dict]:
    """Scanne un carnet. ``units_scope`` :
    - ``"core"`` (**defaut**) : UNITS seulement (la portee historique,
      App-5) ;
    - ``"extended"`` : UNITS + UNITS_EXTENDED. La liste etendue
      couvre les substantifs de comptage trouves sur les cotes
      hors-App-5 (carnet, lemme, modele, ...). C'est l'opt-in
      explicite : sur le corpus mesure, elle rend 36 findings pour
      0 vrai positif (arbitrage coordinateur du 2026-10-21). Un audit
      cible (ex. App-5 seul) peut rejouer en ``"core"`` pour comparer
      la portee historique.

    ``forms`` :
    - ``"strict"`` (**defaut**) : le perimetre mesure — la prose compte
      en chiffres, le stream annonce « Unite : M » ;
    - ``"broad"`` : ajoute les DEUX leviers du cas fondateur #19918 que la
      seule extension du vocabulaire ne couvre pas — les nombres en toutes
      lettres de la prose (« les huit carnets ») et la forme « N unite » du
      stream (« 15 carnets dans Serre100/ »). Le ratio « X sur Y » est
      alors ecarte (X est un sous-compte, pas le total).
    """
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return [{"file": str(path), "error": f"unreadable notebook: {exc}"}]
    if units_scope == "core":
        units = UNITS
    elif units_scope == "extended":
        units = UNITS + "|" + UNITS_EXTENDED
    else:
        raise ValueError(f"units_scope inconnu: {units_scope!r} (attendu 'core' ou 'extended')")
    md_count_re, stream_count_re = _build_count_patterns(units)
    if forms == "strict":
        md_words_re = stream_noun_re = None
    elif forms == "broad":
        md_words_re, stream_noun_re = _build_broad_patterns(_collection_units(units_scope))
    else:
        raise ValueError(f"forms inconnu: {forms!r} (attendu 'strict' ou 'broad')")
    findings: list[dict] = []
    for idx, cell in enumerate(nb["cells"]):
        if cell["cell_type"] != "markdown":
            continue
        src = _unaccent("".join(cell.get("source", [])))
        stream = _unaccent(_nearby_streams(nb["cells"], idx))
        if not stream.strip():
            continue
        # facette 1 : comptes d'unites contredits
        stream_counts: dict[str, set[int]] = {}
        for m in stream_count_re.finditer(stream):
            stream_counts.setdefault(_singular(m.group(1)), set()).add(int(m.group(2)))
        if stream_noun_re is not None:
            # forme « N unite » du stream (« 15 carnets dans Serre100/ »),
            # que la forme « Unite : M » ne voit pas
            for m in stream_noun_re.finditer(stream):
                stream_counts.setdefault(_singular(m.group(2)), set()).add(int(m.group(1)))
        seen_unit_claims: set[tuple[int, str, str]] = set()
        claims = [
            (int(m.group(1)), _singular(m.group(2)), m.start(), m.end())
            for m in md_count_re.finditer(src)
        ]
        if md_words_re is not None:
            claims.extend(
                (NUMBER_WORDS[m.group(1).lower()], _singular(m.group(2)), m.start(), m.end())
                for m in md_words_re.finditer(src)
            )
        for n, unit, m_start, m_end in claims:
            key = (idx, unit, str(n))
            if key in seen_unit_claims:
                continue
            after = src[m_end: m_end + 12]
            before = src[max(0, m_start - 15): m_start]
            ctx_before = src[max(0, m_start - 60): m_start]
            if SUBCOUNT_CONTEXT_RE.search(ctx_before) or SUBCOUNT_CONTEXT_RE.search(
                src[m_end: m_end + 30]
            ):
                continue
            # ratio « X sur Y » : X est un SOUS-compte (« sept carnets sur
            # huit »), pas le total que le stream affiche. Garde propre au
            # mode `broad` : le mode `strict` garde son perimetre mesure.
            if md_words_re is not None and RATIO_SUFFIX_RE.match(after):
                continue
            # enumeration d'identifiants (« deux carnets, 05 et 06 ») :
            # le nombre designe les items listes, pas le total
            if md_words_re is not None and ENUM_SUFFIX_RE.match(after):
                continue
            # plage de valeurs (« 12-18 creneaux ») : la borne haute n'est
            # pas un compte (classe de FP mesuree en `strict`, 6 findings sur
            # le corpus). Garde propre au mode `broad`.
            if md_words_re is not None and re.search(r"\d\s*-\s*$", before):
                continue
            # composé hypotheque (creneaux-salles) ou rapport (creneaux/jour) :
            # l'unite n'y est PAS la meme grandeur que le total du stream
            if after.lstrip().startswith("-") or re.match(r"\s*/\s*\w", after):
                continue
            # operande droite d'un produit « 5 jours x 4 creneaux » : c'est une
            # decomposition du total, pas un compte total contredit
            if re.search(r"[x×]\s*$", before) or re.search(r"\d\s*[x×]\s*$", before):
                continue
            if unit in stream_counts and n not in stream_counts[unit]:
                seen_unit_claims.add(key)
                findings.append(
                    {
                        "file": str(path),
                        "cell_index": idx,
                        "verdict": "FACTUAL_MISLABEL",
                        "kind": "unit-count",
                        "unit": unit,
                        "claimed": str(n),
                        "stream": sorted(stream_counts[unit]),
                        "context": src[max(0, m_start - 40): m_end + 30].strip()[:160],
                    }
                )
        # facette 2 : tuples de formule contredits
        stream_tuples = {(int(m.group(1)), int(m.group(2))) for m in STREAM_TUPLE_RE.finditer(stream)}
        for m in MD_TUPLE_RE.finditer(src):
            t = (int(m.group(1)), int(m.group(2)))
            if stream_tuples and t not in stream_tuples and any(
                t[1] == s[1] and t[0] != s[0] for s in stream_tuples
            ):
                findings.append(
                    {
                        "file": str(path),
                        "cell_index": idx,
                        "verdict": "FACTUAL_MISLABEL",
                        "kind": "tuple-formula",
                        "unit": "tuple",
                        "claimed": f"({t[0]} x {t[1]})^",
                        "stream": [f"({a} x {b})^" for a, b in sorted(stream_tuples)],
                        "context": src[max(0, m.start() - 40): m.end() + 30].strip()[:160],
                    }
                )
    return findings


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--units", choices=("core", "extended"), default="core",
                    help="#20035 : portee du vocabulaire d'unites. "
                         "`core` = App-5 (14 unites, **defaut** depuis "
                         "l'arbitrage coordinateur du 2026-10-21), "
                         "`extended` = + substantifs de comptage trouves sur "
                         "les cotes hors-App-5 (carnet, lemme, modele, ...), "
                         "en opt-in explicite. Le test de regression "
                         "historique (0 FP / 30 carnets) reste rejouable "
                         "dans les deux scopes.")
    ap.add_argument("--forms", choices=("strict", "broad"), default="strict",
                    help="#20035 : formes de compte reconnues. "
                         "`strict` (**defaut**) = le perimetre mesure : la "
                         "prose compte en chiffres, le stream annonce "
                         "'Unite : M'. `broad` ajoute les deux leviers du cas "
                         "fondateur #19918 -- les nombres en toutes lettres "
                         "de la prose ('les huit carnets') et la forme "
                         "'N unite' du stream ('15 carnets dans Serre100/') -- "
                         "et ecarte le ratio 'X sur Y' (X est un sous-compte). "
                         "MESURE 2026-10-29 (1 694 carnets) : `broad` rend "
                         "17 findings en scope `core` contre 13, et 152 en "
                         "scope `extended` contre 40 ; les 123 ajoutes ont ete "
                         "lus un a un, tous faux positifs (sous-comptes, "
                         "quantites derivees). `broad` est donc un INSTRUMENT "
                         "D'AUDIT CIBLE (une serie, un dossier de domaine), "
                         "jamais un gate.")
    ap.add_argument("notebooks", nargs="+", type=Path)
    args = ap.parse_args(argv)

    findings: list[dict] = []
    for p in args.notebooks:
        findings.extend(scan_notebook(p, units_scope=args.units, forms=args.forms))

    if args.json:
        print(json.dumps({"anomaly_count": len(findings), "findings": findings}, ensure_ascii=False, indent=1))
    else:
        for f in findings:
            if "error" in f:
                print(f"[ERROR] {f['file']}: {f['error']}")
                continue
            print(
                f"[FACTUAL_MISLABEL] {f['file']} cell={f['cell_index']} "
                f"{f['kind']} unit={f['unit']} claimed={f['claimed']} "
                f"stream={f['stream']} :: {f['context'][:110]}"
            )
        print(f"anomaly_count: {len(findings)}")
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
