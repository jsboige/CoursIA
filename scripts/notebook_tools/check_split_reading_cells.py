#!/usr/bin/env python3
"""Recensement des cellules de lecture scindees « Lecture » puis « Lecture chiffree ».

Demande user (nit #16554, 2026-09-17, parapluie #16762) : quand un notebook
porte deja une cellule « Lecture », la tranche de densite suivante ajoute une
seconde cellule d'interpretation -- « Lecture chiffree » -- au lieu de
fusionner. Resultat : deux cellules d'interpretation consecutives avec
recouvrement PARTIEL de contenu, l'une derriere l'autre. Ce n'est pas un
doublon franc (les deux cellules disent des choses differentes ET se
repetent en partie) : un detecteur de duplication verbatim ne le voit pas,
et pedagogiquement le lecteur ne sait plus laquelle fait foi.

Ce script fait le RECENSEMENT structurel + la mesure de recouvrement :

  1. Signal structurel : paires de cellules markdown CONSECUTIVES dont les
     titres sont des en-tetes d'interpretation (Lecture / Lecture chiffree /
     Interpretation / Analyse). Sous-classes :
       - ``named_split``   : « Lecture ... » puis « Lecture chiffree ... » --
                             le defaut nomme par le user ;
       - ``generic_pair``  : autre couple d'en-tetes d'interpretation consecutifs.
  2. Mesure de recouvrement entre les deux cellules : Jaccard sur les mots
     pleins + containment des mots rares intra-notebook (df <= 4, meme
     mecanique que detect_repeated_prose.py signal B, reutilise par import).

Variante secondaire ``separated_by_code`` : meme couple d'en-tetes separe par
UNE cellule de code (la lecture chiffree interprete la sortie) -- signale
separement, le defaut user est la paire consecutive.

Le seuil de recouvrement N'EST PAS un verdict de fusion : la fusion est une
decision pedagogique par notebook (acceptance #16762). Le recensement dit
ou regarder ; il ne dit pas quoi couper.

Mode DIFF (#17464) : ``detect_added_readings`` signale les cellules markdown
INSEREES dans une PR qui violent la regle user « une sortie = une lecture » :

  - ``SECOND_READING``      : cellule markdown ajoutee sous une sortie de code
                              qui porte **plus de lectures en tete qu'en base**
                              (les bases de la campagne #13410 ajoutaient des
                              paragraphes *sans en-tete* derives de la lecture --
                              invisibles au detecteur consecutive). Le constat
                              est un **compte par sortie**, pas un jugement par
                              cellule : voir la decision #17044 ci-dessous ;
  - ``READING_BEFORE_CODE`` : cellule markdown ajoutee directement devant une
                              cellule de code AVEC sortie (la lecture doit
                              suivre la sortie, pas la preceder) ;
  - ``EXERCISE_READING``    : cellule markdown ajoutee juste apres une cellule
                              d'exercice (stub sans sortie) -- l'etudiant ne
                              verra pas la lecture tant qu'il n'a pas complete.

Le mode diff prend deux notebooks en argument (``--base``) et signale chaque
cellule ajoutee (par multiset de sources) dont la **nouvelle** position viole
la regle. La difference des en-tetes vides vient de la campagne #17021
(26 lectures inserees sur App-1-NQueens, 16 sur App-14b-ConnectFour) qui
passait sous l'organe consecutive d'origine -- le veto user dit pourtant la
meme regle.

Decision #17044 (ai-01, c.5836401913) : le cliquet **compte**, il ne diffe pas
les sources. Un ``SECOND_READING`` n'existe que si le nombre de lectures
rattachees a une MEME sortie de code augmente entre la base et la tete ; la
sortie est identifiee par la source de sa cellule de code. Une cellule markdown
dont la source est neuve n'est pas, a elle seule, un ajout. Trois
discriminants topologiques accumules avant cette decision (revision au meme
slot, id de base encore present, « premiere lecture legitime ») sont retires :
chacun ne couvrait qu'une variante du meme geste, et le dernier *avalait une
addition reelle* -- une lecture posee a un slot ou la base portait deja de la
markdown etait classee en revision meme quand le compte montait (#17062, 6
sites). Un 4e discriminant « fusion par absorption » (recouvrement de mots) a
ete ecarte : il ajoutait un seuil de plus a un empilement qui avait deja rate
deux fois cette classe.

Carve-out #17777 (decision ai-01 2026-09-25, « option a ») : deux formes
canoniques du depot n'ont jamais ete des lectures, et le mode diff les
signalait :

  - l'**enonce d'exercice** ``## Exercice N`` place a cote de son stub
    (enonce visible, stub separe, compte par ``count_exercises``) -- il tombait
    dans ``READING_BEFORE_CODE`` quand il precede son stub, dans
    ``EXERCISE_READING`` quand il suit le stub precedent. Replier ces enonces
    en commentaires ``#`` degraderait la lecture pour satisfaire l'organe :
    c'est l'option ecartee. Le carve-out ne s'applique PAS a une interpretation
    deguisee sous un titre d'exercice (en-tete d'interpretation dissimule, ou
    citation d'une sortie) -- elle reste signalee ;
  - l'**en-tete de section** (``## 2. Tests statistiques``, ``## Conclusion``,
    meme suivi de plusieurs paragraphes) n'est pas une « lecture deja
    presente » : la premiere lecture posee derriere un code qui n'en avait pas
    est le geste prescrit, pas un doublonnage. Le discriminant est le titre,
    pas la longueur du corps. ``is_reading_or_prose`` le porte -- c'est le
    predicat que le releve par sortie (#17044) consomme aussi.

Mode CLIQUET (#17044) : ``--base-ref <ref> [--head HEAD]`` compare chaque carnet
modifie entre la base et la tete et rend le verdict du cliquet -- rouge
seulement si la PR **augmente** ce que l'organe voit sur un carnet qu'elle
touche :

  - ``regressed`` = au moins un CONSTAT nomme. Le constat est lui-meme
    l'augmentation : pour ``SECOND_READING``, le nombre de lectures rattachees a
    une MEME sortie de code monte entre la base et la tete (decision #17044,
    c.5836401913) ; pour les deux autres buckets, la place de la cellule ajoutee.
    Le compte des paires consecutives n'est plus un verdict -- une hausse qui ne
    vient d'aucune sortie (encarts, transitions) n'est pas une violation. Les
    findings deja sur ``main`` sont donc *grandfathered* : c'est un cliquet, pas
    un plancher absolu.
  - les renames sont resolus via ``--name-status -M`` (un carnet renomme est lu
    a son ANCIEN chemin dans la base -- sans quoi le renommage passerait pour un
    ajout et tous ses findings pour des augmentations) ;
  - une base irresoluble est une ERREUR (rc=1), jamais un cliquet vide : lire un
    carnet absent de la base comme « ajoute » ferait rougir la PR entiere sur un
    probleme de fetch.

``--self-test`` joue six controles, hors git et hors reseau : trois positifs
(lecture empilee nommee ; lecture ajoutee SANS en-tete, invisible au detecteur
consecutive ; fusion blanche **plus** une lecture ajoutee sur une AUTRE sortie)
et trois negatifs (deux lectures fusionnees en une ; modification de code sans
lecture ajoutee ; encart sans code execute au-dessus).

Codes de retour : 0 = aucun finding ; 1 = cible introuvable, fichier designe
illisible, ou base irresoluble ; 2 = findings (avec --fail-on-findings). En mode
dossier, un carnet illisible est **rapporte sur stderr et saute** : il
n'interrompt pas le recensement et ne fait pas rougir le scan (cf #17044).
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import unicodedata
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from detect_repeated_prose import content_words, markdown_cells  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parents[2]
MAX_DF = 4  # un mot "rare" apparait dans <= 4 cellules du notebook

TITLE_STRIP_RE = re.compile(r"^[#*\-\s`>]+|[#*\s`>:]+$")
# Pas de `\b` apres la racine : ces racines sont des PREFIXES, pas des mots
# entiers. Avec `\b`, `interpre` suivi de `t` (« Interpretation ») n'a pas de
# frontiere de mot, le match echoue, et la forme de titre d'interpretation
# DOMINANTE du corpus etait invisible a l'organe (#17134 : 133 paires
# `generic_pair` dans 78 carnets, plus 3 `separated_by_code`). Le match reste
# ancre en `^` : « une analyse de X » n'est toujours pas un en-tete de lecture.
INTERPRETATION_RE = re.compile(
    r"^(lecture|interpre|interpret|analyse)", re.IGNORECASE
)
NAMED_SECOND_RE = re.compile(r"^lecture\s+chiffr", re.IGNORECASE)
NAMED_FIRST_RE = re.compile(r"^lecture\b", re.IGNORECASE)

# Heuristique cellule d'exercice : un stub TODO sans sortie ni execution_count.
EXERCISE_TOKENS = ("TODO", "A completer", "à compléter", "Exercice")

# Carve-out #17777 (decision ai-01 2026-09-25) : l'enonce d'exercice
# (`## Exercice N`) place a cote de son stub est la **forme canonique du
# depot** -- enonce visible, stub separe, compte par `count_exercises`.
# L'organe ne doit donc pas le compter comme une lecture : sans ce carve-out
# il tombe dans READING_BEFORE_CODE (l'enonce precede son propre stub) ou dans
# EXERCISE_READING (il suit le stub precedent quand les paires enonce|stub
# s'enchainent). Replier les enonces en commentaires `#` degraderait la
# lecture pour satisfaire l'organe -- l'option ecartee par la decision.
#
# Deux garde-fous distinguent l'enonce d'une **interpretation deguisee sous un
# titre d'exercice** : un en-tete d'interpretation dissimule dans le corps, et
# la citation d'une sortie -- le vocabulaire de l'interpretation, pas celui de
# l'enonce.
EXERCISE_STATEMENT_TITLE_RE = re.compile(r"^#{1,6}\s*exercice\b", re.IGNORECASE)
HIDDEN_INTERPRETATION_HEADING_RE = re.compile(
    r"^#{1,6}\s*(lecture|interpre|interpret|analyse)", re.IGNORECASE
)
OUTPUT_CITATION_RE = re.compile(
    r"\b(?:l[ae]s?|une?|cette?)\s+(?:sorties?|outputs?|prints?|affichages?)\b"
    r"|\bl\s*['’]\s*(?:sortie|output|affichage)\b"
    r"|\bcomme\s+le\s+montre\s+(?:la|le|l['’])"
    r"|\b(?:on\s+observe|on\s+voit|on\s+lit)\b",
    re.IGNORECASE,
)


def deaccent(s: str) -> str:
    return "".join(
        c for c in unicodedata.normalize("NFKD", s) if not unicodedata.combining(c)
    )


def cell_source(c: dict) -> str:
    s = c.get("source", "")
    return "".join(s) if isinstance(s, list) else s


def cell_output_text(cell: dict) -> str:
    """Concatene le texte de toutes les sorties d'une cellule de code."""
    parts = []
    for o in cell.get("outputs") or []:
        if isinstance(o, dict):
            t = o.get("text")
            if isinstance(t, list):
                parts.append("".join(t))
            elif isinstance(t, str):
                parts.append(t)
            data = o.get("data")
            if isinstance(data, dict) and "text/plain" in data:
                d = data["text/plain"]
                parts.append("".join(d) if isinstance(d, list) else str(d))
    return "\n".join(parts)


def cell_title(src: str) -> str:
    """Premiere ligne qui PORTE un titre, nettoyee des marques markdown.

    Ce n'est deliberement pas « premiere ligne non vide » : une ligne de
    separation (`***`, `---`) est non vide et ne porte aucun titre. S'y arreter
    rendait un titre VIDE -- donc la cellule entiere invisible au detecteur,
    meme quand son en-tete etait bien une lecture (#17134, seconde borne de la
    meme famille que le `\\b` de INTERPRETATION_RE). Le cas se rencontre a chaque
    repli de conclusion qui ouvre la cellule sur un separateur.
    """
    for line in src.splitlines():
        line = line.strip()
        if not line:
            continue
        title = TITLE_STRIP_RE.sub("", line).strip()
        if title:
            return title
    return ""


def is_interpretation_title(title: str) -> bool:
    return bool(INTERPRETATION_RE.match(deaccent(title).lower()))


def is_named_second(title: str) -> bool:
    return bool(NAMED_SECOND_RE.match(deaccent(title).lower()))


def is_reading_cell(cell: dict) -> bool:
    """Une cellule markdown est une 'lecture' au sens de la regle user si elle
    porte un en-tete d'interpretation (Lecture / Lecture chiffree /
    Interpretation / Analyse). Les '### Conclusion', '### Mise en place',
    '### Resultats' ne sont PAS des lectures : ce sont des transitions /
    organisation, pas des commentaires de sortie.

    Cette definition sert de discriminant dans le mode DIFF : on signale
    une 'lecture ajoutee' quand la cellule de code en base avait DEJA une
    lecture (de ce type la) derriere elle -- pas une simple transition.
    """
    if cell.get("cell_type") != "markdown":
        return False
    return is_interpretation_title(cell_title(cell_source(cell)))


def looks_like_reading_after_exercise(cell: dict) -> bool:
    """Heuristique plus large qu'``is_reading_cell`` : une cellule md qui
    suit un exercice peut etre une 'lecture pour la sortie attendue' meme
    si elle n'a pas d'en-tete 'Lecture / Analyse'. Le spec #17464 (bucket
    3) dit « apres une cellule d'exercice (stub TODO / sans sortie) » sans
    exiger un en-tete : un paragraphe descriptif sur la sortie attendue
    apres un stub compte autant qu'un '### Lecture' formel.

    On accepte une md SI :
      - elle porte un en-tete d'interpretation (Lecture / Analyse / etc.)
        ; OU
      - elle est constituee d'un (ou plusieurs) paragraphe(s) de prose
        substantielle (> 80 caracteres au total hors titre eventuel) sans
        etre une simple section structurelle.

    On REJETTE les md purement structurels (## Conclusion, ## Exercice
    N, ## References), qui n'ont qu'un en-tete suivi d'un corps court
    ou vide -- ce sont des transitions, pas des lectures.
    """
    if cell.get("cell_type") != "markdown":
        return False
    if is_reading_cell(cell):
        return True
    src = cell_source(cell).strip()
    if not src:
        return False
    # Si la premiere ligne est un titre markdown (# ## ### ...), on
    # accepte si le corps (apres la premiere ligne) fait > 80 chars.
    first_line = src.split("\n", 1)[0].lstrip()
    if first_line.startswith("#"):
        body = src.split("\n", 1)[1].strip() if "\n" in src else ""
        return len(body) > 80
    # Pas de titre markdown : c'est un paragraphe libre. S'il est > 80 chars,
    # c'est vraisemblablement une lecture descriptive (pas juste un
    # en-tete de section).
    return len(src) > 80


def is_exercise_cell(cell: dict) -> bool:
    """Une cellule de code est 'exercise' si elle porte un marqueur d'exercice
    OU un stub TODO dans son source. On accepte aussi une sortie litterale
    ``Exercice a completer`` : la convention des carnets CoursIA est d'afficher
    ce message quand l'etudiant n'a pas complete (cf C.1) -- la cellule reste
    pedagogiquement un exercice, meme si elle a ete executee une fois.

    Cette definition suit le contrat C.1 (``pas d'erreur volontaire dans un
    exercice``) : un exercice abouti a execution_count != None et une sortie
    utile, donc il ne ressemble plus a un stub -- l'heuristique reste
    aplicable tant que la cellule declare sa nature d'exercice.
    """
    if cell.get("cell_type") != "code":
        return False
    src = cell_source(cell)
    if any(tok in src for tok in EXERCISE_TOKENS):
        return True
    # Sortie litterale "Exercice a completer" (avec/sans accent, casse libre)
    out_text = cell_output_text(cell).strip().lower()
    out_text_deac = deaccent(out_text)
    return (
        "exercice a completer" in out_text_deac
        or "exercice a terminer" in out_text_deac
        or "a completer" in out_text_deac
    )


def is_reading_or_prose(cell: dict) -> bool:
    """Vrai si la cellule md **commente une sortie** : une lecture titree
    (Lecture / Interpretation / Analyse) ou un paragraphe non titre.

    Le complement est ce que la decision #17777 nomme « un en-tete de
    section » : une cellule dont le titre est un titre d'organisation
    (``## 2. Tests statistiques``, ``## Conclusion``, ``## References``) --
    elle structure le parcours, elle ne commente rien. Le discriminant est le
    **titre**, pas la longueur du corps : ``## 3. Bootstrap et IC95`` suivi de
    trois paragraphes reste un titre de section.

    Le mode diff s'en sert pour savoir si un code avait **deja** une lecture
    derriere lui : sinon, l'ajout d'une lecture est le geste PRESCRIT par le
    mandat, pas un doublonnage.
    """
    if cell.get("cell_type") != "markdown":
        return False
    if is_reading_cell(cell):
        return True
    src = cell_source(cell).strip()
    if not src:
        return False
    return not src.split("\n", 1)[0].lstrip().startswith("#")


def is_exercise_statement(cell: dict, cells: list[dict], idx: int) -> bool:
    """Vrai si ``cells[idx]`` est un **enonce d'exercice** au sens de la forme
    canonique du depot : un titre `## Exercice N` adjacent a son stub.

    Quatre conditions, toutes necessaires (#17777, decision ai-01
    2026-09-25 « option a, le carve-out d'organe ») :

      1. la premiere ligne non vide est un en-tete `Exercice ...` ;
      2. la cellule precedente **ou** suivante est un stub d'exercice
         (``is_exercise_cell``) -- l'enonce vit a cote de son stub ;
      3. aucun en-tete d'interpretation n'est dissimule dans le corps
         (un `### Lecture :` sous le titre d'exercice) ;
      4. le corps ne cite pas de sortie (``OUTPUT_CITATION_RE``) : citer une
         sortie est le geste de l'interpretation, pas celui de l'enonce.

    Les conditions 3 et 4 sont les garde-fous du controle negatif de la
    decision : « une interpretation deguisee sous un titre d'exercice » reste
    signalee.
    """
    if cell.get("cell_type") != "markdown":
        return False
    lines = cell_source(cell).splitlines()
    k = next((i for i, line in enumerate(lines) if line.strip()), None)
    if k is None:
        return False
    if not EXERCISE_STATEMENT_TITLE_RE.match(lines[k].strip()):
        return False
    prev_cell = cells[idx - 1] if idx > 0 else None
    next_cell = cells[idx + 1] if idx + 1 < len(cells) else None
    if not any(
        c is not None and is_exercise_cell(c) for c in (prev_cell, next_cell)
    ):
        return False
    body = lines[k + 1:]
    has_hidden_heading = any(
        HIDDEN_INTERPRETATION_HEADING_RE.match(line.strip())
        for line in body if line.strip()
    )
    cites_output = bool(
        OUTPUT_CITATION_RE.search(deaccent("\n".join(body)).lower())
    )
    return not (has_hidden_heading or cites_output)


def overlap_metrics(nb: dict, i: int, j: int) -> dict:
    """Jaccard mots pleins + containment mots rares entre cellules i et j."""
    words = {ci: content_words(t) for ci, t in markdown_cells(nb)}
    df: Counter[str] = Counter()
    for ws in words.values():
        df.update(ws)
    wi, wj = words.get(i, set()), words.get(j, set())
    union = wi | wj
    jaccard = round(len(wi & wj) / len(union), 3) if union else 0.0
    rare_i = {w for w in wi if df[w] <= MAX_DF}
    rare_shared = rare_i & wj
    containment = round(len(rare_shared) / len(rare_i), 3) if rare_i else 0.0
    return {
        "jaccard": jaccard,
        "rare_containment": containment,
        "shared_rare_words": len(rare_shared),
        "shared_rare_sample": sorted(rare_shared)[:8],
    }


def detect(nb: dict) -> list[dict]:
    cells = nb.get("cells", [])
    titles = {
        i: cell_title(cell_source(c))
        for i, c in enumerate(cells)
    }
    findings: list[dict] = []
    for i in range(len(cells) - 1):
        a, b = cells[i], cells[i + 1]
        if a.get("cell_type") != "markdown" or b.get("cell_type") != "markdown":
            continue
        ta, tb = titles[i], titles[i + 1]
        if not (is_interpretation_title(ta) and is_interpretation_title(tb)):
            continue
        kind = (
            "named_split"
            if NAMED_FIRST_RE.match(deaccent(ta).lower()) and is_named_second(tb)
            else "generic_pair"
        )
        findings.append({
            "type": kind,
            "cells": [i, i + 1],
            "titles": [ta[:70], tb[:70]],
            **overlap_metrics(nb, i, i + 1),
        })
    # Variante secondaire : meme couple separe par UNE cellule de code.
    for i in range(len(cells) - 2):
        a, mid, b = cells[i], cells[i + 1], cells[i + 2]
        if mid.get("cell_type") != "code":
            continue
        if a.get("cell_type") != "markdown" or b.get("cell_type") != "markdown":
            continue
        ta, tb = titles[i], titles[i + 2]
        if not (is_interpretation_title(ta) and is_named_second(tb)):
            continue
        # Ne pas doubler un named_split deja compte (cas impossible ici :
        # la cellule du milieu est du code), garder pour la lisibilite.
        findings.append({
            "type": "separated_by_code",
            "cells": [i, i + 2],
            "titles": [ta[:70], tb[:70]],
            **overlap_metrics(nb, i, i + 2),
        })
    return findings


# --- #17464 : mode DIFF -- cellule ajoutee qui viole la regle ----------------


def _classify_context(cells: list[dict], idx: int) -> tuple[str, str]:
    """Renvoie (prev_role, next_role) pour la cellule idx.

    prev_role / next_role sont parmi : "md", "code_with_output", "exercise", "BOUNDARY".
    "code_with_output" = cellule de code executee (a une sortie ou un exec_count).
    """
    def role(c):
        if c is None:
            return "BOUNDARY"
        if c.get("cell_type") == "markdown":
            return "md"
        if is_exercise_cell(c):
            return "exercise"
        return "code_with_output"

    prev = cells[idx - 1] if idx > 0 else None
    nxt = cells[idx + 1] if idx + 1 < len(cells) else None
    return role(prev), role(nxt)


def _output_key_above(cells: list[dict], idx: int) -> str | None:
    """Source de la cellule de code dont ``cells[idx]`` commente la sortie.

    La sortie est identifiee par la **source de sa cellule de code** (#17044,
    decision ai-01 c.5836401913). La remontee s'arrete a la premiere cellule de
    code : c'est elle, et elle seule, que la lecture commente. ``None`` s'il n'y
    a rien a lire -- aucun code au-dessus, code d'exercice, ou code jamais
    execute.
    """
    for j in range(idx - 1, -1, -1):
        c = cells[j]
        if c.get("cell_type") != "code":
            continue
        if is_exercise_cell(c):
            return None
        if c.get("execution_count") is not None or (c.get("outputs") or []):
            return cell_source(c)
        return None
    return None


def readings_by_output(nb: dict) -> Counter[str]:
    """Nombre de lectures rattachees a chaque sortie de code du carnet.

    C'est ce compte, et lui seul, que le mode diff compare entre la base et la
    tete (#17044, decision c.5836401913) : une cellule markdown dont la source
    est neuve n'est pas, a elle seule, un ajout -- une fusion, une revision ou
    un deplacement laissent ce compte inchange.
    """
    cells = nb.get("cells", [])
    counts: Counter[str] = Counter()
    for i, c in enumerate(cells):
        if not is_reading_or_prose(c):
            continue
        key = _output_key_above(cells, i)
        if key is not None:
            counts[key] += 1
    return counts


def increased_outputs(base_nb: dict | None, head_nb: dict) -> dict[str, int]:
    """Sorties dont le nombre de lectures AUGMENTE de la base a la tete.

    Une sortie absente de la base est ignoree : elle n'a pas de compte
    anterieur auquel comparer, et la premiere lecture posee sous un code neuf
    est le geste que le mandat PRESCRIT, pas un doublonnage. C'est ce qui
    distingue « ajouter une lecture » de « rendre une sortie a sa lecture ».
    """
    if base_nb is None:
        return {}
    base_readings = readings_by_output(base_nb)
    head_readings = readings_by_output(head_nb)
    return {
        key: head_readings[key] - n
        for key, n in base_readings.items()
        if head_readings.get(key, 0) > n
    }


def _finding(kind: str, cells: list[dict], idx: int) -> dict:
    """Constat nomme pour la cellule ``idx``, avec son contexte immediat."""
    prev_role, next_role = _classify_context(cells, idx)
    prev = cells[idx - 1] if idx > 0 else None
    nxt = cells[idx + 1] if idx + 1 < len(cells) else None
    prev_src = cell_source(prev)[-60:] if prev is not None else ""
    nxt_src = cell_source(nxt)[:60] if nxt is not None else ""
    return {
        "type": kind,
        "cells": [idx],
        "src_first_120": cell_source(cells[idx])[:120].replace("\n", " | "),
        "prev_role": prev_role,
        "next_role": next_role,
        "prev_src_last_60": prev_src.replace("\n", " | "),
        "next_src_first_60": nxt_src.replace("\n", " | "),
    }


def _attached_sources(nb: dict, key: str) -> set[str]:
    """Sources des cellules qu'une base rattache a la sortie ``key``.

    Sert a distinguer, dans le releve final, la cellule que la tete a fait
    ENTRER sur cette sortie (sa source n'y etait pas rattachee en base) du
    doublon byte-identique et de la revision deplacee.
    """
    cells = nb.get("cells", [])
    return {
        cell_source(c) for i, c in enumerate(cells)
        if _output_key_above(cells, i) == key
    }


def detect_added_readings(head_nb: dict, base_nb: dict | None) -> list[dict]:
    """Mode DIFF (#17464) : signale les cellules markdown **ajoutees** dans une PR
    dont la position viole la regle user « une sortie = une lecture ».

    Algorithme :
      1. Si ``base_nb`` est None, retourne une liste vide.
      2. Diff par multiset de sources (entre par sources, pas par id -- la
         campagne a produit des cellules sans id et des ids dupliques).
      3. Une cellule qui REVISE en place celle qui occupait le meme slot n'est
         pas un ajout : le mandat prescrit cette revision (« si on rajoute une
         lecture, on modifie le paragraphe existant »). Trois signaux l'exemptent
         -- id conserve (meme decale), source identique au meme index, ou deux
         cellules markdown au meme index.
      4. Pour chaque cellule ajoutee qui est markdown, classifier via le
         **contexte HEAD** :
           - ``EXERCISE_READING``    prev_role == "exercise"
           - ``READING_BEFORE_CODE`` next_role == "code_with_output"
           - ``SECOND_READING``      la sortie que la cellule commente porte
                                     **plus de lectures en tete qu'en base**

    Le discriminant de ``SECOND_READING`` est un **compte par sortie**, pas un
    jugement par cellule (#17044, decision ai-01 c.5836401913) : on releve, pour
    chaque sortie (identifiee par la source de sa cellule de code), le nombre de
    lectures qui la suivent, en base et en tete. Le constat n'existe que si ce
    compte MONTE. Une fusion de deux lectures en une, un deplacement, une
    revision laissent le compte inchange ; une sortie absente de la base est
    ignoree (sa premiere lecture est le geste prescrit). Les deux filtres
    topologiques que ce compte remplace -- « premiere lecture legitime apres un
    code », « encart sans code execute au-dessus » -- sont subsumes : aucune de
    ces formes ne fait monter le compte, alors que chacun d'eux laissait passer
    une addition REELLE posee a cote d'une revision.

    Le compte prime sur la place : une lecture ajoutee sous une sortie qui en
    portait deja est un ``SECOND_READING`` **meme si** sa position la fait
    ressembler a une lecture introductive. Sans cette primaute le constat
    retombait sur la revision en place qui l'accompagne, c'est-a-dire sur le
    geste que le mandat prescrit.

    Les deux autres buckets restent **positionnels** : la place d'une cellule
    ajoutee y est jugee comme avant, exemptions de revision comprises.

    Sortie : liste de dicts ``{type, cells, src_first_120, prev_role,
    next_role, prev_src_last_60, next_src_first_60}``, triee par position.
    """
    if base_nb is None:
        return []
    base_cells = base_nb.get("cells", [])
    head_cells = head_nb.get("cells", [])
    base_srcs = [cell_source(c) for c in base_cells]
    head_srcs = [cell_source(c) for c in head_cells]

    base_counter: Counter[str] = Counter(base_srcs)
    head_counter: Counter[str] = Counter(head_srcs)
    # Les ids de la base, consommes un a un : une cellule dont l'id vit encore a
    # ete revisee, meme si une fusion a decale son index (#17044).
    base_id_pool: Counter[str] = Counter(
        c.get("id") for c in base_cells if c.get("id")
    )

    # #17044 -- budget de lectures ajoutees, par sortie. C'est ce dictionnaire,
    # et lui seul, qui autorise un SECOND_READING ; chaque unite est consommee
    # une fois, par une cellule nommee dans le constat.
    excess = increased_outputs(base_nb, head_nb)

    findings: list[dict] = []
    # Cellules ajoutees qui se disputent le budget d'une meme sortie : le
    # verdict se tranche apres la boucle, quand toutes sont connues.
    pending: dict[str, list[int]] = {}
    reported: set[int] = set()

    for idx, src in enumerate(head_srcs):
        if head_counter[src] <= base_counter[src]:
            base_counter[src] += 1
            continue
        cell = head_cells[idx]
        if cell.get("cell_type") != "markdown":
            base_counter[src] += 1
            continue

        # Revision en place, pas insertion (cf. etape 3 du docstring) :
        #   (a) l'id de la cellule vit encore en base -- meme a un autre index,
        #       ce qu'une fusion provoque systematiquement ;
        #   (b)/(c) le meme index portait DEJA du markdown en base : la tete a
        #       revise ce slot. Le signal ne depend pas de la classification
        #       lecture/exercice, sinon un simple echappement de `$` dans une
        #       cellule sans id suffisait a la faire passer pour un ajout
        #       (OR-tools-Stiegler, #17747) et le cliquet rougissait le geste
        #       que le mandat prescrit.
        # (b) (source identique au meme index) est un cas particulier de (c)
        # des lors que la cellule de tete est markdown, ce que le test ci-dessus
        # a deja etabli.
        is_rewrite = False
        head_id = cell.get("id")
        if head_id and base_id_pool.get(head_id, 0) > 0:
            base_id_pool[head_id] -= 1
            is_rewrite = True
        if (not is_rewrite and idx < len(base_cells)
                and base_cells[idx].get("cell_type") == "markdown"):
            is_rewrite = True
        if is_rewrite:
            base_counter[src] += 1
            continue

        # Carve-out #17777 (decision ai-01 2026-09-25) : un enonce d'exercice
        # adjacent a son stub n'est pas une lecture. Sans ce filtre il tombe
        # dans READING_BEFORE_CODE (l'enonce precede son propre stub) ou dans
        # EXERCISE_READING (il suit le stub precedent quand les paires
        # enonce|stub s'enchainent) -- mesure sur #17777 : 11 findings sur 3
        # carnets, tous des enonces.
        if is_exercise_statement(cell, head_cells, idx):
            base_counter[src] += 1
            continue

        prev_role, next_role = _classify_context(head_cells, idx)
        key = _output_key_above(head_cells, idx)
        # Le COMPTE prime sur la topologie (#17044, decision c.5836401913). Une
        # cellule rattachee a une sortie qui porte plus de lectures qu'en base
        # EST une seconde lecture, quoi qu'en dise sa place : posee devant la
        # cellule de code SUIVANTE, la topologie seule la lirait comme une
        # lecture introductive, alors qu'elle commente la sortie du dessus.
        if key is not None and excess.get(key, 0) > 0:
            pending.setdefault(key, []).append(idx)
            base_counter[src] += 1
            continue
        bucket = _bucket_for(prev_role, next_role)
        if bucket == "SECOND_READING":
            # Topologie de seconde lecture, mais aucune sortie en deficit :
            # il n'y a rien a signaler (premiere lecture legitime sous un code
            # neuf, encart sans code a sortie au-dessus, revision en place).
            base_counter[src] += 1
            continue
        # Filtre final : EXERCISE_READING_CANDIDATE -> EXERCISE_READING si
        # la cellule ressemble a une lecture (titre d'interpretation OU
        # prose > 80 chars apres la premiere ligne). On REJETTE les
        # en-tetes purement structurels (## Conclusion, ## Exercice N,
        # ## References entre exercices).
        if bucket == "EXERCISE_READING_CANDIDATE":
            bucket = "EXERCISE_READING" if looks_like_reading_after_exercise(cell) else None
        if bucket is None:
            base_counter[src] += 1
            continue
        findings.append(_finding(bucket, head_cells, idx))
        reported.add(idx)
        base_counter[src] += 1

    # Le releve est par SORTIE, pas par cellule : plusieurs cellules peuvent se
    # disputer un meme budget, et celle qui a fait monter le compte n'est pas
    # toujours celle que les exemptions de revision ont laissee passer. Trois
    # rangs, dans cet ordre :
    #   1. les ajouts francs -- la source n'existait nulle part en base ;
    #   2. les cellules dont la source n'etait PAS rattachee a cette sortie en
    #      base : c'est le deplacement qui les y a fait entrer, et c'est lui qui
    #      a mis la sortie en deficit. C'est le geste a nommer ;
    #   3. les autres (doublon byte-identique, revision deplacee), dans l'ordre
    #      du document.
    # Le cliquet ne rend jamais rouge sans constat nomme.
    for key, remaining in excess.items():
        if remaining <= 0:
            continue
        held = _attached_sources(base_nb, key)
        pend = pending.get(key, [])
        attached = [
            i for i, c in enumerate(head_cells)
            if i not in reported and i not in pend
            and _output_key_above(head_cells, i) == key
        ]
        moved = [i for i in attached if cell_source(head_cells[i]) not in held]
        rest = [i for i in attached if cell_source(head_cells[i]) in held]
        for idx in (pend + moved + rest)[:remaining]:
            findings.append(_finding("SECOND_READING", head_cells, idx))
            reported.add(idx)

    findings.sort(key=lambda f: f["cells"][0])
    return findings


def _bucket_for(prev_role: str, next_role: str) -> str | None:
    """Map (prev, next) vers un bucket preliminaire, ou None si rien a signaler.

    Pour ``SECOND_READING`` apres code, l'organe applique un discriminant
    base (voir ``detect_added_readings``) pour distinguer premiere lecture
    legitime d'un doublonnage. Cette fonction ne tranche que la topologie
    immediate. Le filtre final (is_reading_cell) affine : on ne signale
    ``EXERCISE_READING`` que si la cellule est reellement une LECTURE
    (en-tete d'interpretation), pas un simple en-tete structurel (Conclusion,
    Exercice N, References).
    """
    if prev_role == "exercise":
        return "EXERCISE_READING_CANDIDATE"
    if next_role in ("code_with_output", "exercise"):
        # Une lecture ajoutee devant un exercice OU un code deja execute
        # precede le resultat qu'elle est censee commenter -- dans les deux
        # cas la place canonique est APRES, pas avant.
        return "READING_BEFORE_CODE"
    if prev_role in ("md", "code_with_output"):
        return "SECOND_READING"
    return None


def iter_notebooks(root: Path) -> list[Path]:
    skip_parts = {".lake", "_output", ".ipynb_checkpoints", "node_modules", "_peters"}
    return sorted(
        p for p in root.rglob("*.ipynb")
        if not (skip_parts & set(p.parts))
    )


def _read_nb(path: Path) -> dict:
    """Lecture tolerante : un carnet corrompu leve JSONDecodeError, handled
    par l'appelant (cf #17044)."""
    return json.loads(path.read_text(encoding="utf-8"))


# --- #17044 : mode CLIQUET -- delta base vs PR -------------------------------

SKIP_PARTS = {".lake", "_output", ".ipynb_checkpoints", "node_modules", "_peters"}


def _git(args: list[str], cwd: str | Path | None = None) -> str | None:
    """Sortie stdout d'une commande git, ou None si elle echoue."""
    try:
        out = subprocess.run(
            ["git", *args], cwd=cwd, capture_output=True,
            encoding="utf-8", errors="replace", check=False,
        )
    except OSError:
        return None
    return out.stdout if out.returncode == 0 else None


def resolve_base(base: str, head: str = "HEAD",
                 cwd: str | Path | None = None) -> str | None:
    """merge-base(base, head), ou None si la base est irresoluble.

    Le point de comparaison est ``head``, pas le HEAD du depot : la lane passe
    toujours ``HEAD``, mais rejouer une PR non encore mergee (controle
    positif) exige de comparer a SA tete, pas a la branche courante.
    """
    out = _git(["merge-base", base, head], cwd=cwd)
    if out and out.strip():
        return out.strip()
    # merge-base echoue aussi quand l'historique est superficiel ; on accepte
    # alors la ref elle-meme, mais seulement si elle existe vraiment.
    verify = _git(["rev-parse", "--verify", f"{base}^{{commit}}"], cwd=cwd)
    return verify.strip() if verify and verify.strip() else None


def changed_notebook_pairs(base: str, head: str = "HEAD",
                           cwd: str | Path | None = None) -> list[tuple[str | None, str]]:
    """(chemin en base, chemin en tete) pour chaque carnet touche.

    ``--name-status -M`` : un rename sort en ``R<score>  ancien  nouveau``, et
    c'est l'ANCIEN chemin qui porte le contenu de base. Le lire au nouveau
    chemin rendrait ``None``, et le carnet renomme serait vu comme ajoute --
    tous ses findings deviendraient des augmentations (#17044).
    """
    out = _git(["diff", "--name-status", "-M", base, head, "--", "*.ipynb"], cwd=cwd)
    if out is None:
        return []
    pairs: list[tuple[str | None, str]] = []
    for line in out.splitlines():
        parts = line.split("\t")
        if len(parts) < 2:
            continue
        status = parts[0].strip()
        if status.startswith("D"):
            continue  # carnet supprime : rien a comparer
        if status.startswith("R") or status.startswith("C"):
            if len(parts) < 3:
                continue
            base_path, head_path = parts[1], parts[2]
        else:
            base_path, head_path = parts[1], parts[1]
        head_posix = head_path.strip().replace("\\", "/")
        base_posix = base_path.strip().replace("\\", "/")
        if SKIP_PARTS & set(Path(head_posix).parts):
            continue
        pairs.append((base_posix, head_posix))
    return sorted(pairs, key=lambda p: p[1])


def read_notebook_at(ref: str, path: str,
                     cwd: str | Path | None = None) -> dict | None:
    """Carnet JSON a une ref git (None = absent ou illisible)."""
    raw = _git(["show", f"{ref}:{path}"], cwd=cwd)
    if raw is None:
        return None
    try:
        return json.loads(raw)
    except ValueError:
        return None


def ratchet_rows(base_ref: str, head: str = "HEAD",
                 cwd: str | Path | None = None) -> list[dict] | None:
    """Lignes du cliquet : une par carnet touche. None = base irresoluble."""
    base = resolve_base(base_ref, head, cwd=cwd)
    if base is None:
        return None
    rows: list[dict] = []
    for base_path, head_path in changed_notebook_pairs(base, head, cwd=cwd):
        head_nb = read_notebook_at(head, head_path, cwd=cwd)
        if head_nb is None:
            continue  # illisible en tete : le recensement ne peut rien dire
        base_nb = read_notebook_at(base, base_path, cwd=cwd) if base_path else None
        base_total = len(detect(base_nb)) if base_nb is not None else 0
        head_total = len(detect(head_nb))
        added = detect_added_readings(head_nb, base_nb)
        rows.append({
            "notebook": head_path,
            "base_total": base_total,
            "head_total": head_total,
            "delta": head_total - base_total,
            "added": added,
            # Le verdict EST le constat (#17044, decision c.5836401913) : le
            # cliquet compte les lectures par sortie, il ne diffe plus les
            # sources. Les deux totaux restent rendus, mais pour l'information
            # -- une hausse de paires qui ne vient d'aucune sortie (encarts,
            # transitions) n'est pas une violation. Corollaire : jamais de rouge
            # sans constat nomme, ce que la consommation du budget garantit.
            "regressed": bool(added),
        })
    return rows


def _nb(cells: list[tuple[str, str, str | None]]) -> dict:
    """Carnet minimal pour les controles : (cell_type, source, id).

    Les cellules de code portent une sortie et un execution_count : c'est la
    condition d'une lecture (« rien a lire » sinon, cf ``_output_key_above``),
    donc l'omettre rendrait les controles positifs vacues.
    """
    out = []
    for t, s, i in cells:
        c: dict = {"cell_type": t, "source": s}
        if i:
            c["id"] = i
        if t == "code":
            c["execution_count"] = 1
            c["outputs"] = [{"output_type": "stream", "text": "1\n"}]
        out.append(c)
    return {"cells": out}


def self_test() -> int:
    """Controles positifs et negatifs du cliquet, sans git ni reseau."""
    code = ("code", "print(1)", "c0")
    lecture = ("markdown", "### Lecture\nLe total vaut 1.", "m1")
    lecture_chiffree = ("markdown", "### Lecture chiffree\nLe total vaut 1, mesure.", "m2")
    base = _nb([code, lecture])

    checks: list[tuple[str, bool, str]] = []

    # Positif 1 -- une lecture NOMMEE empilee derriere une lecture existante.
    head = _nb([code, lecture, lecture_chiffree])
    added = detect_added_readings(head, base)
    checks.append((
        "positif 1 lecture nommee empilee",
        any(f["type"] == "SECOND_READING" for f in added)
        and len(detect(head)) > len(detect(base)),
        f"added={[f['type'] for f in added]} "
        f"compte {len(detect(base))} -> {len(detect(head))}",
    ))

    # Positif 2 -- lecture ajoutee SANS en-tete apres un code qui en portait
    # deja une : le compte consecutive ne bouge pas, le mode diff mord.
    base2 = _nb([code, lecture])
    head2 = _nb([
        code,
        lecture,
        ("markdown", "Le total vaut 1, et c'est bien le total attendu ici.", "m3"),
    ])
    added2 = detect_added_readings(head2, base2)
    checks.append((
        "positif 2 lecture sans en-tete (invisible au consecutive)",
        bool(added2) and len(detect(head2)) == len(detect(base2)),
        f"added={[f['type'] for f in added2]} "
        f"compte {len(detect(base2))} -> {len(detect(head2))}",
    ))

    # Negatif 1 -- deux lectures FUSIONNEES en une (le remede prescrit).
    merged = ("markdown", "### Lecture\nLe total vaut 1, mesure et verifie.", "m1")
    head3 = _nb([code, merged])
    base3 = _nb([code, lecture, lecture_chiffree])
    added3 = detect_added_readings(head3, base3)
    checks.append((
        "negatif 1 lectures fusionnees",
        not added3 and len(detect(head3)) <= len(detect(base3)),
        f"added={[f['type'] for f in added3]} "
        f"compte {len(detect(base3))} -> {len(detect(head3))}",
    ))

    # Negatif 2 -- modification de code, aucune lecture ajoutee.
    head4 = _nb([("code", "print(2)", "c0"), lecture])
    added4 = detect_added_readings(head4, base)
    checks.append((
        "negatif 2 code modifie sans lecture ajoutee",
        not added4 and len(detect(head4)) == len(detect(base)),
        f"added={[f['type'] for f in added4]} "
        f"compte {len(detect(base))} -> {len(detect(head4))}",
    ))

    # Negatif 3 -- encart de prose sans code a sortie au-dessus (preamble,
    # bandeau de statut) : il n'y a rien a lire, ce n'est pas une seconde
    # lecture (mesure : #17484, bandeau « statut epistemique »).
    titre = ("markdown", "# Titre du carnet\n\nPublic : Decouverte.", "m0")
    head5 = _nb([titre, ("markdown", "> **Statut epistemique** -- sans verdict a ce jour.", "m1")])
    added5 = detect_added_readings(head5, _nb([titre]))
    checks.append((
        "negatif 3 encart sans code au-dessus",
        not added5,
        f"added={[f['type'] for f in added5]}",
    ))

    # Positif 3 -- critere 3 de la decision #17044 : une fusion reste VERTE,
    # mais une lecture ajoutee sur une AUTRE sortie reste ROUGE. Le cliquet
    # compte par sortie : il ne blanchit pas la PR entiere des qu'une de ses
    # sorties a ete fusionnee, et il ne rougit pas la fusion elle-meme.
    # `suite` est inchange entre les deux cotes : sans elle, la lecture
    # fusionnee deviendrait adjacente a la cellule de code suivante et serait
    # signalee READING_BEFORE_CODE -- un autre constat, qui masquerait celui
    # qu'on veut eprouver.
    a1 = ("markdown", "### Lecture\nA1.", "a1")
    a2 = ("markdown", "### Lecture chiffree\nA2.", "a2")
    fused = ("markdown", "### Lecture\nA1 et A2 fusionnes.", "a1")
    suite = ("markdown", "## 4. Suite du parcours", "h1")
    b1 = ("markdown", "### Lecture\nB1.", "b1")
    b2 = ("markdown", "### Lecture chiffree\nB2 ajoutee.", "b2")
    code2 = ("code", "print(2)", "c1")
    base6 = _nb([code, a1, a2, suite, code2, b1])
    head6 = _nb([code, fused, suite, code2, b1, b2])
    added6 = detect_added_readings(head6, base6)
    checks.append((
        "positif 3 fusion verte + lecture ajoutee sur une autre sortie rouge",
        [f["type"] for f in added6] == ["SECOND_READING"]
        and added6[0]["cells"] == [5],
        f"added={[(f['type'], f['cells']) for f in added6]} "
        f"compte par sortie {dict(readings_by_output(base6))} -> "
        f"{dict(readings_by_output(head6))}",
    ))

    ok = True
    for label, passed, detail in checks:
        print(f"  {'PASS' if passed else 'ECHEC'}  {label} -- {detail}")
        ok = ok and passed
    print(f"self-test cliquet : {'PASS' if ok else 'ECHEC'} "
          f"({sum(1 for _, p, _ in checks if p)}/{len(checks)})")
    return 0 if ok else 1


def scan_root(root: Path, as_json: bool, fail_on_findings: bool = False,
              base_root: Path | None = None) -> int:
    """Mode dossier. Si ``base_root`` est fourni, applique le mode diff : pour
    chaque carnet du head, cherche son pendant dans base (par chemin relatif).
    Un carnet present dans head mais absent dans base est scanne en mode
    standalone (toutes ses lectures sont des ajouts). Un carnet present dans
    base mais absent dans head est ignore : on ne signale pas des retraits.
    """
    total = 0
    per_kind: Counter[str] = Counter()
    unreadable: list[str] = []
    rows = []

    targets = list(iter_notebooks(root))
    base_by_rel: dict[str, Path] = {}
    if base_root is not None:
        for p in iter_notebooks(base_root):
            try:
                rel = p.relative_to(base_root)
            except ValueError:
                continue
            base_by_rel[str(rel).replace("\\", "/")] = p

    for head_path in targets:
        try:
            rel = head_path.relative_to(root)
        except ValueError:
            rel = Path(head_path.name)
        rel_str = str(rel).replace("\\", "/")
        try:
            head_nb = _read_nb(head_path)
        except (OSError, json.JSONDecodeError) as e:
            # #17044 : un carnet illisible ne doit PAS annuler le recensement.
            print(f"ERREUR lecture {head_path}: {e}", file=sys.stderr)
            unreadable.append(str(head_path.relative_to(root)))
            continue

        base_nb = None
        if base_root is not None:
            base_path = base_by_rel.get(rel_str)
            if base_path is not None:
                try:
                    base_nb = _read_nb(base_path)
                except (OSError, json.JSONDecodeError) as e:
                    print(f"ERREUR lecture base {base_path}: {e}", file=sys.stderr)
                    # base illisible : degrade en mode standalone (pas de diff)

        if base_root is not None:
            findings = detect_added_readings(head_nb, base_nb)
        else:
            findings = detect(head_nb)

        if not findings:
            continue
        total += len(findings)
        for f in findings:
            per_kind[f["type"]] += 1
            rows.append({"file": rel_str, **f})

    if unreadable:
        print(
            f"\nATTENTION : {len(unreadable)} carnet(s) illisible(s), NON recenses "
            f"-- le total ci-dessous est partiel :",
            file=sys.stderr,
        )
        for u in unreadable:
            print(f"  - {u}", file=sys.stderr)
    if as_json:
        print(json.dumps(rows, ensure_ascii=False, indent=1))
    else:
        for r in rows:
            extra = ""
            if "prev_role" in r:
                extra = (
                    f" prev={r['prev_role']:8s} next={r['next_role']:8s}"
                    f" src[:120]={r.get('src_first_120','')[:90]}"
                )
            print(
                f"{r['type']:22s} {r['file']}  cellules {r['cells']}{extra}"
            )
        suffix = f" -- {len(unreadable)} illisible(s)" if unreadable else ""
        print(f"\nTotal : {total} ({dict(per_kind)}){suffix}")
    return 2 if (fail_on_findings and total) else 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("path", nargs="?", default=str(REPO_ROOT / "MyIA.AI.Notebooks"),
                    help="notebook ou dossier a scanner (head, en mode diff)")
    ap.add_argument("--json", action="store_true", dest="as_json")
    ap.add_argument("--fail-on-findings", action="store_true")
    ap.add_argument(
        "--base",
        default=None,
        help=(
            "Chemin du notebook ou dossier de BASE pour le mode diff "
            "(#17464). Avec --base, l'organe signale les cellules markdown "
            "INSEREES dans head qui violent la regle 'une sortie = une "
            "lecture' ; sans --base, comportement historique (recensement "
            "consecutive d'en-tetes)."
        ),
    )
    ap.add_argument(
        "--base-ref",
        default=None,
        help=(
            "Ref git de BASE pour le mode CLIQUET (#17044) : l'organe resout "
            "le merge-base, lit chaque carnet modifie a sa version de base, et "
            "rougit seulement si la tete AUGMENTE ce qu'il voit (lecture "
            "ajoutee, ou compte de paires superieur). Les findings deja sur la "
            "base sont grandfathered."
        ),
    )
    ap.add_argument("--head", default="HEAD",
                    help="Ref git examinee en mode cliquet (defaut: HEAD)")
    ap.add_argument(
        "--self-test",
        action="store_true",
        help="Controles positif et negatif du cliquet, sans git ni reseau",
    )
    args = ap.parse_args(argv)

    if args.self_test:
        return self_test()

    if args.base_ref:
        rows = ratchet_rows(args.base_ref, args.head)
        if rows is None:
            print(f"base irresoluble : {args.base_ref}", file=sys.stderr)
            return 1
        bad = [r for r in rows if r["regressed"]]
        if args.as_json:
            print(json.dumps({
                "base_ref": args.base_ref, "head": args.head,
                "changed": len(rows), "regressed": len(bad), "rows": rows,
            }, ensure_ascii=False, indent=1))
        else:
            print(f"base {args.base_ref} | {len(rows)} carnet(s) modifie(s) | "
                  f"{len(bad)} en regression")
            for r in rows:
                tag = "REGRESSED" if r["regressed"] else "OK"
                delta = f"+{r['delta']}" if r["delta"] >= 0 else str(r["delta"])
                print(f"  {tag:9s} {r['notebook']}  "
                      f"paires {r['base_total']} -> {r['head_total']} ({delta})")
                for f in r["added"]:
                    print(f"      {f['type']:22s} cellules {f['cells']} "
                          f"src[:120]={f.get('src_first_120', '')[:80]}")
            if bad:
                print("\nCliquet : la PR augmente les lectures scindees sur au "
                      "moins un carnet qu'elle touche. Fusionner la lecture "
                      "ajoutee dans la lecture existante (le mandat user : "
                      "« si on rajoute une lecture, on modifie le paragraphe "
                      "de lecture existant, on n'en rajoute pas un deuxieme »).")
        return 2 if (args.fail_on_findings and bad) else 0

    target = Path(args.path)
    if not target.exists():
        print(f"introuvable : {target}", file=sys.stderr)
        return 1
    base_path = Path(args.base) if args.base else None
    if base_path is not None and not base_path.exists():
        print(f"introuvable : {base_path}", file=sys.stderr)
        return 1

    if target.is_file():
        try:
            head_nb = _read_nb(target)
        except (OSError, json.JSONDecodeError) as e:
            print(f"ERREUR lecture {target}: {e}", file=sys.stderr)
            return 1
        if base_path is not None:
            if base_path.is_file():
                try:
                    base_nb = _read_nb(base_path)
                except (OSError, json.JSONDecodeError) as e:
                    print(f"ERREUR lecture {base_path}: {e}", file=sys.stderr)
                    return 1
            else:
                # base is a folder but target is a file -- mismatch
                print(
                    f"mode diff fichier-a-dossier non supporte : --base={base_path}",
                    file=sys.stderr,
                )
                return 1
            findings = detect_added_readings(head_nb, base_nb)
        else:
            findings = detect(head_nb)
        if args.as_json:
            print(json.dumps(findings, ensure_ascii=False, indent=1))
        elif findings:
            for f in findings:
                if "prev_role" in f:
                    print(
                        f"{f['type']:22s} cellules {f['cells']} "
                        f"prev={f['prev_role']:8s} next={f['next_role']:8s} "
                        f"src[:120]={f.get('src_first_120','')[:90]}"
                    )
                else:
                    print(
                        f"{f['type']} cellules {f['cells']} J={f['jaccard']} "
                        f"C={f['rare_containment']} «{f['titles'][0]}» + «{f['titles'][1]}»"
                    )
        else:
            print("clean")
        return 2 if (args.fail_on_findings and findings) else 0
    rc = scan_root(target, args.as_json, args.fail_on_findings, base_path)
    return rc


if __name__ == "__main__":
    sys.exit(main())
