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

  - ``SECOND_READING``      : cellule markdown ajoutee juste avant ou apres
                              une lecture existante (les bases de la campagne
                              #13410 ajoutaient des paragraphes *sans en-tete*
                              derives de la lecture -- invisibles au detecteur
                              consecutive) ;
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

Mode CLIQUET (#17044) : ``--base-ref <ref> [--head HEAD]`` compare chaque carnet
modifie entre la base et la tete et rend le verdict du cliquet -- rouge
seulement si la PR **augmente** ce que l'organe voit sur un carnet qu'elle
touche :

  - ``regressed`` = au moins une lecture AJOUTEE (mode diff, position-aware) OU
    ``len(detect(head)) > len(detect(base))`` (le compte des paires consecutive).
    Les findings deja sur ``main`` sont donc *grandfathered* : c'est un cliquet,
    pas un plancher absolu.
  - les renames sont resolus via ``--name-status -M`` (un carnet renomme est lu
    a son ANCIEN chemin dans la base -- sans quoi le renommage passerait pour un
    ajout et tous ses findings pour des augmentations) ;
  - une base irresoluble est une ERREUR (rc=1), jamais un cliquet vide : lire un
    carnet absent de la base comme « ajoute » ferait rougir la PR entiere sur un
    probleme de fetch.

``--self-test`` joue cinq controles, hors git et hors reseau : deux positifs
(lecture empilee nommee ; lecture ajoutee SANS en-tete, invisible au detecteur
consecutive) et trois negatifs (deux lectures fusionnees en une ; modification de
code sans lecture ajoutee ; encart sans code execute au-dessus).

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


def detect_added_readings(head_nb: dict, base_nb: dict | None) -> list[dict]:
    """Mode DIFF (#17464) : signale les cellules markdown **ajoutees** dans une PR
    dont la position viole la regle user « une sortie = une lecture ».

    Algorithme :
      1. Si ``base_nb`` est None, retourne une liste vide.
      2. Diff par multiset de sources (entre par sources, pas par id -- la
         campagne a produit des cellules sans id et des ids dupliques).
      3. Pour chaque cellule ajoutee qui est markdown, classifier via le
         **contexte HEAD** :
           - ``EXERCISE_READING``    prev_role == "exercise"
           - ``READING_BEFORE_CODE`` next_role == "code_with_output"
           - ``SECOND_READING``      prev_role == "md"
                                       (lecture ajoutee derriere une lecture
                                       deja presente)
                                     OU prev_role == "code_with_output"
                                        ET la cellule de code en question
                                        etait **elle-meme deja precede d'une
                                        lecture en base** (sinon : ajout
                                        legitime d'une premiere lecture pour
                                        un nouveau code)

    Le discriminant pour ``SECOND_READING`` apres code : on regarde en base
    la cellule qui precede le meme code (identifiee par egalite de source).
    Si en base cette cellule de code etait deja suivie d'une lecture markdown,
    l'ajout est un doublonnage ; sinon, c'est la premiere lecture legitime.

    Sortie : liste de dicts ``{type, cells, src_first_120, prev_role,
    next_role, prev_src_last_60, next_src_first_60}``.
    """
    if base_nb is None:
        return []
    base_cells = base_nb.get("cells", [])
    head_cells = head_nb.get("cells", [])
    base_srcs = [cell_source(c) for c in base_cells]
    head_srcs = [cell_source(c) for c in head_cells]

    # Pour le discriminant SECOND_READING : index par source de toutes les
    # cellules de base dont la source est DU CODE A SORTIE UTILE, et map
    # "ce code etait-il deja suivi d'une cellule de LECTURE" (pas
    # n'importe quelle markdown -- un "Conclusion" terminal n'est pas une
    # lecture au sens de la regle, meme s'il suit une cellule de code).
    base_code_positions: dict[str, list[int]] = {}
    for i, src in enumerate(base_srcs):
        c = base_cells[i]
        if c.get("cell_type") == "code":
            ec = c.get("execution_count")
            outs = c.get("outputs") or []
            if (ec is not None or outs) and not is_exercise_cell(c):
                base_code_positions.setdefault(src, []).append(i)

    base_counter: Counter[str] = Counter(base_srcs)
    head_counter: Counter[str] = Counter(head_srcs)

    # #17044 -- les IDs de la base, consommes un a un. Le discriminant
    # d'origine exigeait la MEME position pour reconnaitre une rewrite par son
    # id ; une fusion (ou toute insertion/suppression au-dessus) decale les
    # index, et la cellule reecrite repartait alors comme un AJOUT. Mesure sur
    # 11 PR notebook mergees : 3 rouges, dont 2 PR de FUSION -- le remede
    # prescrit par le mandat user -- toutes deux expliquees par ce decalage.
    base_id_pool: Counter[str] = Counter(
        c.get("id") for c in base_cells if c.get("id")
    )

    findings: list[dict] = []
    for idx, src in enumerate(head_srcs):
        if head_counter[src] <= base_counter[src]:
            base_counter[src] += 1
            continue
        cell = head_cells[idx]
        if cell.get("cell_type") != "markdown":
            base_counter[src] += 1
            continue

        # Discriminant 0 : REWRITE (pas d'insertion). On considere qu'une
        # cellule est une REWRITE -- et NON un ajout -- quand au moins
        # l'UN des trois signaux tient :
        #   (a) meme position index-for-index ET meme source (meme
        #       contenu exact -- ne mord que sur un doublon de source, une
        #       revision par definition ne repasse pas ici) ;
        #   (b) l'id de la cellule existe encore en base -- MEME a un autre
        #       index (#17044). Une fusion retire ou insere des cellules
        #       au-dessus, donc l'index se decale : exiger la meme position
        #       faisait passer la rewrite pour un ajout. Le ticket #17464 note
        #       que la campagne a produit des cellules sans id ET des ids
        #       dupliques -- l'id est donc consomme une fois, ce qui borne les
        #       doublons sans reouvrir la porte ;
        #   (c) meme position ET les deux cellules sont markdown : la tete
        #       a revise celle qui occupait ce slot (#17044, etendu #17747).
        #       Signal topologique, indispensable sur les carnets SANS id (le
        #       corpus en contient -- cf. les deux carnets du controle positif).
        # La regle user dit « fusionner / reecrire, pas empiler » : la
        # reecriture EST l'action prescrite. Ne pas la signaler.
        is_rewrite = False
        head_id = cell.get("id")
        if head_id and base_id_pool.get(head_id, 0) > 0:
            base_id_pool[head_id] -= 1
            is_rewrite = True
        if (not is_rewrite and idx < len(base_cells)
                and base_cells[idx].get("cell_type") == "markdown"
                and cell_source(base_cells[idx]) == src):
            is_rewrite = True
        #   (c) meme position ET les DEUX cellules sont MARKDOWN : la tete a
        #       REVISE celle qui occupait ce slot (#17044). Le mandat prescrit
        #       cette revision ; sans ce signal elle n'etait reconnue que sur
        #       les carnets porteurs d'ids, donc le remede etait puni des que
        #       les cellules n'en avaient pas (le corpus en contient : les deux
        #       carnets du controle positif #17028 sont dans ce cas). Un
        #       EMPILEMENT reel a cote n'est pas vu ici : la lecture empilee
        #       arrive a un index ou la base porte autre chose (ou rien), et
        #       le compte de paires, lui, monte.
        #
        #       Le signal ne depend PAS de la classification lecture/exercice
        #       (#17747) : une revision de prose en place n'est pas un
        #       empilement, quel que soit le titre. Exiger « les deux sont des
        #       lectures » rouvrait sur les carnets SANS id le faux positif que
        #       #17044 avait ferme pour les lectures. Mesure fondatrice : un
        #       simple echappement de `$` (``39,66 $`` -> ``39,66 \$``) dans
        #       une cellule sans id titree « ### Exercice 3 » suffisait a la
        #       faire passer pour un ajout, et le cliquet rougissait le geste
        #       que le mandat PRESCRIT.
        if (not is_rewrite and idx < len(base_cells)
                and base_cells[idx].get("cell_type") == "markdown"
                and cell.get("cell_type") == "markdown"):
            is_rewrite = True
        if is_rewrite:
            base_counter[src] += 1
            continue

        prev_role, next_role = _classify_context(head_cells, idx)
        bucket = _bucket_for(prev_role, next_role)
        # Discriminant SECOND_READING : si prev_role == "code_with_output",
        # verifier en base si ce code etait **deja suivi** d'une cellule
        # markdown (au sens large du ticket user : « deja suivie d'au moins
        # une cellule markdown » -- la distinction lecture vs transition
        # est tranchee par la pedagogie, pas par le format).
        # Si la base avait deja une md derriere ce code, ajouter une md
        # supplementaire derriere est un doublonnage. Si la base n'avait
        # rien derriere ce code (markdown), c'est la premiere lecture
        # legitime (et NON une violation).
        if bucket == "SECOND_READING" and prev_role == "code_with_output":
            prev_cell = head_cells[idx - 1] if idx > 0 else None
            if prev_cell is not None:
                prev_src = cell_source(prev_cell)
                prev_positions = base_code_positions.get(prev_src, [])
                already_had_md_after = any(
                    (i + 1 < len(base_cells)
                     and base_cells[i + 1].get("cell_type") == "markdown")
                    for i in prev_positions
                )
                if not already_had_md_after:
                    # premiere lecture legitime pour ce code -> ne pas signaler
                    bucket = None
        # #17044 -- SECOND_READING apres une MARKDOWN : le bucket ne regardait
        # que la topologie (md, md) et signalait donc tout encart insere entre
        # deux cellules de prose (mesure : un bandeau « statut epistemique » en
        # tete de notebook, #17484 -- aucun code au-dessus). La definition de
        # l'issue est « deux cellules de lecture pour une MEME cellule de
        # code » : sans code a sortie au-dessus, il n'y a rien a lire, donc pas
        # de seconde lecture. Le cas fondateur reste capte -- ses paragraphes
        # sans en-tete sont tous poses sous un code a sortie (mesure : 7/7).
        if (bucket == "SECOND_READING" and prev_role == "md"
                and not _reads_code_above(head_cells, idx)):
            bucket = None
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
        prev = head_cells[idx - 1] if idx > 0 else None
        nxt = head_cells[idx + 1] if idx + 1 < len(head_cells) else None
        prev_src = (cell_source(prev)[-60:] if prev is not None else "")
        nxt_src = (cell_source(nxt)[:60] if nxt is not None else "")
        findings.append({
            "type": bucket,
            "cells": [idx],
            "src_first_120": src[:120].replace("\n", " | "),
            "prev_role": prev_role,
            "next_role": next_role,
            "prev_src_last_60": prev_src.replace("\n", " | "),
            "next_src_first_60": nxt_src.replace("\n", " | "),
        })
        base_counter[src] += 1
    return findings


def _reads_code_above(cells: list[dict], idx: int) -> bool:
    """Vrai si la cellule ``idx`` commente la sortie d'un code situe au-dessus.

    Motif vise par l'issue #17044 : « deux cellules de lecture pour une MEME
    cellule de code ». Une prose ajoutee dans une zone qui ne suit AUCUN code a
    sortie (preamble d'un notebook, bandeau de statut, en-tete de section) n'est
    pas une seconde lecture -- il n'y a rien a lire au-dessus.
    """
    for j in range(idx - 1, -1, -1):
        c = cells[j]
        if c.get("cell_type") != "code":
            continue
        if is_exercise_cell(c):
            return False
        return bool(c.get("execution_count") is not None or (c.get("outputs") or []))
    return False


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
        if "/_archive/" in f"/{head_path}":
            # Convention `_archive/` (docs/reference/_archive-convention.md) :
            # chaque carnet archive porte une banniere tombstone en tete de
            # fichier -- markdown avant code par construction. La regle
            # pedagogique ne s'applique plus a un carnet sorti du parcours.
            continue
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
            "regressed": bool(added) or head_total > base_total,
        })
    return rows


def _nb(cells: list[tuple[str, str, str | None]]) -> dict:
    """Carnet minimal pour les controles : (cell_type, source, id).

    Les cellules de code portent une sortie et un execution_count : c'est la
    condition d'une lecture (« rien a lire » sinon, cf ``_reads_code_above``),
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
