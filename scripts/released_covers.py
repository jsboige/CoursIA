#!/usr/bin/env python3
"""Predicat « [RELEASED] + acceptance deja couverte » (#20351), sans dependance.

Extrait de `pick_idle_grain.py` (tranche #23762) : le workflow
`candidate-delivered-advisory` n'embarque que trois fichiers dans son
`sparse-checkout`, et `pick_idle_grain` en tire des dizaines au niveau module
(`series_saturation`, `grain_tag`, `gh_payload_cache`) -- importer le predicat
cassait donc le balayage en CI (`ModuleNotFoundError`, panne du 29/10 au 01/11,
commentaire #23762 c.6564437892). Ce module est importable seul : `re` et
`unicodedata`, rien d'autre.

Les deux organes l'importent :
- `pick_idle_grain._delivered_state` (sonde pleine du tapis) ;
- `candidate_delivered` (balayage CI).

Fonction pure, testable sans reseau. Un detecteur se valide par ses faux
NEGATIFS : voir `scripts/tests/test_pick_released_signal.py`.
"""

from __future__ import annotations

import re
import unicodedata

# #20351 : `[RELEASED]` + « acceptance deja couverte » = LIVRAISON pour le
# tapis. Le marqueur `[RELEASED]` a deux sens dans la flotte : soit une lane
# rend la main sur un item qu'elle n'a pas livre (barriere reelle -> l'item
# DOIT rester servi), soit elle rend la main en constatant que l'acceptance
# est deja couverte par un travail livre (l'item ne doit PLUS remonter).
# La sonde pleine ne lisait que `[INFO] candidate-delivered` : un item clot par
# la seconde forme gardait une « derniere visite » ancienne et revenait en
# tete du tapis indefiniment (11 tetes de tapis mortes mesurees le 2026-10-11
# par myia-po-2027:CoursIA).
#
# On ne reconnait donc QUE la forme couverte : l'en-tete `[RELEASED]` et le
# motif de couverture doivent etre sur la MEME ligne (le protocole ecrit
# `[RELEASED] lane <machine:workspace> -- <motif>`), et le motif doit etre
# AFFIRMATIF -- « acceptance deja couverte » et non « l'acceptance n'est pas
# couverte, on rend la main », qui est l'autre cas (barriere) et doit rester
# servi. La negation est donc cherchee explicitement, et non par un mot
# generique comme « pas » : une ligne « acceptance deja couverte, pas de
# travail restant » est une couverture, pas une negation.
_RELEASED_HEADER_RE = re.compile(r"^\s*(?:#{1,6}\s*)?\[RELEASED\](?=\s|:|$)")
# Les motifs sont compares sur une ligne NORMALISEE (accents retires) : la
# flotte ecrit indifféremment « deja couverte », « déjà couverte », « rien a
# reparer », « rien à réparer ». Un motif ecrit en ASCII matcherait la
# forme accentuee, l'inverse non -- la normalisation est donc faite sur la
# ligne, pas sur le motif.
#
# Le motif est ANCRE sur l'ACCEPTANCE de l'item (« acceptance deja couverte »,
# « l'acceptance est couverte », « acceptance deja livree ») : c'est la forme
# canonique que la flotte a employee sur la cohorte du dispatch central
# (#20351), et c'est la seule dont le sens est de niveau ITEM. Les formes
# « deja livre » / « deja couvert » sans « acceptance » ont ete ecartees sur
# mesure : sur les 512 issues ouvertes, elles ne matchaient que des
# livraisons de SOUS-GRAIN (« la Tranche A est deja livree », « le carnet 03
# est deja livre », « grain deja livre ») -- les ecarter aurait retire du
# tapis des items encore actionnables (FLEAU, le faux positif d'un detecteur
# se mesure par ses faux NEGATIFS). Les formes « rien a reparer » /
# « aucun travail restant » restent, Completees par la garde de perimetre
# ci-dessous.
_COVERAGE_MOTIF_RE = re.compile(
    r"(?:"
    r"acceptance\s+(?:\w+\s+){0,2}(?:couvert\w*|satisfaite|livr\w+)"
    r"|scope\s+couvert\w*"
    r"|rien\s+a\s+repar\w+"
    r"|aucun\s+travail\s+restant"
    r"|aucune\s+tranche\s+restante"
    r"|plus\s+rien\s+a\s+faire"
    r")",
    re.IGNORECASE,
)
_COVERAGE_NEGATED_RE = re.compile(
    r"(?:pas|non|jamais)\s+(?:couvert\w*|satisfaite|livr\w+)",
    re.IGNORECASE,
)
# « pour cette lane » : une couverture rapportee a une lane n'est pas une
# couverture de l'item -- les autres lanes peuvent encore le servir. Mesure :
# #18767 (« aucune tranche restante POUR CETTE LANE ») garde 4 sous-modules a
# couvrir ; le traiter comme livre aurait ecarte un item actionnable.
_LANE_SCOPED_RE = re.compile(r"cette\s+(?:lane|equipe)", re.IGNORECASE)
# Un substantif de SOUS-ITEM dans la meme clause que le motif : la couverture
# porte alors sur une tranche, un carnet, un grain -- pas sur l'item.
_SCOPE_NOUN_RE = re.compile(
    r"\b(?:tranche|carnet|grain|sous-grain|sous-issue|notebook|pli|palier|"
    r"lot|portion|partie|etape|exercice|bloc|audit|fichier|script|cellule)\b",
    re.IGNORECASE,
)
# Separateurs de clause : la garde de perimetre et la garde de scope de lane
# ne regardent que la clause qui porte le motif.
_CLAUSE_BOUNDARY_RE = re.compile(r"[:;,.—–]")


def _strip_accents(text: str) -> str:
    """Minuscules sans accents : « déjà » -> « deja », « à » -> « a »."""
    decomposed = unicodedata.normalize("NFKD", text or "")
    return "".join(c for c in decomposed if not unicodedata.combining(c)).lower()


def _clause_window(text: str, start: int, end: int) -> tuple[str, str]:
    """(avant, apres) la clause qui contient `[start, end)`, sans les bornes."""
    head = text[:start]
    tail = text[end:]
    head_bounds = list(_CLAUSE_BOUNDARY_RE.finditer(head))
    tail_bounds = list(_CLAUSE_BOUNDARY_RE.finditer(tail))
    clause_head = head[head_bounds[-1].end():] if head_bounds else head
    clause_tail = tail[:tail_bounds[0].start()] if tail_bounds else tail
    return clause_head, clause_tail


def _released_covers_acceptance(body: str) -> bool:
    """Une ligne porte-t-elle `[RELEASED]` ET un motif d'acceptance couverte ?

    Fonction pure, testable sans reseau : c'est le seul point de la
    correction qui decide d'un nouveau verdict.

    Trois gardes font écran, dans cet ordre :
    1. la negation (« l'acceptance n'est pas couverte ») ;
    2. le perimetre de SOUS-ITEM (« la Tranche A est deja livree ») ;
    3. le scope de LANE (« aucune tranche restante pour cette lane »).
    """
    for raw_line in (body or "").splitlines():
        if not _RELEASED_HEADER_RE.match(raw_line):
            continue
        line = _strip_accents(raw_line)
        if _COVERAGE_NEGATED_RE.search(line):
            continue
        for match in _COVERAGE_MOTIF_RE.finditer(line):
            clause_head, clause_tail = _clause_window(
                line, match.start(), match.end())
            if _SCOPE_NOUN_RE.search(clause_head):
                continue
            if _LANE_SCOPED_RE.search(clause_tail):
                continue
            return True
    return False
