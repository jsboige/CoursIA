#!/usr/bin/env python3
"""L'exemption « Hors flotte » (#17713) lue par les deux tapis (#26893).

Module extrait par plafond de lignes : le predicat est partage par le tapis
rapide (ecart HORSFLOTTE) et le tirage lourd (filter_candidates, raison
``hors_flotte``). Fonctions pures, sans reseau. Dans le tapis rapide,
l'ecart DOMINE les autres : une issue hors flotte n'est pas un grain de
lane, quel que soit son etat de livraison (#26893).
"""
from __future__ import annotations

import re

_FENCE_RE = re.compile(r"```.*?(?:```|\Z)", re.DOTALL)
_PHRASE_RE = re.compile(r"hors\s+flotte", re.IGNORECASE)
# Decoration de tete de ligne qui reste une DECLARATION : puce, tiret, gras.
# Le blockquote `>` n'en fait PAS partie : une citation du marqueur n'est pas
# une declaration -- #26893 le cite en bloc pour decrire le defaut et reste
# un grain de flotte ordinaire.
_TETE_RE = re.compile(
    r"^[ \t]*(?:[-*+•–—][ \t]*){0,2}(?:\*\*[ \t]*)?hors\s+flotte\b",
    re.IGNORECASE)


def hors_flotte_declaration(body: str | None) -> str | None:
    """L'extrait de la ligne qui DECLARE l'exemption hors flotte, sinon None.

    Formes mesurees le 16/11 (#26893, Marathon II) : la ligne qui COMMENCE
    par « Hors flotte » (canonique #17713, p. ex. #26612), le span gras en
    tete de ligne qui la porte (« **Travail hors flotte ...** » #26870,
    « **Etat du ... -- livre hors flotte ...** » #26849), la ligne citant la
    regle (« Suivi Marathon II hors flotte #17713 » #26905). La prose ne
    declare pas : #26751 raconte « une session hors flotte » sans etre hors
    flotte. Le code entre fences n'est pas lu.
    """
    for ligne in _FENCE_RE.sub("", body or "").splitlines():
        if _TETE_RE.match(ligne):
            return ligne.strip()[:72]
        tete = ligne.lstrip()
        if tete.startswith("**"):
            fin = tete.find("**", 2)
            if _PHRASE_RE.search(tete[2:] if fin == -1 else tete[2:fin]):
                return ligne.strip()[:72]
        # La citation de la regle ne vaut declaration qu'en prose nue : une
        # puce ou un bloc qui mentionne « hors flotte #17713 » decrit une
        # contribution tierce ( faux positifs mesures : #10643, #20250,
        # #25509, #25670 -- des EPICs de flotte citant des livraisons cloud).
        if tete[:1] not in ">*-+" and "#17713" in ligne and _PHRASE_RE.search(ligne):
            return ligne.strip()[:72]
    return None


def ecart_hors_flotte(body: str | None) -> str | None:
    """Motif d'ecart du tapis rapide : la declaration, citee."""
    extrait = hors_flotte_declaration(body)
    return f"declaration hors flotte (#17713) : {extrait}" if extrait else None
