#!/usr/bin/env python3
"""La FORME positive d'un echec d'OUTIL : quand un code d'echec est-il le
MOTIF COURANT du rendu ?

Le rendu courant d'un [RELEASED] tient en deux blocs : le **bloc du
marqueur** (ce que la lane rend) et le **bloc des essais** qui l'ajuente (les
essais consommes). Les blocs suivants sont des rappels : un code qui n'y
figure pas n'est pas le motif courant.

La portee locale (un echec d'outil ne gele que la lane qui l'a subi) est
reservee aux formes **positivement identifiees** : le format **explicite**
`motif: <code>` dans le bloc du marqueur ; la forme **Rust mesuree**
(22/11) `code (fournee w3p, 22/11)` dans le bloc du marqueur ou celui des
essais -- elle porte sa **fournee** ET sa date. Toute autre mention d'un
code est un rappel : le gel reste **global** (fail-CLOSED).

Review du 26/11 (#28440) : le bloc qui suit le marqueur n'est le bloc des
**essais** que si le marqueur **annonce** des essais ; et une clause de
**rappel date** (« Essai du 22/11 : ... ») se rapporte a un essai passe :
elle ne nomme pas le motif courant, meme avec la forme Rust complete.
"""
from __future__ import annotations

import re

#: Le format explicite : le code est **nomme** comme motif du rendu.
_MOTIF_EXPLICITE_RE = re.compile(r"\bmotif\s*:\s*([\w-]+)")

#: Le marqueur du rendu : le bloc qui le porte.
_MARQUEUR_RE = re.compile(r"\[\s*RELEASED\s*\]", re.IGNORECASE)

#: La forme Rust mesuree : le code, sa **fournee** et sa date (`22/11`).
_FORME_RUST_RE = re.compile(
    r"([\w-]+)\s*\([^()]*\bfournee\b[^()]*\d{1,2}/\d{1,2}[^()]*\)")

#: Le marqueur **annonce**-t-il des essais ? (« 2 essais contenu consommes »)
_ANNONCE_ESSAIS_RE = re.compile(r"\bessais?\b", re.IGNORECASE)

#: Un **rappel date** d'essai : « Essai du 22/11 : ... » — l'essai passe.
_RAPPEL_DATE_RE = re.compile(r"\bessais?\s+du\s+\d{1,2}\s*/\s*\d{1,2}",
                             re.IGNORECASE)

#: La fenetre de contexte : le rappel date precede immediatement le code.
_FENETRE = 60


def _blocs(corps: str) -> list[str]:
    """Les blocs du commentaire : les paragraphes, separes par une ligne vide."""
    return [b for b in re.split(r"\n\s*\n", corps or "") if b.strip()]


def bloc_courant(corps: str) -> tuple[str, str | None]:
    """Le bloc du marqueur du rendu, et le bloc des essais qui le suit.

    Le DERNIER marqueur parle : c'est lui qui decrit l'etat courant. Le
    bloc qui le suit n'est le bloc des **essais** que si le marqueur
    **annonce** des essais : sinon c'est un rappel, qui ne nomme pas le
    motif courant (review du 26/11, #28440).
    """
    bs = _blocs(corps)
    for i in range(len(bs) - 1, -1, -1):
        if _MARQUEUR_RE.search(bs[i]):
            suivant = bs[i + 1] if i + 1 < len(bs) else None
            if suivant and _ANNONCE_ESSAIS_RE.search(bs[i]):
                return bs[i], suivant
            return bs[i], None
    return "", None


def _formes_rust(bloc: str) -> set[str]:
    """Les codes en forme Rust mesuree, **hors rappels dates**.

    « Essai du 22/11 : verify-reject (fournee w3p, 22/11) » porte la forme
    complete, mais elle se rapporte a un essai passe : elle ne nomme pas le
    motif courant.
    """
    bas = bloc.lower()
    trouves: set[str] = set()
    for m in _FORME_RUST_RE.finditer(bas):
        if _RAPPEL_DATE_RE.search(bas[max(0, m.start() - _FENETRE):m.start()]):
            continue
        trouves.add(m.group(1))
    return trouves


def codes_identifies(corps: str) -> set[str]:
    """Les codes d'echec **positivement identifies** comme motif courant.

    Le corps est lu en minuscules et sans accent (l'appelant normalise).
    """
    marqueur, essais = bloc_courant(corps)
    trouves = {m.group(1) for m in _MOTIF_EXPLICITE_RE.finditer(marqueur.lower())}
    for bloc in (marqueur, essais):
        if bloc:
            trouves |= _formes_rust(bloc)
    return trouves
