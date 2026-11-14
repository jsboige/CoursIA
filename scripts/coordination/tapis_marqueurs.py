#!/usr/bin/env python3
"""Lecture des marqueurs de fil pour le tapis rapide (#22983, #26414).

Fonctions pures, sans reseau : un commentaire d'issue devient une suite
d'evenements (`Evt`) lus en tete de ligne, avec la decoration que tolere
`check_lane_claim.py`. Extrait de `tapis_rapide.py` pour tenir son plafond de
lignes ; `tapis_rapide.py` reexporte ce qu'il utilise.
"""
from __future__ import annotations

import re
from dataclasses import dataclass
from datetime import UTC, datetime

OUVRE = frozenset({"CLAIMED", "CLAIMED-AMEND"})
FERME = frozenset({"RELEASED", "DELIVERED", "CANCELLED", "ABANDONED", "DONE"})
VISITE = frozenset({"CLAIMED", "CLAIMED-AMEND", "DELIVERED"})
ROUVRE = frozenset({"NOT-DELIVERED", "RELEASED", "CLAIMED", "CLAIMED-AMEND"})

# Un marqueur est en tete de N'IMPORTE QUELLE ligne (souvent apres `Grain:`),
# avec la decoration que tolere `check_lane_claim.py`.
_DECOR = (r"^[ \t]*(?:[#>*+\-\u2192\u27a1\u279c\u00bb\u2022\u2013\u2014]{1,6}[ \t]*)*"
          r"(?:\*\*|__)?[ \t]*")
_MARQUEUR_RE = re.compile(
    _DECOR + r"\[\s*(CLAIMED-AMEND|CLAIMED|RELEASED|DELIVERED|OVERRIDE|CANCELLED|ABANDONED"
    r"|DONE|NOT-DELIVERED|UNFROZEN|FROZEN|CLOSURE REVIEW)\s*\](.*)$",
    re.MULTILINE | re.IGNORECASE)
# `[INFO] candidate-delivered`, ou `[INFO] lane X -- candidate-delivered` (forme mesuree
# sur #20603, 13/11) : le mot sur la ligne du tag, sauf nie juste avant.
_INFO_LIVRE_RE = re.compile(
    _DECOR + r"\[INFO\][^\n]{0,120}?(?<!not )(?<!non )(?<!pas )\bcandidate-delivered\b",
    re.MULTILINE | re.IGNORECASE)
_FENCE_RE = re.compile(r"```.*?(?:```|\Z)", re.DOTALL)  # du code cite un marqueur sans le poser
_PATHS_RE = re.compile(r"(?<![`\"'\w])paths\s*:\s*(\S[^\n]*)", re.IGNORECASE)
_KEEP_RE = re.compile(r"verdict\s*:\s*\**\s*KEEP\b", re.IGNORECASE)
_LANE_RE = re.compile(r"\blane\s*:?\s+`?([\w.-]+:[\w.-]+)", re.IGNORECASE)
_LANE_NUE_RE = re.compile(r"\b(myia-[\w.-]+:[\w.-]+)")
_JAMAIS = datetime.min.replace(tzinfo=UTC)


@dataclass(frozen=True)
class Evt:
    """Un marqueur lu en tete de ligne d'un commentaire."""

    quand: datetime
    marque: str
    lane: str | None
    paths: str | None
    reste: str


def _dt(texte: str | None) -> datetime | None:
    try:
        d = datetime.fromisoformat(texte or "")
    except ValueError:
        return None
    return d if d.tzinfo else d.replace(tzinfo=UTC)


def _iso(d: datetime) -> str:
    return d.astimezone(UTC).strftime("%Y-%m-%dT%H:%M:%SZ")


def _lane(ligne: str, texte: str) -> str | None:
    """Sur la ligne du marqueur, le premier jeton `lane X` ou `myia-...:...` nu ;
    sinon le premier `lane X` du commentaire."""
    trouves = [m for m in (_LANE_RE.search(ligne), _LANE_NUE_RE.search(ligne)) if m]
    m = min(trouves, key=lambda m: m.start(1)) if trouves else _LANE_RE.search(texte)
    return m.group(1).rstrip(".") if m else None


def lane_de_pr(pr: dict) -> str | None:
    """Le premier `lane <machine:workspace>` du body (la ligne `Grain:`), pour
    ne pas prendre une lane citee plus bas."""
    m = _LANE_RE.search(pr.get("body") or "")
    return m.group(1).rstrip(".") if m else None


def evenements(comments: list[dict]) -> list[Evt]:
    """Les marqueurs des commentaires disponibles, dans l'ordre du fil."""
    evts: list[Evt] = []
    for c in comments:
        texte = _FENCE_RE.sub("", c.get("body") or "")
        quand = _dt(c.get("created_at")) or _JAMAIS
        for m in _MARQUEUR_RE.finditer(texte):
            p = _PATHS_RE.search(m.group(2))
            evts.append(Evt(quand, m.group(1).upper(), _lane(m.group(0), texte),
                            p.group(1).strip() if p else None, m.group(2)))
    return sorted(evts, key=lambda e: e.quand)


def claims_ouverts(evts: list[Evt]) -> dict[str, Evt]:
    """Par lane, CLAIMED* ouvre et RELEASED/DELIVERED ferme ; OVERRIDE attribue
    l'issue a sa lane et ferme les autres."""
    ouverts: dict[str, Evt] = {}
    for e in evts:
        if e.lane is None:
            continue
        if e.marque == "OVERRIDE":
            ouverts.clear()
        if e.marque in OUVRE or e.marque == "OVERRIDE":
            ouverts[e.lane] = e
        elif e.marque in FERME:
            ouverts.pop(e.lane, None)
    return ouverts


def _rouverte(evts: list[Evt], depuis: datetime) -> bool:
    """Un commentaire posterieur rouvre-t-il l'issue ?"""
    return any(e.quand > depuis and (e.marque in ROUVRE or (
        e.marque == "CLOSURE REVIEW" and _KEEP_RE.search(e.reste))) for e in evts)
