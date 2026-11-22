#!/usr/bin/env python3
"""Le DERNIER GRAIN d'une issue : trois etats qu'il ne faut pas confondre.

Le classement du tapis raisonne aujourd'hui sur une seule quantite : la
**visite**. Cette quantite melange deux choses qui n'ont pas le meme sens :

  - un **grain** : une lane a **pris en charge** l'issue (un marqueur
    nominatif `[CLAIMED]` / `[CLAIMED-AMEND]` / `[DELIVERED]`). C'est une
    seance de travail sur l'issue elle-meme ;
  - un **passage** : une **citation Git** (un commit, une PR qui cite
    l'issue). C'est une trace d'activite **autour** de l'issue, pas sur
    l'issue.

Les deux rajeunissent aujourd'hui le meme compteur. Consequence mesuree
(releve du 18/11 22:38Z, 454 issues) : **45 issues** n'ont recu qu'une mention
Git et aucune prise en charge -- elles sont comptees comme « visitees » par
le classement, alors qu'aucune lane ne les a servies. L'absence de marqueur
n'etablit rien quand le fil lu est **partiel** : elle est **non mesurable**.

Ce module rend les trois etats, separement :

  ``grain``          une prise en charge nominative dans la fenetre ;
  ``passage_seul``   des citations Git, mais aucune prise en charge ;
  ``jamais_servie``  aucun signal du tout, fil **complet** : absence etablie ;
  ``non_measurable`` aucun marqueur lisible, mais le fil n'est **pas**
                     complet : l'absence n'est **pas** etablie.

Ce qui **ne** rajeunit pas le dernier grain : une **qualification** (le verdict
d'un banc qui relit le fil) est une lecture, pas une prise en charge ; une
**apparition dans une liste** (un releve, un recensement, un classement) ne dit
pas qui a travaille sur l'issue.

Fonctions PURES, sans reseau. La mesure groupee se branche par
``depuis_signaux`` ; le fil lu par ``depuis_evenements``.

Usage :

    python scripts/coordination/tapis_dernier_grain.py \
        --releve scripts/tests/fixtures/tapis/dernier_grain_7j.json --json
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from dataclasses import dataclass
from datetime import datetime, timedelta
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import tapis_seance  # noqa: E402
from coordination.tapis_marqueurs import FERME, MARQUEUR_GRAIN, VISITE, Evt, _dt, _iso  # noqa: E402

#: Une prise en charge : le marqueur doit etre **nominatif** (une lane nommee).
GRAIN = "grain"
#: Des citations Git, mais aucune prise en charge.
PASSAGE = "passage_seul"
#: Aucun signal, et le fil est complet : l'absence est etablie.
JAMAIS = "jamais_servie"
#: Aucun marqueur lisible, fil partiel : l'absence n'est pas etablie.
NON_MESURABLE = "non_measurable"

#: L'ordre du classement : une issue sans grain passe devant une issue
#: servie ; l'etat non mesurable passe **apres** l'absence etablie (on
#: ne sert pas en premier ce dont on ignore l'etat), mais **avant** un grain.
RANG = {JAMAIS: 0, PASSAGE: 1, NON_MESURABLE: 2, GRAIN: 3}

#: Une prise en charge fait une **SEANCE** : deux marqueurs de la meme lane a
#: moins de `SEANCE_H` heures d'intervalle n'en font qu'une. La regle des
#: **instants** vit ici (`seances`) ; celle des **marqueurs** -- une livraison
#: en ouvre une neuve (#27338) -- vit dans `coordination/tapis_seance.py`.
SEANCE_H = 24


def seances(instants: list[datetime], depuis: datetime | None = None) -> int:
    """Le nombre de seances : un ecart de plus de SEANCE_H en ouvre une neuve."""
    n, avant = 0, None
    for t in sorted(t for t in instants if depuis is None or t >= depuis):
        if avant is None or t - avant > timedelta(hours=SEANCE_H):
            n += 1
        avant = t
    return n


def cle_tri(e) -> tuple:
    """La cle de tri du classement : l'etat de grain, puis l'anciennete.

    L'etat passe avant l'anciennete : une absence ETABLIE (aucune lane n'a
    jamais pris l'issue) passe devant un PASSAGE (une activite Git sans
    prise en charge), qui passe devant une absence NON MESURABLE (fil
    partiel : on ne sert pas en premier ce dont on ignore l'etat). Une issue
    servie passe en dernier.

    `etat_grain is None` : la voie legere ne lit pas le fil, elle ne peut pas
    distinguer un grain d'un passage -- l'ordre historique est conserve.
    """
    etat = getattr(e, "etat_grain", None)
    if etat is None:
        return (e.visites_total > 0, e.cree_le, e.derniere_visite or "", e.numero)
    return (RANG.get(etat, len(RANG)), e.cree_le, e.derniere_visite or "", e.numero)


@dataclass(frozen=True)
class EtatGrain:
    """L'etat de grain d'une issue, et les deux horodatages qui le fondent."""

    numero: int
    etat: str
    dernier_grain: str | None = None
    dernier_passage: str | None = None
    grains: int = 0
    passages: int = 0

    @property
    def rajeunit(self) -> bool:
        """Un grain rajeunit-il le classement ? Seul un grain le fait."""
        return self.etat == GRAIN

    @property
    def rang(self) -> int:
        return RANG.get(self.etat, len(RANG))


def _marqueurs_grain(evts: list[Evt]) -> list[datetime]:
    """Les instants des prises en charge **nominatives**.

    Un marqueur de visite sans lane nommee n'est pas un grain : personne ne
    peut en etre responsable, donc il ne dit rien de l'historique de l'issue.
    Une lecture (`VISITE-INFO`) non plus : c'est une qualification.
    """
    return [ev.quand for ev in evts
            if ev.marque in MARQUEUR_GRAIN and ev.lane]


def _passages(citations: list[dict]) -> list[datetime]:
    """Les instants des citations Git (les passages)."""
    return [d for c in citations if (d := _dt(c.get("date")))]


def compter_grains(evts: list[Evt],
                    depuis: datetime) -> tuple[str | None, int, int]:
    """Les **visites** : seances de prises en charge **ou** de lectures.

    Une citation Git n'est pas une visite : elle n'entre pas dans le compte,
    et elle ne rajeunit pas la derniere visite. `depuis` est le debut du tour
    -- c'est la fenetre qui decide, pas la date du dernier grain. L'ensemble
    lu est `VISITE` : une lecture d'une lane y compte aussi (#27590). Les
    seances suivent la regle des marqueurs (`tapis_seance.par_lane`) : une
    livraison en ouvre une neuve (#27338).
    """
    par_lane: dict[str, list[Evt]] = {}
    for ev in evts:
        if ev.lane and (ev.marque in VISITE or ev.marque in FERME):
            par_lane.setdefault(ev.lane, []).append(ev)
    tous = [ev.quand for evs in par_lane.values() for ev in evs
            if ev.marque in VISITE]
    return ((_iso(max(tous)) if tous else None),
            sum(tapis_seance.par_lane(evs) for evs in par_lane.values()),
            sum(tapis_seance.par_lane(evs, depuis) for evs in par_lane.values()))


def depuis_evenements(evts: list[Evt], citations: list[dict], *,
                      numero: int = 0, fil_complet: bool = True,
                      depuis: datetime | None = None) -> EtatGrain:
    """L'etat de grain d'une issue, depuis les evenements et les citations.

    `depuis` borne la **fenetre** : le classement raisonne sur le tour (7 j
    par defaut), et un grain plus ancien ne rajeunit rien -- c'est la
    fenetre qui decide, pas la date du dernier grain.

    `fil_complet` dit si le fil lu est le fil entier : c'est lui qui
    distingue « aucune prise en charge » (etablie) de « absence non
    mesurable ».
    """
    if depuis is not None:
        evts = [ev for ev in evts if ev.quand >= depuis]
    grains = _marqueurs_grain(evts)
    passages = [d for d in _passages(citations) if depuis is None or d >= depuis]
    if grains:
        etat = GRAIN
    elif passages:
        etat = PASSAGE
    elif fil_complet:
        etat = JAMAIS
    else:
        etat = NON_MESURABLE
    return EtatGrain(
        numero=numero, etat=etat,
        dernier_grain=_iso(max(grains)) if grains else None,
        dernier_passage=_iso(max(passages)) if passages else None,
        grains=len(grains), passages=len(passages))


def depuis_signaux(*, numero: int, marqueurs: int, mentions_git: int,
                   fil_tronque: bool) -> EtatGrain:
    """L'etat de grain depuis un **releve groupe** (aucun appel par issue).

    C'est la forme que donne la mesure groupee : combien de marqueurs
    nominatifs dans la fenetre, combien de mentions Git, et si la fenetre
    de fil etait tronquee. Meme semantique que `depuis_evenements`, sans
    lecture : les compteurs y sont agreges, pas les instants.
    """
    if marqueurs:
        etat = GRAIN
    elif mentions_git:
        etat = PASSAGE
    elif fil_tronque:
        etat = NON_MESURABLE
    else:
        etat = JAMAIS
    return EtatGrain(numero=numero, etat=etat, grains=marqueurs,
                     passages=mentions_git)


def classer_releve(rows: list[dict]) -> dict:
    """Rejoue un releve groupe : les etats, les compteurs, les candidats.

    Le rejeu ne **rafraichit** rien : l'apparition d'une issue dans un releve
    n'est pas une prise en charge (cf l'entete du module).
    """
    etats = []
    for r in rows:
        etats.append(depuis_signaux(
            numero=int(r.get("n") or 0),
            marqueurs=int(r.get("marqueurs") or 0),
            mentions_git=int(r.get("mentions_git") or 0),
            fil_tronque=bool(r.get("fil_tronque"))))
    compteurs = Counter(e.etat for e in etats)
    return {
        "issues": len(etats),
        "compteurs": dict(compteurs),
        "sans_grain": compteurs.get(JAMAIS, 0) + compteurs.get(PASSAGE, 0),
        "sans_grain_etat_etabli": compteurs.get(JAMAIS, 0),
        "non_measurable": compteurs.get(NON_MESURABLE, 0),
        "candidats_sans_grain": sorted(
            e.numero for e in etats if e.etat in (JAMAIS, PASSAGE)),
        "etats": [{"numero": e.numero, "etat": e.etat} for e in etats],
    }


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--releve", required=True, help="releve groupe (JSON)")
    p.add_argument("--json", action="store_true")
    args = p.parse_args(argv)
    data = json.loads(Path(args.releve).read_text(encoding="utf-8"))
    rapport = classer_releve(data.get("rows") or [])
    if args.json:
        print(json.dumps(rapport, ensure_ascii=False, indent=2))
    else:
        print("issues: {} | {}".format(rapport["issues"], rapport["compteurs"]))
        print("sans grain (etat etabli): {} | non mesurable: {}".format(
            rapport["sans_grain_etat_etabli"], rapport["non_measurable"]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
