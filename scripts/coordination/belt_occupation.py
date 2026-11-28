#!/usr/bin/env python3
"""L'OCCUPATION d'un grain : une PR OUVERTE d'une autre lane le porte deja (27/11).

Le tirage central a servi des grains **deja en vol** -- mesure du coordinateur
(cycle c0166) : sur 37 grains dispatches, 29 avaient une PR ouverte, dont 24
portees par une AUTRE lane. Les lanes recevaient du travail porte ailleurs, et
rendaient « deja livre » ou rien.

``record`` (``belt_queues.py``) refuse donc un grain qu'une PR ouverte d'une
autre lane traite, comme il refuse un grain ``delivered``. Trois limites,
nommees :

- un **conteneur** (EPIC, umbrella) n'est pas refuse : ses filles se livrent
  par des PRs qui le citent (`Part of #N`) -- c'est sa facon ordinaire d'etre
  servi, chaque lane sur son sous-grain ;
- la PR de la **lane servie elle-meme** n'est pas un refus : elle continue son
  travail (5 des 29 PRs de la mesure), meme si une autre lane porte aussi le
  grain -- une consolidation se sert a plusieurs (#20298, trois lanes) ;
- une PR **sans tag ``Grain:``** n'est attribuee a aucune lane : rien ne prouve
  qu'elle n'est pas celle d'une autre lane -- le grain est refuse, et le motif
  nomme la PR.

Une lecture des PRs ouvertes **impossible** n'est pas un ensemble vide : c'est
une absence de mesure, dite et ecrite dans la repartition, et le refus ne
s'applique pas.

C'est, cote distribution, la regle ``COUVERTE`` du tapis rapide (hors
conteneur, une PR ouverte qui cite l'issue ecarte le grain) --
docs/reference/tapis-rapide.md, « Ce qui ecarte un candidat ». Mesure du
27/11 sur les PRs ouvertes : 299 lues, 50 sans tag ``Grain:``.
"""
from __future__ import annotations

from collections.abc import Callable


def index_par_issue(prs: list[dict], lane_de: Callable[[dict], str | None],
                    issues_de: Callable[[dict], set[int]],
                    ) -> dict[int, dict[str | None, list[int]]]:
    """Les PRs ouvertes qui traitent chaque issue, par lane porteuse.

    ``lane_de`` et ``issues_de`` sont les lecteurs de ``belt_queues`` (une
    seule definition de chacun) : ce module ne l'importe pas, pour rester
    importable de lui. Une PR sans tag figure sous la cle ``None``.
    """
    index: dict[int, dict[str | None, list[int]]] = {}
    for pr in prs:
        lane = lane_de(pr)
        numero = int(pr.get("number") or 0)
        for n in issues_de(pr):
            index.setdefault(n, {}).setdefault(lane, []).append(numero)
    return index


def est_conteneur(grain: dict) -> bool:
    """Un conteneur (EPIC, umbrella), aux deux formes de tirage."""
    return bool(grain.get("conteneur")) or grain.get("klass") == "umbrella"


def refus(numero: int, lane: str, grain: dict,
          index: dict[int, dict[str | None, list[int]]]) -> str | None:
    """Le motif du refus, ou ``None`` quand le grain peut entrer dans la file."""
    if est_conteneur(grain):
        return None
    porteuses = index.get(numero) or {}
    if lane in porteuses:
        # La lane porte deja le grain : elle continue son travail, qu'une autre
        # lane le porte aussi ou non (une consolidation se sert a plusieurs --
        # #20298, trois lanes, mesure du 27/11).
        return None
    if not porteuses:
        return None
    qui = ", ".join(
        f"{'sans tag `Grain:`' if porteuse is None else porteuse} "
        f"(PR {', '.join(f'#{p}' for p in sorted(prs))})"
        for porteuse, prs in sorted(porteuses.items(), key=lambda kv: str(kv[0])))
    return (f"#{numero} est deja porte par une PR ouverte d'une autre lane : "
            f"{qui} -- le grain est en vol, il n'entre pas dans la file {lane}")
