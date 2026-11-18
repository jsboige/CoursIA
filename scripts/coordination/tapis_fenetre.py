#!/usr/bin/env python3
"""La FENETRE du tapis : celle du pool classe, et celle du fil.

Deux fenetres, un seul module -- la fenetre est la meme notion des deux
cotes : ce que la lecture presente, et ce qu'elle laisse hors champ.

**La fenetre du POOL** (`bloc`) : le bloc servi. Le CLASSEMENT reste l'ordre
(les issues jamais visitees d'abord, puis les plus anciennes) ; c'est la
FENETRE qui avance -- un bloc CONTIGU par tranche de 4 h, decale par lane.
Sans elle, la tete du classement reste figee et la liste `3 x grains` ecrase
les issues jamais visitees : mesure du 18/11 (pool de 441 issues), **38
issues couvertes sur 12 tours**, dont **114 jamais visitees hors de portee**
et une tete toujours la meme. Avec elle, un tour complet du pool tient en
`ceil(pool / taille)` tranches, et les blocs d'un tour sont disjoints : toute
issue est proposee une fois avant qu'une autre le soit deux fois.

**La fenetre du FIL** (`suffit`, `noter`) : la lecture groupee ne voit que
les 12 derniers commentaires ; la qualification dit si cette fenetre EST le
fil complet, et le dit sur le grain servi -- y compris le cas ou la fenetre
ne contenait aucun marqueur decisif.
"""
from __future__ import annotations

import hashlib
import sys
from datetime import datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import gh_bulk, gh_snapshot
from coordination.tapis_rapide import PART_CONTENEURS

#: Tranches de 4 h par jour : la fenetre avance d'un bloc par tranche.
TRANCHES_JOUR = 6


def _compteur(maintenant: datetime) -> int:
    """Un compteur monotone de tranches de 4 h -- la fenetre avance avec."""
    return maintenant.toordinal() * TRANCHES_JOUR + maintenant.hour // 4


def _decalage(lane: str, cle: str, n: int) -> int:
    """Le decalage de la lane sur une liste : deux lanes ne balayent pas le
    meme bloc."""
    if n <= 0:
        return 0
    return int(hashlib.sha256(f"{lane}|{cle}".encode("utf-8")).hexdigest(), 16) % n


def bloc(grains: list, conteneurs: list, n_grains: int, taille: int, lane: str,
         maintenant: datetime, bloc_suivant: int = 0) -> tuple[list, dict]:
    """Le bloc servi : la fenetre qui avance sur le pool classe.

    Les GRAINS et les CONTENEURS ont chacun leur tranche et leur bloc : un
    conteneur ne passe jamais devant un grain (#26926), et son quota tient
    dans la file comme dans la voie lourde.

    `bloc_suivant` decale le bloc de N blocs : c'est la VAGUE suivante de la
    prise en charge -- le bloc suivant dans le meme ordre classe, donc
    toujours dans la fenetre de la lane.
    """
    quota = max(1, int(n_grains * PART_CONTENEURS)) if conteneurs else 0
    part = max(taille - quota, 1)
    n_g, n_c = len(grains), len(conteneurs)
    compteur = _compteur(maintenant) + bloc_suivant
    d_g = (_decalage(lane, "grains", n_g) + compteur * part) % n_g if n_g else 0
    d_c = (_decalage(lane, "conteneurs", n_c) + compteur * quota) % n_c if n_c else 0
    b_g = [grains[(d_g + i) % n_g] for i in range(min(part, n_g))]
    b_c = [conteneurs[(d_c + i) % n_c] for i in range(min(quota, n_c))]
    return b_g + b_c, {
        "taille": taille, "grains": len(b_g), "conteneurs": len(b_c),
        "bloc": (d_g // part) + 1 if n_g else 0,
        "blocs": (n_g + part - 1) // part if n_g else 1,
        "pool": n_g, "tranche": compteur}


def suffit(it: dict | None) -> bool:
    """La fenetre des 12 derniers commentaires est-elle le fil complet ?

    Vrai quand l'issue porte moins de 12 commentaires : la lecture groupee
    a alors deja tout lu, et le fil complet n'est pas relu.
    """
    if not it:
        return True
    return (it.get("comments_total") or 0) <= len(it.get("comments") or [])


def noter(e, it: dict | None) -> None:
    """Publie ce que la fenetre a decide, et ce qu'elle a laisse hors champ.

    Trois cas nommes : la fenetre EST le fil complet ; le fil complet a ete
    relu et aucun marqueur decisif n'y etait ; l'ecart porte son code et son
    motif.
    """
    it = it or {}
    lus, total = len(it.get("comments") or []), it.get("comments_total") or 0
    if total <= lus:
        e.notes.append(f"fenetre = fil complet ({lus} commentaire(s))")
    else:
        # La relecture elle-meme est deja notee par l'organe de re-verification
        # (« fil complet relu (N commentaires) ») : on ne la repete pas, on dit
        # ce que la FENETRE avait laisse hors champ.
        e.notes.append(f"fenetre de {lus} commentaires sur {total} : "
                       f"aucun marqueur decisif hors fenetre")


def fil_complet(numero: int, repo: str = gh_bulk.DEPOT_GH) -> list[dict]:
    """Le FIL COMPLET d'une issue, dans la forme des marqueurs.

    L'organe `gh_snapshot` pagine en REST : c'est le **fil complet**, pas la
    fenetre des 12 derniers commentaires de la lecture groupee -- le marqueur
    qui ecarte un grain peut etre plus ancien que la fenetre (#27179).
    """
    return [{"created_at": c.get("createdAt") or "",
             "author": (c.get("author") or {}).get("login") or "",
             "body": c.get("body") or ""}
            for c in gh_snapshot.fetch_issue_comments(repo, numero)]
