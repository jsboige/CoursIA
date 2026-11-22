#!/usr/bin/env python3
"""La FENETRE du FIL : ce que la lecture presente, et ce qu'elle laisse hors champ.

La lecture groupee ne voit que les 12 derniers commentaires ; la qualification
dit si cette fenetre EST le fil complet, et le dit sur le grain servi -- y
compris le cas ou la fenetre ne contenait aucun marqueur decisif. La fenetre
du POOL (le bloc servi, et la rotation par numero) est dans
`coordination.tapis_rotation` : deux fenetres, deux modules (extrait du 19/11).
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import gh_bulk, gh_snapshot


def total_connus(it: dict | None) -> int | None:
    """Le nombre de commentaires de l'issue, ou None s'il est INCONNU.

    Fail-CLOSED (reserve Hermes, #27242) : un `comments_total` absent ou non
    entier ne vaut PAS 0 -- il vaut inconnu, et un inconnu ne s'acquitte pas."""
    if not it:
        return None
    total = it.get("comments_total")
    return total if isinstance(total, int) else None


def suffit(it: dict | None) -> bool:
    """La fenetre des 12 derniers commentaires est-elle le fil complet ?

    Vrai quand l'issue porte moins de 12 commentaires : la lecture groupee a
    alors deja tout lu. Faux quand le total est INCONNU : une fenetre dont on
    ignore la taille ne peut pas etre declaree « le fil complet ».
    """
    total = total_connus(it)
    if total is None:
        return False
    return total <= len(it.get("comments") or [])


def noter(e, it: dict | None) -> None:
    """Publie ce que la fenetre a decide, et ce qu'elle a laisse hors champ."""
    it = it or {}
    lus = len(it.get("comments") or [])
    total = total_connus(it)
    if total is None:
        e.notes.append(f"total des commentaires inconnu ({lus} lu(s)) : "
                       "la fenetre n'est pas declaree fil complet")
    elif total <= lus:
        e.notes.append(f"fenetre = fil complet ({lus} commentaire(s))")
    else:
        # La relecture elle-meme est notee ailleurs : on dit ce que la
        # FENETRE avait laisse hors champ.
        e.notes.append(f"fenetre de {lus} commentaires sur {total} : "
                       "aucun marqueur decisif hors fenetre")


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
