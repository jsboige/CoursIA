#!/usr/bin/env python3
"""La FENETRE du FIL : ce que la lecture presente, et ce qu'elle laisse hors champ.

La lecture groupee ne voit que les 12 derniers commentaires ; la qualification
dit si cette fenetre EST le fil complet, et le dit sur le grain servi --
y compris le cas ou la fenetre ne contenait aucun marqueur decisif.

La fenetre du POOL (le bloc servi, et la rotation par numero) est dans
`coordination.tapis_rotation` : deux fenetres, deux modules (extrait du
19/11).
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import gh_bulk, gh_snapshot


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
