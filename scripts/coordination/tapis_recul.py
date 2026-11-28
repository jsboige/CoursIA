#!/usr/bin/env python3
"""Le recul du tapis : les ecarts servis en second temps (#22983, #27059).

Le tapis ne refuse jamais : les ecarts COUVERTE, RELACHEE et MERGEE ne
jettent pas l'issue du pool, ils la servent APRES les autres -- un grain
libre passe toujours devant, et le recul a son palier apres le tour, jamais
devant les issues libres. Un ecart dur (GEL, PAUSE, PLAFOND, ...) l'emporte
toujours sur un recul, et un claim vivant d'une autre lane verrouille aussi
une issue en recul.

Extrait de `tapis_rapide.py` pour tenir son plafond de lignes au moment ou
la fusion avec main y ajoute les ecarts de fond et la pause -- le meme geste
que `tapis_attente.py` (#27726). Fonctions pures sur `Etat` ; aucun
processus lance.
"""
from __future__ import annotations

from typing import TYPE_CHECKING

from coordination import tapis_equilibre

if TYPE_CHECKING:
    from datetime import datetime

    from coordination.tapis_rapide import Etat

# Mesure du 17/11 07:33Z, lane po-2028:CoursIA : 16 servables sur 400 lues,
# dont 11 conteneurs ; COUVERTE 41, RELACHEE 47, MERGEE 79 ecartees.
RECULS = frozenset({"COUVERTE", "RELACHEE", "MERGEE"})


def servable(e: Etat) -> bool:
    """Servie si aucun ecart, ou un ecart de recul (servie apres les autres)."""
    return e.ecart is None or e.ecart in RECULS


def _servable(e: Etat) -> bool:
    """Une issue que le tapis peut servir.

    Le #27059 elargit cette notion aux ecarts de recul (COUVERTE, RELACHEE,
    MERGEE) : quand sa definition est presente, on la suit, sinon celle
    d'avant (aucun ecart dur) -- sans quoi `ordonner` ecarterait du tour des
    issues que le tirage du #27059 entend servir."""
    f = globals().get("servable")
    return f(e) if f is not None else e.ecart is None


def lignes_recul(recul: dict | None) -> list[str]:
    """La ligne de sortie texte : combien d'issues servies en recul, par code.

    Ecrite ici, dans le module qui decide du recul (le rendu ne fait que
    l'ajouter a ses lignes) -- meme geste que `tapis_sature.lignes_urne`.
    """
    if not recul:
        return []
    return ["Servies en recul, apres les autres : " + ", ".join(
        f"{code} {len(v)}" for code, v in recul.items())]


def _palier_recul(etats_: list[Etat], file: list[Etat], pris: set[int],
                  reportes: list[Etat], quota: int, grains: int, graine: str,
                  maintenant: datetime) -> None:
    """Les issues en recul (RECULS), apres le tour (#27059) ; un grain passe devant un
    conteneur hors quota (#26926), une issue deja visitee jamais devant un reporte (#27590)."""
    en_recul = [e for e in etats_ if e.ecart in RECULS]
    recul_file = sorted((e for e in en_recul if e.mon_claim),
                        key=lambda e: (e.cree_le, e.numero))
    recul_file += tapis_equilibre.ordre(
        etats_, [e for e in en_recul if not e.mon_claim], graine, maintenant)
    attente = {e.numero for e in reportes if not tapis_equilibre.est_marathon(e)}
    for e in recul_file:
        if len(file) >= grains:
            break
        if e.visites > 0 and attente:
            continue
        if e.conteneur and quota <= 0:
            continue
        quota -= e.conteneur
        file.append(e)
        pris.add(e.numero)
