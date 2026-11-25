#!/usr/bin/env python3
"""Les deux ECARTEURS DE FOND du tirage (#27179, #26973).

Extraits de `tapis_rapide.py` pour tenir le plafond de lignes de ce module :
un depassement se paie en extrayant un module, pas en relevant le plafond.

1. la **re-decision** (#27179) : un grain servi au fil tronque se re-decide sur
   son fil complet ; hors ligne ou cache, la fenetre reste la fenetre ;
2. l'**ecart de saturation** (#26973) : les conteneurs dont tous les enfants
   sont fermes sortent de la file, et le tirage est refait pour les remplacer
   par un grain reel. La mesure porte sur les seuls conteneurs de la file, et
   elle est fail-OPEN : une panne n'ecarte rien. Un rejeu `--lecture` est hors
   ligne : rien n'est mesure, rien n'est ecarte.

**ORDRE** : la re-decision passe AVANT la saturation. Les deux marquent le
meme objet (`e.ecart`) et la saturation est la seule des deux a ne JAMAIS
effacer une marque etrangere : la re-decision, elle, RECALCULE `e.ecart`
depuis le fil complet -- appliquee apres, elle pourrait rendre servable un
conteneur qui vient d'etre mesure sature. Dans cet ordre les deux exclusions
subsistent : `ordonner` ne garde que les items dont `e.ecart is None`.
"""
from coordination import gh_bulk, gh_recherche, tapis_sature


def ecarts_de_fond(tous: list, file: list, args, lecture, run, maintenant,
                   graine: str, lire_fils, reordonner) -> tuple[list, dict | None]:
    """Les deux ecarteurs de FOND, dans l'ordre qui les rend cumulatifs.

    `reordonner` est le rappel qui refait le classement : il est fourni par
    l'appelant, qui porte `ordonner`.
    """
    reverif = None
    if not args.lecture and not lecture.depuis_cache:
        from coordination import tapis_reverif
        file, reverif = tapis_reverif.passer(
            tous, file, args.grains, args.lane, maintenant, args.jours, graine,
            lecture, lire_fils)
    if not args.lecture:
        file = tapis_sature.ecarter_satures(
            tous, file,
            lambda n: gh_recherche.chercher_enfants(run, gh_bulk.DEPOT_GH, n),
            reordonner)
    return file, reverif
