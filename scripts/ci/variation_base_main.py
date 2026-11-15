#!/usr/bin/env python3
"""Filtre ``--base main`` partage par les organes G-VAR-2/3 (#18940).

Pourquoi ce module
------------------
Les organes G-VAR-2 (variation_light_cap.py) et G-VAR-3
(variation_adjacency_guard.py) consomment la liste des PRs mergees dans la
journee pour calculer le budget LIGHT d'une lane et son adjacent precedent.
Cette liste provient d'un appel :

    gh pr list --state merged --search "merged:$TODAY" --limit 500 \
        --json number,body,mergedAt,labels[,files]

**Defaut structurel mesure** : l'appel rend TOUTES les PRs mergees dans la
journee, y compris celles empilees sur une branche de feature puis mergees
dans cette branche avant d'etre empilees sur `main`. Une PR empilee a une
``baseRefName != "main"`` : elle n'est pas encore visible sur la branche
par defaut, donc elle ne pese pas dans le budget G-VAR de la lane et ne peut
pas compter comme ``prev:`` d'une PR ulterieure.

**Controle positif (#18910)** : PR empilee sur ``test/18775-k07-budget-mensuel``,
mergee 2026-10-02T01:39Z, apparaissait comme ``prev_pr`` de #18822 -- faux
adjacent declenche par l'absence de filtre.

API
---
``filter_base_main(merged_prs, *, warn=print)`` prend la liste brute retournee
par ``gh pr list`` et renvoie la liste filtree (les entrees sans ``baseRefName``
sont preservees pour la retrocompatibilite -- avant le fix, le champ etait
absent du JSON ; un fichier historique reste exploitable tel quel).

Le module est volontairement pur (zello, sans argparse, sans reseau) : il est
importe par les 2 organes et exerce par ``scripts/tests/test_variation_base_main.py``.

Convention de sortie
--------------------
Une PR est conservee si :
  - ``baseRefName`` est absent (retrocompat) ; OU
  - ``baseRefName == "main"``.

Une PR est filtree si :
  - ``baseRefName`` est present et different de ``"main"`` (PR empilee).

Une PR sans ``baseRefName`` **et** sans aucun autre champ de la triplette
``number/body/mergedAt`` est preservee avec un ``warn`` (donnees partielles
non filtree) -- le detecteur aval decide de son traitement.
"""
from __future__ import annotations

from typing import Callable

# Nom canonique de la branche par defaut. Le module est strict : un PR
# empilee sur une branche de release (``release/1.0``) ou un fork n'est PAS
# comptabilisee dans le budget G-VAR de la lane.
MAIN_BRANCH = "main"


def filter_base_main(
    merged_prs: list[dict],
    *,
    warn: Callable[[str], None] = print,
) -> list[dict]:
    """Filtre les PRs dont ``baseRefName`` est connu et different de ``main``.

    Les PRs sans champ ``baseRefName`` (donnees historiques ou producers
    anterieurs au fix) sont preservees : la retrocompatibilite du consumer
    prevaut sur la purete. Un producer qui omettait ``baseRefName`` par
    accident **aujourd'hui** serait silencieux, mais aucun des 4 sites
    concernes ne le fait -- le champ est ajoute au `--json` au commit de
    la PR #18940.

    Parameters
    ----------
    merged_prs:
        Liste brute retournee par ``gh pr list --state merged --json
        number,body,mergedAt,labels,files,baseRefName`` (ou une version
        anterieure sans ``baseRefName``).
    warn:
        Sink pour les messages d'information (par defaut ``print`` sur
        stdout). Les organes passent typiquement ``sys.stderr.write``.

    Returns
    -------
    list[dict]
        Nouvelle liste, sans les PRs empilees. L'ordre est preserve.
    """
    if not isinstance(merged_prs, list):
        raise TypeError(
            f"filter_base_main attend une liste, reçu {type(merged_prs).__name__}"
        )

    kept: list[dict] = []
    dropped = 0
    for pr in merged_prs:
        if not isinstance(pr, dict):
            # Une entree non-dict est une corruption ; on preserve pour ne pas
            # perdre silencieusement un grain et on signale.
            warn(f"variation_base_main: entrée non-dict ignorée: {pr!r}")
            kept.append(pr)
            continue
        base = pr.get("baseRefName")
        if base is None:
            # Retrocompat : producteur historique sans baseRefName.
            kept.append(pr)
            continue
        if base == MAIN_BRANCH:
            kept.append(pr)
        else:
            dropped += 1
    if dropped:
        warn(
            f"variation_base_main: {dropped} PR(s) empilée(s) filtrée(s) "
            f"(baseRefName != {MAIN_BRANCH!r})"
        )
    return kept


__all__ = ["filter_base_main", "MAIN_BRANCH"]
