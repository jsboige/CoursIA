#!/usr/bin/env python3
"""Les citations des PRs OUVERTES : le travail EN COURS compte comme une visite.

Le classement leger ne voyait que les commits **merges** (`gh_bulk`) : une
issue sur laquelle huit PRs sont ouvertes, mais pas encore mergees, restait a
`visites = 0` -- donc en tete de rotation. Le tapis la resservait alors que le
travail etait deja fait (famine du 19/11/2026).

La regle de citation est celle du chemin des commits merges : une mention
`#N` dans le corps. La date retenue est la **derniere activite** de la PR
(`updated_at`) : une PR ouverte mais abandonnee depuis trois mois ne doit pas
tenir une issue en tete de rotation.
"""
from __future__ import annotations

import re

_CITE_RE = re.compile(r"#(\d+)\b")


def des_prs_ouvertes(prs: list[dict]) -> dict[int, list[dict]]:
    """Les issues citees par les PRs ouvertes, au format des citations de commits.

    L'auto-reference est exclue : une PR ne se cite pas elle-meme.
    """
    cites: dict[int, list[dict]] = {}
    for pr in prs:
        numero = int(pr.get("number") or 0)
        corps = pr.get("body") or ""
        date = pr.get("updated_at") or pr.get("created_at") or ""
        for n in sorted({int(x) for x in _CITE_RE.findall(corps)} - {numero}):
            cites.setdefault(n, []).append(
                {"sha": "pr" + str(numero), "date": date,
                 "sujet": pr.get("title") or "", "ferme": False,
                 "ouvert": True})
    return cites
