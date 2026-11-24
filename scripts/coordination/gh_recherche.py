#!/usr/bin/env python3
"""La RECHERCHE GitHub du tapis rapide : qui parle de ce numero (#26973).

Le depot ne declare pas ses enfants dans l'API GitHub (la sous-issues d'un
EPIC y est vide) : la filiation est une DECLARATION dans le corps de
l'issue. L'API de recherche est donc le seul moyen de trouver les enfants
d'un conteneur, FERMES compris -- c'est ce qui permet de dire « tous les
enfants sont fermes » plutot que « aucun enfant ouvert n'est visible ».

Ce module est le transport de cette lecture. Comme `gh_bulk`, il ne lance
aucun processus : il appelle le `run` injecte, et il rend une mesure
**annoncee** (complete ou non) pour que l'appelant puisse fail-OPEN.
"""
from __future__ import annotations

import json
from pathlib import Path

import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination.gh_bulk import LectureIncomplete, Run, _appel  # noqa: E402

TIMEOUT_S = 90
PAR_PAGE = 100


def chercher_enfants(run: Run, depot: str, numero: int,
                     max_pages: int = 3) -> tuple[list[dict], bool]:
    """Les issues qui mentionnent `numero`, et la completude de la mesure.

    La mesure est paginee : au-dela de `max_pages`, la completude est
    `False` et l'appelant doit fail-OPEN (un conteneur dont on n'a pas vu
    tous les enfants ne peut pas etre declare sature). Une panne transitoire
    rend la meme chose : une mesure incomplete ne prouve rien.
    """
    trouves: list[dict] = []
    total = 0
    for page in range(1, max_pages + 1):
        argv = ["gh", "api", f"search/issues?q=repo:{depot}+is:issue+{numero}"
                          f"&per_page={PAR_PAGE}&page={page}"]
        texte = _appel(run, argv, "enfants", page)
        if texte is None:
            return trouves, False
        try:
            donnees = json.loads(texte)
        except ValueError as exc:
            raise LectureIncomplete("enfants", page, f"reponse illisible : {exc}") from exc
        total = int(donnees.get("total_count") or 0)
        trouves += [{"number": it.get("number"), "state": (it.get("state") or "").lower(),
                     "body": it.get("body") or "", "pr": bool(it.get("pull_request"))}
                    for it in donnees.get("items") or []]
        if len(trouves) >= total:
            return trouves, True
    return trouves, len(trouves) >= total
