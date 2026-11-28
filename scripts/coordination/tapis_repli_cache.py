#!/usr/bin/env python3
"""Le CACHE LOCAL du repli : son fichier, sa lecture, ses metadonnees.

Extrait de `tapis_repli.py` le 24/11 : le repli a grandi (la **cause
nommee**, le grain de harnais) et le module passait son plafond de lignes.
Le cache est un tout : le chemin du fichier, sa lecture **meme perime**, et
la conversion en metadonnees -- il sort dans son propre module, comme
`tapis_leger_texte` pour `tapis_leger` (22/11).

Le cache peut etre **perime** : c'est la panne du reseau qui le rend seul
disponible, et un pool d'il y a quelques heures vaut mieux qu'un tirage
vide. Au-dela de `TTL_S`, il ne vaut plus rien : le repli rend alors
l'echec de lecture, comme avant.
"""
from __future__ import annotations

import json
import time
from pathlib import Path

#: Un cache de plus de sept jours ne vaut plus rien : le pool a trop change.
TTL_S = 7 * 24 * 3600


def chemin_cache(dossier: Path, jours: int) -> Path:
    """Le fichier de cache du tirage rapide : le meme nom, le meme dossier."""
    return dossier / f"lecture-{jours}j.json"


def lire(dossier: Path, jours: int, ttl_s: int = TTL_S) -> dict | None:
    """Le cache local, lu meme perime (c'est un repli), ou None.

    Un cache absent, illisible ou trop vieux rend None : l'appelant rend
    alors l'echec de lecture, comme avant.
    """
    try:
        brut = json.loads(chemin_cache(dossier, jours).read_text(encoding="utf-8"))
        age = time.time() - float(brut.get("_epoch", 0))
    except (OSError, ValueError, TypeError, AttributeError):
        return None
    return None if age > ttl_s else brut


def metas_de(cache: dict) -> list[dict]:
    """Les metadonnees du cache : la forme que rend `gh_selection.metadonnee`."""
    metas: list[dict] = []
    for it in cache.get("issues") or []:
        try:
            numero = int(it["number"])
        except (KeyError, TypeError, ValueError):
            continue
        metas.append({"number": numero, "title": it.get("title") or "",
                      "created_at": it.get("created_at") or "",
                      "updated_at": it.get("updated_at") or "",
                      "labels": [str(l) for l in (it.get("labels") or [])]})
    return metas


def citations_de(cache: dict) -> dict[int, list]:
    """Les citations du cache, indexees par numero d'issue.

    Une cle illisible est **ignoree** : le repli sert un pool degrade, pas un
    pool casse -- une citation perdue ne doit pas faire tomber le repli.
    """
    citations: dict[int, list] = {}
    for cle, valeur in (cache.get("citations") or {}).items():
        try:
            citations[int(cle)] = valeur
        except (TypeError, ValueError):
            continue
    return citations
