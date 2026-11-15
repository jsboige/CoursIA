"""Le fichier de cache du tapis rapide : lire si frais, ecrire sans deque.

Seam d'extraction (#22630, 14/11) : `gh_cache.py` porte le **protocole** de
lecture unique (verrou, repli reseau, deserialisation) ; ce module porte le
**fichier** -- le lire quand il est frais, l'ecrire de facon atomique. Un
plafond de lignes se paie par une extraction, pas par un plafond releve
(: `scripts/tests/test_tapis_rapide.py`).
"""
from __future__ import annotations

import json
import os
import tempfile
import time
from dataclasses import asdict
from pathlib import Path
from typing import Any


def frais(chemin: Path, cache_s: int) -> dict | None:
    """Le contenu du cache s'il est plus jeune que `cache_s` secondes, sinon None.

    Un cache absent, illisible ou perime rend None : la lecture se fait sur le
    reseau.
    """
    if cache_s <= 0:
        return None
    try:
        brut = json.loads(chemin.read_text(encoding="utf-8"))
        if time.time() - float(brut.pop("_epoch")) < cache_s:
            return brut
    except (OSError, ValueError, KeyError, TypeError, AttributeError):
        pass  # cache absent ou illisible : relu sur le reseau
    return None


def ecrire(chemin: Path, lecture: Any) -> None:
    """Ecrit le cache de facon atomique (jamais un cache a moitie ecrit).

    Un cache non ecrit ne change pas le tirage : l'echec est ignore.
    """
    try:
        chemin.parent.mkdir(parents=True, exist_ok=True)
        fd, tmp = tempfile.mkstemp(dir=chemin.parent, suffix=".tmp")
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            json.dump({**asdict(lecture), "_epoch": time.time()}, fh, ensure_ascii=False)
        os.replace(tmp, chemin)
    except (OSError, TypeError, ValueError):
        pass
