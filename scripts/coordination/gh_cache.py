"""Le cache local du tapis rapide : une seule lecture reseau par machine (#22630).

Le cache de lecture (`%LOCALAPPDATA%/CoursIA/tapis_rapide/lecture-<N>j.json`) est
partage par machine : deux lanes qui tirent AU MEME MOMENT lisaient chacune le
reseau, et le credit gh etait paye deux fois pour le meme contenu.

Ce module porte la machinerie du cache et du verrou ; `gh_bulk` garde les
lectures. Le verrou vient de `gh_snapshot.lock_directory` (#22630) : un seul
organe, deux repertoires proteges (l'instantane du depot et le cache du tapis
rapide). Il n'est jamais bloquant -- au delai, la lecture part au reseau sans
lui : un verrou ne doit jamais empecher un tirage.
"""
from __future__ import annotations

import json
import os
import tempfile
import time
from collections.abc import Callable
from contextlib import contextmanager
from dataclasses import asdict
from pathlib import Path
from typing import Any


class TimeoutVerrou(TimeoutError):
    """Le verrou partage n'a pas ete obtenu dans le delai.

    Elle ne doit pas fuir vers l'appelant : le repli est la lecture reseau.
    """


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


@contextmanager
def verrou(dossier: Path, timeout: float = 120.0):
    """Le verrou de lecture partage, ou un no-op si l'organe est absent.

    Sans `gh_snapshot` (import impossible), la lecture se fait comme avant :
    un verrou ne doit jamais empecher un tirage.
    """
    try:
        from coordination import gh_snapshot
    except ImportError:
        yield None
        return
    try:
        with gh_snapshot.lock_directory(dossier, timeout) as lock_path:
            yield lock_path
    except gh_snapshot.SnapshotLockTimeout as exc:
        raise TimeoutVerrou(str(exc)) from exc


def lire_unique(chemin: Path, cache_s: int, lecture_reseau: Callable[[], Any],
                depuis_cache: Callable[[dict], Any]) -> Any:
    """Une seule lecture reseau par machine et par instant (#22630).

    Le cache est relu **apres** avoir obtenu le verrou : si une autre lane a
    rafraichi pendant l'attente, cette passe ne consomme aucun credit gh. Au
    delai du verrou, la lecture se fait sans lui -- jamais de tirage bloque.
    """
    brut = frais(chemin, cache_s)
    if brut is not None:
        return depuis_cache(brut)

    def _lire_puis_ecrire() -> Any:
        lecture = lecture_reseau()
        if cache_s > 0:  # cache desactive : aucune trace sur le disque
            ecrire(chemin, lecture)
        return lecture

    try:
        with verrou(chemin.parent):
            brut = frais(chemin, cache_s)
            if brut is not None:
                return depuis_cache(brut)  # l'autre lane a rafraichi pendant l'attente
            return _lire_puis_ecrire()
    except TimeoutVerrou:
        return _lire_puis_ecrire()
