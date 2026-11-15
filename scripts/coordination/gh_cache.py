"""Le cache local du tapis rapide : une seule lecture reseau par machine (#22630).

Le cache de lecture (`%LOCALAPPDATA%/CoursIA/tapis_rapide/lecture-<N>j.json`) est
partage par machine : deux lanes qui tiraient au meme instant lisaient chacune le
reseau, et le credit gh etait paye deux fois pour le meme contenu.

Ce module porte le **protocole** de lecture unique (verrou, repli reseau,
deserialisation) ; le **fichier** lui-meme est dans `gh_cache_fichier.py`. Le
verrou vient de `gh_snapshot.lock_directory` (#22630) : un seul organe, deux
repertoires proteges (l'instantane du depot et le cache du tapis rapide).

Il n'est jamais bloquant -- au sens ou **un tirage n'est jamais empeche** : au
delai du verrou (120 s), la lecture part au reseau sans lui ; un verrou qui ne
peut pas etre cree (permissions, disque plein) part aussi au reseau ; un cache
frais mais de structure incorrecte est relu sur le reseau. Ces trois replis sont
distincts : une erreur **de la lecture reseau** elle-meme n'est jamais rejouee.
"""
from __future__ import annotations

from collections.abc import Callable
from contextlib import ExitStack, contextmanager
from pathlib import Path
from typing import Any

try:
    from .gh_cache_fichier import ecrire, frais
except ImportError:  # pragma: no cover - import direct, hors paquet
    from gh_cache_fichier import ecrire, frais


class TimeoutVerrou(TimeoutError):
    """Le verrou partage n'a pas ete obtenu dans le delai.

    Elle ne doit pas fuir vers l'appelant : le repli est la lecture reseau.
    """


#: Sentinelle : la deserialisation du cache a echoue (structure invalide).
_ABSENT = object()


@contextmanager
def verrou(dossier: Path, timeout: float = 120.0):
    """Le verrou de lecture partage, ou un no-op si l'organe est absent.

    Sans `gh_snapshot` (import impossible), la lecture se fait comme avant :
    un verrou ne doit jamais empecher un tirage.

    Un verrou qui ne peut pas etre **cree** (permissions, disque plein) est
    traite comme un verrou absent : seule l'**acquisition** est protegee (via
    `ExitStack`) -- une `OSError` venue de la lecture reseau, elle, se
    propage (elle ne doit pas etre rejouee).
    """
    try:
        from coordination import gh_snapshot
    except ImportError:
        yield None
        return
    with ExitStack() as pile:
        try:
            lock_path = pile.enter_context(gh_snapshot.lock_directory(dossier, timeout))
        except gh_snapshot.SnapshotLockTimeout as exc:
            raise TimeoutVerrou(str(exc)) from exc
        except OSError:
            # Repertoire de cache ou fichier de verrou non creat : la lecture
            # part au reseau SANS verrou.
            yield None
            return
        yield lock_path


def lire_unique(chemin: Path, cache_s: int, lecture_reseau: Callable[[], Any],
                depuis_cache: Callable[[dict], Any]) -> Any:
    """Une seule lecture reseau par machine et par instant (#22630).

    Le cache est relu **apres** avoir obtenu le verrou : si une autre lane a
    rafraichi pendant l'attente, cette passe ne consomme aucun credit gh. Au
    delai du verrou, la lecture se fait sans lui -- jamais de tirage bloque.

    Trois replis, distincts : un cache frais mais de **structure incorrecte**
    (la deserialisation leve) repart sur le reseau -- la deserialisation avait
    ete sortie du `try`, et un `{"_epoch": <maintenant>}` sans les champs
    attendus leveait une `KeyError` hors de tout traitement ; un verrou **non
    cree** ne bloque pas non plus ; le cache **desactive** (`cache_s <= 0`) ne
    prend **pas** le verrou.
    """
    def _lire_puis_ecrire() -> Any:
        lecture = lecture_reseau()
        if cache_s > 0:  # cache desactive : aucune trace sur le disque
            ecrire(chemin, lecture)
        return lecture

    def _cache_ou_repli(brut: dict) -> Any:
        """Le cache deserialise, ou `_ABSENT` s'il ne se laisse pas lire."""
        try:
            return depuis_cache(brut)
        except (KeyError, TypeError, ValueError, AttributeError):
            return _ABSENT

    brut = frais(chemin, cache_s)
    if brut is not None:
        valeur = _cache_ou_repli(brut)
        if valeur is not _ABSENT:
            return valeur

    if cache_s <= 0:
        # Cache desactive : ni lecture du cache, ni verrou (attendre un
        # verrou pour ne rien relire serait une attente pure).
        return _lire_puis_ecrire()

    try:
        with verrou(chemin.parent):
            brut = frais(chemin, cache_s)
            if brut is not None:
                valeur = _cache_ou_repli(brut)
                if valeur is not _ABSENT:
                    return valeur  # l'autre lane a rafraichi pendant l'attente
            return _lire_puis_ecrire()
    except TimeoutVerrou:
        return _lire_puis_ecrire()
