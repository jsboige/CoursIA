"""Reprise bornee sur pression de fork (EAGAIN) -- primitive partagee par les gardes.

Origine -- la vague de rouges du 2026-09-14. `f149f2fe93` (mergee sur `main` le
2026-09-13T23:08:17Z, #15833 sur #14598) a fait passer `Scripts Tests (CPU)` a
`pytest-xdist -n 4 --dist loadscope`. Quatre workers executant en parallele des
gardes qui forkent `git` saturent la table de processus du runner : le spawn
suivant est refuse avec `BlockingIOError: [Errno 11]` -- `EAGAIN`.

`EAGAIN` est transitoire PAR DEFINITION : le noyau refuse *un processus de plus*,
il ne signale pas une panne. Echouer au premier refus convertit un pic de charge
en rouge de base.

Trois gardes ont recu cette reprise separement -- `check_twin_parity` (#16125),
`check_kernel_suffix_canon` et `check_exec_ratchet` (#16157) : meme boucle, meme
backoff, meme filtre d'errno, trois ecritures. Ce module est l'ecriture unique,
sur le modele de `naming_canon.py` (#15503) : meme classe de probleme -- une
primitive redefinie par plusieurs organes -- et donc meme reponse.

PORTEE -- ce que ce module fait, et ce qu'il ne fait pas
--------------------------------------------------------
Il rend un echec de spawn TRANSITOIRE surmontable. Il ne reduit PAS la pression
de fork : le fan-out des gardes reste le meme, et le reduire (un
`git cat-file --batch` en flux plutot que N forks) est un axe distinct, laisse
ouvert par #16111 faute d'instrumentation du runner.

Il ne decide pas non plus de ce qu'un garde fait quand la reprise est epuisee.
La derniere `OSError` REMONTE, et chaque garde garde sa politique par-dessus :
`check_slot_reservation` la laisse remonter (fail-closed), `check_exec_ratchet`
et `check_source_output_ratchet` l'enveloppent en `None` (fail-open -- arbitrage
en cours dans #16164). Mutualiser la reprise ne doit pas uniformiser la
semantique de sortie en passant : ces deux politiques repondent a des questions
differentes, et le choix appartient a chaque garde.

Le filtre est ETROIT, et c'est le point qui compte : seuls `EAGAIN` et
`EWOULDBLOCK` sont retentes ; toute autre `OSError` remonte au premier appel.
Sans cela, une panne permanente -- git absent, `ENOENT` -- deviendrait trois
essais silencieux, et le remede serait pire que le mal.
"""
from __future__ import annotations

import errno
import subprocess
import time

# `EWOULDBLOCK` est un alias d'`EAGAIN` sous Linux ; il peut differer ailleurs.
FORK_PRESSURE_ERRNOS = (errno.EAGAIN, getattr(errno, "EWOULDBLOCK", errno.EAGAIN))

ATTEMPTS = 3
BACKOFF = (0.05, 0.15)  # avant les 2e et 3e tentatives


def is_fork_pressure(exc: BaseException) -> bool:
    """Vrai pour un refus de spawn transitoire, et pour rien d'autre."""
    return isinstance(exc, OSError) and exc.errno in FORK_PRESSURE_ERRNOS


def run_with_fork_retry(args, **kwargs) -> subprocess.CompletedProcess:
    """`subprocess.run(args, **kwargs)`, retente de facon bornee sur EAGAIN.

    Les `kwargs` sont transmis VERBATIM : ce module ne prend aucune position sur
    le mode texte, l'encodage, `cwd`, `env` ou `check`. Un garde qui lit du
    binaire (`text=False`, sans `encoding=`) et un garde qui lit de l'utf-8
    passent par la meme porte sans que l'un impose sa forme a l'autre -- c'est
    la condition pour que la mutualisation n'introduise aucun changement de
    comportement hors pression de fork.

    Rend le `CompletedProcess` du premier spawn qui aboutit. A l'epuisement des
    tentatives, remonte la derniere `OSError` de pression de fork.
    """
    derniere: OSError | None = None
    for tentative in range(ATTEMPTS):
        if tentative:
            time.sleep(BACKOFF[tentative - 1])
        try:
            return subprocess.run(args, **kwargs)
        except OSError as exc:
            if not is_fork_pressure(exc):
                raise
            derniere = exc
    raise derniere  # `ATTEMPTS >= 1` garantit que `derniere` est renseignee
