#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Nombre de workers xdist borne par le plafond memoire du cgroup (#21802).

La jambe `tests/ (58)` de `ict-tests.yml` lancait `-n 4` workers quel que soit
le runner qui la recoit. Elle porte les memes etiquettes que `Scripts Tests
(CPU)` (`self-hosted, coursia-ephemeral, coursia-linux`), donc elle peut
atterrir sur les slots persistants plafonnes a 1,5 Gio
(`docker run --memory=1610612736`), ou quatre workers ont ete tues par le
cgroup : `dmesg` porte `Memory cgroup out of memory: Killed process (python)`
a `CONSTRAINT_MEMCG`, et le job sortait en 137.

La regle : le nombre de workers se calcule a l'execution d'apres la limite
memoire lue dans le cgroup du conteneur, divisee par le **budget memoire
mesure** d'un worker. Sans plafond lisible (`max`, fichier absent, cgroup v1
"illimite"), on retombe sur la valeur nominale.

Le budget n'est pas pose au jugement : c'est le RSS de pointe mesure sur la
suite reelle du job (voir `RSS_BUDGET_PAR_WORKER_MIB`).

Perimetre : cet organe sert la suite ICT. Le nombre de workers de la suite
`scripts` est borne dans son propre workflow, ou la regle est un worker par
Gio entier de plafond (#21554) ; les deux suites n'ont pas le meme profil
memoire, et les melanger ferait porter a l'une la calibration de l'autre.

Ce module est l'organe natif du calcul : il est appele par le workflow et
couvert par les tests dans `scripts/tests/test_cgroup_worker_budget.py`.
"""

from __future__ import annotations

import sys
from pathlib import Path

# Valeur nominale : celle des slots sans plafond lisible.
DEFAULT_WORKERS = 4
# Plafond haut : la suite ne gagne rien au-dela (le chemin critique est un
# module unique sous `--dist loadscope`).
MAX_WORKERS = 4

# Suite ICT (`ict/tests/`, job `ICT tests/ (58)`) : budget MESURE le 2026-10-21
# sur ai-01 (echantillonnage de l'arbre de processus toutes les 0,5 s,
# `-n 4 --dist loadscope`, 292 s, meme chemin de tests que le job) :
#   - pic de l'arbre complet (4 workers + master) : 2 182,6 MiB a 155 s
#   - pic du master xdist                       :     54,8 MiB
#   - pic du worker le plus lourd               : 1 181,4 MiB
# Le budget retenu est le **worker le plus lourd** (1 181 MiB), et non la
# moyenne par worker (545,7 MiB) : sous `--dist loadscope` un module lourd
# reste epingle a un worker, donc le conteneur doit pouvoir tenir ce worker
# la charge, pas sa moyenne. Avec la moyenne, un conteneur a 1,5 Gio aurait
# recu 2 workers pour une charge reelle de 1 181 + 326 + 55 = 1 561 MiB --
# au-dela du plafond : le kill par cgroup qu'on cherche a eviter.
RSS_BUDGET_PAR_WORKER_MIB = 1181

# RSS de pointe du master xdist (processus pytest de l'etat), reserve en plus
# du budget des workers : le plafond doit couvrir le master ET les workers.
RSS_RESERVE_MASTER_MIB = 256

CGROUP_ROOT = Path("/sys/fs/cgroup")

# cgroup v1 : la valeur "illimite" est un entier enorme (2^63 ou plus).
_V1_UNLIMITED_FLOOR = 1 << 62


def read_memory_limit_bytes(root: Path = CGROUP_ROOT) -> int | None:
    """Limite memoire du cgroup courant, en octets.

    cgroup v2 : `<root>/memory.max` (la valeur litterale `max` = pas de
    plafond). cgroup v1 : `<root>/memory/memory.limit_in_bytes`.

    Renvoie None si la limite est absente, illisible ou illimite -- l'appelant
    retombe alors sur la valeur nominale.
    """
    v2 = root / "memory.max"
    if v2.is_file():
        try:
            raw = v2.read_text(encoding="utf-8").strip()
        except OSError:
            raw = ""
        if raw and raw != "max":
            try:
                return int(raw)
            except ValueError:
                pass

    v1 = root / "memory" / "memory.limit_in_bytes"
    if v1.is_file():
        try:
            raw = v1.read_text(encoding="utf-8").strip()
        except OSError:
            return None
        try:
            value = int(raw)
        except ValueError:
            return None
        if value <= 0 or value >= _V1_UNLIMITED_FLOOR:
            return None
        return value

    return None


def compute_workers(
    limit_bytes: int | None,
    budget_mib: int = RSS_BUDGET_PAR_WORKER_MIB,
    reserve_mib: int = RSS_RESERVE_MASTER_MIB,
    maximum: int = MAX_WORKERS,
    default: int = DEFAULT_WORKERS,
) -> int:
    """Nombre de workers xdist permis par une limite memoire donnee.

    `limit_bytes` : plafond du cgroup en octets, ou None (absent ou
    illimite) -- auquel cas `default` est rendu.
    """
    if limit_bytes is None:
        return default
    limit_mib = limit_bytes / (1024 * 1024)
    usable = limit_mib - reserve_mib
    if usable <= 0:
        return 1
    workers = int(usable // max(1, budget_mib))
    if workers < 1:
        return 1
    return min(workers, maximum)


def describe(limit_bytes: int | None) -> str:
    """Phrase de diagnostic : plafond lu et workers retenus."""
    if limit_bytes is None:
        limit_text = "absent ou illimite"
    else:
        limit_text = "%.2f Gio (%d octets)" % (limit_bytes / (1024 ** 3), limit_bytes)
    return "xdist workers: %d (cgroup memory limit: %s ; budget par worker: %d MiB ; reserve master: %d MiB)" % (
        compute_workers(limit_bytes),
        limit_text,
        RSS_BUDGET_PAR_WORKER_MIB,
        RSS_RESERVE_MASTER_MIB,
    )


def main(argv: list[str] | None = None) -> int:
    """Ecrit le diagnostic sur stderr et le nombre de workers sur stdout."""
    args = list(sys.argv[1:] if argv is None else argv)
    if args:
        print("aucun argument attendu : %s" % " ".join(args), file=sys.stderr)
        return 2
    limit = read_memory_limit_bytes()
    print(describe(limit), file=sys.stderr)
    print(compute_workers(limit))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
