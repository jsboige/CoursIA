#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Nombre de workers xdist borne par le plafond memoire du cgroup (#21802).

Le job `Scripts Tests (CPU)` lancait `-n 4` workers quel que soit le runner qui
le recoit. Sur les slots persistants `myia-po-2024-linux-persist-*`, plafonnes
a 1,5 Gio (`docker run --memory=1610612736`), quatre workers ont ete tues par
le cgroup : `dmesg` porte `Memory cgroup out of memory: Killed process
(python)` a `CONSTRAINT_MEMCG`, et le job sortait en 137.

La regle : le nombre de workers se calcule a l'execution d'apres la limite
memoire lue dans le cgroup du conteneur, divisee par le **budget memoire
mesure** d'un worker. Sans plafond lisible (`max`, fichier absent, cgroup v1
"illimite"), on retombe sur la valeur nominale.

Le budget n'est pas pose au jugement : c'est le RSS de pointe mesure sur la
suite reelle du job (voir `RSS_BUDGET_PAR_WORKER_MIB` et la mesure citee dans
le corps de la PR).

Ce module est l'organe natif du calcul : il est appele par les workflows et
couvre les tests dans `scripts/tests/test_cgroup_worker_budget.py`.
"""

from __future__ import annotations

import sys
from pathlib import Path

# Valeur nominale, inchangee pour les slots a 4 Gio.
DEFAULT_WORKERS = 4
# Plafond haut : la suite ne gagne rien au-dela (le chemin critique est un
# module unique sous `--dist loadscope`).
MAX_WORKERS = 4

# RSS de pointe mesure d'un worker xdist sur la suite du job
# `Scripts Tests (CPU)` (liste de chemins identique a celle du workflow).
#
# Mesure (poste ai-01, 2026-10-21, echantillonnage de l'arbre de processus
# toutes les 0,5 s, `-n 4 --dist loadscope`, 3 028 s) :
#   - pic de l'arbre complet (4 workers + master) : 4 605,1 MiB, atteint a 219 s
#   - pic du master xdist                            :   199,1 MiB
#   - charge CONCURRENTE par worker au pic de l'arbre : 4 605,1 / 4 = 1 151,3 MiB
# C'est cette derniere valeur qui dimensionne un worker : c'est ce que le
# conteneur doit tenir pour faire tourner N workers. Le pic ABSOLU d'un worker
# isole (2 130,7 MiB) vient d'un sous-processus transitoire (`git merge-base`,
# 828 MiB) et ne doit pas dimensionner un runner de 4 Go.
# Les valeurs locales (Windows) sont un majorant de la CI Linux : le garde
# errer du cote sur.
#
# Base retenue pour cette suite : la CHARGE CONCURRENTE moyenne au pic de
# l'arbre (4 605,1 / 4). La suite `scripts` a un profil reparti (le pic d'un
# worker isole vient d'un sous-processus transitoire, `git merge-base`, pas
# d'un module epingle), donc la moyenne est la bonne base. La suite `ICT`,
# elle, a un module epingle sous `--dist loadscope` : la base y est le worker
# le plus lourd (voir `RSS_BUDGET_PAR_WORKER_MIB_ICT`).
RSS_BUDGET_PAR_WORKER_MIB = 1152

# Suite ICT (`ict/tests/`, job `ICT tests/ (58)`) : budget propre, MESURE le
# 2026-10-21 sur ai-01 (meme methode : echantillonnage de l'arbre toutes les
# 0,5 s, `-n 4 --dist loadscope`, 292 s, meme chemin de tests que le job) :
#   - pic de l'arbre complet (4 workers + master) : 2 182,6 MiB a 155 s
#   - pic du master xdist                       :     54,8 MiB
#   - pic du worker le plus lourd               : 1 181,4 MiB
# Le budget retenu est le **worker le plus lourd** (1 181 MiB), et non la
# moyenne par worker (545,7 MiB) : sous `--dist loadscope` un module lourd
# reste epingle a un worker, donc le conteneur doit pouvoir tenir ce worker
# la charge, pas sa moyenne. Avec la moyenne, un conteneur a 1,5 Gio aurait
# recu 2 workers pour une charge reelle de 1 181 + 326 + 55 = 1 561 MiB --
# au-dela du plafond : le kill par cgroup qu'on cherche a eviter.
RSS_BUDGET_PAR_WORKER_MIB_ICT = 1181

# Budget par suite. Une suite inconnue retombe sur le budget de la suite
# `scripts` (la plus exigeante).
BUDGETS_PAR_SUITE = {
    "scripts": RSS_BUDGET_PAR_WORKER_MIB,
    "ict": RSS_BUDGET_PAR_WORKER_MIB_ICT,
}

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


def budget_for(suite: str) -> int:
    """Budget memoire par worker de la suite nommee, en MiB."""
    return BUDGETS_PAR_SUITE.get(suite, RSS_BUDGET_PAR_WORKER_MIB)


def describe(limit_bytes: int | None, suite: str = "scripts") -> str:
    """Phrase de diagnostic : plafond lu et workers retenus."""
    budget = budget_for(suite)
    if limit_bytes is None:
        limit_text = "absent ou illimite"
    else:
        limit_text = "%.2f Gio (%d octets)" % (limit_bytes / (1024 ** 3), limit_bytes)
    return "xdist workers: %d (cgroup memory limit: %s ; suite: %s ; budget par worker: %d MiB ; reserve master: %d MiB)" % (
        compute_workers(limit_bytes, budget_mib=budget),
        limit_text,
        suite,
        budget,
        RSS_RESERVE_MASTER_MIB,
    )


def main(argv: list[str] | None = None) -> int:
    """Ecrit le diagnostic sur stderr et le nombre de workers sur stdout.

    `--suite <nom>` selectionne le budget mesure de la suite concernee.
    """
    args = list(sys.argv[1:] if argv is None else argv)
    suite = "scripts"
    if "--suite" in args:
        index = args.index("--suite")
        try:
            suite = args[index + 1]
        except IndexError:
            print("--suite exige un nom de suite", file=sys.stderr)
            return 2
    limit = read_memory_limit_bytes()
    print(describe(limit, suite), file=sys.stderr)
    print(compute_workers(limit, budget_mib=budget_for(suite)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
