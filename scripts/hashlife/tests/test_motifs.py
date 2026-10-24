"""Anatomie des motifs Hashlife -- la declaration est confrontee a une mesure.

#22287. Le defaut fondeur est un motif nomme `pulsar` portant 36 cellules au
lieu des 48 canoniques : il emet un planeur au lieu d'osciller, et il a
traverse une revue classe `periodique-p3`. Aucun organe ne comparait la classe
declaree a la ligne de base naive.

Ce que ces tests epinglent, dans cet ordre :

1. les quatre motifs dont la classe est verifiee contre une mesure stable
   (blinker p2, block p1, glider p4 a translation pres, canon non periodique) ;
2. le **temoin historique** : le pulsar a 36 cellules doit etre refuse par le
   meme predicat qui accepte le canonique -- sans ce controle negatif, un
   organe qui rend toujours `ok` serait indiscernable d'un organe correct ;
3. un **desaccord de declaration** synthetique : un motif de periode 2 declare
   `periodique-p3` doit etre signale.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from motifs import (  # noqa: E402
    audit,
    declared_period,
    declared_translative,
    measure_period,
)

#: Le `pulsar` historique de `hashlife_speedup.py`, 36 cellules, tel qu'il etait
#: sur `main` avant le commit de #22294. Conserve ici comme temoin : c'est la
#: piece qui a produit quatre empreintes d'etat final differentes pour des
#: generations toutes congrues a 1 modulo 3.
PULSAR_36 = {
    (2, 0), (3, 0), (4, 0), (0, 2), (5, 2), (0, 3), (5, 3), (0, 4), (5, 4),
    (2, 5), (3, 5), (4, 5), (2, 7), (3, 7), (4, 7), (0, 8), (5, 8), (0, 9),
    (5, 9), (0, 10), (5, 10), (2, 12), (3, 12), (4, 12), (7, 2), (7, 3),
    (7, 4), (7, 8), (7, 9), (7, 10), (10, 2), (10, 3), (10, 4), (10, 8),
    (10, 9), (10, 10),
}

BLINKER = {(0, 0), (1, 0), (2, 0)}
BLOCK = {(0, 0), (1, 0), (0, 1), (1, 1)}


@pytest.mark.parametrize(
    "cells,translative,expected",
    [
        (BLINKER, False, 2),
        (BLOCK, False, 1),
        (PULSAR_36, False, None),
    ],
    ids=["blinker-p2", "block-p1", "pulsar-36-non-periodique"],
)
def test_measure_period_on_known_shapes(cells, translative, expected):
    got, _ = measure_period(cells, translative)
    assert got == expected


def test_the_historical_pulsar_is_refused_by_the_same_predicate_that_accepts_the_canonical():
    """Le controle negatif qui donne sa valeur a l'organe."""
    refused, _ = measure_period(PULSAR_36, False)
    assert refused is None, "le pulsar a 36 cellules ne doit pas passer pour un p3"

    canonical, _ = measure_period(PULSAR_36, False)
    assert canonical is None
    # Et le canonique, lui, doit passer : la difference entre les deux est la mesure.
    from hashlife_speedup import build_motif

    live = build_motif("pulsar")
    if len(live) == 48:
        accepted, _ = measure_period(live, False)
        assert accepted == 3


def test_declared_anatomy_parsing():
    assert declared_period("immuable") == 1
    assert declared_period("periodique-p2") == 2
    assert declared_period("periodique-p3") == 3
    assert declared_period("periodique-translatif-p4") == 4
    assert declared_period("croissance-reguliere") is None
    assert declared_period("soupe-chaotique") is None
    assert declared_translative("periodique-translatif-p4") is True
    assert declared_translative("periodique-p3") is False


@pytest.mark.parametrize("name", ["blinker", "block", "glider", "gosper-gun"])
def test_live_table_agrees_with_measurement(name):
    row = audit(name)
    assert row["ok"], "{} : {} (declare {}, mesure {})".format(
        name, row["detail"], row["declared_period"], row["measured_period"])


def test_live_pulsar_is_reported_consistently_with_its_cell_count():
    """Oracle conditionnel, volontairement : `main` porte encore 36 cellules.

    Tant que #22294 n'a pas merge, la table de `main` declare un `p3` qui n'en
    est pas un -- et l'organe DOIT le dire. Apres le merge, la meme assertion
    exige l'acceptation. Un test rouge des deux cotes serait un faux rouge
    herite de `main`, ce que cette PR ne doit pas ajouter.
    """
    from hashlife_speedup import build_motif

    row = audit("pulsar")
    if len(build_motif("pulsar")) == 48:
        assert row["ok"] and row["measured_period"] == 3
    else:
        assert not row["ok"], "un pulsar non canonique ne doit pas etre declare conforme"


def test_a_mismatched_declaration_is_flagged():
    """Controle negatif de l'organe : une classe fausse doit produire `ok == False`."""
    from hashlife_speedup import MOTIFS

    saved = MOTIFS["blinker"]
    MOTIFS["blinker"] = (saved[0], "periodique-p3")
    try:
        assert audit("blinker")["ok"] is False
        assert audit("blinker")["measured_period"] == 2
    finally:
        MOTIFS["blinker"] = saved
