#!/usr/bin/env python3
"""Tests de la memoire longue d'affluence (#16625, mandat user 2026-09-18).

Le compteur 24 h de fetch_visits est anti-collision intra-journee : il
retombe a zero des que la flotte ralentit 12 h et rend son poids plein au
sujet frequente. #16625 demande une SECONDE grandeur -- le compte cumule de
PRs mergees citant l'issue sur 30 j -- qui coexiste avec la premiere.

Dimensionnement (mesure 2026-09-18, 2921 PRs mergees / 30 j) : mediane du
pool ouvert = 1 (intouchable, /1.09 max), tete #13410 = 83 (/3.6). Ces tests
pinned les deux bouts : la mediane ne sait pas que le facteur existe, la
tete est mordue, et le contre-exemple explicite de l'acceptance 4 (reprise
apres 12 h d'arret de flotte) ne rend pas son poids plein au parking.

Run:
    python -m pytest scripts/tests/test_pick_parking_memory.py
"""
from __future__ import annotations

import math
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import pick_idle_grain as pig  # noqa: E402


def _item(n=13410, genre="docs", age=30, idle=1):
    return {"number": n, "klass": "grain", "title": "sweep", "age": age,
            "idle": idle, "genre": genre}


def test_long_visits_divide_the_head():
    """83 PRs/30 j (la tete mesuree, #13410) -> /3.63, la forme log2 douce."""
    w0 = pig.weight(_item(), None)
    w83 = pig.weight(_item(), None, long_visits={13410: 83})
    assert math.isclose(w0 / w83, 1.0 + math.log2(1.0 + 83 / 16.0),
                        rel_tol=1e-9)


def test_median_of_pool_is_untouched():
    """1 PR/30 j (la mediane mesuree du pool) -> /1.09 : le fond ne bouge pas."""
    w0 = pig.weight(_item(), None)
    w1 = pig.weight(_item(), None, long_visits={13410: 1})
    assert math.isclose(w0 / w1, 1.0 + math.log2(1.0 + 1 / 16.0),
                        rel_tol=1e-9)
    assert w0 / w1 < 1.10


def test_12h_fleet_pause_keeps_parking_amortized():
    """Acceptance 4 de #16625 : la fenetre 24 h retombee (visits vides) ne
    rend PAS son poids plein au sujet a memoire longue."""
    w_full = pig.weight(_item(), None)
    w_pause = pig.weight(_item(), None, visits={},
                         long_visits={13410: 31})
    assert math.isclose(w_full / w_pause,
                        1.0 + math.log2(1.0 + 31 / 16.0), rel_tol=1e-9)
    assert w_pause < w_full / 2.5


def test_both_windows_coexist_multiplicatively():
    """Le 24 h (anti-collision) et le 30 j (memoire) sont deux grandeurs
    distinctes : leurs diviseurs se composent, l'un ne remplace pas l'autre."""
    w0 = pig.weight(_item(), None)
    w_both = pig.weight(_item(), None, visits={13410: 8},
                        long_visits={13410: 31})
    expected = ((1.0 + math.log2(1.0 + 8 / 4.0))
                * (1.0 + math.log2(1.0 + 31 / 16.0)))
    assert math.isclose(w0 / w_both, expected, rel_tol=1e-9)


def test_draw_carries_parking_flag_and_visits_long():
    """Le pick rendu porte la memoire et le signal parking -- c'est la que
    la mesure devient consigne pour la lane et le coordinateur."""
    items = [_item(13410), _item(999, genre="notebook-python")]
    picks = pig.draw(items, 2, random.Random(1), None,
                     long_visits={13410: 83})
    by_number = {p["number"]: p for p in picks}
    assert by_number[13410]["visits_long"] == 83
    assert by_number[13410]["parking"] is True
    assert by_number[999]["visits_long"] == 0
    assert by_number[999]["parking"] is False


def test_parking_threshold_boundary():
    """12 PRs/30 j (une tous les 2,5 j) = veine ouverte ; 11 ne l'est pas."""
    for seen, expected in ((11, False), (12, True), (83, True)):
        item = _item(13410)
        pig.weight(item, None, long_visits={13410: seen})
        flag = item["visits_long"] >= pig.PARKING_SIGNAL_THRESHOLD
        assert flag is expected, f"seen={seen}"


def test_gvar_factors_unchanged_under_long_visits():
    """G-VAR-1 (CONTENU x2) et G-VAR-3 (prev_genre x0.25) survivent au
    facteur long : la memoire ne doit pas defaire les gates existants."""
    base = pig.weight(_item(genre="notebook-python"), None,
                      long_visits={13410: 83})
    contenu = pig.weight(_item(genre="docs"), None,
                         long_visits={13410: 83})
    # docs n'est pas CONTENU : le notebook-python pese 2x plus, facteur
    # long identique par ailleurs.
    assert math.isclose(base / contenu, 2.0, rel_tol=1e-9)
    penalized = pig.weight(_item(genre="notebook-python"), "notebook-python",
                           long_visits={13410: 83})
    assert math.isclose(base / penalized, 4.0, rel_tol=1e-9)


def test_fetch_visits_cache_name_separates_windows(monkeypatch):
    """Les deux fenetres partagent la fonction mais pas l'identite de cache :
    1 j sous le nom `visits`, 30 j sous `long_visits` -- sinon le status de
    l'une ecrase celui de l'autre et un stale 30 j se lirait sur la colonne
    du jour."""
    import json

    calls = []

    class _FakeCompleted:
        def __init__(self, stdout):
            self.stdout = stdout

    def fake_run(cmd, **kwargs):
        calls.append(cmd)
        return _FakeCompleted("[]")

    # Rend une liste vide : le compteur est vide, seule la commande importe.
    monkeypatch.setattr(pig.subprocess, "run", fake_run)

    class _NullCache:
        pass

    pig.fetch_visits(days=1, cache_name="visits")
    pig.fetch_visits(days=30, cache_name="long_visits")
    assert len(calls) == 2
    stamps = [c[c.index("--search") + 1] if "--search" in c else None
              for c in calls]
    assert stamps[0] != stamps[1], "les deux fenetres doivent couper a des dates distinctes"
