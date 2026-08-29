#!/usr/bin/env python3
"""Garde d'admission du picker (#13420) : ce qu'il DOIT refuser, et surtout
ce qu'il ne doit PAS refuser.

Ce garde existe parce que la ponderation ne mordait pas. Mesure du 2026-08-29 :
le tirage place deja 62 % de sa masse au-dela de 7 jours et sous-pondere les
issues du jour a 0.39x -- pourtant 70 des 112 issues travaillees en 48 h
avaient moins de 24 h (63 %, contre 3.9 % de masse au tirage). L'ecart de 16x
dit que le travail n'arrive pas par le tirage mais par le steering et
l'auto-pick, deux chemins qu'aucun poids ne touche. D'ou un refus, applicable
quel que soit le chemin de selection.

Un garde se valide par ses FAUX NEGATIFS -- les formes qu'il doit attraper et
qu'un jeu de motifs ecrit a la main laisse passer sans jamais lever d'erreur.
Le cas decisif ici est `test_consolidation_admise_dans_la_zone_saturee` : un
garde qui refuserait le remede en meme temps que le mal serait exactement le
defaut que le miroir de polarite avait ete ajoute pour corriger (#12607
tombait a 0.36x comme les paires qu'il devait solder).
"""

import datetime as dt
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import pick_idle_grain as pick  # noqa: E402
from series_saturation import CONSOLIDATION, EXPANSION, NEUTRAL  # noqa: E402

ZONE = "Search/Part4-Metaheuristics"


def _iso(hours_ago):
    return (pick.NOW - dt.timedelta(hours=hours_ago)).strftime("%Y-%m-%dT%H:%M:%SZ")


def _item(number=9001, hours=100, labels=None, pol=NEUTRAL, parent=None):
    return {
        "number": number,
        "title": "grain de test",
        "labels": labels or [],
        "created_at": _iso(hours),
        "age": int(hours // 24),
        "idle": 0,
        "genre": "notebook-python",
        "parent": parent,
        "polarity": pol,
        "klass": "grain",
    }


def _zone(new_notebooks=5, con=0, exp=3):
    return {ZONE: {"new_notebooks": new_notebooks, CONSOLIDATION: con,
                   EXPANSION: exp, NEUTRAL: 0}}


# --- dwell ----------------------------------------------------------------

def test_issue_du_jour_refusee():
    cause = pick.admissibility(_item(hours=2), {}, {})
    assert cause is not None and cause.startswith("DWELL"), cause


def test_issue_agee_admise():
    assert pick.admissibility(_item(hours=10 * 24), {}, {}) is None


def test_seuil_exact_admis():
    """A l'heure pile le grain passe : le refus est `<`, pas `<=`."""
    assert pick.admissibility(_item(hours=24.5), {}, {}) is None


def test_label_urgent_court_circuite_le_dwell():
    """Le dwell vise l'emballement d'audit, pas un correctif de securite."""
    for lb in ("urgent", "security", "regression", "P0", "HOTFIX"):
        assert pick.admissibility(_item(hours=1, labels=[lb]), {}, {}) is None, lb


def test_dwell_zero_desactive_le_garde():
    assert pick.admissibility(_item(hours=0.1), {}, {}, dwell_hours=0.0) is None


# --- parite de zone -------------------------------------------------------

def test_expansion_refusee_en_zone_sans_remede():
    cause = pick.admissibility(_item(pol=EXPANSION), _zone(), {9001: ZONE})
    assert cause is not None and cause.startswith("ZONE SANS REMEDE"), cause


def test_consolidation_admise_dans_la_zone_saturee():
    """LE faux negatif qui compte : le remede doit passer la ou le mal bute.

    Refuser #12607 (consolidation MGS) en meme temps que les paires qu'il
    devait solder rendrait la zone saturee INTRAVAILLABLE -- et le mandat user
    du 2026-08-28 demande exactement l'inverse : que la zone saturee appelle
    de la consolidation.
    """
    assert pick.admissibility(_item(pol=CONSOLIDATION), _zone(),
                              {9001: ZONE}) is None


def test_expansion_admise_des_qu_un_remede_existe():
    """Un seul grain de consolidation ouvert leve le veto : le garde porte sur
    l'ABSENCE de remede, pas sur la parite stricte (qui se degraderait en
    consommant le remede -- voir le commentaire dans pick_idle_grain.py)."""
    assert pick.admissibility(_item(pol=EXPANSION), _zone(con=1),
                              {9001: ZONE}) is None


def test_expansion_admise_hors_zone_saturee():
    assert pick.admissibility(_item(pol=EXPANSION), _zone(new_notebooks=2),
                              {9001: ZONE}) is None


def test_zone_heritee_du_parent():
    """Un sous-grain ne cite pas la famille : elle vient de son EPIC parent."""
    it = _item(number=9002, pol=EXPANSION, parent=7777)
    cause = pick.admissibility(it, _zone(), {7777: ZONE})
    assert cause is not None and cause.startswith("ZONE SANS REMEDE"), cause


def test_zone_non_mesuree_n_invente_pas_de_refus():
    """balance vide = mesure absente. Un zero d'absence de donnee ne doit pas
    se lire comme un zero de remede, sinon le garde refuse tout le pool des
    que `fetch_series_visits` echoue."""
    assert pick.admissibility(_item(pol=EXPANSION), {}, {9001: ZONE}) is None


def test_le_dwell_prime_sur_la_zone():
    """Ordre des causes : un grain neuf ET en zone sans remede est refuse pour
    dwell -- la cause la plus reparable en premier."""
    cause = pick.admissibility(_item(hours=2, pol=EXPANSION), _zone(),
                               {9001: ZONE})
    assert cause.startswith("DWELL"), cause
