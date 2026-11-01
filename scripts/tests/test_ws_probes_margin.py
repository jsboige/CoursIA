#!/usr/bin/env python3
"""Tests du coeur pur de `ws_probes_margin.py` (#21823).

L'instrument repond a une question unique -- quelle perturbation faut-il pour
deplacer un item ? -- et toute sa valeur tient a la **separation des sens** :
un item ne peut etre **gagne** que si sa classe reelle est le second score,
alors que n'importe quel item actuellement **correct** peut etre perdu. Puiser
dans le mauvais vivier rapporte la marge la plus petite du jeu au lieu de la
marge pertinente, qui est plus chere : c'est ce defaut que ce fichier verrouille.

Instance mesuree (po-2024, test translate, scikit-learn 1.8.0) : la marge
minimale du jeu vaut `9.28e-03` sur un item **deja faux**, tandis que l'ecart
entre sieges exige de detruire un item correct, dont la marge la moins chere
vaut `1.24e-02`. Les deux nombres different, et le premier est le piege.
"""

import os
import sys

import numpy as np
import pytest

sys.path.insert(
    0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "repro")
)

from ws_probes_margin import DEFAULT_NOISE_BOUND, analyse  # noqa: E402


# Quatre items, construits pour que la marge minimale du jeu ne soit ni gagnable
# ni perdable : c'est le cas reel qui a produit l'erreur de sens.
#   item 0 : correct,   marge 0.005 -> PERDABLE
#   item 1 : faux,      marge 0.001 -> ni gagnable ni perdable (classe reelle
#                                      hors des deux premiers scores)
#   item 2 : correct,   marge 0.010 -> PERDABLE
#   item 3 : faux,      marge 0.020 -> GAGNABLE (classe reelle = second score)
GAP = [0.005, 0.001, 0.010, 0.020]
PRED = [0, 1, 2, 3]
Y = [0, 0, 2, 9]
RUNNER_UP_IS_TRUE = [False, False, False, True]


def _data(gap=GAP, pred=PRED, y=Y, runner_up_is_true=RUNNER_UP_IS_TRUE):
    pred = np.asarray(pred)
    y = np.asarray(y)
    return {
        "gap": np.asarray(gap, dtype=float),
        "pred": pred,
        "y": y,
        "runner_up_is_true": np.asarray(runner_up_is_true, dtype=bool),
        "accuracy": float((pred == y).mean()),
        "n_test": int(len(y)),
    }


def test_overall_minimum_is_not_the_gain_margin():
    """La marge la plus petite du jeu n'est pas la marge pour gagner un item."""
    rep = analyse("translated", _data())
    assert rep["min_gap"] == pytest.approx(0.001)
    assert rep["min_gap_index"] == 1
    # Seul l'item 3 peut etre gagne : sa marge est quatre fois la minimale.
    assert rep["cheapest_gain_margin"] == pytest.approx(0.020)
    # Les perdables sont les items corrects, tries par marge.
    assert rep["cheapest_loss_margin"] == pytest.approx(0.005)
    assert rep["cheapest_perturbation"] == pytest.approx(0.005)


def test_being_above_the_other_environment_requires_losing_items():
    """Nous sommes plus haut : il faut detruire un item correct, pas en gagner un.

    L'autre environnement mesure 0.25 quand nous mesurons 0.50 sur 4 items : un
    item d'ecart, dans le sens d'une PERTE. Le vivier est donc celui des items
    corrects, et la reponse est 0.005 -- surtout pas la marge minimale du jeu
    (0.001, item 1, qui n'est ni gagnable ni perdable).
    """
    rep = analyse("translated", _data(), other_accuracy=0.25)
    assert rep["delta_items"] == 1
    assert rep["direction"] == "PERDRE"
    assert rep["required_perturbation"] == pytest.approx(0.005)
    assert rep["required_perturbation"] != pytest.approx(rep["min_gap"])


def test_being_below_the_other_environment_requires_gaining_items():
    """Nous sommes plus bas : le vivier est celui des items gagnables (0.020)."""
    rep = analyse("translated", _data(), other_accuracy=0.75)
    assert rep["delta_items"] == -1
    assert rep["direction"] == "GAGNER"
    assert rep["required_perturbation"] == pytest.approx(0.020)


def test_k_th_cheapest_of_the_right_direction():
    """Pour deux items a perdre, c'est la marge du deuxieme perdable le moins cher."""
    rep = analyse("translated", _data(), other_accuracy=0.0)
    assert rep["delta_items"] == 2
    assert rep["required_perturbation"] == pytest.approx(0.010)


def test_pool_exhausted_returns_none():
    """Plus d'items a perdre que de perdables : la question n'a pas de reponse."""
    rep = analyse("translated", _data(), other_accuracy=-1.0)
    assert rep["delta_items"] > 2
    assert rep["required_perturbation"] is None


def test_measured_scale_is_not_arithmetic():
    """A l'echelle mesuree, la perturbation requise depasse largement le bruit."""
    rep = analyse("translated", _data(), other_accuracy=0.25)
    assert rep["required_perturbation"] > DEFAULT_NOISE_BOUND * 1e6
