#!/usr/bin/env python3
"""Dispositif d'auto-évaluation (#18207) : la passe de test du module partagé.

Ce que ce fichier garde
-----------------------
Le module `MyIA.AI.Notebooks/ML/DataScienceWithAgents/auto_evaluation.py` est
appelé par des cellules insérées dans six carnets. Trois familles de dérives
sont possibles après coup, et chacune a son test :

- **la correction fuit dans la sortie committée** : si la fonction affiche la
  réponse alors que l'apprenant n'a pas répondu, la sortie par défaut (C.2)
  donne le corrigé, et l'exercice formatif n'en est plus un. C'est la propriété
  la plus fragile du dispositif : elle se teste sur l'état « non répondu » ;
- **une question cassée fait rougir le carnet** : une bonne réponse hors des
  lettres proposées, un texte vide, un moment inconnu -- autant d'erreurs
  d'auteur qui doivent lever à l'exécution (C.1 exige que la cellule tourne,
  donc l'erreur doit être vue à l'écriture, jamais silencieuse) ;
- **la sortie dérive** : deux exécutions identiques doivent rendre le même
  texte, sinon la sortie committée bouge à chaque passage de kernel sans
  qu'aucune cellule source ait changé.

Le scanner se valide par ses faux négatifs
------------------------------------------
Un test qui ne vérifie que « la fonction ne lève pas » ne voit aucune des trois.
Le test de non-fuite est donc **explicite dans les deux sens** : la marque
d'absence de réponse doit être présente, et la marque de correction doit être
absente. Un affichage qui remplacerait la question par un simple « OK » resterait
vert partout ailleurs.
"""

import io
import os
import sys
from contextlib import redirect_stdout

import pytest

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
MODULE_DIR = os.path.join(ROOT, "MyIA.AI.Notebooks", "ML", "DataScienceWithAgents")
sys.path.insert(0, MODULE_DIR)

from auto_evaluation import MOMENTS, question  # noqa: E402

CHOIX = [
    "Pour accélérer l'entraînement",
    "Pour mesurer la performance sur des données jamais vues à l'entraînement",
    "Pour équilibrer les classes",
]
EXPLICATION = "Le test simule des données que le modèle n'a jamais vues."


def _capture(**kwargs):
    """Exécute `question` et rend (valeur de retour, texte affiché)."""
    buf = io.StringIO()
    with redirect_stdout(buf):
        valeur = question(**kwargs)
    return valeur, buf.getvalue()


def test_non_repondu_retourne_none():
    valeur, _ = _capture(texte="Pourquoi séparer ?", choix=CHOIX, bonne="B",
                         explication=EXPLICATION)
    assert valeur is None


def test_non_repondu_ne_donne_pas_la_correction():
    """La propriété C.2 du dispositif : la sortie par défaut ne contient pas le corrigé."""
    _, texte = _capture(texte="Pourquoi séparer ?", choix=CHOIX, bonne="B",
                        explication=EXPLICATION)
    assert "Réponse non donnée" in texte
    assert "Pourquoi :" not in texte
    assert EXPLICATION not in texte
    assert "Juste." not in texte


def test_non_repondu_annonce_les_choix_et_l_invite():
    _, texte = _capture(texte="Pourquoi séparer ?", choix=CHOIX, bonne="B",
                        explication=EXPLICATION)
    assert "A. Pour accélérer l'entraînement" in texte
    assert "B. Pour mesurer la performance sur des données jamais vues à l'entraînement" in texte
    assert "C. Pour équilibrer les classes" in texte
    assert "reponse=None" in texte


def test_reponse_juste():
    valeur, texte = _capture(texte="Pourquoi séparer ?", choix=CHOIX, bonne="B",
                             explication=EXPLICATION, reponse="B")
    assert valeur is True
    assert "Juste." in texte
    assert "Pourquoi : " + EXPLICATION in texte
    assert "Réponse non donnée" not in texte


def test_reponse_fausse_dit_la_bonne_lettre():
    valeur, texte = _capture(texte="Pourquoi séparer ?", choix=CHOIX, bonne="B",
                             explication=EXPLICATION, reponse="A")
    assert valeur is False
    assert "Incorrect — la bonne réponse est B." in texte
    assert "Pourquoi : " + EXPLICATION in texte


def test_sortie_deterministe():
    """Deux appels identiques rendent le même texte : la sortie committée est stable."""
    _, premier = _capture(texte="Pourquoi séparer ?", choix=CHOIX, bonne="B",
                          explication=EXPLICATION)
    _, second = _capture(texte="Pourquoi séparer ?", choix=CHOIX, bonne="B",
                         explication=EXPLICATION)
    assert premier == second


@pytest.mark.parametrize("moment", MOMENTS)
def test_chaque_moment_s_affiche(moment):
    _, texte = _capture(texte="Question ?", choix=CHOIX, bonne="B",
                        explication=EXPLICATION, moment=moment)
    assert moment in ("avant", "pendant", "apres")
    assert "Question ?" in texte


@pytest.mark.parametrize(
    "kwargs",
    [
        {"moment": "milieu"},                                    # moment inconnu
        {"choix": ["une seule"]},                                # moins de deux choix
        {"choix": [f"option {i}" for i in range(9)]},            # plus de huit choix
        {"bonne": "D"},                                          # bonne hors des lettres
        {"bonne": "b"},                                          # lettre minuscule
        {"reponse": "D"},                                        # réponse hors des lettres
        {"texte": "   "},                                        # question vide
        {"explication": "  "},                                   # correction vide
    ],
)
def test_entree_d_auteur_mal_formee_leve(kwargs):
    base = dict(texte="Question ?", choix=CHOIX, bonne="B", explication=EXPLICATION)
    base.update(kwargs)
    with pytest.raises(ValueError):
        question(**base)