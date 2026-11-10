#!/usr/bin/env python3
"""Tests de ``render_prompt`` -- ponctuation de la definition (#22422).

Defaut mesure : le gabarit enveloppe la definition entre parentheses puis
ajoute un point (``... "{title}" ({definition}). ``). Une definition qui se
termine deja par un point produisait donc ``(….).`` dans une consigne
committee, double ponctuation visible par l'eleve.

Le correctif retire **un** point terminal (apres trim) avant l'enveloppe. Ces
tests epinglent le defaut, la non-regression des definitions non ponctuees,
et deux frontieres volontairement non touchees (points de suspension,
ponctuation forte).
"""
from fallacy_detection.cartesian_dataset_builder import Pair, render_prompt

DEF_PONCTUEE = "A claim is true because an authority says so."
DEF_NUE = "A claim is true because an authority says so"


def _pair(polarity: str = "fallacy", node_pk: int = 944) -> Pair:
    return Pair("P1", "train", polarity, node_pk, "family", 1, True, "s1")


def _texts(definition_en: str, definition_fr: str) -> dict:
    return {
        "nodes": {
            "F944": {
                "en": ("Appeal to authority", definition_en, ["an example"]),
                "fr": ("Appel a l'autorite", definition_fr, ["un exemple"]),
            }
        },
        "scenarios": {
            "s1": {
                "title": "Debate",
                "context": "Two people argue.",
                "issue": "One cites a celebrity.",
                "smoothTalker": "Alice",
                "drawer": "Bob",
                "titre": "Debat",
                "contexte": "Deux personnes discutent.",
                "enjeu": "L'un cite une celebrite.",
                "baratineur": "Alice",
                "piocheur": "Bob",
            }
        },
    }


def test_definition_ponctuee_ne_produit_plus_de_double_ponctuation():
    prompt = render_prompt(_pair(), _texts(DEF_PONCTUEE, DEF_PONCTUEE), "en")
    assert ".)." not in prompt, "double ponctuation encore presente"
    assert f'({DEF_NUE}). ' in prompt, "le point de la phrase doit rester unique"


def test_definition_non_ponctuee_reste_inchangee():
    prompt = render_prompt(_pair(), _texts(DEF_NUE, DEF_NUE), "en")
    assert f"({DEF_NUE}). " in prompt
    assert ".)." not in prompt


def test_espace_avant_le_point_terminal_est_absorbe():
    prompt = render_prompt(_pair(), _texts(DEF_NUE + " .", DEF_NUE), "en")
    assert f"({DEF_NUE}). " in prompt
    assert " )." not in prompt


def test_points_de_suspension_non_amputes():
    """Une definition finissant par « ... » garde ses points : seule la
    ponctuation finale ajoutee par le gabarit compte."""
    prompt = render_prompt(_pair(), _texts("A claim that is dubious...", DEF_NUE), "en")
    assert "(A claim that is dubious...). " in prompt


def test_ponctuation_forte_conservee():
    """Le correctif ne touche que le point : « ! » n'est pas retire."""
    prompt = render_prompt(_pair(), _texts("An authority said so!", DEF_NUE), "en")
    assert "(An authority said so!). " in prompt


def test_le_defaut_ne_depend_pas_de_la_langue():
    prompt = render_prompt(
        _pair(),
        _texts(DEF_NUE, "Une affirmation est vraie parce qu'une autorite le dit."),
        "fr",
    )
    assert ".)." not in prompt
    assert "(Une affirmation est vraie parce qu'une autorite le dit). " in prompt
