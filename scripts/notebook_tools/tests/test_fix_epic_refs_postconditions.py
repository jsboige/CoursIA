"""Tests de non-régression des postconditions à la couture EPIC."""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import fix_epic_refs as fer  # noqa: E402


def test_postcondition_refuse_un_lien_vidé() -> None:
    """La couture interdit de supprimer le contenu d'un lien parenthésé."""
    with pytest.raises(ValueError, match="texte de lien vide"):
        fer._strip_clause("([Epic #16774](https://github.com/jsboige/CoursIA/issues/16774))")


def test_postcondition_refuse_une_accentuation_vidée() -> None:
    """La couture interdit de supprimer le contenu d'une emphase."""
    with pytest.raises(ValueError, match="accentuation videe"):
        fer._strip_clause("| *Epic #4588, strate 3*")


def test_postcondition_refuse_un_separateur_orphelin() -> None:
    """Une barre ou un séparateur laissé près de la coupe est refusé."""
    with pytest.raises(ValueError, match="separateurs orphelins"):
        fer._strip_clause("5 — Epic #5104 / #5104")


def test_postcondition_refuse_une_preposition_orpheline() -> None:
    """Une préposition française suivie d'une virgule ne survit pas au retrait."""
    with pytest.raises(ValueError, match="preposition orpheline"):
        fer._strip_clause("relève de l'Epic #4956, dont le mécanisme dépend du modèle.")


def test_postcondition_refuse_une_elision_orpheline() -> None:
    """L'article élidé ne reste pas seul après le retrait de sa référence."""
    with pytest.raises(ValueError, match="elision orpheline"):
        fer._strip_clause("dans l'Epic #123, nous présentons le résultat")


def test_postcondition_accepte_fermeture_emphase_eloignee() -> None:
    """Une emphase légitime éloignée de la couture n'est pas signalée."""
    result = fer._strip_clause("*Titre*, 1948. EPIC #1206.")
    assert result is not None
    assert result[0] == "*Titre*, 1948."
