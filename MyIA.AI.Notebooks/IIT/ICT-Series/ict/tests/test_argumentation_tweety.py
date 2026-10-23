"""Tests de la jonction TweetyProject -- organe natif (#7742, jambe C3).

Le banc mesure la parite entre l'instrument de la serie
(:func:`ict.argumentation.grounded_labeling`) et l'oracle Java
(``SimpleGroundedReasoner``) sur 12 AF canoniques et 200 AF aleatoires
(seed 42). Il mesure aussi la **lecture** d'un AF construit par l'organe.

L'organe est hors depot (JARs et JDK non versionnes, mesures le 2026-10-20).
Quand il manque, les tests sont **sautes avec la raison mesuree** -- jamais
transformes en succes, jamais remplaces par un chiffre par defaut.
"""

from __future__ import annotations

import os
import sys

import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from ict import tweety_bridge as bridge  # noqa: E402

_AVAILABLE, _REASON = bridge.availability()

pytestmark = pytest.mark.skipif(
    not _AVAILABLE,
    reason=f"organe TweetyProject indisponible : {_REASON}",
)


# --------------------------------------------------------------------------- #
#  Gate 1 : parite sur les 12 AF canoniques                                   #
# --------------------------------------------------------------------------- #


@pytest.mark.parametrize(
    "name,af",
    bridge.canonical_cases(),
    ids=[name for name, _ in bridge.canonical_cases()],
)
def test_canonical_parity(name, af):
    """Instrument et oracle rendent la MEME extension grounded, cas par cas.

    Un desaccord sur un seul cas nomme le defaut : la semantique de la serie
    n'est alors plus celle de Dung 1995 telle que TweetyProject l'implemente,
    et toute trajectoire mesuree sur un AF de cette forme serait a relire.
    """
    instrument = bridge.instrument_grounded(af)
    native = bridge.native_grounded(af)
    assert instrument == native, (
        f"{name} : instrument={sorted(instrument)} oracle={sorted(native)}"
    )


# --------------------------------------------------------------------------- #
#  Gate 2 : parite sur 200 AF aleatoires (seed 42)                            #
# --------------------------------------------------------------------------- #


def test_random_battery_parity_200():
    """200 AF aleatoires reproductibles : zero desaccord, zero cas saute.

    Le compte est deplace, pas seulement le verdict : un banc qui rendrait
    « accord » sur 190 cas en en sautant 10 silencieusement passerait ce test
    sans avoir mesure ce qu'il annonce.
    """
    result = bridge.parity(bridge.random_cases(seed=42, count=200))
    assert result["n"] == 200, f"banc incomplet : {result['n']} cas"
    assert result["desaccord"] == 0, (
        f"{result['desaccord']} desaccord(s) : "
        + ", ".join(
            str(row["name"])
            for row in result["rows"]
            if not row["accord"]
        )
    )
    assert result["accord"] == 200


# --------------------------------------------------------------------------- #
#  Gate 3 : l'oracle n'est pas un echo -- il discrimine                       #
# --------------------------------------------------------------------------- #


def test_oracle_discriminates_non_empty_and_empty():
    """L'oracle rend des extensions VIDE et NON VIDE attendues -- pas un echo.

    Trois valeurs concretes : chaine 5 -> {0, 2, 4} ; Nixon diamond -> vide ;
    auto-attaque -> vide. Si l'oracle echoait l'instrument, ces valeurs
    seraient indistinguables d'une constante ; elles sont ici ecrites en dur,
    independamment de l'implementation testee.
    """
    cases = dict(bridge.canonical_cases())
    assert bridge.native_grounded(cases["chaine 5"]) == frozenset({0, 2, 4})
    assert bridge.native_grounded(cases["cycle 2 (Nixon)"]) == frozenset()
    assert bridge.native_grounded(cases["auto-attaque"]) == frozenset()
    assert bridge.native_grounded(cases["aucune attaque"]) == frozenset({0, 1, 2})


# --------------------------------------------------------------------------- #
#  Gate 4 : lecture dans l'autre sens (organe -> serie)                       #
# --------------------------------------------------------------------------- #


@pytest.mark.parametrize(
    "name,af",
    bridge.canonical_cases(),
    ids=[name for name, _ in bridge.canonical_cases()],
)
def test_roundtrip_af_from_native(name, af):
    """``af_from_native(build_native_af(af))`` rend le meme AF.

    La jonction n'est complete que si l'instrument peut consommer un AF
    construit par l'organe : arguments et attaques doivent survivre au
    trajet aller-retour (les listes peuvent differer par l'ordre, pas par le
    contenu).
    """
    rebuilt = bridge.af_from_native(bridge.build_native_af(af))
    assert rebuilt.arguments == af.arguments, name
    assert set(rebuilt.attacks) == set(af.attacks), name


# --------------------------------------------------------------------------- #
#  Gate 5 : l'absence de l'organe est nommee, jamais un succes                #
# --------------------------------------------------------------------------- #


def test_availability_reason_is_path_free():
    """La raison d'indisponibilite ne porte aucun chemin absolu.

    Elle est destinee a une sortie de carnet commitee : un chemin machine y
    serait une fuite (classe MACHINE_PATH des ratchets d'outputs). Le test
    verifie la forme de la raison, pas la disponibilite -- il tourne dans les
    deux etats.
    """
    _, reason = bridge.availability()
    if not _AVAILABLE:
        assert reason, "une indisponibilite doit porter sa raison"
    assert ":\\" not in reason and ":/" not in reason, reason