"""Tests de la jonction Argumentum -- organe EPITA argumentation_lib (#7742, jambe C3).

La jonction 8sexies validait l'instrument de la serie contre TweetyProject
brut ; celle-ci le valide contre la pile que la serie Argument_Analysis
consomme : ``TweetyInitializer`` + ``AFHandler`` (organe EPITA vendored,
#4960). La parite est inter-organes, sur la MEME JVM que la jonction Tweety
(un processus, une seule JVM -- le pont n'en lance jamais une deuxieme).

Deux organes hors depot sont en prerequis : TweetyProject (JARs + JDK, la
JVM vient de la jonction 8sexies) et l'alias de routage ``tweety_initializer``
(PR #21657, sans lui la couche AF de l'organe est morte a l'import depuis
le merge C186f). Quand un prerequis manque, les tests sont **sautes avec la
raison mesuree** -- jamais transformes en succes, jamais remplaces par un
chiffre par defaut.
"""

from __future__ import annotations

import os
import sys

import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from ict import argumentum_bridge as bridge  # noqa: E402
from ict import tweety_bridge  # noqa: E402


def _probe():
    """JVM via la jonction Tweety d'abord, puis disponibilite de l'organe."""
    ok, reason = tweety_bridge.availability()
    if not ok:
        return False, f"jonction Tweety indisponible, JVM non demarree ({reason})"
    try:
        tweety_bridge.ensure_jvm()
    except Exception as exc:  # noqa: BLE001 - toute panne est une raison de saut
        return False, f"JVM non demarree ({type(exc).__name__})"
    return bridge.availability()


_AVAILABLE, _REASON = _probe()

pytestmark = pytest.mark.skipif(
    not _AVAILABLE,
    reason=f"organe EPITA argumentation_lib indisponible : {_REASON}",
)


# --------------------------------------------------------------------------- #
#  Gate 1 : parite organe EPITA vs instrument, 12 AF canoniques               #
# --------------------------------------------------------------------------- #


@pytest.mark.parametrize(
    "name,af",
    tweety_bridge.canonical_cases(),
    ids=[name for name, _ in tweety_bridge.canonical_cases()],
)
def test_canonical_parity(name, af):
    """Instrument et organe EPITA rendent la MEME extension grounded, cas par cas.

    Un desaccord nommerait un defaut de sémantique dans l'un des deux bouts :
    soit l'instrument de la serie, soit la couche AF vendored -- dans les deux
    cas la trajectoire mesuree sur un AF de cette forme serait a relire.
    """
    instrument = tweety_bridge.instrument_grounded(af)
    organ = bridge.organ_grounded(af)
    assert instrument == organ, (
        f"{name} : instrument={sorted(instrument)} organe={sorted(organ)}"
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
    result = bridge.parity(tweety_bridge.random_cases(seed=42, count=200))
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
#  Gate 3 : l'organe n'est pas un echo -- valeurs ecrites en dur               #
# --------------------------------------------------------------------------- #


def test_organ_discriminates_non_empty_and_empty():
    """L'organe EPITA rend les extensions attendues, pas un echo de l'instrument.

    Trois valeurs concretes, independantes de l'implementation testee :
    chaine 5 -> {0, 2, 4} ; Nixon diamond -> vide ; auto-attaque -> vide.
    Elles recoupent les temoins de la jonction Tweety (8sexies) : l'organe
    EPITA et l'oracle TweetyProject brut rendent les memes valeurs.
    """
    cases = dict(tweety_bridge.canonical_cases())
    assert bridge.organ_grounded(cases["chaine 5"]) == frozenset({0, 2, 4})
    assert bridge.organ_grounded(cases["cycle 2 (Nixon)"]) == frozenset()
    assert bridge.organ_grounded(cases["auto-attaque"]) == frozenset()
    assert bridge.organ_grounded(cases["aucune attaque"]) == frozenset({0, 1, 2})


# --------------------------------------------------------------------------- #
#  Gate 4 : l'absence de l'organe est nommee, jamais un succes                #
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
