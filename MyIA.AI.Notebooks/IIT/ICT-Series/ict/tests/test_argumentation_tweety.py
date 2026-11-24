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


# --------------------------------------------------------------------------- #
#  Gate 6 : parite du labelling complet (212 cas)                             #
# --------------------------------------------------------------------------- #


def test_labelling_parity_212():
    """Le labelling COMPLET de l'instrument egale le labelling derive du natif.

    La parite de l'extension IN (gates 1-2) est aveugle a la separation
    ``out`` / ``undec`` -- c'est pourtant celle que les trajectoires de
    croyance consomment. Ce gate confronte, sur les 212 cas du banc
    (12 canoniques + 200 aleatoires), le labelling de l'instrument au
    labelling derive de l'extension native
    (:func:`ict.tweety_bridge.labelling_from_extension`) : zero desaccord
    attendu, compte deplace comme au gate 2.
    """
    cases = bridge.canonical_cases() + bridge.random_cases(seed=42, count=200)
    result = bridge.parity(cases)
    assert result["n"] == 212, f"banc incomplet : {result['n']} cas"
    assert result["label_desaccord"] == 0, (
        f"{result['label_desaccord']} desaccord(s) de labelling : "
        + ", ".join(
            str(row["name"])
            for row in result["rows"]
            if not row["label_accord"]
        )
    )
    assert result["label_accord"] == 212


# --------------------------------------------------------------------------- #
#  Gate 7 : la jambe labelling attrape le mutant que la parite IN laisse passer#
# --------------------------------------------------------------------------- #


def test_mutant_all_out_is_caught_by_labelling_parity():
    """Un mutant « tout non-IN = out » passe la parite IN et MORT au gate 6.

    Temoin negatif volontairement faux (proposition consultant du 24/10,
    #7742 c.6381512618 §1) : le mutant respecte les ensembles IN mais
    n'emet jamais ``undec``. Mesures attendues, ecrites en dur comme au
    gate 3, independamment de l'implementation testee :

    - la parite IN le laisse passer sur les 212 cas ;
    - la comparaison de labelling l'attrape sur **chaque** cas portant au
      moins un ``undec`` reel -- et seulement ceux-la : sans ``undec``, le
      mutant est indistinguable du vrai labelling ;
    - 147 des 212 cas portent au moins un ``undec`` (decompte re-mesure
      le 2026-11-10 depuis l'instrument pur Python, = mesure consultant).
    """
    cases = bridge.canonical_cases() + bridge.random_cases(seed=42, count=200)
    with_undec = 0
    caught = 0
    for name, af in cases:
        native = bridge.native_grounded(af)
        true_label = bridge.labelling_from_extension(af, native)
        mutant_in = frozenset(a for a, v in true_label.items() if v == "in")
        mutant_label = {
            a: ("in" if a in mutant_in else "out") for a in af.arguments
        }
        # La parite IN (gates 1-2) ne peut pas le voir : memes ensembles IN.
        assert mutant_in == native, f"{name} : le mutant doit garder l'extension"
        if any(v == "undec" for v in true_label.values()):
            with_undec += 1
            caught += int(mutant_label != true_label)
            assert mutant_label != true_label, (
                f"{name} : cas a undec reel, le mutant doit etre attrape"
            )
        else:
            assert mutant_label == true_label, (
                f"{name} : sans undec le mutant est indistinguable"
            )
    assert with_undec == 147, (
        f"decompte undec={with_undec}, attendu 147 (banc 212 cas, seed 42)"
    )
    assert caught == with_undec, "un cas a undec a echappe a la jambe labelling"
