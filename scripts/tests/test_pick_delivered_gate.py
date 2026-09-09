"""Tests du garde de lane sur l'urne `delivered` (#15069).

Mandat user 2026-09-07 : « je ne veux pas que Minimax, notre plus petit
modele, soit en charge ni de merger, ni de fermer des issues ». L'urne
`delivered` prescrit une fermeture -- fermer remonte au coordinateur,
la verification pre-fermeture se delegue a l'adjoint, jamais aux
workers.

Un detecteur se valide par ses faux negatifs : le controle positif
(lane habilitee -> urne servie) est AUSSI obligatoire que le negatif
(lane worker -> jamais servie), sinon le garde pourrait refuser tout
le monde et paraitrait vert.

Cas fondateur : #13903, fermee par myia-po-2024:CoursIA-2 (lane MiniMax)
qui appliquait la regle R5 telle qu'elle etait lisible -- urne
`delivered` servie par le picker sans garde de lane.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from pick_idle_grain import (  # noqa: E402
    DELIVERED_URN_LANES,
    URN_NAMES,
    apply_delivered_urn_gate,
    delivered_urn_allowed,
)

DEFAULT_URNS = "grain,umbrella,delivered"


def test_entitled_lanes_are_exactly_the_short_list():
    """Liste explicite et courte, par conception (#15069) : le
    coordinateur (deux dashboards) et l'adjoint. Rien d'autre."""
    assert DELIVERED_URN_LANES == frozenset({
        "myia-ai-01:CoursIA",
        "myia-ai-01:CoursIA-2",
        "myia-po-2025:CoursIA-2",
    })


@pytest.mark.parametrize("lane", sorted(DELIVERED_URN_LANES))
def test_positive_control_entitled_lane_receives_delivered(lane):
    """Controle POSITIF exige par #15069 : une lane habilitee recoit
    toujours l'urne, par defaut comme en demande explicite -- le garde
    ne doit pas refuser tout le monde."""
    urns, notice = apply_delivered_urn_gate(
        lane, DEFAULT_URNS, DEFAULT_URNS, set(URN_NAMES))
    assert "delivered" in urns
    assert notice is None
    urns, notice = apply_delivered_urn_gate(
        lane, "grain,delivered", DEFAULT_URNS, {"grain", "delivered"})
    assert "delivered" in urns
    assert notice is None
    assert delivered_urn_allowed(lane)


WORKER_LANES = [
    "myia-po-2024:CoursIA-2",  # cas fondateur #13903 (lane MiniMax)
    "myia-po-2023:CoursIA-2",
    "myia-po-2026:CoursIA-2",
    "myia-po-2027:CoursIA-2",
    "myia-po-2025:CoursIA-2-x",  # prefixe de l'adjoint != adjoint
    "myia-po-2026:CoursIA",
    "myia-po-2023:CoursIA",
    "myia-po-2024:CoursIA",
    "myia-po-2025:CoursIA",
    "myia-po-2027:CoursIA",
    None,  # pas de lane = pas d'identite habilitee
]


@pytest.mark.parametrize("lane", WORKER_LANES)
def test_negative_control_worker_never_receives_delivered(lane):
    """Controle NEGATIF exige par #15069 : une lane worker ne recoit
    JAMAIS l'urne, quel que soit le chemin (defaut ou explicite)."""
    assert not delivered_urn_allowed(lane)
    # Defaut : retiree avec un avis, sans echec (le defaut ne doit pas
    # faire echouer chaque worker a chaque tirage).
    urns, notice = apply_delivered_urn_gate(
        lane, DEFAULT_URNS, DEFAULT_URNS, set(URN_NAMES))
    assert "delivered" not in urns
    assert "grain" in urns and "umbrella" in urns
    assert notice is not None and "#15069" in notice
    # Explicite : refus (la demande explicite porte l'intention de fermer).
    with pytest.raises(ValueError, match="reservee aux lanes habilitees"):
        apply_delivered_urn_gate(
            lane, "grain,delivered", DEFAULT_URNS, {"grain", "delivered"})


def test_gate_inactive_when_delivered_not_selected():
    """--urns grain,umbrella : le garde ne fait rien (rien a retirer,
    aucun avis parasite)."""
    urns, notice = apply_delivered_urn_gate(
        "myia-po-2024:CoursIA-2", "grain,umbrella", DEFAULT_URNS,
        {"grain", "umbrella"})
    assert urns == {"grain", "umbrella"}
    assert notice is None


def test_filter_candidates_excludes_delivered_for_worker_urns():
    """Bout en bout du cote selection : une fois l'urne retiree, la
    machinerie existuelle (check `urns` de filter_candidates) exclut
    toute candidate-delivered du tirage d'une lane worker."""
    from pick_idle_grain import filter_candidates

    items = [
        {"number": 1, "klass": "grain", "age": 10, "idle": 1},
        {"number": 2, "klass": "delivered", "age": 10, "idle": 1},
    ]
    lane = "myia-po-2024:CoursIA-2"
    urns, _ = apply_delivered_urn_gate(
        lane, DEFAULT_URNS, DEFAULT_URNS, set(URN_NAMES))
    kept, funnel = filter_candidates(items, urns=urns)
    assert [it["number"] for it in kept] == [1]
    assert funnel["by_urn"]["delivered"] == 0
