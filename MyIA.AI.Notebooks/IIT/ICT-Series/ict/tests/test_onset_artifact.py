"""Tests du schema d'artefact du runner onset (#21998).

Aucun test ne charge de modele ni de stack d'entrainement : :mod:`ict.onset_artifact`
est pur, et c'est precisement pour cela qu'il existe separement du runner.

Le defaut couvert est celui mesure sur la flotte : un artefact qui ne dit pas son
budget de completion laisse le lecteur incapable de savoir sous quel regime de
troncature la mesure a ete prise. `ict25_arms.py` a servi des comparaisons entre
cap 1024 et cap 80 sans que rien, dans les fichiers, ne permette de le voir.
"""

from __future__ import annotations

import json

from ict.onset_artifact import (
    DEFAULT_MAX_COMPLETION_LENGTH,
    SCRIPT_ID,
    artifact_payload,
)


def _payload(**overrides):
    base = dict(
        model="Qwen/Qwen3.5-9B-Base",
        max_steps=120,
        lr=1e-5,
        num_gen=4,
        seeds=[0, 1, 42, 7],
        max_completion_length=DEFAULT_MAX_COMPLETION_LENGTH,
        results={"W": [{"seed": 0, "hack_early": 0.0, "hack_late": 0.1}]},
        summary={"W": {"median_early": 0.0, "median_late": 0.1, "verdict": "x"}},
    )
    base.update(overrides)
    return artifact_payload(**base)


def test_artifact_records_the_completion_budget():
    assert _payload()["max_completion_length"] == DEFAULT_MAX_COMPLETION_LENGTH


def test_artifact_records_the_effective_budget_not_the_default():
    """Un run lance avec un autre cap doit l'ecrire tel quel, pas le defaut."""
    assert _payload(max_completion_length=1024)["max_completion_length"] == 1024


def test_default_budget_stays_the_baseline_regime():
    """80 est le regime des artefacts baseline 0.5B : le changer change la serie.

    Ce n'est pas une calibration (la mesure EOS de #13596 montre qu'a 80 les
    completions sont tronquees) mais un parametre de protocole. Le pin rend le
    changement visible dans le diff plutot que silencieux dans un defaut.
    """
    assert DEFAULT_MAX_COMPLETION_LENGTH == 80


def test_artifact_names_the_script_that_produced_it():
    assert _payload()["script"] == SCRIPT_ID


def test_artifact_keeps_every_measured_field():
    payload = _payload()
    for key in ("model", "max_steps", "lr", "num_generations", "seeds", "results", "summary"):
        assert key in payload, f"champ mesure perdu : {key}"


def test_artifact_is_json_serialisable():
    """L'artefact part dans un fichier : il doit survivre a json.dumps."""
    text = json.dumps(_payload(), indent=1)
    assert json.loads(text)["max_completion_length"] == DEFAULT_MAX_COMPLETION_LENGTH


def test_seeds_are_copied_not_aliased():
    """Le payload ne doit pas partager la liste de l'appelant (mutabilite)."""
    seeds = [0, 1]
    payload = _payload(seeds=seeds)
    seeds.append(99)
    assert payload["seeds"] == [0, 1]
