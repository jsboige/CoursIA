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
import re
from pathlib import Path

from ict.onset_artifact import (
    DEFAULT_MAX_COMPLETION_LENGTH,
    SCRIPT_ID,
    artifact_payload,
    seed_metrics,
)


def _payload(**overrides):
    base = {
        "model": "Qwen/Qwen3.5-9B-Base",
        "max_steps": 120,
        "lr": 1e-5,
        "num_gen": 4,
        "seeds": [0, 1, 42, 7],
        "max_completion_length": DEFAULT_MAX_COMPLETION_LENGTH,
        "results": {"W": [{"seed": 0, "hack_early": 0.0, "hack_late": 0.1}]},
        "summary": {"W": {"median_early": 0.0, "median_late": 0.1, "verdict": "x"}},
    }
    base.update(overrides)
    return artifact_payload(**base)


def test_artifact_records_the_completion_budget():
    assert _payload()["max_completion_length"] == DEFAULT_MAX_COMPLETION_LENGTH


def test_artifact_records_the_effective_budget_not_the_default():
    """Un run lance avec un autre cap doit l'ecrire tel quel, pas le defaut."""
    assert _payload(max_completion_length=1024)["max_completion_length"] == 1024


def test_default_budget_matches_the_measured_baseline_artifacts():
    """1024 est le regime mesure des artefacts de reference de la serie.

    Les artefacts `ict25_onset-W_120steps.json` / `_S_120steps.json` portent
    `script = ict25_arms.py` et `git_commit = 602c2ca5975b` / `bef6527045b6`, et
    a ces commits l'ecrivain passait `max_completion_length=1024` a
    `GRPOConfig`. 80 n'est pas ce regime : c'est un regime qui tronque
    systematique (mesure EOS de #13596 : min = max = 80 sur 40/40 steps).

    Ce n'est pas une calibration mais un parametre de protocole : le pin rend le
    changement visible dans le diff plutot que silencieux dans un defaut.
    """
    assert DEFAULT_MAX_COMPLETION_LENGTH == 1024


def test_default_budget_is_the_one_the_baseline_writer_uses():
    """Temoin vivant du lien « le cap par defaut = le cap du producteur ».

    La reserve de la revue du 25/10 reprochait a la prose de nommer un regime
    « baseline » que personne ne verifiait. Ce test le verifie : l'ecrivain des
    artefacts de reference (`ict25_arms.py`) importe sa constante depuis
    `scripts/ict25_records.py`, et elle doit valoir le meme nombre que le
    defaut de l'artefact onset. Le fichier est lu, pas importe : le module tire
    ses dependances, on ne veut pas les payer dans un test de schema.
    """
    source = Path(__file__).resolve().parents[2] / "scripts" / "ict25_records.py"
    assert source.exists(), f"le producteur des artefacts de reference a disparu : {source}"
    trouve = re.search(
        r"^DEFAULT_MAX_COMPLETION_LENGTH\s*=\s*(\d+)\s*$",
        source.read_text(encoding="utf-8"), re.MULTILINE)
    assert trouve, "scripts/ict25_records.py ne declare plus DEFAULT_MAX_COMPLETION_LENGTH"
    assert int(trouve.group(1)) == DEFAULT_MAX_COMPLETION_LENGTH


def test_seed_metrics_records_the_effective_budget():
    """Le resultat de graine porte le budget effectif, comme l'artefact.

    La promesse « et dans chaque resultat de graine » de la docstring etait
    invérifiable : `run_seed` exigeait le stack d'entrainement. La fonction
    pure `seed_metrics` la rend testable — ce test en est le temoin.
    """
    metriques = seed_metrics(
        arm="W", seed=42, train_s=1.5, max_completion_length=1024,
        hack=[0, 1, 1, 0], mc=[1, 1, 0, 0], reward=[1, 1, 0, 0],
        steps=[0, 0, 1, 1], max_steps=2,
    )
    assert metriques["max_completion_length"] == 1024
    assert metriques["arm"] == "W"
    assert metriques["seed"] == 42
    assert metriques["per_step"] == [0.5, 0.5]
    # Le partage en deux moities (early / late) reste celui du runner.
    assert metriques["hack_early"] == 0.5
    assert metriques["hack_late"] == 0.5


def test_seed_metrics_records_a_budget_that_differs_from_the_default():
    """Un run lance avec un autre cap doit l'ecrire tel quel, pas le defaut."""
    metriques = seed_metrics(
        arm="S", seed=7, train_s=0.5, max_completion_length=384,
        hack=[0, 0], mc=[0, 0], reward=[0, 0], steps=[0, 0], max_steps=1,
    )
    assert metriques["max_completion_length"] == 384
    assert metriques["max_completion_length"] != DEFAULT_MAX_COMPLETION_LENGTH


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
