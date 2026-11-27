"""Tests du coeur du service HMM / Viterbi (hors kernel, hors gateway).

Le coeur est charge par **chemin de fichier** : la suite partagee
``scripts-tests.yml`` tourne en ``--import-mode importlib`` (``pytest.ini``) et
le dossier du test n'est pas ajoute a ``sys.path`` -- un import par nom echouerait.
"""

import importlib.util
from pathlib import Path

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location(
    "hmm_viterbi_core", HERE / "hmm_viterbi_core.py"
)
core = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(core)

run = core.run

# Modele meteo classique (celui du docstring du coeur et du carnet phare).
WEATHER = {
    "states": ["EnSoleil", "Pluie"],
    "pi": [0.6, 0.4],
    "A": [[0.7, 0.3], [0.4, 0.6]],
    "B": {
        "EnSoleil": {"promenade": 0.7, "magasin": 0.4, "nettoyage": 0.1},
        "Pluie": {"promenade": 0.1, "magasin": 0.4, "nettoyage": 0.6},
    },
}


def weather(obs):
    """Copie du modele meteo avec la suite d'observations donnee."""
    p = dict(WEATHER)
    p["observations"] = obs
    return p


# ------------------------------------------------------------------------ ok


def test_happy_path_status_ok():
    r = run(weather(["promenade", "magasin", "nettoyage"]))
    assert r["status"] == "ok"
    assert r["n_states"] == 2
    assert r["n_observations"] == 3


def test_path_length_matches_observations():
    r = run(weather(["promenade", "magasin", "nettoyage", "promenade"]))
    assert len(r["best_path"]) == 4


def test_path_uses_declared_states():
    r = run(weather(["promenade", "magasin", "nettoyage"]))
    assert all(s in WEATHER["states"] for s in r["best_path"])


def test_deterministic():
    a = run(weather(["promenade", "magasin", "nettoyage"]))
    b = run(weather(["promenade", "magasin", "nettoyage"]))
    assert a["best_path"] == b["best_path"]
    assert a["best_path_log_prob"] == b["best_path_log_prob"]


def test_forward_geq_viterbi():
    # P(observations) somme sur TOUS les chemins >= la meilleure trajectoire.
    r = run(weather(["promenade", "magasin", "nettoyage"]))
    assert r["observation_log_prob"] >= r["best_path_log_prob"] - 1e-9


def test_single_observation():
    r = run(weather(["promenade"]))
    assert r["status"] == "ok"
    assert len(r["best_path"]) == 1


def test_single_state_model():
    p = {
        "states": ["S"],
        "observations": ["x", "y", "z"],
        "pi": [1.0],
        "A": [[1.0]],
        "B": {"S": {"x": 0.5, "y": 0.3, "z": 0.2}},
    }
    r = run(p)
    assert r["status"] == "ok"
    assert r["best_path"] == ["S", "S", "S"]


def test_unknown_observation_symbol_is_floored_not_error():
    # 'tempeste' absent de B : le decodage reste defini (floor EPS), pas d'erreur.
    r = run(weather(["promenade", "tempeste", "nettoyage"]))
    assert r["status"] == "ok"
    assert len(r["best_path"]) == 3


def test_strongly_informative_model_picks_obvious_path():
    # Emissions quasi deterministes : le chemin optimal est evident.
    p = {
        "states": ["A", "B"],
        "observations": ["a", "a", "b", "b"],
        "pi": [0.5, 0.5],
        "A": [[0.9, 0.1], [0.1, 0.9]],
        "B": {
            "A": {"a": 0.95, "b": 0.05},
            "B": {"a": 0.05, "b": 0.95},
        },
    }
    r = run(p)
    assert r["best_path"] == ["A", "A", "B", "B"]


# -------------------------------------------------------------------- invalid


def test_missing_states_invalid():
    p = {k: v for k, v in weather(["x"]).items() if k != "states"}
    assert run(p)["status"] == "invalid"


def test_empty_observations_invalid():
    assert run(weather([]))["status"] == "invalid"


def test_pi_length_mismatch_invalid():
    p = weather(["x"])
    p["pi"] = [0.5, 0.5, 0.0]  # 3 valeurs pour 2 etats
    assert run(p)["status"] == "invalid"


def test_pi_sum_not_one_invalid():
    p = weather(["x"])
    p["pi"] = [0.6, 0.2]  # bonne longueur, somme 0.8
    assert run(p)["status"] == "invalid"


def test_transition_shape_mismatch_invalid():
    p = weather(["x"])
    p["A"] = [[0.7, 0.3, 0.0], [0.4, 0.6, 0.0]]  # 3 colonnes pour 2 etats
    assert run(p)["status"] == "invalid"


def test_negative_probability_invalid():
    p = weather(["x"])
    p["pi"] = [-0.6, 1.6]
    assert run(p)["status"] == "invalid"


def test_missing_emission_state_invalid():
    p = weather(["x"])
    p["B"] = {"EnSoleil": {"x": 1.0}}  # etat 'Pluie' manquant
    assert run(p)["status"] == "invalid"


def test_non_dict_payload_invalid():
    assert run(["pas", "un", "dict"])["status"] == "invalid"
    assert run(None)["status"] == "invalid"


def test_run_never_raises():
    for bad in [None, 42, "x", [], {"states": "x"}, {"states": 5}]:
        assert run(bad)["status"] in ("ok", "invalid", "error")
