"""Tests du coeur du service MDP — iteration de la politique (AIMA-Gateway #19571).

Le coeur est charge **par chemin de fichier** (``importlib`` + ``Path(__file__)``).
Les tests croisent aussi l'iteration de la valeur : sur un meme MDP, les deux
algorithmes convergent vers la meme politique et des valeurs proches sur les
exemples testés. Leurs compteurs utilisent des unités différentes et ne permettent
pas de comparer directement leur coût.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent


def _load(name: str):
    spec = importlib.util.spec_from_file_location(name, HERE / f"{name}.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)  # type: ignore[union-attr]
    return mod


pi_core = _load("mdp_policy_iteration_core")
vi_core = _load("mdp_value_iteration_core")
run = pi_core.run


# --- MDP minimal a main : politique et valeurs optimales connues ------------
TINY = {
    "states": ["A", "B"],
    "actions": ["goA", "goB"],
    "T": {
        "A": {"goA": {"A": 1.0}, "goB": {"B": 1.0}},
        "B": {"goA": {"A": 1.0}, "goB": {"B": 1.0}},
    },
    "R": {
        "A": {"goA": 0.0, "goB": 0.0},
        "B": {"goA": 0.0, "goB": 10.0},
    },
    "gamma": 0.9,
}


def build_gridworld():
    """Variante du gridworld 4x3 d'AIMA (même construction que les tests VI)."""
    cols, rows = 4, 3
    obstacles = {(1, 1), (1, 3)}
    terminal_reward = {(0, 3): 1.0, (2, 0): -1.0}
    step_cost = -0.04
    cells = [(r, c) for r in range(rows) for c in range(cols) if (r, c) not in obstacles]
    states = [f"{r},{c}" for (r, c) in cells]
    actions = ["N", "S", "E", "W"]
    delta = {"N": (-1, 0), "S": (1, 0), "E": (0, 1), "W": (0, -1)}

    def in_bounds(r, c):
        return 0 <= r < rows and 0 <= c < cols

    def is_obs(r, c):
        return (r, c) in obstacles

    T: dict = {}
    R: dict = {}
    for (r, c) in cells:
        T[f"{r},{c}"] = {}
        R[f"{r},{c}"] = {}
        for a in actions:
            if (r, c) in terminal_reward:
                T[f"{r},{c}"][a] = {f"{r},{c}": 1.0}
                R[f"{r},{c}"][a] = 0.0
                continue
            dr, dc = delta[a]
            nr, nc = r + dr, c + dc
            if not in_bounds(nr, nc) or is_obs(nr, nc):
                nr, nc = r, c
            perps = [(-1, 0), (1, 0)] if a in ("N", "S") else [(0, -1), (0, 1)]
            outcomes: dict[str, float] = {}

            def add(rr, cc, p):
                if not in_bounds(rr, cc) or is_obs(rr, cc):
                    rr, cc = r, c
                key = f"{rr},{cc}"
                outcomes[key] = outcomes.get(key, 0.0) + p

            add(nr, nc, 0.8)
            add(r + perps[0][0], c + perps[0][1], 0.1)
            add(r + perps[1][0], c + perps[1][1], 0.1)
            T[f"{r},{c}"][a] = outcomes
            R[f"{r},{c}"][a] = sum(
                probability * terminal_reward.get(tuple(map(int, state.split(","))), step_cost)
                for state, probability in outcomes.items()
            )
    return states, actions, T, R


def test_stable_policy_requires_converged_evaluation() -> None:
    payload = {
        "states": ["s"], "actions": ["a"],
        "T": {"s": {"a": {"s": 1.0}}},
        "R": {"s": {"a": 1.0}}, "gamma": 0.9,
        "theta": 1e-6, "max_iterations": 1,
    }
    out = run(payload)
    assert out["value"]["s"] == 1.0
    assert out["converged"] is False


def test_final_changed_policy_gets_bounded_evaluation() -> None:
    payload = {
        "states": ["s"], "actions": ["a", "b"],
        "T": {"s": {"a": {"s": 1.0}, "b": {"s": 1.0}}},
        "R": {"s": {"a": 0.0, "b": 1.0}}, "gamma": 0.9,
        "theta": 1e-6, "max_iterations": 1,
    }
    out = run(payload)
    assert out["policy"] == {"s": "b"}
    assert out["value"]["s"] == 1.0
    assert out["converged"] is False


@pytest.mark.parametrize("invalid", [float("nan"), float("inf"), float("-inf"), 10**400])
@pytest.mark.parametrize("field", ["T", "R"])
def test_unsupported_numeric_values_rejected(invalid: float | int, field: str) -> None:
    import copy

    payload = copy.deepcopy(TINY)
    if field == "T":
        payload["T"]["A"]["goA"]["A"] = invalid
    else:
        payload["R"]["A"]["goA"] = invalid
    assert run(payload)["status"] == "invalid"


def test_valid_contract_ok():
    out = run(TINY)
    assert out["status"] == "ok"
    assert set(out) >= {"status", "policy", "value", "improvement_steps", "converged", "n_states"}
    assert out["n_states"] == 2


def test_optimal_policy_tiny():
    assert run(TINY)["policy"] == {"A": "goB", "B": "goB"}


def test_optimal_value_tiny():
    out = run(TINY)
    assert out["value"]["B"] == pytest.approx(100.0, abs=1e-3)
    assert out["value"]["A"] == pytest.approx(90.0, abs=1e-3)


def test_converged_before_cap():
    out = run({**TINY, "max_iterations": 100})
    assert out["converged"] is True
    assert out["improvement_steps"] < 100


def test_determinism():
    a = run(TINY)
    b = run(TINY)
    assert a["policy"] == b["policy"]
    assert a["value"] == b["value"]


# --- Croisement avec l'iteration de la valeur -------------------------------

def test_agrees_with_value_iteration_on_tiny():
    pi = run(TINY)
    vi = vi_core.run(TINY)
    assert pi["policy"] == vi["policy"]
    for s in TINY["states"]:
        assert pi["value"][s] == pytest.approx(vi["value"][s], abs=1e-3)


def test_agrees_with_value_iteration_on_gridworld():
    states, actions, T, R = build_gridworld()
    payload = {"states": states, "actions": actions, "T": T, "R": R, "gamma": 0.9}
    pi = run(payload)
    vi = vi_core.run(payload)
    assert pi["policy"] == vi["policy"]
    for s in states:
        assert pi["value"][s] == pytest.approx(vi["value"][s], abs=1e-3)


def test_policy_iteration_fewer_steps_than_value_backups():
    """Compare les compteurs sur cet exemple, sans comparer les coûts de calcul."""
    states, actions, T, R = build_gridworld()
    payload = {"states": states, "actions": actions, "T": T, "R": R, "gamma": 0.9}
    pi = run(payload)
    vi = vi_core.run(payload)
    assert pi["improvement_steps"] < vi["iterations"]


# --- Entrées hors contrat ----------------------------------------------------

def test_non_dict_payload_invalid():
    out = run("pas un dict")
    assert out["status"] == "invalid"


def test_empty_states_invalid():
    assert run({**TINY, "states": []})["status"] == "invalid"


def test_duplicate_states_invalid():
    assert run({**TINY, "states": ["A", "A"]})["status"] == "invalid"


def test_missing_reward_action_invalid():
    R = {"A": {"goA": 0.0}, "B": {"goA": 0.0, "goB": 10.0}}
    assert run({**TINY, "R": R})["status"] == "invalid"


def test_transition_not_normalized_invalid():
    T = {
        "A": {"goA": {"A": 0.5}, "goB": {"B": 1.0}},
        "B": {"goA": {"A": 1.0}, "goB": {"B": 1.0}},
    }
    out = run({**TINY, "T": T})
    assert out["status"] == "invalid"
    assert "somme" in out["error"]


@pytest.mark.parametrize("gamma", [1.0, -0.1])
def test_gamma_out_of_range_invalid(gamma):
    assert run({**TINY, "gamma": gamma})["status"] == "invalid"


def test_gridworld_converges_and_extremes():
    states, actions, T, R = build_gridworld()
    out = run({"states": states, "actions": actions, "T": T, "R": R, "gamma": 0.9})
    assert out["status"] == "ok"
    assert out["converged"] is True
    for terminal in ("0,3", "2,0"):
        assert out["value"][terminal] == 0.0
        for action in actions:
            assert T[terminal][action] == {terminal: 1.0}
            assert R[terminal][action] == 0.0
    assert out["value"]["0,2"] > out["value"]["2,1"]
