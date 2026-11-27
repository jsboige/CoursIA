"""Tests du coeur du service MDP — iteration de la valeur (AIMA-Gateway #19571).

Le coeur est charge **par chemin de fichier** (``importlib`` + ``Path(__file__)``) :
la suite partagee ``scripts-tests.yml`` tourne en ``--import-mode importlib``
(``pytest.ini``) et le dossier du test n'est pas ajoute a ``sys.path``, un import
par nom echouerait.
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


core = _load("mdp_value_iteration_core")
run = core.run


# --- MDP minimal a main : politique et valeurs optimales connues ------------
# Dans B, "goB" reste et rapporte +10 a chaque pas : V*(B) = 10 / (1 - 0.9) = 100.
# Dans A, "goB" amene en B : V*(A) = 0.9 * V*(B) = 90. Politique optimale : goB partout.
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
    """Variante du gridworld 4x3 d'AIMA : deux obstacles et deux terminaux."""
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
            # les deux directions perpendiculaires partagent le bruit 0.2 (0.1 + 0.1)
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
    assert set(out) >= {"status", "policy", "value", "iterations", "converged", "n_states"}
    assert out["n_states"] == 2


def test_optimal_policy_tiny():
    out = run(TINY)
    assert out["policy"] == {"A": "goB", "B": "goB"}


def test_optimal_value_tiny():
    out = run(TINY)
    assert out["value"]["B"] == pytest.approx(100.0, abs=1e-3)
    assert out["value"]["A"] == pytest.approx(90.0, abs=1e-3)


def test_converged_before_cap():
    out = run({**TINY, "max_iterations": 1000})
    assert out["converged"] is True
    assert out["iterations"] < 1000


def test_determinism():
    a = run(TINY)
    b = run(TINY)
    assert a["policy"] == b["policy"]
    assert a["value"] == b["value"]
    assert a["iterations"] == b["iterations"]


def test_greedy_policy_is_argmax_of_value():
    out = run(TINY)
    states, actions, T, R = TINY["states"], TINY["actions"], TINY["T"], TINY["R"]
    gamma = TINY["gamma"]
    V = out["value"]
    for s in states:
        best = max(
            actions,
            key=lambda a: R[s][a] + gamma * sum(T[s][a].get(sp, 0.0) * V[sp] for sp in states),
        )
        assert out["policy"][s] == best


def test_non_dict_payload_invalid():
    out = run("pas un dict")
    assert out["status"] == "invalid"
    assert "error" in out


def test_empty_states_invalid():
    out = run({**TINY, "states": []})
    assert out["status"] == "invalid"


def test_duplicate_states_invalid():
    out = run({**TINY, "states": ["A", "A"]})
    assert out["status"] == "invalid"


def test_missing_reward_action_invalid():
    R = {"A": {"goA": 0.0}, "B": {"goA": 0.0, "goB": 10.0}}
    out = run({**TINY, "R": R})
    assert out["status"] == "invalid"


def test_transition_not_normalized_invalid():
    T = {
        "A": {"goA": {"A": 0.5}, "goB": {"B": 1.0}},
        "B": {"goA": {"A": 1.0}, "goB": {"B": 1.0}},
    }
    out = run({**TINY, "T": T})
    assert out["status"] == "invalid"
    assert "somme" in out["error"]


def test_negative_transition_invalid():
    T = {
        "A": {"goA": {"A": 1.1}, "goB": {"B": 1.0}},
        "B": {"goA": {"A": 1.0}, "goB": {"B": 1.0}},
    }
    out = run({**TINY, "T": T})
    assert out["status"] == "invalid"


@pytest.mark.parametrize("gamma", [1.0, -0.1, 1.5])
def test_gamma_out_of_range_invalid(gamma):
    out = run({**TINY, "gamma": gamma})
    assert out["status"] == "invalid"
    assert "gamma" in out["error"]


def test_missing_transition_state_invalid():
    T = {"A": {"goA": {"A": 1.0}, "goB": {"B": 1.0}}}  # B manquant
    out = run({**TINY, "T": T})
    assert out["status"] == "invalid"


def test_gridworld_converges():
    states, actions, T, R = build_gridworld()
    out = run({"states": states, "actions": actions, "T": T, "R": R, "gamma": 0.9})
    assert out["status"] == "ok"
    assert out["converged"] is True
    assert out["n_states"] == 10


def test_gridworld_terminal_extremes():
    states, actions, T, R = build_gridworld()
    out = run({"states": states, "actions": actions, "T": T, "R": R, "gamma": 0.9})
    values = out["value"]
    for terminal in ("0,3", "2,0"):
        assert values[terminal] == 0.0
        for action in actions:
            assert T[terminal][action] == {terminal: 1.0}
            assert R[terminal][action] == 0.0
    assert values["0,2"] > values["2,1"]
