"""Comparaison des algorithmes du carnet SC-08 à de petits oracles exhaustifs."""

import collections
import contextlib
import io
import itertools
import json
from pathlib import Path

import pytest

pytest.importorskip("z3")
pytest.importorskip("numpy")

ALTERNATIVES = ("A", "B", "C")
RANKINGS = list(itertools.permutations(ALTERNATIVES))
NOTEBOOK = (
    Path(__file__).resolve().parents[2]
    / "MyIA.AI.Notebooks/GameTheory/SocialChoice/08-Kemeny-RankedPairs-Dodgson.ipynb"
)


def load_notebook_functions() -> dict:
    """Exécute les cellules nécessaires, sélectionnées par leur contenu."""
    notebook = json.loads(NOTEBOOK.read_text(encoding="utf-8"))
    markers = (
        "# Configuration et imports",
        "def pairwise_margin(",
        "# Test 2 : profil divergent",
        "def ranked_pairs(",
        "def dodgson_score(",
        "# Encodage Z3 du Kemeny winner",
        "def kemeny_z3(",
    )
    namespace = {}
    with contextlib.redirect_stdout(io.StringIO()):
        for marker in markers:
            matches = [
                "".join(cell["source"])
                for cell in notebook["cells"]
                if cell["cell_type"] == "code" and marker in "".join(cell["source"])
            ]
            assert len(matches) == 1, f"Cellule introuvable ou ambiguë : {marker}"
            exec(matches[0], namespace)
    return namespace


def agreement_score(ranking: tuple, profile: tuple) -> int:
    """Compte directement les accords entre classement et bulletins."""
    return sum(
        voter.index(first) < voter.index(second)
        for voter in profile
        for first, second in itertools.combinations(ranking, 2)
    )


def ranked_pairs_oracle(profile: tuple) -> tuple:
    """Construit les arcs avec une recherche exhaustive de chemins simples."""
    pairs = []
    for first, second in itertools.permutations(ALTERNATIVES, 2):
        margin = sum(
            (voter.index(first) < voter.index(second))
            - (voter.index(second) < voter.index(first))
            for voter in profile
        )
        if margin > 0:
            pairs.append((-margin, first, second))
    locked = set()

    def reaches(node: str, target: str, path: set) -> bool:
        return node == target or any(
            reaches(neighbor, target, path | {neighbor})
            for neighbor in ALTERNATIVES
            if (node, neighbor) in locked and neighbor not in path
        )

    for _, first, second in sorted(pairs):
        if not reaches(second, first, {second}):
            locked.add((first, second))
    winners = {
        candidate for candidate in ALTERNATIVES
        if not any(target == candidate for _, target in locked)
    }
    return winners, locked


def dodgson_bfs(profile: tuple, candidate: str) -> int:
    """Cherche le minimum dans le graphe de tous les swaps adjacents."""
    queue = collections.deque([(profile, 0)])
    seen = {profile}
    while queue:
        current, cost = queue.popleft()
        if all(
            sum(voter.index(candidate) < voter.index(other) for voter in current)
            > len(current) // 2
            for other in ALTERNATIVES if other != candidate
        ):
            return cost
        for index, voter in enumerate(current):
            for position in range(len(ALTERNATIVES) - 1):
                changed = list(voter)
                changed[position], changed[position + 1] = (
                    changed[position + 1], changed[position]
                )
                successor = current[:index] + (tuple(changed),) + current[index + 1:]
                if successor not in seen:
                    seen.add(successor)
                    queue.append((successor, cost + 1))
    raise AssertionError(f"Aucune solution pour {profile}, {candidate}")


def test_socialchoice_algorithms_against_exhaustive_oracles():
    functions = load_notebook_functions()
    for voter_count in (1, 2, 3):
        for profile in itertools.product(RANKINGS, repeat=voter_count):
            scores = {ranking: agreement_score(ranking, profile) for ranking in RANKINGS}
            best = max(scores.values())
            winners = {ranking[0] for ranking, score in scores.items() if score == best}
            brute = functions["kemeny_bruteforce"](profile, ALTERNATIVES)
            z3_result = functions["kemeny_z3"](profile, ALTERNATIVES)
            assert (brute[0], brute[2]) == (best, winners), profile
            assert z3_result[0] == "OPTIMAL", profile
            assert (z3_result[1], z3_result[3]) == (best, winners), profile
            assert scores[tuple(z3_result[2])] == best, profile

            order, actual_winners = functions["ranked_pairs"](profile, ALTERNATIVES)
            expected_winners, locked = ranked_pairs_oracle(profile)
            assert actual_winners == expected_winners, profile
            assert all(order.index(first) < order.index(second) for first, second in locked), profile

            for candidate in ALTERNATIVES:
                actual = functions["dodgson_score"](candidate, profile, ALTERNATIVES)
                assert actual == dodgson_bfs(profile, candidate), (profile, candidate)

    graph = collections.defaultdict(set, {"A": {"B"}, "B": {"C"}})
    assert functions["creates_cycle"](graph, "C", "A", ALTERNATIVES)
    assert not functions["creates_cycle"](graph, "A", "C", ALTERNATIVES)
    assert functions["dodgson_score"]("C", [("A", "B", "C")] * 3, ALTERNATIVES) == 4
