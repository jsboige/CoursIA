"""Coeur reutilisable d'optimisation du voyageur de commerce (TSP) par metaheuristiques.

Pli 0 v2 (#27218) : le carnet MGS-07-TSP devient cours + TP + service web. Ce
module porte le contrat `POST /search/tsp` partage par les deux frontends (Kernel
Gateway notebook-http sur le carnet, service FastAPI `mgs_tsp_service.py`).

Voie technique (organ-first, reponse dans le body de PR) : la serie MGS tourne
sous kernel C# (.NET Interactive) et consomme directement le sous-module
`Search/MetaGeneticSharp` via `#r` sur les DLLs compilees. Aucun binding Python
de MetaGeneticSharp n'existe : on porte donc en Python le MEME algorithme que le
carnet phare demontre (GA panmictique + modele insulaire sur permutations), avec
la meme formule de fitness que GeneticSharp.Extensions (`TspFitness`) et les
memes operateurs (selection elitiste, OrderedCrossover OX1, ReverseSequenceMutation,
reinsertion elitiste par fitness).

Portee de la parite : reproductibilite seedee INTERNE a Python (deux runs avec
les memes entrees produisent le meme tour et la meme distance), pas une bit-parite
cross-langage avec le RNG FastRandom de GeneticSharp — intrinsequement fragile sur
un GA stochastique et hors criteres d'acceptation de #27218.
"""

from __future__ import annotations

import math
import random
from typing import Any, Callable


class TspInputError(ValueError):
    """Entree malformee : villes, algorithme ou parametres invalides (status invalid)."""


class TspRunError(RuntimeError):
    """Echec inattendu pendant l'optimisation (status error)."""


# Algorithmes servis par le contrat. "ga" = GA panmictique (baseline du carnet) ;
# "islands" = modele insulaire (config 2 du carnet).
ALLOWED_ALGORITHMS = ("ga", "islands")

# Bornes de validation des parametres (statuts invalid au-dela).
MIN_CITIES = 4
MAX_CITIES = 200
MIN_POPULATION = 4
MAX_POPULATION = 1000
MIN_GENERATIONS = 1
MAX_GENERATIONS = 5000

# Probabilites par defaut du moteur MetaGeneticAlgorithm (cf MetaGeneticAlgorithm.cs).
DEFAULT_CROSSOVER_PROB = 0.75
DEFAULT_MUTATION_PROB = 0.1


def _validate_payload(payload: Any) -> tuple[list[tuple[str, float, float]], str, dict[str, int]]:
    """Valide le corps de la requete et retourne (villes, algorithme, parametres)."""
    if not isinstance(payload, dict):
        raise TspInputError("le corps de la requete doit etre un objet JSON")

    cities = payload.get("cities")
    if not isinstance(cities, list):
        raise TspInputError("cities doit etre une liste de villes")
    if len(cities) < MIN_CITIES:
        raise TspInputError(f"il faut au moins {MIN_CITIES} villes (recu {len(cities)})")
    if len(cities) > MAX_CITIES:
        raise TspInputError(f"au plus {MAX_CITIES} villes (recu {len(cities)})")

    parsed: list[tuple[str, float, float]] = []
    seen_names: set[str] = set()
    for index, city in enumerate(cities):
        if not isinstance(city, dict):
            raise TspInputError(f"ville #{index} : objet attendu")
        name = city.get("name")
        if not isinstance(name, str) or not name:
            raise TspInputError(f"ville #{index} : name (chaine non vide) requis")
        if name in seen_names:
            raise TspInputError(f"nom de ville duplique : {name!r}")
        seen_names.add(name)
        try:
            x = float(city["x"])
            y = float(city["y"])
        except (KeyError, TypeError, ValueError) as exc:
            raise TspInputError(f"ville {name!r} : coordonnees x/y numeriques requises") from exc
        if not (math.isfinite(x) and math.isfinite(y)):
            raise TspInputError(f"ville {name!r} : coordonnees finies requises")
        parsed.append((name, x, y))

    algorithm = payload.get("algorithm", "ga")
    if algorithm not in ALLOWED_ALGORITHMS:
        raise TspInputError(
            "algorithme inconnu : " + repr(algorithm)
            + " (attendus : " + ", ".join(ALLOWED_ALGORITHMS) + ")"
        )

    params = payload.get("params", {})
    if not isinstance(params, dict):
        raise TspInputError("params doit etre un objet JSON")

    def _int_param(key: str, default: int, low: int, high: int) -> int:
        raw = params.get(key, default)
        if isinstance(raw, bool) or not isinstance(raw, int):
            raise TspInputError(f"parametre {key} : entier requis")
        if not (low <= raw <= high):
            raise TspInputError(f"parametre {key} hors bornes [{low}, {high}] : {raw}")
        return raw

    population = _int_param("population", 100, MIN_POPULATION, MAX_POPULATION)
    generations = _int_param("generations", 500, MIN_GENERATIONS, MAX_GENERATIONS)
    seed = _int_param("seed", 42, -(2**31), 2**31 - 1)

    # Partition insulaire : island_size x island_nb = population (cf IslandMetaHeuristic).
    if algorithm == "islands":
        island_nb = params.get("island_nb", 4)
        if isinstance(island_nb, bool) or not isinstance(island_nb, int) or island_nb < 2:
            raise TspInputError("parametre island_nb : entier >= 2 requis")
        if population % island_nb != 0:
            raise TspInputError(
                f"population ({population}) doit etre divisible par island_nb ({island_nb})"
            )
    else:
        island_nb = params.get("island_nb", 4)

    return parsed, algorithm, {
        "population": population,
        "generations": generations,
        "seed": seed,
        "island_nb": island_nb,
        "migration_period": params.get("migration_period", 5),
        "migration_mode": params.get("migration_mode", "Static"),
    }


def _distance_matrix(cities: list[tuple[str, float, float]]) -> list[list[float]]:
    """Matrice des distances euclidiennes (meme metrique que TspFitness)."""
    n = len(cities)
    dist = [[0.0] * n for _ in range(n)]
    for i in range(n):
        xi, yi = cities[i][1], cities[i][2]
        for j in range(i + 1, n):
            xj, yj = cities[j][1], cities[j][2]
            d = math.hypot(xi - xj, yi - yj)
            dist[i][j] = d
            dist[j][i] = d
    return dist


def _tour_length(tour: list[int], dist: list[list[float]]) -> float:
    """Longueur du tour cyclique (somme euclidienne, retour a la ville de depart)."""
    n = len(tour)
    total = 0.0
    for k in range(n):
        total += dist[tour[k]][tour[(k + 1) % n]]
    return total


def _random_tour(n: int, rng: random.Random) -> list[int]:
    """Permutation initiale aleatoire (population initiale reproductible)."""
    tour = list(range(n))
    rng.shuffle(tour)
    return tour


def _ordered_crossover(parent_a: list[int], parent_b: list[int], rng: random.Random) -> list[int]:
    """OrderedCrossover (OX1) : segment de A conserve, le reste dans l'ordre de B.

    Meme operateur que GeneticSharp.OrderedCrossover : on tire deux points de
    coupe, on copie le segment de A, puis on remplit les positions restantes avec
    les genes de B (dans leur ordre d'apparition, en sautant ceux deja presents).
    """
    n = len(parent_a)
    cut1, cut2 = sorted(rng.sample(range(n), 2))
    child: list[int | None] = [None] * n
    child[cut1:cut2 + 1] = parent_a[cut1:cut2 + 1]
    present = set(parent_a[cut1:cut2 + 1])

    fill = [gene for gene in parent_b if gene not in present]
    fi = 0
    for pos in list(range(0, cut1)) + list(range(cut2 + 1, n)):
        child[pos] = fill[fi]
        fi += 1
    return [int(g) for g in child]


def _reverse_sequence_mutation(tour: list[int], rng: random.Random) -> list[int]:
    """ReverseSequenceMutation : inverse un sous-segment aleatoire du tour."""
    n = len(tour)
    if n < 2:
        return tour[:]
    i, j = sorted(rng.sample(range(n), 2))
    mutated = tour[:]
    mutated[i:j + 1] = reversed(mutated[i:j + 1])
    return mutated


def _evolve_island(
    population: list[list[int]],
    dist: list[list[float]],
    rng: random.Random,
    crossover_prob: float,
    mutation_prob: float,
) -> list[list[int]]:
    """Une generation GA panmictique : selection elitiste -> OX1 -> RSM -> reinsertion.

    Reproduit DefaultMetaHeuristic (selection.SelectChromosomes sur toute la
    population, croisement par paires adjacentes, mutation par index, reinsertion
    elitiste par fitness). L'elitisme conserve le meilleur individu.
    """
    size = len(population)
    n = len(population[0])
    # Evaluation (fitness = longueur, on minimise).
    lengths = [_tour_length(tour, dist) for tour in population]

    # Selection elitiste : on trie par longueur croissante pour appareiller les meilleurs.
    order = sorted(range(size), key=lambda idx: lengths[idx])
    parents = [population[idx] for idx in order]

    # Croisement par paires adjacentes avec test de probabilite.
    offspring: list[list[int]] = []
    i = 0
    while i + 1 < len(parents):
        if rng.random() <= crossover_prob:
            offspring.append(_ordered_crossover(parents[i], parents[i + 1], rng))
            offspring.append(_ordered_crossover(parents[i + 1], parents[i], rng))
        else:
            offspring.append(parents[i][:])
            offspring.append(parents[i + 1][:])
        i += 2
    if len(parents) % 2 == 1:
        offspring.append(parents[-1][:])

    # Mutation par index.
    for k in range(len(offspring)):
        if rng.random() <= mutation_prob:
            offspring[k] = _reverse_sequence_mutation(offspring[k], rng)

    # Reinsertion elitiste par fitness : on conserve les `size` meilleurs parmi
    # parents + offspring (FitnessBasedElitistReinsertion).
    combined = parents + offspring
    combined_lengths = [_tour_length(tour, dist) for tour in combined]
    best_order = sorted(range(len(combined)), key=lambda idx: combined_lengths[idx])
    return [combined[idx] for idx in best_order[:size]]


def _run_ga(
    dist: list[list[float]],
    n: int,
    population_size: int,
    generations: int,
    rng: random.Random,
) -> tuple[list[int], float, list[float]]:
    """GA panmictique (baseline du carnet) : retourne (meilleur tour, distance, historique)."""
    population = [_random_tour(n, rng) for _ in range(population_size)]
    history: list[float] = []
    for _ in range(generations):
        population = _evolve_island(population, dist, rng, DEFAULT_CROSSOVER_PROB, DEFAULT_MUTATION_PROB)
        history.append(min(_tour_length(tour, dist) for tour in population))
    best = min(population, key=lambda tour: _tour_length(tour, dist))
    return best, _tour_length(best, dist), history


def _run_islands(
    dist: list[list[float]],
    n: int,
    population_size: int,
    generations: int,
    island_nb: int,
    migration_period: int,
    rng: random.Random,
) -> tuple[list[int], float, list[float]]:
    """Modele insulaire : population partitionnee, migration periodique statique.

    Reproduit IslandMetaHeuristic : chaque ile evolue independamment (DefaultMetaHeuristic
    locale), et tous les `migration_period` generations une migration statique echange
    des chromosomes ENTIERS entre iles (meilleurs emigrent, remplacent les pires).
    """
    island_size = population_size // island_nb
    # Partition initiale : population initiale decoupee en iles contigues.
    initial = [_random_tour(n, rng) for _ in range(population_size)]
    islands = [initial[i * island_size:(i + 1) * island_size] for i in range(island_nb)]

    history: list[float] = []
    for gen in range(1, generations + 1):
        # Migration periodique (avant l'evolution, comme ScopedSelectParentPopulation).
        if migration_period > 0 and gen % migration_period == 0:
            islands = _migrate_static(islands, dist)

        # Chaque ile evolue d'une generation.
        for idx in range(island_nb):
            islands[idx] = _evolve_island(
                islands[idx], dist, rng, DEFAULT_CROSSOVER_PROB, DEFAULT_MUTATION_PROB
            )
        flat = [tour for island in islands for tour in island]
        history.append(min(_tour_length(tour, dist) for tour in flat))

    flat = [tour for island in islands for tour in island]
    best = min(flat, key=lambda tour: _tour_length(tour, dist))
    return best, _tour_length(best, dist), history


def _migrate_static(
    islands: list[list[list[int]]], dist: list[list[float]]
) -> list[list[list[int]]]:
    """Migration statique en anneau : le meilleur de chaque ile remplace le pire de la suivante.

    Migration de chromosomes ENTIERS (permutations completes), jamais d'arithmetique
    sur les genes — c'est le point d'agnosticite que le carnet demontre.
    """
    island_nb = len(islands)
    emigrants: list[list[int]] = []
    for island in islands:
        best = min(island, key=lambda tour: _tour_length(tour, dist))
        emigrants.append(best[:])

    new_islands = [ [tour[:] for tour in island] for island in islands ]
    for idx in range(island_nb):
        target = (idx + 1) % island_nb
        # Le pire de l'ile cible est remplace par l'emigrant de l'ile source.
        worst_idx = max(
            range(len(new_islands[target])),
            key=lambda k: _tour_length(new_islands[target][k], dist),
        )
        new_islands[target][worst_idx] = emigrants[idx]
    return new_islands


def run(payload: Any) -> dict[str, Any]:
    """Execute le contrat POST /search/tsp et retourne le bloc ``data``.

    Retourne ``{"best_tour": [noms...], "distance": float, "history": [float...]}``
    — best_tour dans l'ordre de visite (noms de villes), history = longueur du
    meilleur tour par generation (courbe de convergence).
    """
    cities, algorithm, params = _validate_payload(payload)

    n = len(cities)
    dist = _distance_matrix(cities)
    # RNG dedie et seede : reproductibilite interne (deux runs identiques -> meme tour).
    rng = random.Random(params["seed"])

    try:
        if algorithm == "ga":
            best, distance, history = _run_ga(
                dist, n, params["population"], params["generations"], rng
            )
        else:
            best, distance, history = _run_islands(
                dist, n, params["population"], params["generations"],
                params["island_nb"], params["migration_period"], rng,
            )
    except (TspInputError, TspRunError):
        raise
    except Exception as exc:  # optimisation inattendue (bug interne)
        raise TspRunError("echec de l'optimisation : " + str(exc)) from exc

    names = [cities[gene][0] for gene in best]
    return {
        "best_tour": names,
        "distance": round(distance, 6),
        "history": [round(h, 6) for h in history],
    }
