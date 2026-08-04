"""Tests unitaires pour ``ict.sensitivity`` (ICT-15b, strate 5, #7288 / Epic #4588).

Le module transpose le theoreme de Huang (2019) -- ``s(f) >= sqrt(deg(f))``
pour les fonctions booleennes sur l'hypercube -- au graphe de transition
Markovien d'une trajectoire ICT. La sensibilite locale ``s_x(f)`` y est le
nombre de **voisins** ``y`` (arete du graphe symetrise) ou ``f(y) != f(x)``.

Les gates ci-dessous sont falsifiables et portent sur des proprietes
mathematiques reelles du module (pas des smoke tests) :

  1. (Gate bornes) ``s_x`` est un entier dans ``[0, n_symbols-1]`` : un
     noeud n'est jamais son propre voisin (diagonale nulle de W), donc le
     nombre de voisins ou ``f`` bascule est plafonne par ``n-1``.
  2. (Gate fonction constante) si ``f`` est constante, aucun basculement :
     ``s_x = 0`` partout.
  3. (Gate invariance par complement) ``s_x(f) == s_x(not f)`` car le
     basculement ``f(y) != f(x)`` est invariant par negation logique.
  4. (Gate plafond = degre) ``s_x <= degre(x)`` ou ``degre(x)`` est le
     nombre d'aretes incidentes dans W : on ne peut basculer que sur les
     voisins existants.
  5. (Gate cycle parite) sur un cycle a 4 noeuds avec ``f = parite``,
     ``s_x = 2`` partout (2 noeuds de parite opposee sur le vocabulaire).
  6. (Gate fonction point) avec ``f(x) = 1`` ssi ``x = k``, le point
     ``k`` bascule sur tous les autres (``s_k = n-1``) et chaque autre
     noeud bascule uniquement vers ``k`` (``s_x = 1``).

Note honnete (G.9) -- semantique du voisinage avec smoothing : avec
``laplace_smoothing = 1e-9`` (defaut), ``transition_matrix`` ajoute
l'epsilon a TOUTES les paires, donc ``W[x, y] > 0`` (comparaison stricte,
l.116 du module) couvre **tout le vocabulaire** hors diagonale -- pas
seulement les aretes de transition observees. Le docstring de
``transition_graph`` ("les aretes absentes restent a 0") est vrai pour le
*poids exact* 0.0, mais le smoothing les met a 1e-9 > 0. Consequence :
``local_sensitivity`` mesure le **basculement global de f** sur le
vocabulaire (nombre de ``y != x`` avec ``f(y) != f(x)``), et le degre
``(W[x] > 0).sum()`` vaut systematiquement ``n-1``. C'est coherent avec
``huang_conjecture_test`` qui utilise le meme ``W`` (``deg_proxy =
mean(degres) = n-1``). Le module est auto-coherent ; cette note corrige
une lecture naive "voisinage = aretes reelles du graphe de transition".
  7. (Gate overflow vocabulaire) plus de labels distincts que
     ``n_symbols`` => ``ValueError`` (garde-fou documente l.101-104).
  8. (Gate distribution max/mean) ``sensitivity_distribution["max"]`` et
     ``["mean"]`` coincident avec ``max``/``mean`` de ``s`` sur les noeuds
     visites.
  9. (Gate distribution n_visited) ``["n_visited"] == len(set(states))``.
 10. (Gate distribution std/p95) ``std >= 0`` et ``min <= p95 <= max``.
 11. (Gate huang domaine verdict) le verdict est dans
     ``{consistent, inconsistent, inconclusive}``.
 12. (Gate huang inconclusive courte) une trajectoire trop courte
     (``< 2 * n_symbols`` transitions) => verdict ``inconclusive``.
 13. (Gate huang threshold) ``threshold == sqrt(deg_proxy)`` (definition).
 14. (Gate huang proxy injecte) un ``proxy_degree_fn`` injecte est respecte :
     ``deg_proxy`` prend sa valeur, ``threshold = sqrt`` de celle-ci.
 15. (Gate huang consistent/inconsistent) sur une trajectoire longue, le
     verdict ``consistent`` ssi ``s_max >= threshold`` ; une fonction
     constante y produit ``inconsistent`` (``s_max = 0``).

Implementation : numpy seul, deterministe, GPU-free. Les chaines sont
construites a la main (cycle 4-noeuds, fonction constante/point/parite).
Aucune dependance externe. Cf ``conftest.py`` pour le chargement du
package ``ict``.

Note honnete (G.9) : ``huang_conjecture_test`` l.207 passe ``states`` brut
(non encode en ids) a ``transition_graph``, contrairement a
``local_sensitivity`` l.108 qui encode. Non bloquant pour des labels
entiers ``0..n-1`` (les tests ci-dessous n'utilisent que cela) ; incoherence
documentee, pas corrigee (le module est verifie tel quel, comme spectral et
bistable).
"""

from __future__ import annotations

import math
import os
import sys

# Permettre l'import direct depuis le package ict (sans installation dev).
_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

import numpy as np
import pytest

from ict import sensitivity
from ict.spectral import transition_graph


# --------------------------------------------------------------------------- #
#  Fixtures : trajectoires concretes construites a la main                      #
# --------------------------------------------------------------------------- #
# Cycle oriente 0->1->2->3->0 repete : arêtes symétrisees 0-1, 1-2, 2-3, 3-0.
CYCLE_STATES = [0, 1, 2, 3] * 6  # 24 tokens, 23 transitions, 4 labels distincts.
N_CYCLE = 4


def _parity(n: int) -> int:
    """Fonction d'etat : parite (booleenne 0/1)."""
    return n % 2


def _constant_zero(_: int) -> int:
    """Fonction d'etat constante (jamais de basculement)."""
    return 0


def _point_k(k: int):
    """Fonction d'etat ``f(x) = 1`` ssi ``x == k`` (sinon 0)."""

    def f(x: int) -> int:
        return 1 if x == k else 0

    return f


# --------------------------------------------------------------------------- #
#  local_sensitivity                                                            #
# --------------------------------------------------------------------------- #
def test_local_sensitivity_bounds_shape_and_integer_dtype():
    """Gate 1 : s_x entier dans [0, n-1], shape (n_symbols,)."""
    s = sensitivity.local_sensitivity(CYCLE_STATES, N_CYCLE, _parity)
    assert s.shape == (N_CYCLE,)
    # Entier (le module construit un tableau int).
    assert np.issubdtype(s.dtype, np.integer)
    assert np.all(s >= 0)
    # Un noeud n'est jamais son propre voisin (W a diagonale nulle), donc
    # le nombre de voisins ou f bascule est plafonne par n_symbols - 1.
    assert np.all(s <= N_CYCLE - 1)


def test_local_sensitivity_constant_function_is_zero():
    """Gate 2 : f constante => s_x = 0 partout (aucun basculement)."""
    s = sensitivity.local_sensitivity(CYCLE_STATES, N_CYCLE, _constant_zero)
    assert np.all(s == 0)


def test_local_sensitivity_complement_invariance():
    """Gate 3 : s_x(f) == s_x(non f) (le basculement est invariant par negation).

    f(y) != f(x)  <=>  (1-f(y)) != (1-f(x))  : complementer f ne change pas
    quels couples basculent.
    """
    def parity(x: int) -> int:
        return x % 2

    def not_parity(x: int) -> int:
        return 1 - (x % 2)

    s_f = sensitivity.local_sensitivity(CYCLE_STATES, N_CYCLE, parity)
    s_nf = sensitivity.local_sensitivity(CYCLE_STATES, N_CYCLE, not_parity)
    assert np.array_equal(s_f, s_nf)


def test_local_sensitivity_bounded_by_graph_degree():
    """Gate 4 : s_x <= degre(x) = (W[x] > 0).sum() (aretes incidentes).

    On ne peut basculer que sur les voisins qui existent dans le graphe.
    """
    s = sensitivity.local_sensitivity(CYCLE_STATES, N_CYCLE, _parity)
    # Degre de chaque noeud dans le graphe symetrise (transition_graph attend
    # des ids entiers ; CYCLE_STATES est deja 0..n-1).
    W = transition_graph(CYCLE_STATES, N_CYCLE)
    degrees = (W > 0).sum(axis=1)
    assert np.all(s <= degrees)


def test_local_sensitivity_cycle_parity_is_two_everywhere():
    """Gate 5 : sur le vocabulaire 4 avec f=parite, s_x = 2 partout.

    f = x % 2 = [0,1,0,1] (2 pairs, 2 impairs). Avec voisinage = vocabulaire
    (smoothing, cf note module), chaque noeud bascule sur les 2 noeuds de
    parite opposee => s = [2,2,2,2].
    """
    s = sensitivity.local_sensitivity(CYCLE_STATES, N_CYCLE, _parity)
    assert np.array_equal(s, np.array([2, 2, 2, 2]))
    assert np.all(s == 2)


def test_local_sensitivity_point_function_localizes_to_k():
    """Gate 6 : f(x)=1 ssi x=k => s_k = n-1, autres basculent vers k (s=1).

    f = [1,0,0,0] (k=0). Le noeud 0 (f=1) bascule sur tous les autres (f=0)
    => s_0 = n-1 = 3. Chaque autre noeud (f=0) bascule uniquement vers 0
    (f=1) => s = 1. Donc s = [3,1,1,1].
    """
    s = sensitivity.local_sensitivity(CYCLE_STATES, N_CYCLE, _point_k(0))
    W = transition_graph(CYCLE_STATES, N_CYCLE)
    degrees = (W > 0).sum(axis=1)
    # s_0 = degre(0) = n-1 : tous les autres valent 0 != f(0)=1.
    assert s[0] == degrees[0]
    assert s[0] == N_CYCLE - 1
    # Les autres (1,2,3) basculent uniquement vers k=0 (f=1 != 0).
    assert s[1] == 1
    assert s[2] == 1
    assert s[3] == 1
    # s global <= degre.
    assert np.all(s <= degrees)


def test_local_sensitivity_raises_on_too_many_unique_labels():
    """Gate 7 : > n_symbols labels distincts => ValueError (garde-fou l.101-104)."""
    # 5 labels distincts (0..4) mais n_symbols=4.
    states = [0, 1, 2, 3, 4, 0, 1, 2, 3, 4]
    with pytest.raises(ValueError):
        sensitivity.local_sensitivity(states, 4, _parity)


# --------------------------------------------------------------------------- #
#  sensitivity_distribution                                                     #
# --------------------------------------------------------------------------- #
def test_sensitivity_distribution_max_mean_match_local_on_visited():
    """Gate 8 : distribution['max']/'mean' == max/mean de s sur les noeuds visites."""
    dist = sensitivity.sensitivity_distribution(CYCLE_STATES, N_CYCLE, _parity)
    s = sensitivity.local_sensitivity(CYCLE_STATES, N_CYCLE, _parity)
    # Tous les noeuds 0..3 sont visites (CYCLE_STATES couvre le vocabulaire).
    assert dist["max"] == float(np.max(s))
    assert dist["mean"] == pytest.approx(float(np.mean(s)))


def test_sensitivity_distribution_n_visited_counts_unique_states():
    """Gate 9 : n_visited == len(set(states))."""
    dist = sensitivity.sensitivity_distribution(CYCLE_STATES, N_CYCLE, _parity)
    assert dist["n_visited"] == len(set(CYCLE_STATES))
    assert dist["n_visited"] == N_CYCLE


def test_sensitivity_distribution_std_nonneg_p95_in_range():
    """Gate 10 : std >= 0 et p95 dans [0, max] (coherence d'une distribution)."""
    dist = sensitivity.sensitivity_distribution(CYCLE_STATES, N_CYCLE, _parity)
    assert dist["std"] >= 0.0
    assert 0.0 <= dist["p95"] <= dist["max"]


# --------------------------------------------------------------------------- #
#  huang_conjecture_test                                                        #
# --------------------------------------------------------------------------- #
_HUANG_VERDICTS = {"consistent", "inconsistent", "inconclusive"}


def test_huang_verdict_is_in_documented_domain():
    """Gate 11 : verdict dans {consistent, inconsistent, inconclusive}."""
    out = sensitivity.huang_conjecture_test(CYCLE_STATES, N_CYCLE, _parity)
    assert out["verdict"] in _HUANG_VERDICTS


def test_huang_inconclusive_on_short_trajectory():
    """Gate 12 : trajectoire trop courte (< 2*n_symbols transitions) => inconclusive.

    Garde-fou documente l.217-219 : n_transitions < 2*n_symbols => la
    distribution de sensibilite est sousechantillonnee.
    """
    # n_symbols=4, 2 transitions (< 2*4=8) => inconclusive.
    short = [0, 1, 2]
    out = sensitivity.huang_conjecture_test(short, 4, _parity)
    assert out["verdict"] == "inconclusive"
    assert out["n_transitions"] == 2
    assert out["n_transitions"] < 2 * 4


def test_huang_threshold_is_sqrt_of_deg_proxy():
    """Gate 13 : threshold == sqrt(deg_proxy) (definition de la conjecture)."""
    out = sensitivity.huang_conjecture_test(CYCLE_STATES, N_CYCLE, _parity)
    assert out["threshold"] == pytest.approx(math.sqrt(out["deg_proxy"]))


def test_huang_proxy_degree_fn_injected_is_respected():
    """Gate 14 : un proxy_degree_fn injecte determine deg_proxy et threshold."""
    fixed = 9.0  # deg_proxy arbitraire.

    def fixed_proxy(states, n_symbols):
        return fixed

    out = sensitivity.huang_conjecture_test(
        CYCLE_STATES, N_CYCLE, _parity, proxy_degree_fn=fixed_proxy
    )
    assert out["deg_proxy"] == fixed
    assert out["threshold"] == pytest.approx(math.sqrt(fixed))


def test_huang_consistent_when_s_max_meets_threshold():
    """Gate 15a : trajectoire longue + s_max >= threshold => consistent.

    Cycle 4-noeuds, f=parite : s_max=2, deg_proxy=degre moyen=2,
    threshold=sqrt(2)~1.414 < 2 => consistent.
    """
    out = sensitivity.huang_conjecture_test(CYCLE_STATES, N_CYCLE, _parity)
    # Trajectoire longue (pas inconclusive).
    assert out["n_transitions"] >= 2 * N_CYCLE
    assert out["verdict"] != "inconclusive"
    # s_max=2 >= threshold~1.414.
    assert out["s_max"] >= out["threshold"]
    assert out["verdict"] == "consistent"


def test_huang_inconsistent_for_constant_function_long_trajectory():
    """Gate 15b : f constante sur trajectoire longue => s_max=0 < threshold => inconsistent.

    Verdict honnetement negatif (pas de fabrication d'un consistent) : c'est
    exactement la discipline G.1 que le module revendique (l.40-42).
    """
    out = sensitivity.huang_conjecture_test(CYCLE_STATES, N_CYCLE, _constant_zero)
    assert out["n_transitions"] >= 2 * N_CYCLE
    assert out["verdict"] != "inconclusive"
    assert out["s_max"] == 0
    assert out["verdict"] == "inconsistent"
