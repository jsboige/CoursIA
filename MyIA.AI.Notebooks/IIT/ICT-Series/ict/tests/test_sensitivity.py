"""Tests du module :mod:`ict.sensitivity` (ICT-15b strate 5, Epic #4588).

Ce module transpose le **theoreme de Huang (2019)** -- pour toute fonction
booleenne ``f: {0,1}^n -> {0,1}``, ``s(f) >= sqrt(deg(f))`` -- au graphe de
transition Markovien d'une trajectoire ICT. La sensibilite locale ``s_x(f)``
compte les voisins ``y`` (au sens du graphe symetrise :func:`transition_graph`)
ou la fonction d'etat ``f`` bascule. La conjecture ICT-15b teste si
``s_max(f) >= sqrt(deg_proxy(f))`` avec un verdict honnete
(``consistent`` / ``inconsistent`` / ``inconclusive``).

Chaque test verrouille un invariant falsifiable, valeur spot-checkee
empiriquement AVANT l'assertion (methode G.9) : sensibilite nulle pour une
fonction constante, borne par le degre du graphe, invariance de label,
verdicts ``inconclusive`` (trajectoire trop courte / noeud isole) vs
``consistent`` vs ``inconsistent`` (proxy force). Pattern herite de
``test_sorting_metrics.py`` : bootstrap ``sys.path`` module-level, sans
fixtures, assertions documentees. Module autonome (numpy seul, GPU-free).
"""

from __future__ import annotations

import os
import sys

import numpy as np
import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from ict import sensitivity as s  # noqa: E402
from ict.spectral import transition_graph  # noqa: E402


# --------------------------------------------------------------------------- #
#  local_sensitivity : sensibilite locale sur le graphe de transition
# --------------------------------------------------------------------------- #


def test_local_sensitivity_alternating_identity_returns_one_each():
    """Sur une trajectoire alternee [0,1]*3 (n=2), chaque noeud a l'autre pour
    seul voisin ; avec f=identite, f(bascule) sur ce voisin -> s=[1,1]. Le
    vecteur a la forme (n_symbols,) et un dtype entier (ce sont des comptes)."""
    sens = s.local_sensitivity([0, 1, 0, 1, 0, 1], 2, lambda x: x)
    assert list(sens) == [1, 1]
    assert sens.shape == (2,)
    assert np.issubdtype(sens.dtype, np.integer)


def test_local_sensitivity_constant_function_is_zero():
    """Une fonction constante f(x)=c ne bascule sur AUCUN voisin : la
    sensibilite est 0 partout, independamment de la topologie du graphe."""
    sens = s.local_sensitivity([0, 1, 0, 1, 0, 1], 2, lambda x: 0)
    assert list(sens) == [0, 0]
    # Idem sur un 3-cycle : f constante -> zero partout.
    sens3 = s.local_sensitivity([0, 1, 2, 0, 1, 2, 0, 1, 2], 3, lambda x: 5)
    assert list(sens3) == [0, 0, 0]


def test_local_sensitivity_raises_on_too_many_unique_states():
    """Si la trajectoire contient plus de labels distincts que ``n_symbols``,
    l'encodage echoue : on ne peut pas mapper (n_symbols+1) labels sur
    n_symbols identifiants. ValueError explicite (garde documentee)."""
    with pytest.raises(ValueError, match="n_symbols"):
        s.local_sensitivity([0, 1, 2], 2, lambda x: x)
    with pytest.raises(ValueError):
        # 4 labels distincts, n_symbols=3.
        s.local_sensitivity(["a", "b", "c", "d", "a", "b"], 3, lambda x: x)


def test_local_sensitivity_is_label_invariant():
    """L'encodage des labels (premiere apparition -> entier) rend la
    sensibilite independante du choix de labels : une trajectoire isomorphe
    avec des labels chaines donne le MEME vecteur que ses homologues entiers."""
    int_sens = s.local_sensitivity([0, 1, 0, 1, 0, 1], 2, lambda x: x)
    str_sens = s.local_sensitivity(["a", "b", "a", "b", "a", "b"], 2, lambda x: x)
    assert np.array_equal(int_sens, str_sens)


# --------------------------------------------------------------------------- #
#  Structure plus riche + borne par le degre du graphe
# --------------------------------------------------------------------------- #


def test_local_sensitivity_3cycle_parity_partition():
    """Sur un 3-cycle [0,1,2]*3 (tous les noeuds visites, degre 2), avec
    f=x%2 (f(0)=0, f(1)=1, f(2)=0) : le noeud 1 (f=1) voit ses 2 voisins
    basculer (0 et 2 ont f=0), les noeuds 0 et 2 (f=0) ne voient qu'un
    seul bascule (le noeud 1). -> s=[1,2,1]. Verifie a la main + empirique."""
    sens = s.local_sensitivity([0, 1, 2, 0, 1, 2, 0, 1, 2], 3, lambda x: x % 2)
    assert list(sens) == [1, 2, 1]


def test_local_sensitivity_bounded_by_graph_degree():
    """Contractuellement, s_x(f) = |{voisins y : f(y) != f(x)}| <= |voisins de x|
    = degre du graphe en x. Verifie sur deux topologies (3-cycle, 4-line) ou
    tous les noeuds sont visites."""
    configs = [
        ([0, 1, 2, 0, 1, 2, 0, 1, 2], 3, lambda x: x % 2),
        ([0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3], 4, lambda x: x % 2),
    ]
    for states, n_symbols, f in configs:
        sens = s.local_sensitivity(states, n_symbols, f)
        W = transition_graph(states, n_symbols)
        degree = (W > 0).sum(axis=1)
        assert np.all(sens <= degree), (
            f"sens {sens} depasse le degre {degree} (states={states}, n={n_symbols})"
        )


# --------------------------------------------------------------------------- #
#  sensitivity_distribution : statistiques resumees
# --------------------------------------------------------------------------- #


def test_distribution_returns_documented_keys_and_types():
    """Retourne les 5 cles documentees ; les statistiques sont float, le
    compteur n_visited est int."""
    d = s.sensitivity_distribution([0, 1, 0, 1, 0, 1], 2, lambda x: x)
    assert set(d.keys()) == {"max", "mean", "std", "p95", "n_visited"}
    for k in ("max", "mean", "std", "p95"):
        assert isinstance(d[k], float), f"{k} devrait etre float, recu {type(d[k])}"
    assert isinstance(d["n_visited"], int)


def test_distribution_alternating_values():
    """Sur l'alternance [0,1]*3 (f=x), s=[1,1] sur les 2 noeuds visites :
    max=mean=p95=1.0, std=0.0 (distribution degeneree), n_visited=2."""
    d = s.sensitivity_distribution([0, 1, 0, 1, 0, 1], 2, lambda x: x)
    assert d["max"] == pytest.approx(1.0)
    assert d["mean"] == pytest.approx(1.0)
    assert d["std"] == pytest.approx(0.0)
    assert d["p95"] == pytest.approx(1.0)
    assert d["n_visited"] == 2


def test_distribution_constant_function_zero_stats():
    """Une fonction constante donne s=[0,0] sur les noeuds visites : toutes
    les statistiques sont 0.0 (mais n_visited compte quand meme les noeuds
    effectivement parcourus par la trajectoire)."""
    d = s.sensitivity_distribution([0, 1, 0, 1, 0, 1], 2, lambda x: 0)
    assert d["max"] == pytest.approx(0.0)
    assert d["mean"] == pytest.approx(0.0)
    assert d["std"] == pytest.approx(0.0)
    assert d["p95"] == pytest.approx(0.0)
    assert d["n_visited"] == 2


def test_distribution_3cycle_parity():
    """Sur le 3-cycle (f=x%2), s=[1,2,1] sur 3 noeuds visites : max=2,
    mean=4/3, n_visited=3. Verifie empiriquement."""
    d = s.sensitivity_distribution([0, 1, 2, 0, 1, 2, 0, 1, 2], 3, lambda x: x % 2)
    assert d["max"] == pytest.approx(2.0)
    assert d["mean"] == pytest.approx(4 / 3)
    assert d["n_visited"] == 3


# --------------------------------------------------------------------------- #
#  huang_conjecture_test : verdicts honnetes
# --------------------------------------------------------------------------- #


def test_huang_short_trajectory_is_inconclusive():
    """Garde-fou : une trajectoire trop courte pour etre significative donne
    verdict ``inconclusive`` (jamais de faux consistent/inconsistent). Deux
    declencheurs : (a) n_transitions < 2*n_symbols ; (b) n_visited < 2."""
    # (a) [0,1,0,1] n=2 : 3 transitions < 4 -> inconclusive.
    h_short = s.huang_conjecture_test([0, 1, 0, 1], 2, lambda x: x)
    assert h_short["verdict"] == "inconclusive"
    # (b) [0,0,0,0] n=2 : un seul noeud visite -> inconclusive.
    h_isolated = s.huang_conjecture_test([0, 0, 0, 0], 2, lambda x: x)
    assert h_isolated["verdict"] == "inconclusive"


def test_huang_3cycle_default_proxy_is_consistent():
    """Sur le 3-cycle (f=x%2), s_max=2 (noeud 1) et le proxy par defaut
    (degre moyen) donne un threshold ~1.0 : s_max >= threshold ->
    ``consistent``. Cas propre (ratio ~2, clairement au-dessus de 1)."""
    h = s.huang_conjecture_test(
        [0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2], 3, lambda x: x % 2
    )
    assert h["verdict"] == "consistent"
    assert h["s_max"] == 2
    assert h["s_max"] >= h["threshold"]


def test_huang_custom_proxy_can_force_inconsistent():
    """Un ``proxy_degree_fn`` explicite remplace le degre moyen par defaut.
    Avec proxy=4.0 -> threshold=sqrt(4)=2.0 ; s_max=1 (alternance n=2) < 2.0
    -> verdict ``inconsistent`` (la conjecture echoue pour ce proxy)."""
    h = s.huang_conjecture_test(
        [0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
        2,
        lambda x: x,
        proxy_degree_fn=lambda states, n: 4.0,
    )
    assert h["deg_proxy"] == pytest.approx(4.0)
    assert h["threshold"] == pytest.approx(2.0)
    assert h["verdict"] == "inconsistent"


def test_huang_zero_proxy_yields_infinite_ratio():
    """Quand le proxy vaut 0, threshold=sqrt(0)=0 et le ratio s_max/threshold
    est defini comme +inf (garde division-par-zero du module). Le verdict reste
    ``consistent`` car s_max(>=0) >= threshold(=0)."""
    h = s.huang_conjecture_test(
        [0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
        2,
        lambda x: x,
        proxy_degree_fn=lambda states, n: 0.0,
    )
    assert h["threshold"] == pytest.approx(0.0)
    assert h["ratio"] == float("inf")
    assert h["verdict"] == "consistent"


# --------------------------------------------------------------------------- #
#  huang_conjecture_test : interne (cles, proxy, compte des transitions)
# --------------------------------------------------------------------------- #


def test_huang_uses_custom_proxy_not_default():
    """Quand ``proxy_degree_fn`` est fourni, le degre moyen par defaut n'est
    PAS calcule : ``deg_proxy`` reflete exactement la valeur du proxy custom."""
    h_custom = s.huang_conjecture_test(
        [0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
        2,
        lambda x: x,
        proxy_degree_fn=lambda states, n: 9.0,
    )
    assert h_custom["deg_proxy"] == pytest.approx(9.0)


def test_huang_returns_documented_keys():
    """Le dict de retour porte les 7 cles documentees (s_max, deg_proxy,
    threshold, ratio, n_transitions, n_visited, verdict)."""
    h = s.huang_conjecture_test([0, 1, 0, 1, 0, 1, 0, 1, 0, 1], 2, lambda x: x)
    assert set(h.keys()) == {
        "s_max", "deg_proxy", "threshold", "ratio",
        "n_transitions", "n_visited", "verdict",
    }


def test_huang_n_transitions_is_len_minus_one():
    """``n_transitions`` = nombre de transitions observees = len(states) - 1
    (les transitions sont les adjacences consecutives dans la trajectoire)."""
    states = [0, 1, 0, 1, 0, 1, 0, 1, 0, 1]  # len=10 -> 9 transitions
    h = s.huang_conjecture_test(states, 2, lambda x: x)
    assert h["n_transitions"] == len(states) - 1
    assert h["n_transitions"] == 9
