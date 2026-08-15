"""Test de non-regression pour Issue #9764 : sous f injective et W dense,
la sensibilite mesure trivialement le degre (k-1). Test de garde que
f non-injective discrimine reellement.

Verrouillage : un worktree futur qui retablirait la confusion ou
qui reintroduirait une fonction d'etat injective par defaut ferait
echouer ce test -- le proxy ne discrimine plus.
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

from ict import sensitivity as sens  # noqa: E402


def test_parity_function_on_cycle_not_saturated():
    """Sur un cycle strict k=4 (0->1->2->3), avec f(x) = x % 2 (parite, NON
    injective : f(0)=f(2)=0, f(1)=f(3)=1), la sensibilite discrimine :

    - Noeud 0 : voisins 1 (f=1) et 3 (f=1) -> 2 voisins differents.
    - Noeud 1 : voisins 0 (f=0) et 2 (f=0) -> 2 voisins differents.
    - Noeud 2 : voisins 1 (f=1) et 3 (f=1) -> 2 voisins differents.
    - Noeud 3 : voisins 0 (f=0) et 2 (f=0) -> 2 voisins differents.

    Donc max=mean=2.0, std=0.0. Ce n'est PAS k-1 = 3. C'est la preuve
    que le proxy discrimine reellement quand f n'est pas injective.
    """
    states = [0, 1, 2, 3] * 30  # 120 ticks cycle parfait k=4
    dist = sens.sensitivity_distribution(states, 4, lambda x: x % 2)
    assert dist["max"] == pytest.approx(2.0), (
        f"f=parity sur cycle k=4 devrait donner max=2.0 (k-1)/2, "
        f"pas k-1=3.0. Recu max={dist['max']}. Si ce test echoue, "
        f"le wiring a re-introduit la degenerescence d'identite."
    )
    assert dist["mean"] == pytest.approx(2.0)
    assert dist["std"] == pytest.approx(0.0)


def test_identity_function_on_sparse_graph_saturated():
    """Test miroir du precedent : avec f(x)=x (injective) sur un graphe
    k-1 regulier (random walk de 120 ticks sur k=4), la sensibilite
    sature trivialement a k-1 = 3. C'est le **comportement attendu**,
    pas un defaut -- il est documente dans la docstring du module
    (paragraphe "Domaine de validite", c.9706, Issue #9764).
    """
    rng = np.random.default_rng(0)
    states = rng.integers(0, 4, size=120).tolist()
    dist = sens.sensitivity_distribution(states, 4, lambda x: x)
    assert dist["max"] == pytest.approx(3.0), (
        f"f=identity sur marche aleatoire k=4 sature trivialement a k-1=3.0. "
        f"Recu max={dist['max']}. Si != 3.0, la degenerescence documentee "
        f"a change -- mettre a jour la docstring."
    )
    assert dist["mean"] == pytest.approx(3.0)
    assert dist["std"] == pytest.approx(0.0)


def test_non_injective_function_real_discrimination():
    """Sur la meme marche aleatoire (k=6, 120 ticks, 5 graines), avec
    f(x) = x % 3 (partition en 3 classes : {0,3}, {1,4}, {2,5}), la
    distribution de sensibilite N'est PAS constante :

    - f=0 (noeuds 0, 3) : 4 voisins sur 5 sont en f!=0 -> s=4 ou 5.
    - f=1 (noeuds 1, 4) : 4 voisins sur 5 sont en f!=0 -> s=4 ou 5.
    - f=2 (noeuds 2, 5) : 4 voisins sur 5 sont en f!=0 -> s=4 ou 5.

    Mais comme certains voisins peuvent etre dans la meme classe par
    chance d'echantillonnage (les paires (0,3), (1,4), (2,5) ont une
    probabilite non nulle d'etre observees en transition), la
    distribution peut montrer de la variation. Ce test VERROUILLE
    qu'au moins une graine donne un std > 0 OU un max < k-1.
    """
    seeds = [0, 1, 7, 42, 99]
    n_non_trivial = 0
    for seed in seeds:
        rng = np.random.default_rng(seed)
        states = rng.integers(0, 6, size=120).tolist()
        dist = sens.sensitivity_distribution(states, 6, lambda x: x % 3)
        # max peut etre 4 ou 5 selon que la paire intra-classe est observee.
        # Si on observe au moins un std > 0 OU un max < 5, c'est non-trivial.
        if dist["std"] > 0 or dist["max"] < 5.0:
            n_non_trivial += 1
    # Sur 5 graines avec un graphe dense, on doit observer au moins
    # UNE graine non-triviale (variation de l'echantillonnage).
    assert n_non_trivial >= 1, (
        "Avec f non-injective (x % 3) sur marche aleatoire k=6, la "
        "distribution devrait montrer de la variation sur au moins "
        "une graine. Si 0/5 -> le proxy ne discrimine plus, "
        "regression sur la portee informative."
    )
