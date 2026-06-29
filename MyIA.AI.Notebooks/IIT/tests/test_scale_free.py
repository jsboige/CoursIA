"""Tests du diagnostic de signatures scale-free (module introduit dans ICT-7).

Verifient que la chaine (select_xmin -> hill_alpha -> KS -> comparaison de
modeles) classe correctement des cas de reference connus :
- une vraie loi de puissance synthetique -> scale-free, exposant retrouve ;
- une exponentielle -> echelle caracteristique ;
- un branchement critique (mu=1) -> scale-free, exposant ~ 3/2 (loi de Borel) ;
- un branchement sous-critique -> echelle caracteristique ;
- les deplacements du tri auto-organise (bornes par la taille) -> echelle
  caracteristique.

Stdlib + pytest. Le module ne depend que de la bibliotheque standard."""

import os
import random
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import scale_free as sf  # noqa: E402
from ict.self_sorting import SelfSortingArray, ALGOTYPES  # noqa: E402


def _deplacements_tri(n, n_runs, seed0=0):
    d = []
    for s in range(n_runs):
        vals = random.Random(seed0 + s).sample(range(n), n)
        algos = [ALGOTYPES[i % 2] for i in range(n)]
        arr = SelfSortingArray(vals, algotypes=algos, seed=s).run(max_steps=30000)
        p0, pf = arr.probe.positions[0], arr.probe.positions[-1]
        d.extend(abs(p0[c] - pf[c]) for c in p0)
    return [x for x in d if x >= 1]


def test_ccdf_is_proper_complementary_cdf():
    xs, ps = sf.ccdf([1, 1, 2, 3, 3, 3, 10])
    assert xs == [1, 2, 3, 10]
    assert ps[0] == pytest.approx(1.0)               # P(X >= min) = 1
    assert all(a >= b for a, b in zip(ps, ps[1:]))    # non croissante
    assert ps[-1] == pytest.approx(1 / 7)            # une seule obs >= 10


def test_hill_recovers_synthetic_exponent():
    rng = random.Random(0)
    ech = sf.sample_powerlaw(2.5, 1.0, 6000, rng)
    alpha = sf.hill_alpha(ech, xmin=1.0)
    assert alpha == pytest.approx(2.5, abs=0.15)


def test_powerlaw_sample_is_scale_free():
    rng = random.Random(1)
    ech = sf.sample_powerlaw(2.5, 1.0, 5000, rng)
    xm = sf.select_xmin(ech)
    d = sf.compare_powerlaw_exponential(ech, xmin=xm)
    assert "scale-free" in d["verdict"]
    assert d["loglik_ratio"] > 0


def test_exponential_sample_is_characteristic_scale():
    rng = random.Random(2)
    ech = sf.sample_exponential(0.5, 1.0, 5000, rng)
    xm = sf.select_xmin(ech)
    d = sf.compare_powerlaw_exponential(ech, xmin=xm)
    assert "echelle caracteristique" in d["verdict"]


def test_critical_branching_is_scale_free_with_borel_exponent():
    rng = random.Random(3)
    sizes = [s for s in sf.branching_avalanche_sizes(1.0, 15000, rng) if s < 100000]
    xm = sf.select_xmin(sizes, discrete=True)
    d = sf.compare_powerlaw_exponential(sizes, xmin=xm, discrete=True)
    assert "scale-free" in d["verdict"]
    assert d["alpha"] == pytest.approx(1.5, abs=0.2)   # tau = 3/2 (loi de Borel)


def test_subcritical_branching_has_characteristic_scale():
    rng = random.Random(4)
    sizes = sf.branching_avalanche_sizes(0.6, 15000, rng)
    xm = sf.select_xmin(sizes, discrete=True)
    d = sf.compare_powerlaw_exponential(sizes, xmin=xm, discrete=True)
    assert "echelle caracteristique" in d["verdict"]


def test_sorting_displacement_is_bounded_and_not_scale_free():
    n = 30
    dep = _deplacements_tri(n=n, n_runs=120, seed0=0)
    assert max(dep) <= n - 1                          # borne = echelle caracteristique
    xm = sf.select_xmin(dep, discrete=True)
    d = sf.compare_powerlaw_exponential(dep, xmin=xm, discrete=True)
    assert "echelle caracteristique" in d["verdict"]


def test_select_xmin_minimises_ks():
    rng = random.Random(5)
    sizes = [s for s in sf.branching_avalanche_sizes(1.0, 12000, rng) if s < 100000]
    xm = sf.select_xmin(sizes, discrete=True)
    ks_star = sf.ks_distance(sizes, xm, sf.hill_alpha(sizes, xm, discrete=True))
    # xmin=2 est une valeur observee abondante, donc consideree par select_xmin ;
    # le KS au xmin choisi ne peut donc pas etre pire que celui a xmin=2.
    assert sum(1 for s in sizes if s >= 2) >= 50
    ks_2 = sf.ks_distance(sizes, 2.0, sf.hill_alpha(sizes, 2.0, discrete=True))
    assert ks_star <= ks_2 + 1e-9


def test_rescaled_ccdf_divides_axis():
    data = [2, 4, 6, 8]
    xs0, _ = sf.ccdf(data)
    xs1, _ = sf.rescaled_ccdf(data, scale=2.0)
    assert xs1 == [x / 2.0 for x in xs0]


def test_compare_short_tail_is_indecidable():
    d = sf.compare_powerlaw_exponential([1.0], xmin=1.0)
    assert "indecidable" in d["verdict"]
