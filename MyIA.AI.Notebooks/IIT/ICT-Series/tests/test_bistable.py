"""Tests du modele bistable a bifurcation pli (module ICT-8).

Verifient les proprietes structurelles du modele de paturage de May : etat nu
toujours equilibre, bistabilite a faible pression, disparition du pli, coherence
potentiel/champ de vitesse, relaxation deterministe et reproductibilite de la
simulation stochastique.

Numpy + pytest."""

import os
import sys

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict.bistable import GrazingModel  # noqa: E402


@pytest.fixture
def model():
    return GrazingModel(r=1.0, K=10.0, h=1.0)


def test_bare_state_always_equilibrium(model):
    for c in (0.5, 1.5, 2.5, 3.5):
        assert float(model.rate(0.0, c)) == pytest.approx(0.0)


def test_bistable_at_low_grazing(model):
    # a faible c : deux etats stables alternatifs (haut vegetalise / bas surpature)
    # separes par un equilibre instable -> 3 racines positives ; x=0 est instable.
    eqs = model.equilibria(c=1.8)
    positives = [x for x, _ in eqs if x > 1e-6]
    stable_positives = [x for x, st in eqs if st and x > 1e-6]
    assert len(positives) == 3                  # bas, instable median, haut
    assert len(stable_positives) == 2           # bistabilite : bas + haut
    assert max(stable_positives) > 5.0          # le puits haut est "vegetalise"
    assert min(stable_positives) < 2.0          # le puits bas est "surpature"
    # l'etat vraiment vide n'est PAS un attracteur
    assert (0.0, False) in [(x, st) for x, st in eqs if x == 0.0]


def test_collapse_above_fold(model):
    # bien au-dela du pli : le puits HAUT a disparu, seul l'etat bas subsiste
    positives = [x for x, _ in model.equilibria(c=3.2) if x > 1e-6]
    highs = [x for x in positives if x > 3.0]
    assert len(highs) == 0                      # plus d'attracteur vegetalise
    assert len(positives) == 1                  # seul l'etat surpature bas reste
    assert positives[0] < 1.0


def test_find_fold_in_expected_range(model):
    c_fold = model.find_fold(1.5, 3.5, n=4000)
    assert 2.4 < c_fold < 2.8           # ~2.6 pour r=1,K=10,h=1


def test_potential_is_antiderivative_of_field(model):
    # dV/dx doit valoir -rate (le champ derive d'un potentiel)
    c = 2.0
    xs = np.linspace(0.2, 9.0, 50)
    dx = 1e-5
    dVdx = (model.potential(xs + dx, c) - model.potential(xs - dx, c)) / (2 * dx)
    assert np.allclose(dVdx, -model.rate(xs, c), atol=1e-3)


def test_potential_minima_are_stable_equilibria(model):
    # le puits haut stable doit etre un minimum local du potentiel
    c = 1.8
    stables = sorted(x for x, st in model.equilibria(c) if st and x > 1e-6)
    xhigh = stables[-1]
    V = model.potential
    assert V(xhigh, c) < V(xhigh - 0.3, c)
    assert V(xhigh, c) < V(xhigh + 0.3, c)


def test_relax_converges_to_stable_equilibrium(model):
    c = 1.8
    stable = sorted(x for x, st in model.equilibria(c) if st and x > 1e-6)
    xlow, xhigh = stable[0], stable[-1]
    mid = [x for x, st in model.equilibria(c) if not st and x > 1e-6][0]
    # de part et d'autre de l'equilibre instable median => bassins distincts
    assert model.relax(xhigh + 1.0, c) == pytest.approx(xhigh, abs=0.05)
    assert model.relax(mid + 0.5, c) == pytest.approx(xhigh, abs=0.05)
    # sous le seuil instable, on tombe vers le puits bas (surpature), pas vers 0
    assert model.relax(0.2, c) == pytest.approx(xlow, abs=0.05)
    assert model.relax(mid - 0.2, c) == pytest.approx(xlow, abs=0.05)


def test_simulate_sde_reproducible_and_bounded(model):
    a = model.simulate_sde(c=1.8, x0=7.0, sigma=0.05, dt=0.01, T=5000, seed=11)
    b = model.simulate_sde(c=1.8, x0=7.0, sigma=0.05, dt=0.01, T=5000, seed=11)
    assert np.array_equal(a, b)                 # meme graine => identique
    assert np.all(a >= 0.0)                     # reflexion a 0
    assert a[-2000:].mean() > 5.0               # reste dans le puits haut


def test_simulate_ramp_tips_over(model):
    xs, cs = model.simulate_ramp(c0=1.7, c1=2.9, x0=7.5, sigma=0.04,
                                 dt=0.01, T=80000, seed=12)
    assert cs[0] == pytest.approx(1.7)
    assert xs[0] > 5.0                          # part dans le puits haut
    assert xs[-1] < 1.0                         # a bascule vers l'etat nu


# --------------------------------------------------------------------------- #
#  Edge-cases migrés depuis ict/tests/test_bistable.py (consolidation, MED/test) #
#                                                                               #
#  Propriétés non couvertes ci-dessus : cohérence equilibria() <-> rate(),      #
#  instabilite de l'etat nu via rate_prime, borne isfinite (pas d'explosion     #
#  numerique), lien derivee-seconde <-> stabilite (stable ssi rate_prime < 0).  #
# --------------------------------------------------------------------------- #
def test_equilibria_are_roots_of_rate(model):
    """Tout equilibre x* retourne par equilibria(c) verifie rate(x*, c) ~= 0.

    Valide la coherence interne : equilibria() renvoie bien des points fixes
    du flot (x=0 seul est testé par test_bare_state_always_equilibrium ci-dessus ;
    ce gate itère sur tous les équilibres retournés, y compris le puits haut
    et le col médian).
    """
    for c in [1.0, 2.0, 2.5, 3.0]:
        for x_star, _stable in model.equilibria(c):
            assert abs(model.rate(x_star, c)) < 1e-6, (
                f"rate({x_star}, c={c}) ~= 0 attendu (équilibre), "
                f"got {model.rate(x_star, c)}"
            )


def test_origin_is_unstable(model):
    """rate_prime(0, c) > 0 : l'etat nu est instable (response type III en x^2).

    La response de broutage type III s'annule en x^2 pres de zero, donc la
    vegetation repart toujours du quasi-neant (point documente docstring).
    """
    for c in [1.0, 2.0, 3.0]:
        rp0 = model.rate_prime(0.0, c)
        assert rp0 > 0, f"x=0 instable (rate_prime(0,c)>0), got {rp0} pour c={c}"


def test_stability_matches_rate_prime_sign(model):
    """Un equilibre est stable ssi rate_prime(x*, c) < 0 (puits = min de V),
    instable ssi >= 0 (col = max de V). La signature de la derivee seconde du
    potentiel ``-rate_prime`` discrimine puits/col (lien direct à la théorie
    des bifurcations, distinct de la caractérisation via le potentiel de
    test_potential_minima_are_stable_equilibria).
    """
    for c in [1.5, 2.0, 2.5]:
        for x_star, stable in model.equilibria(c):
            rp = model.rate_prime(x_star, c)
            if stable:
                assert rp < 0, (
                    f"équilibre stable {x_star} (c={c}) doit avoir rate_prime < 0, got {rp}"
                )
            else:
                assert rp >= 0, (
                    f"équilibre instable {x_star} (c={c}) doit avoir rate_prime >= 0, got {rp}"
                )


def test_simulate_sde_shape_and_finite(model):
    """La trajectoire a la bonne taille et reste finie (pas d'explosion numerique).

    test_simulate_sde_reproducible_and_bounded ci-dessus couvre la répétabilité
    et la réflexion (x >= 0) ; ce gate vérifie explicitement l'absence
    d'explosion numérique (isfinite) et la shape exacte.
    """
    traj = model.simulate_sde(c=2.0, x0=5.0, sigma=0.5, dt=0.05, T=1000, seed=7)
    assert traj.shape == (1000,)
    assert np.all(np.isfinite(traj)), "trajectoire doit rester finie"
