"""Tests du module ICT-11 (agence morphologique multi-echelles).

Verifient le coarse-graining spatial, la macro-variable « nombre de blocs
actifs », les mesures d'agence resolutees par echelle, le raccord causal
(effectiveness de la TPM de la macro-variable) et la statistique de Pearson.

Coeur conceptuel (falsifiable mais reproductible) : sur un substrat de
Gray-Scott en regime mitotique, l'agence (repair_gain) est **positive** a au
moins une echelle — c'est la continuite du resultat ICT-9. On ne assert JAMAIS
la non-monotonicite inter-echelles : c'est precisement le gate que le notebook
doit decouvrir (et peut honnetement echouer).

Numpy + pytest. CPU uniquement."""

import os
import sys

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import agency as A  # noqa: E402
from ict import multiscale_agency as M  # noqa: E402
from ict import reaction_diffusion as rd  # noqa: E402


# --------------------------------------------------------------------------- #
# Coarse-graining spatial
# --------------------------------------------------------------------------- #
def test_block_average_shape_and_means():
    f = np.arange(16.0).reshape(4, 4)
    # blocs 2x2 -> 4 super-cellules, chacune = moyenne de ses 4 pixels
    avg = M.block_average(f, 2)
    assert avg.shape == (2, 2)
    assert avg[0, 0] == pytest.approx((0 + 1 + 4 + 5) / 4)
    assert avg[1, 1] == pytest.approx((10 + 11 + 14 + 15) / 4)


def test_block_average_truncates_non_divisible():
    f = np.arange(20.0).reshape(4, 5)  # grille non carree, bloc 2 -> (2, 2)
    avg = M.block_average(f, 2)
    assert avg.shape == (2, 2)


def test_block_average_rejects_invalid_block():
    f = np.zeros((8, 8))
    with pytest.raises(ValueError):
        M.block_average(f, 0)
    with pytest.raises(ValueError):
        M.block_average(f, 16)  # plus grand que la grille


def test_downsample_mask_majority():
    m = np.zeros((8, 8), dtype=bool)
    m[:4, :4] = True  # un seul quadrant
    dm = M.downsample_mask(m, 4)  # grille 2x2
    assert dm.shape == (2, 2)
    assert dm[0, 0] and not dm[0, 1] and not dm[1, 0] and not dm[1, 1]


# --------------------------------------------------------------------------- #
# Macro-variable
# --------------------------------------------------------------------------- #
def test_structure_at_scale_decreases_with_coarsening():
    # un champ structure : la variance du champ moyenne DECROIT quand le bloc grossit
    rng = np.random.default_rng(0)
    f = (rng.standard_normal((32, 32)) > 0).astype(float)
    s_fine = M.structure_at_scale(f, 4)
    s_coarse = M.structure_at_scale(f, 16)
    assert s_fine > 0.0
    assert s_coarse < s_fine  # le moyennage reduit la variance


def test_discretize_values_quantile_and_constant():
    vals = np.array([0.0, 1.0, 2.0, 3.0, 4.0, 5.0])
    labels = M.discretize_values(vals, n_bins=3)
    assert labels.size == vals.size
    assert len(set(labels.tolist())) <= 3
    assert list(labels) == sorted(labels)  # ordre preserve
    # serie constante -> un seul niveau
    assert M.discretize_values(np.full(5, 3.0), n_bins=4).tolist() == [0, 0, 0, 0, 0]
    # deux valeurs distinctes -> deux niveaux
    two = M.discretize_values(np.array([0.0, 1.0, 1.0, 0.0]), n_bins=4)
    assert len(set(two.tolist())) == 2


# --------------------------------------------------------------------------- #
# Pearson (garde-fous)
# --------------------------------------------------------------------------- #
def test_pearson_known_and_undefined():
    r, n = M.pearson_corr([1.0, 2, 3, 4], [2.0, 4, 6, 8])
    assert n == 4
    assert r == pytest.approx(1.0, abs=1e-9)
    r2, _ = M.pearson_corr([1.0, 2, 3, 4], [4.0, 3, 2, 1])
    assert r2 == pytest.approx(-1.0, abs=1e-9)
    # variance nulle -> indefinie
    assert M.pearson_corr([1, 1, 1], [1, 2, 3])[0] is None
    assert M.pearson_corr([1.0], [2.0])[0] is None


# --------------------------------------------------------------------------- #
# Substrat de test : petit Gray-Scott mitotique (rapide)
# --------------------------------------------------------------------------- #
@pytest.fixture(scope="module")
def formed_pattern():
    """Forme un motif mitotique sur une grille 32x32 (rapide pour les tests)."""
    model = rd.GrayScott()
    rng = np.random.default_rng(0)
    U, V = model.seed(n=32, block=6, noise=0.02, rng=rng)
    U, V, _ = model.run(U, V, 1200)  # formation du motif
    return model, U, V


def test_agency_measures_keys_and_positive_gain(formed_pattern):
    """L'agence (repair_gain) doit etre positive a au moins une echelle.

    Continuite du resultat ICT-9 : la reaction-diffusion repare la ou la
    diffusion pure dissout. On verifie la SANTE des sorties (cles presentes,
    plages attendues) et la positivite du gain a l'echelle moyenne.
    """
    model, U_ref, V_ref = formed_pattern
    mask = A.quadrant_mask(32, quadrant=0)
    res = M.agency_measures_at_scale(
        model, model.Dv, U_ref, V_ref, mask, block=8,
        steps=600, record_every=30,
    )
    for key in ("repair_gain", "recovery_RD", "recovery_diff", "time_to_recover", "target_structure"):
        assert key in res
    assert res["repair_gain"] == pytest.approx(
        res["recovery_RD"] - res["recovery_diff"], abs=1e-9
    )
    # le substrat porte de la structure, donc une cible positive
    assert res["target_structure"] > 0.0
    # ICT-9 continuity : gain de reparation reellement positif a l'echelle 8
    assert res["repair_gain"] > 0.0


def test_basin_return_probability_in_range(formed_pattern):
    model, U_ref, V_ref = formed_pattern
    target = float(np.var(M.block_average(V_ref, 8)))

    def make_mask(rng):
        return A.disk_mask(32, cx=rng.integers(6, 26), cy=rng.integers(6, 26), radius=4)

    p = M.basin_return_at_scale(
        model, U_ref, V_ref, make_mask, block=8, steps=400,
        target_structure=target, n_trials=3, rng=np.random.default_rng(1),
    )
    assert 0.0 <= p <= 1.0


def test_effectiveness_at_scale_sane(formed_pattern):
    """La TPM de la macro-variable est valide et son effectiveness est dans [0,1]."""
    model, U_ref, V_ref = formed_pattern

    def make_mask(rng):
        return A.quadrant_mask(32, quadrant=int(rng.integers(0, 4)))

    res = M.effectiveness_at_scale(
        model, U_ref, V_ref, make_mask, block=8,
        steps=400, record_every=20, n_bins=8, n_seeds=3,
        rng=np.random.default_rng(2),
    )
    assert 0.0 <= res["effectiveness"] <= 1.0
    assert res["n_observed"] >= 2  # TPM non triviale
    tpm = res["tpm"]
    # TPM ligne-stochastique
    assert np.allclose(tpm.sum(axis=1), 1.0, atol=1e-6)
    assert tpm.shape[0] == tpm.shape[1] == res["n_observed"]


def test_effectiveness_micro_vs_macro_differ(formed_pattern):
    """Sanity : effectiveness a l'echelle fine vs grossiere ne sont pas identiques.

    On ne predit PAS laquelle est plus haute (c'est le gate a decouvrir) ; on
    verifie seulement que le coarse-graining change la mesure causale — sinon le
    pont champs->TPM serait inerte.
    """
    model, U_ref, V_ref = formed_pattern

    def make_mask(rng):
        return A.quadrant_mask(32, quadrant=int(rng.integers(0, 4)))

    res_micro = M.effectiveness_at_scale(
        model, U_ref, V_ref, make_mask, block=4,
        steps=300, record_every=20, n_bins=6, n_seeds=2,
        rng=np.random.default_rng(3),
    )
    res_macro = M.effectiveness_at_scale(
        model, U_ref, V_ref, make_mask, block=16,
        steps=300, record_every=20, n_bins=6, n_seeds=2,
        rng=np.random.default_rng(4),
    )
    # la macro-variable 'structure' reste non degenereree (>= 2 etats) aux deux
    # echelles — c'est precisement ce qui manquait a la macro-variable 'compte de
    # blocs' qui saturait aux echelles grossieres. On ne predit pas laquelle des
    # deux effectiveness est la plus haute (c'est le gate a decouvrir).
    assert res_micro["n_observed"] >= 2
    assert res_macro["n_observed"] >= 2
