"""Tests du banc case 26 (Comolatti & Hoel 2022, emergence causale repandue).

Croisements du banc contre l'organe (ict.causal_emergence), contre le temoin
verifie du case 25 (ict.hoel_causal_emergence) et contre les formes fermees
scellees au pre-enregistrement (docs/ict/comolatti-hoel-widespread-
pre-enregistrement.md, commit 0f3a704b575).
"""

import json
import pathlib

import numpy as np
import pytest

from ict.causal_emergence import partition_profile
from ict.comolatti_hoel_widespread import (
    BIPARTITE_GROUPS,
    PANEL_ALL,
    bipartite_tpm,
    cs_direct,
    cs_primitives,
    run_all,
    self_copy_tpm,
    spearman,
    system_values,
)
from ict.hoel_causal_emergence import (
    _self_copy_tpm,
    calibrate_fig4,
    element_pair_groups,
    tpm_from_gates,
)

RESULTS_JSON = (pathlib.Path(__file__).parent.parent / "results"
                / "comolatti_hoel_widespread_results.json")


def test_self_copy_matches_witness_h4():
    """Le temoin S2 reconstruit localement egale le constructeur du temoin
    H4 du case 25 (croisement contre la source, en lecture seule)."""
    mine = self_copy_tpm(4, 0.1)
    ref = _self_copy_tpm(4, 0.1)
    np.testing.assert_allclose(mine, ref, atol=1e-15)


def test_bipartite_corners():
    """Coins scelles : eps=0 bijection complement, eps=1 uniforme sur le
    groupe cible ; le macro (organe) est la porte NOT a chaque eps."""
    bij = bipartite_tpm(0.0)
    for c in range(16):
        assert bij[c, 15 - c] == 1.0
    uni = bipartite_tpm(1.0)
    for c in range(16):
        targets = range(8, 16) if c < 8 else range(0, 8)
        for e in range(16):
            expected = 1.0 / 8.0 if e in targets else 0.0
            assert uni[c, e] == pytest.approx(expected)
    not_gate = np.array([[0.0, 1.0], [1.0, 0.0]])
    for eps in (0.0, 0.25, 0.5, 0.75, 1.0):
        macro = partition_profile(bipartite_tpm(eps), BIPARTITE_GROUPS)["macro_tpm"]
        np.testing.assert_allclose(macro, not_gate, atol=1e-12)


def test_g2_closed_forms():
    """Formes fermees scellees : bijection en cycle et TPM uniforme."""
    cycle = np.zeros((4, 4))
    for i in range(4):
        cycle[i, (i + 1) % 4] = 1.0
    sys = system_values(cycle)
    assert sys["eells"] == pytest.approx(1.0)
    assert sys["galton"] == pytest.approx(3.0 / 16.0)
    assert sys["suppes"] == pytest.approx(0.75)
    assert sys["suppes2"] == pytest.approx(4.0)
    assert sys["lewis"] == pytest.approx(1.0)
    assert sys["cheng"] == pytest.approx(1.0)

    uni = np.full((6, 6), 1.0 / 6.0)
    sys_u = system_values(uni)
    for name in ("eells", "galton", "suppes", "lewis", "cheng"):
        assert sys_u[name] == pytest.approx(0.0, abs=1e-12)
    assert sys_u["suppes2"] == pytest.approx(1.0)


def test_dual_impl_agreement():
    """Porte G1 : formule directe et substitution des primitives coincident
    sur le support commun, sur les deux familles de substrats bruites."""
    for tpm in (bipartite_tpm(0.25), self_copy_tpm(4, 0.1)):
        d, p = cs_direct(tpm), cs_primitives(tpm)
        for name in PANEL_ALL:
            mask = ~np.isnan(d[name]) & ~np.isnan(p[name])
            assert mask.any()
            dev = float(np.max(np.abs(d[name][mask] - p[name][mask])))
            assert dev < 1e-12, f"{name}: dev={dev}"


def test_h1b_saturation_exact():
    """Sur S1 (micro deterministe), Cheng sature a 1 aux deux echelles :
    delta exactement nul — l'egalite ponctuelle scellee (H1b)."""
    cal4 = calibrate_fig4()
    s1 = tpm_from_gates(6, cal4["gates"], noise=0.0)
    macro = partition_profile(s1, element_pair_groups(6, [(0, 1), (2, 3), (4, 5)]))
    assert system_values(s1)["cheng"] == pytest.approx(1.0)
    assert system_values(macro["macro_tpm"])["cheng"] == pytest.approx(1.0)


def test_lewis_full_support_identity():
    """Identite analytique mesurable : sur une TPM a SUPPORT PLEIN, la valeur
    systeme de Lewis sous max-entropie est identiquement nulle (la somme
    ponderee des contrastes est exactement nulle) — les ~1e-16 du JSON sur S2
    sont cette identite, pas un defaut de precision du banc. La bipartite S3
    est support par blocs (colonnes du groupe source a zero) : son Lewis
    systeme non nul est attendu."""
    uni = np.full((6, 6), 1.0 / 6.0)
    for tpm in (self_copy_tpm(4, 0.1), uni):
        assert abs(system_values(tpm)["lewis"]) < 1e-12
    assert system_values(bipartite_tpm(0.5))["lewis"] == pytest.approx(0.5333333333)


def test_spearman_hand_reference():
    """Spearman a rangs moyens : references calculees a la main."""
    assert spearman([1, 2, 3], [10, 20, 30]) == pytest.approx(1.0)
    assert spearman([1, 2, 3], [30, 20, 10]) == pytest.approx(-1.0)
    # ties moyens : x = [0,0,1] -> rangs [1.5,1.5,3] ; y -> [1,2.5,2.5]
    # rho = 0.75 / 1.5 = 0.5
    assert spearman([0, 0, 1], [0, 1, 1]) == pytest.approx(0.5)


def test_results_json_consistent_with_module():
    """Le JSON commite et le module courant rendent le meme verdict global,
    portes toutes vertes, instrument exact (stochastic: false)."""
    assert RESULTS_JSON.exists(), "resultats non generes"
    data = json.loads(RESULTS_JSON.read_text(encoding="utf-8"))
    assert data["stochastic"] is False
    assert all(g["ok"] for g in data["gates"].values())
    assert data["global_verdict"] in ("SOUTENU", "REFUTE", "PARTIEL", "NON_CONCLUSIF")
    fresh = run_all()
    assert fresh["global_verdict"] == data["global_verdict"]
    assert {k: v["verdict"] for k, v in fresh["hypotheses"].items()} == {
        k: v["verdict"] for k, v in data["hypotheses"].items()
    }
