"""Tests du diagnostic borne du miss P2 « Parite esprit etendu » (case 9).

Verrouillent les observations du run pre-enregistre (issuecomment-5558855068)
: reproduction exacte du run historique, refutation des quatre causes, verdict
final DISSOCIATION_GRADUEE_REELLE. Le simulateur est deterministe par seed --
les valeurs sont figees a 1e-6 pres.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from ict.extended_mind_store import ExtendedAgent, FactWorld
from ict.phat_extended_mind_diag import (
    HISTORICAL_RHO_OTTO,
    NoPinOtto,
    otto_arm_metrics,
    run_diag,
)

RESULTS_PATH = (Path(__file__).parent.parent / "results"
                / "phat_extended_mind_diag_results.json")


@pytest.fixture(scope="module")
def diag() -> dict:
    return run_diag()


def test_gate_p0_reproduction_exacte(diag):
    """Le bras nominal reproduit le run historique a 1e-6 pres."""
    assert diag["gate_P0_reproduction"] is True
    for row, hist in zip(diag["repro_rows"], HISTORICAL_RHO_OTTO):
        assert row["rho"] == pytest.approx(hist, abs=1e-6)


def test_h1_epinglage_absorbe_moins_qu_estime(diag):
    """Sans epinglage : mediane 3.02 (bande predite [3.3, 4.5] ratee).

    L'estimation « ~3.9 sans adaptation » de la note d'origine est
    refutee par mesure : l'absorption n'explique pas le miss.
    """
    h1 = diag["hypotheses"]["H1_nopin"]
    assert h1["median"] == pytest.approx(3.0215727780367265, abs=1e-6)
    assert h1["ge3_count"] == 3
    assert h1["held"] is False


def test_h2_capacite_non_monotone(diag):
    """Scan k : medianes plates non-monotones, k=18 ne franchit pas.

    La lecture « force de localisation bornee par k/n = 6/24 » est
    refutee : k=18 (mesurable, n_consult >= 69/seed) reste a 0/5 >= 3.
    """
    h2 = diag["hypotheses"]["H2_scan_k"]
    expected = [2.6624451211528966, 2.463951753357483,
                2.7518477506898575, 2.488870874531171]
    assert h2["medians"] == pytest.approx(expected, abs=1e-6)
    assert h2["monotone"] is False
    assert h2["k18_ge3_count"] == 0
    assert h2["k18_measurable"] is True
    assert h2["held"] is False


def test_h3_miss_systematique_20_seeds(diag):
    """20 seeds : mediane 2.87 < 3, IQR 0.47 -- pas un artefact de puissance."""
    h3 = diag["hypotheses"]["H3_power"]
    assert h3["median"] == pytest.approx(2.866824106513697, abs=1e-6)
    assert h3["iqr"] == pytest.approx(0.46715641487711324, abs=1e-6)
    assert h3["power_artifact"] is False
    assert sum(1 for r in diag["power_rhos"] if r >= 3.0) == 4


def test_h4_miss_dans_numerateur(diag):
    """num = 2.90 < 3 : le miss vit dans la localisation, pas le den = 1.18."""
    h4 = diag["hypotheses"]["H4_decomposition"]
    assert h4["num_median"] == pytest.approx(2.9041367406962597, abs=1e-6)
    assert h4["den_median"] == pytest.approx(1.1786500026792175, abs=1e-6)
    assert h4["held"] is False


def test_verdict_dissociation_graduee_reelle(diag):
    """Branche 4 de l'arbre pre-enregistre : aucune cause tenue."""
    assert diag["verdict"] == "DISSOCIATION_GRADUEE_REELLE"


def test_results_json_synchro_avec_run(diag):
    """Le JSON committe est le run frais (livrable verrouille)."""
    committed = json.loads(RESULTS_PATH.read_text(encoding="utf-8"))
    assert committed["verdict"] == diag["verdict"]
    assert committed["gate_P0_reproduction"] == diag["gate_P0_reproduction"]
    for key in ("H1_nopin", "H2_scan_k", "H3_power", "H4_decomposition"):
        assert committed["hypotheses"][key] == pytest.approx(
            diag["hypotheses"][key]), key
    assert [r["rho"] for r in committed["repro_rows"]] == pytest.approx(
        [r["rho"] for r in diag["repro_rows"]])
    assert committed["power_rhos"] == pytest.approx(diag["power_rhos"])


def test_nopin_pins_toujours_vides():
    """NoPinOtto garde la lecture gatee mais vide la pression d'epinglage."""
    agent = NoPinOtto(n_keys=4, cache_k=1, seed=0)
    world = FactWorld(n_keys=4, seed=0)
    agent.store[0] = 1.0
    agent.cache.clear()  # forcer une consultation externe
    agent.p_read = 0.0  # echec garanti -> pression incrementee puis videe
    agent.answer(0)
    assert agent.pins == {}
    assert isinstance(agent, ExtendedAgent)


def test_determinisme_par_seed():
    a = otto_arm_metrics(3)
    b = otto_arm_metrics(3)
    assert a == b
