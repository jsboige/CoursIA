"""Tests du jouet « réduction objective Orch-OR » (:mod:`ict.penrose_orch_or`, case 24, #8182).

Chaque test ancre une clause du scellé v1 (+ amendement v2 du 2026-11-20) sur
une propriété mécanique du banc — les bandes vivent dans ``BANDS`` du module,
source unique. Pattern hérité de la famille : bootstrap ``sys.path``
module-level, pas de fixtures, tolérances commentées, gates falsifiables.

Substance vérifiée :

- Constantes : n_c équivalent-masse ≈ 9167, E_c ≈ 1,06×10⁻⁴⁷ J (formule p.61) ;
- Réseau : plancher dur respecté, imbrication des préfixes (K-ladder = densification) ;
- P3a : linéarité Fermi à la précision machine + porte croisés/propres ≤ 10⁻⁶ ;
- P3b : blob quadratique — chat ratio dans [0.80, 1.05], doublement (4096, 8192)
  dans [3.5, 4.5] à étendue fixe (correction de plancher < 5 %) ;
- P3c : N(τ/2)/N(τ) = 2.00 ± 0.02 en Fermi (exact par linéarité), 2^(1/α_eff)
  dans [1.39, 1.49] en blob — l'« hésitation » 2×/√2 est une séparation de régimes ;
- P3d : confrontation analytique aux nombres publiés (2×10¹⁰, ~10⁹, ratio 20) ;
- P1/P2 : loi de vie et effet dual sur ensembles M réduits (tests rapides) ;
- Null (a) : la calibration sélectionne M = 40 000 (demi-largeur Wilson ≤ 0.005) ;
- Verdict : borné — SUPPORTED exige les cinq prédictions ET les deux nulls.
"""

from __future__ import annotations

import math
import os
import sys

import numpy as np
import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from ict import penrose_orch_or as po  # noqa: E402


# ---------------------------------------------------------------------------
#  Constantes gelées — arithmétique de la source reproduite.
# ---------------------------------------------------------------------------
def test_constants_match_source_arithmetic():
    """n_c = m_t/m_c ≈ 9166,7 (équivalent-masse, scellé §6.3) et
    E_c = G·m_c²/a_c ≈ 1,06×10⁻⁴⁷ J ; E par tubuline ≈ 9,72×10⁻⁴⁴ J."""
    assert po.N_CARBON == pytest.approx(9166.67, abs=0.5)
    assert po.E_CARBON == pytest.approx(1.060e-47, rel=2e-3)
    assert po.E_TUBULIN_FERMI == pytest.approx(9.72e-44, rel=2e-3)


def test_n25ms_matches_published_order_of_magnitude():
    """N(25 ms) ≈ 4,3×10¹⁰ — facteur ~2,2 vs « roughly 2 × 10¹⁰ » (bande P3d [1.5, 3.5])."""
    n25 = po.required_tubulins_fermi(25e-3)
    assert n25 == pytest.approx(4.34e10, rel=2e-2)
    conf = po.confrontation_source()
    assert conf["ok"], f"P3d attendu OK, reçu {conf}"
    assert conf["n25_over_n500"] == pytest.approx(20.0, abs=0.1)


def test_constat_eg_quoted_vs_hbar():
    """Le constat documenté : E_G cité 10⁻¹⁰ eV vs ħ/25 ms ≈ 2,63×10⁻¹⁴ eV
    (facteur ~3 800) — rapporté sans bande (scellé §6.4)."""
    conf = po.confrontation_source()
    assert conf["constat"]["hbar_over_25ms_ev"] == pytest.approx(2.63e-14, rel=2e-2)
    assert conf["constat"]["factor"] == pytest.approx(3800.0, rel=0.05)


# ---------------------------------------------------------------------------
#  Réseau : plancher dur + imbrication des préfixes.
# ---------------------------------------------------------------------------
def test_disc_sampling_respects_hardcore_and_disc():
    sites = po.sample_disc(7, 512, po.DIAM_BLOB, po.HARDCORE_BLOB)
    d2 = np.sum((sites[:, None, :] - sites[None, :, :]) ** 2, axis=-1)
    np.fill_diagonal(d2, np.inf)
    assert d2.min() >= po.HARDCORE_BLOB**2 - 1e-24, "plancher dur 2 nm violé"
    assert np.all(np.hypot(sites[:, 0], sites[:, 1]) <= po.DIAM_BLOB / 2)


def test_k_ladder_prefixes_are_nested():
    """L'échelle de densification = préfixes du même processus par graine."""
    full = po.sample_disc(7, 256, po.DIAM_FERMI, po.HARDCORE_FERMI)
    prefix = po.sample_disc(7, 64, po.DIAM_FERMI, po.HARDCORE_FERMI)
    assert np.array_equal(prefix, full[:64])


# ---------------------------------------------------------------------------
#  P3a — Fermi linéaire, porte croisés/propres.
# ---------------------------------------------------------------------------
def test_fermi_linearity_and_cross_gate():
    """E_G^F = K·n_c·E_c à la précision machine, croisés/propres ≤ 10⁻⁶
    (attendu ~10⁻¹² — la porte a cinq ordres de marge), 2 variantes."""
    sites = po.sample_disc(7, 256, po.DIAM_FERMI, po.HARDCORE_FERMI)
    rng = np.random.default_rng(61)
    for k in (64, 256):
        common = np.tile(np.array([1.0, 0.0]), (k, 1))
        indep = rng.normal(size=(k, 2))
        indep /= np.linalg.norm(indep, axis=1, keepdims=True)
        for dirs in (common, indep):
            res = po.eg_fermi(sites[:k], dirs)
            assert res["linearity_ratio"] == pytest.approx(1.0, abs=1e-6)
            assert res["cross_over_self"] <= po.BANDS["p3a_cross_gate"]


def test_fermi_required_tubulins_linear_in_tau():
    """Fermi : N(τ/2)/N(τ) = 2.00 exact (linéarité analytique, P3c-Fermi)."""
    ratio = po.required_tubulins_fermi(12.5e-3) / po.required_tubulins_fermi(25e-3)
    assert ratio == pytest.approx(2.0, abs=po.BANDS["p3c_fermi_hi"] - 2.0)


# ---------------------------------------------------------------------------
#  P3b/P3c — blob quadratique à étendue fixe (amendement v2).
# ---------------------------------------------------------------------------
_BLOB_CACHE: dict[int, dict[int, float]] = {}


def _blob_energies(seed: int) -> dict[int, float]:
    if seed not in _BLOB_CACHE:
        lattice = po.sample_disc(seed, 8192, po.DIAM_BLOB, po.HARDCORE_BLOB)
        _BLOB_CACHE[seed] = {k: po.eg_blob(lattice[:k])["total"] for k in (4096, 8192)}
    return _BLOB_CACHE[seed]


@pytest.mark.parametrize("seed", [0, 1, 7])
def test_blob_cat_ratio_in_band(seed):
    """E_G^B/[2G·E_AA] ∈ [0.80, 1.05] au régime chat D = 8·R_lat (v2)."""
    eg = _blob_energies(seed)
    for k in (4096, 8192):
        lattice = po.sample_disc(seed, 8192, po.DIAM_BLOB, po.HARDCORE_BLOB)
        res = po.eg_blob(lattice[:k])
        assert po.BANDS["p3b_cat_lo"] <= res["cat_ratio"] <= po.BANDS["p3b_cat_hi"], (
            f"cat_ratio hors bande à K={k}, seed={seed}: {res['cat_ratio']:.3f}")


@pytest.mark.parametrize("seed", [0, 1, 7])
def test_blob_doubling_in_band(seed):
    """Doublement (4096 → 8192) ∈ [3.5, 4.5] — quadratique corrigée du
    plancher (prédit ~3.86, amendement v2 point 2)."""
    eg = _blob_energies(seed)
    doubling = eg[8192] / eg[4096]
    assert po.BANDS["p3b_doubling_lo"] <= doubling <= po.BANDS["p3b_doubling_hi"], (
        f"doublement hors bande seed={seed}: {doubling:.3f}"
    )


@pytest.mark.parametrize("seed", [0, 1, 7])
def test_blob_required_ratio_sqrt2_band(seed):
    """N_B(τ/2)/N_B(τ) ∈ [1.39, 1.49] (bande v2 : √2 élargie, α_eff ≈ 1.95)."""
    eg = _blob_energies(seed)
    tau8192 = po.HBAR / eg[8192]
    ratio = po.required_tubulins_blob(eg, tau8192) / po.required_tubulins_blob(eg, 2 * tau8192)
    assert po.BANDS["p3c_blob_lo"] <= ratio <= po.BANDS["p3c_blob_hi"], (
        f"ratio blob hors bande seed={seed}: {ratio:.4f}"
    )


# ---------------------------------------------------------------------------
#  P1/P2 — loi de vie et effet dual (ensembles réduits pour le test).
# ---------------------------------------------------------------------------
def test_lifetime_law_holds():
    """M = 40 000 (calibré) : moyenne ET demi-vie dans les bandes P1."""
    res = po.lifetime_checks(42, 40_000)
    assert res["ok"], f"P1 attendu OK : {res['ladder']}"
    for row in res["ladder"].values():
        assert row["halflife_ratio"] == pytest.approx(math.log(2), abs=0.03)
        assert row["survival_ln2"] == pytest.approx(0.5, abs=0.02)


def test_dual_effect_couple_linked():
    """P2 : le même 1/(1+η) règle τ̂(η)/τ̂(0) ET la rétention, null b neutre."""
    res = po.dual_effect_checks(42, 40_000)
    assert res["ok"], f"P2 attendu OK : {res['by_eta']}"
    assert res["null_b_ok"]
    assert res["null_b"] == [True] * len(po.ETA_GRID)


def test_p_effective_control_is_exactly_neutral():
    """b = 0.5 → P(A) = 0.5 exactement quel que soit η (contrôle exclu, scellé §4)."""
    for eta in po.ETA_GRID:
        assert po._p_effective(0.5, eta) == pytest.approx(0.5)


# ---------------------------------------------------------------------------
#  Calibration + verdict borné.
# ---------------------------------------------------------------------------
def test_calibration_selects_m40000():
    """La grille sélectionne M = 40 000 (0.98/√M = 0.0049 ≤ 0.005 ; 20 000
    donne 0.0069 > 0.005) — null (a) tenu sur les graines 11/22/33."""
    calib = po.calibrate()
    assert calib["m_selected"] == 40_000
    assert calib["null_a_ok"]


def test_verdict_bounded_supported_path():
    """Verdict SUPPORTED : cinq prédictions + deux nulls — construit, pas simulé."""
    def seed_stub(ok=True, doubling=3.9, cat=0.91):
        p3b_ok = ok and 3.5 <= doubling <= 4.5 and 0.80 <= cat <= 1.05
        return {
            "p1": {"ok": ok, "ladder": {"25": {"mean_ratio": 1.0, "halflife_ratio": 0.693}}},
            "p2": {"ok": ok, "null_b_ok": True,
                   "by_eta": {"1": {"ok_tau": True, "ok_retention": True}}},
            "p3a": {"ok": True, "gate_ok": True},
            "p3b": {"ok": p3b_ok, "doubling_4096_8192": doubling},
            "p3c": {"ok": True},
        }
    calib = {"null_a_ok": True, "m_selected": 40_000}
    v = po.verdict(calib, [seed_stub() for _ in range(5)])
    assert v["verdict"] == "SUPPORTED"
    assert all(v["checks"].values())
    # Une graine cassée (1/5) : SUPPORTED exige ≥ 4/5 — tient encore.
    seeds = [seed_stub(ok=False)] + [seed_stub() for _ in range(4)]
    assert po.verdict(calib, seeds)["verdict"] == "SUPPORTED"
    # Null a cassé : NON_CONCLUSIF_INSTRUMENT, jamais SUPPORTED.
    bad_calib = {"null_a_ok": False, "m_selected": None}
    assert "NON_CONCLUSIF_INSTRUMENT" in po.verdict(bad_calib, [seed_stub() for _ in range(5)])["verdict"]
    # Blob ~linéaire (doublement 2.1) sur 3 graines : REFUTED au sens régimes.
    lin = [seed_stub(doubling=2.1) for _ in range(3)] + [seed_stub() for _ in range(2)]
    assert "REFUTED" in po.verdict(calib, lin)["verdict"]
