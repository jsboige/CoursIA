"""Tests CPU des campagnes de regimes generatifs (suivi #20071).

Ce qui est couvert :

- ``overlap_energy`` : extremes mesures sur bases synthetiques orthonormees
  (sous-espaces disjoints -> 0, confondus -> 1, base vide -> NaN) et presence
  dans le rapport comme dans les bandes du temoin (``untrained_null`` reprend
  les cles du rapport automatiquement -- verifie) ;
- ``position_contre_bande`` : les trois positions rendues par leur nom, et le
  cas degrade (metrique ou bande non finie) rendu ``"n/a"`` -- un niveau
  degrade se RAPPORTE, il ne leve pas ;
- ``sweep_channel_noise`` : la lecture est rendue A TOUS les niveaux, y compris
  ceux ou le gate echoue -- c'est la correction de protocole du critere 1, la
  question etant la lisibilite du facteur et non la reussite du modele ; et le
  plancher a gamma = 1 vaut ln(3) + ln(2) EXACT (identite analytique, elle
  valide la plomberie du sweep du canal au niveau muet) ;
- ``conditional_campaign`` : structure des deux bancs (conditionnel +
  controle independant au meme enfant), appariement EXACT des marginales sur
  les matrices, prime d'information conditionnelle >= 0, graines multiples.

Les passes sont mini (steps <= 60, sequences courtes) : ces tests valident le
PROTOCOLE, pas les verdicts -- les verdicts viennent de la campagne complete
commitee dans ``results/`` et lue par le carnet ICT-36.
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import numpy as np
import pytest

from ict import factor_geometry_regimes as freg
from ict import factor_geometry_trained as fgt

if not fgt.HAS_TORCH:
    pytest.skip("torch requis pour les campagnes (mesures numpy seulement sinon)", allow_module_level=True)


UNIFORME_JOINT = float(np.log(3.0) + np.log(2.0))


def test_overlap_energy_extremes():
    q, _ = np.linalg.qr(np.random.default_rng(0).normal(size=(8, 8)))
    a, autre = q[:, :2], q[:, 2:4]
    # sous-espaces disjoints : chaque direction de a est orthogonale a autre
    assert fgt.overlap_energy(a, autre) == pytest.approx(0.0, abs=1e-12)
    # sous-espaces confondus : energie maximale
    assert fgt.overlap_energy(a, a) == pytest.approx(1.0, abs=1e-12)
    # partiellement confondus : une direction commune sur deux -> 0.5
    demi = np.concatenate([a[:, :1], autre[:, :1]], axis=1)
    assert fgt.overlap_energy(a, demi) == pytest.approx(0.5, abs=1e-12)
    # base vide (cible de rang nul, gamma = 1) : NaN, pas d'exception
    assert np.isnan(fgt.overlap_energy(np.zeros((8, 0)), a))


def test_rapport_et_temoin_prennent_overlap_energy():
    rng = np.random.default_rng(1)
    h = rng.normal(size=(400, 8))
    bel_a = rng.dirichlet(np.ones(3), size=400)
    bel_b = rng.dirichlet(np.ones(3), size=400)
    rep = fgt.factor_geometry_report(h, bel_a, bel_b)
    assert "overlap_energy" in rep
    assert 0.0 <= rep["overlap_energy"] <= 1.0
    import torch

    x = torch.from_numpy(rng.integers(0, 3, size=(4, 100, 2)).astype(np.int64))
    temoin = fgt.untrained_null(
        lambda sd: fgt.FactoredRNN(n_a=3, n_b=3, seed=sd), x, bel_a[:400], bel_b[:400], n_init=5
    )
    assert "overlap_energy" in temoin
    assert temoin["overlap_energy"]["n"] == 5.0


def test_position_contre_bande():
    bande = {"p05": 0.2, "p95": 0.4, "n": 6.0}
    assert freg.position_contre_bande(0.1, bande) == "sous_bande"
    assert freg.position_contre_bande(0.3, bande) == "dans_bande"
    assert freg.position_contre_bande(0.5, bande) == "dessus_bande"
    assert freg.position_contre_bande(float("nan"), bande) == "n/a"
    vide = {"p05": float("nan"), "p95": float("nan"), "n": 0.0}
    assert freg.position_contre_bande(0.3, vide) == "n/a"


def test_sweep_rend_lecture_aux_niveaux_a_gate_echec():
    """Critere 1 : la falsifiable se joue AUX niveaux muets -- lecture rendue quand meme."""
    lignes = freg.sweep_channel_noise(
        gammas=(1.0,), length=20, n_train=8, n_val=4, steps=10, eval_every=5, n_init=5
    )
    (l,) = lignes
    assert "gate" in l
    assert l["rapport"] is not None, "la lecture doit exister meme a gate echoue"
    assert l["temoin"] is not None
    for m in ("probe_r2_a", "probe_r2_b", "overlap_coef_max", "overlap_energy", "additivity_gap"):
        assert m in l["rapport"]
        # la position est rendue SANS lever ; a ce mini-budget (160 pas) le
        # transitoire de la filtration garde de la variance aux cibles, donc
        # la metrique peut etre finie ("dans_bande") comme degenereree
        # ("n/a") -- les deux sont des lectures honnetes, aucune n'est une erreur
        assert freg.position_contre_bande(l["rapport"][m], l["temoin"][m]) in (
            "dans_bande",
            "sous_bande",
            "dessus_bande",
            "n/a",
        )


def test_sweep_plancher_gamma1_identite_analytique():
    """gamma = 1 : emissions muettes -> plancher joint = ln(3) + ln(2) EXACT."""
    lignes = freg.sweep_channel_noise(
        gammas=(1.0,), length=20, n_train=8, n_val=4, steps=5, eval_every=5, n_init=5
    )
    (l,) = lignes
    assert l["plancher_joint"] == pytest.approx(UNIFORME_JOINT, abs=1e-9)
    assert l["plancher_a"] == pytest.approx(float(np.log(3.0)), abs=1e-9)
    assert l["plancher_b"] == pytest.approx(float(np.log(2.0)), abs=1e-9)


def test_sweep_gamma0_lecture_finie_et_gate():
    lignes = freg.sweep_channel_noise(
        gammas=(0.0,), length=20, n_train=16, n_val=4, steps=60, eval_every=20, n_init=5
    )
    (l,) = lignes
    assert np.isfinite(l["plancher_joint"])
    assert l["plancher_joint"] < UNIFORME_JOINT - 0.1  # le canal non bruite porte de l'information
    r = l["rapport"]
    assert np.isfinite(r["overlap_energy"])
    assert np.isfinite(r["probe_r2_a"])


def test_conditional_campaign_structure_et_appariement():
    camp = freg.conditional_campaign(
        length=20, n_train=8, n_val=4, steps=20, eval_every=10, n_init=5, model_seeds=(0, 1)
    )
    assert camp["appariement"]["matrices_exact"] is True
    assert camp["planchers"]["prime_conditionnelle"] >= 0.0
    for nom in ("conditionnel", "independant"):
        ent = camp["resultats"][nom]
        assert set(ent["par_seed"]) == {0, 1}, "le verdict doit porter plusieurs graines"
        for e in ent["par_seed"].values():
            assert np.isfinite(e["rapport"]["overlap_energy"])
        assert ent["temoin"]["overlap_energy"]["n"] == 5.0


def test_main_quick_ecrit_les_deux_artefacts(tmp_path):
    rc = freg.main(["--quick", "--out-dir", str(tmp_path)])
    assert rc == 0
    art1 = tmp_path / "ict36_regime1_sweep_bruit_canal.json"
    art2 = tmp_path / "ict36_regime2_conditionnel.json"
    assert art1.exists() and art2.exists()
    import json

    d1 = json.loads(art1.read_text(encoding="utf-8"))
    assert d1["protocole"]["steps"] == 20
    assert len(d1["niveaux"]) >= 1
    d2 = json.loads(art2.read_text(encoding="utf-8"))
    assert d2["appariement"]["matrices_exact"] is True
