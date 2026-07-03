"""Tests du module ict.mdl (ICT-16, strate 5 Epic #4588, See #5099).

Verifient les 4 fonctions du scope ICT-16 :
  - prior Krichevsky-Trofimov (``kt_log2``, ``_tpm_line_bits``)
  - ``tpm_description_length`` (codelength d'une TPM empirique)
  - ``two_part_code`` (modele + residu sur split apprentissage / held-out)
  - ``entropy_rate_estimate`` (plug-in par entropies de bloc)
  - ``complexity_entropy_sweep`` (bosse complexite-entropie)

Le controle *sans complaisance* : un cycle deterministe DOIT avoir un
``residual_bits`` held-out ~ 0 sous un modele appris sur la trajectoire
elle-meme ; un bruit iid DOIT avoir un ``model_bits`` non nul et un
``residual_bits/n`` ~ ``H_1`` par symbole.

Numpy + pytest, comme les tests existants du package.
"""

import os
import sys

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import mdl as M  # noqa: E402


# --------------------------------------------------------------------------- #
#  Prior Krichevsky-Trofimov                                                  #
# --------------------------------------------------------------------------- #


def test_kt_log2_zero_count_is_neg_half_bit():
    # KT : log2(0 + 1/2) = -1 bit. Borne inferieure connue.
    assert M.kt_log2(0, k=2) == pytest.approx(-1.0, abs=1e-12)


def test_kt_log2_monotone_in_count():
    # n=0 < n=1 < n=2 : KT additif est strictement croissant.
    a = M.kt_log2(0, k=2)
    b = M.kt_log2(1, k=2)
    c = M.kt_log2(2, k=2)
    assert a < b < c


def test_kt_log2_negative_count_raises():
    with pytest.raises(ValueError):
        M.kt_log2(-1, k=2)


# --------------------------------------------------------------------------- #
#  Codelength du modele                                                       #
# --------------------------------------------------------------------------- #


def test_tpm_description_length_kt_can_be_negative():
    # NOTE (propriete fondamentale de KT, lecon C197-HARD #1) : KT peut
    # renvoyer des codelengths NEGATIVES pour des comptes < 1 -- le prior
    # "offre" des bits imaginaires (chaque compte 0 contribue +1 bit de
    # prior, ce qui peut etre compense par la constante multinomiale).
    # C'est pourquoi le code deux parties est preferable a la comparaison
    # directe de ``model_bits`` entre modeles.
    assert M.tpm_description_length(np.eye(4)) < 0
    assert M.tpm_description_length(np.ones((4, 4))) < 0


def test_tpm_description_length_more_categories_smaller_with_kt():
    # Avec KT, plus de categories = codelength potentiellement plus
    # negative (plus de prior multinomial offert). Ce n'est pas un
    # "modele plus simple" : c'est l'effet du prior. Le bon comparateur
    # est ``total_bits = model_bits + residual_bits`` (cf
    # ``two_part_code``), pas ``model_bits`` seul.
    counts_small = np.array([[10.0, 0.0], [0.0, 10.0]])
    counts_big = np.array([[10.0, 0.0, 0.0, 0.0],
                           [0.0, 10.0, 0.0, 0.0],
                           [0.0, 0.0, 10.0, 0.0],
                           [0.0, 0.0, 0.0, 10.0]])
    # KT : big < small (plus de prior offert pour les zeros).
    assert (M.tpm_description_length(counts_big)
            < M.tpm_description_length(counts_small))


def test_tpm_description_length_non_square_raises():
    with pytest.raises(ValueError):
        M.tpm_description_length(np.ones((2, 3)))


def test_tpm_description_length_negative_raises():
    with pytest.raises(ValueError):
        M.tpm_description_length(np.array([[-1.0, 0.5], [0.0, 1.0]]))


# --------------------------------------------------------------------------- #
#  Code deux parties                                                          #
# --------------------------------------------------------------------------- #


def test_two_part_code_too_short_raises():
    with pytest.raises(ValueError):
        M.two_part_code([0])


def test_two_part_code_deterministic_periodic_low_residual():
    # Un cycle deterministe (periode 3) doit produire un residual_bits
    # held-out ~ 0 : le modele appris sur l'apprentissage capture
    # parfaitement la dynamique, et les transitions held-out sont
    # parfaitement predites.
    seq = [0, 1, 2] * 50  # 150 etats, 149 transitions
    out = M.two_part_code(seq, split=0.5)
    # n_heldout = len(heldout) = 75 (toutes les transitions du split).
    assert out["n_heldout"] == 75
    assert out["n_covered"] == 75
    # Residual par transition held-out ~ 0.08 bits (KT smoothing log2(0.94)).
    assert out["residual_bits"] / out["n_heldout"] < 0.2


def test_two_part_code_iid_high_residual():
    # Une trajectoire iid (tiree d'une distribution uniforme sur 4
    # etats) doit avoir un residuel held-out substantiel : un modele
    # appris sur la moitie d'apprentissage ne predit pas mieux que le
    # hasard sur la moitie held-out. Le residuel par transition est
    # proche de H_1 = log2(4) = 2 bits.
    rng = np.random.default_rng(42)
    seq = rng.integers(0, 4, size=500).tolist()
    out = M.two_part_code(seq, split=0.5)
    # 4 categories -> H_1 = 2 bits par symbole. KT lissage ~ 1.95.
    assert out["residual_bits"] / out["n_heldout"] > 1.5


def test_two_part_code_model_bits_non_negative():
    seq = [0, 1, 0, 1, 0, 1] * 10
    out = M.two_part_code(seq, split=0.5)
    assert out["model_bits"] >= 0
    assert out["residual_bits"] >= 0
    assert out["total_bits"] == pytest.approx(
        out["model_bits"] + out["residual_bits"]
    )


def test_two_part_code_split_one_nearly_zero_residual():
    # split=1.0 : n_train est plafonne a n_trans - 1 (le code reserve au
    # moins 1 transition held-out pour avoir un signal non-vide). Sur
    # cette 1 transition held-out, KT applique un cout < 1 bit.
    seq = [0, 1, 2] * 30  # 90 etats, 89 transitions
    out = M.two_part_code(seq, split=1.0)
    assert out["n_heldout"] == 1
    assert out["residual_bits"] < 1.0


# --------------------------------------------------------------------------- #
#  Taux d'entropie plug-in                                                     #
# --------------------------------------------------------------------------- #


def test_entropy_rate_deterministic_zero():
    # Sequence constante : un seul 1-gramme, H_1 = 0 -> taux = 0.
    seq = [0] * 50
    h = M.entropy_rate_estimate(seq, block=1)
    assert h["H_block"] == pytest.approx(0.0)
    assert h["entropy_rate"] == pytest.approx(0.0)


def test_entropy_rate_iid_matches_log2_cardinal():
    # Sequence iid uniforme sur 4 etats : H_1 = log2(4) = 2 bits par
    # symbole. Le taux a block=1 doit etre exactement 2.
    rng = np.random.default_rng(0)
    seq = rng.integers(0, 4, size=2000).tolist()
    h = M.entropy_rate_estimate(seq, block=1)
    assert h["entropy_rate"] == pytest.approx(2.0, abs=0.05)


def test_entropy_rate_periodic_below_uniform():
    # Sequence periodique (periode 3) : H_1 = log2(3) < 2 (uniforme 4).
    # Le taux a block=1 doit etre inferieur au taux iid du test
    # precedent.
    seq = [0, 1, 2] * 100
    h = M.entropy_rate_estimate(seq, block=1)
    assert h["entropy_rate"] < 2.0
    assert h["entropy_rate"] > 0.0


def test_entropy_rate_block_too_large_raises():
    seq = [0, 1, 2]
    with pytest.raises(ValueError):
        M.entropy_rate_estimate(seq, block=4)


# --------------------------------------------------------------------------- #
#  Bosse complexite-entropie                                                  #
# --------------------------------------------------------------------------- #


def test_complexity_entropy_sweep_returns_rows():
    # Trois trajectoires : deterministe, periodique, iid.
    seq_det = [0, 1] * 100
    seq_per = [0, 1, 2] * 50
    rng = np.random.default_rng(7)
    seq_iid = rng.integers(0, 3, size=300).tolist()
    out = M.complexity_entropy_sweep(
        [seq_det, seq_per, seq_iid],
        blocks=(1, 2, 3),
        splits=(0.5,),
        rng=np.random.default_rng(123),
        n_shuffles=2,
    )
    assert "rows" in out and "summary" in out
    assert out["summary"]["n_rows"] > 0
    # Les trois trajectoires produisent des H_rate differents.
    H_rates = sorted({row["H_rate"] for row in out["rows"]})
    assert len(H_rates) >= 2


def test_complexity_entropy_sweep_summary_has_peak():
    # Le resume doit indiquer la position du pic (bosse).
    rng = np.random.default_rng(11)
    seqs = []
    # Trajectoires de complexite croissante par k_etats.
    for k in (2, 3, 4, 5):
        seqs.append(rng.integers(0, k, size=400).tolist())
    out = M.complexity_entropy_sweep(
        seqs,
        blocks=(1, 2),
        splits=(0.5,),
        rng=np.random.default_rng(0),
        n_shuffles=2,
    )
    summary = out["summary"]
    assert "peak_H_rate" in summary
    assert "peak_model_bits" in summary
    assert summary["peak_H_rate"] >= summary["H_rate_min"]
    assert summary["peak_H_rate"] <= summary["H_rate_max"]


def test_complexity_entropy_sweep_empty_input_safe():
    out = M.complexity_entropy_sweep([])
    assert out["rows"] == []
    assert out["summary"]["n_rows"] == 0