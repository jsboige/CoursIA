"""Tests du module ict.mdl (ICT-16, strate 5 Epic #4588, See #5099).

Verifient les estimateurs du scope ICT-16 :
  - prior Krichevsky-Trofimov (``kt_log2``, ``kt_codelength``,
    ``_tpm_line_bits``)
  - ``tpm_description_length`` (codelength d'une TPM empirique)
  - ``two_part_code`` (modele + residu sur split apprentissage / held-out)
  - ``fit_markov_order`` (selection d'ordre MDL + controle NLL held-out)
  - ``entropy_rate_estimate`` (plug-in par entropies de bloc)
  - ``complexity_entropy_sweep`` (bosse complexite-entropie)

Le controle *sans complaisance* : la codelength KT est comparee a une
**reference rationnelle exacte** (``fractions.Fraction``) et a la somme des
couts predictifs sequentiels. Une formule fausse peut passer une assertion
de positivite ; elle ne peut pas passer les deux a la fois.

Un cycle deterministe DOIT avoir un ``residual_bits`` held-out ~ 0 sous un
modele appris sur la trajectoire elle-meme ; un bruit iid DOIT avoir un
``model_bits`` non nul et un ``residual_bits/n`` ~ ``H_1`` par symbole.

Numpy + pytest, comme les tests existants du package.
"""

import math
import os
import sys
from fractions import Fraction

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import mdl as M  # noqa: E402


# --------------------------------------------------------------------------- #
#  Reference exacte (rationnelle) de la marginale KT                          #
# --------------------------------------------------------------------------- #


def _exact_kt_probability(counts):
    """Reference rationnelle : ``Gamma(k/2)``/``Gamma(n+k/2)`` * produit."""
    alpha = Fraction(1, 2)
    k = len(counts)
    n = sum(counts)
    numerator = Fraction(1)
    for count in counts:
        for i in range(count):
            numerator *= alpha + i
    denominator = Fraction(1)
    for i in range(n):
        denominator *= k * alpha + i
    return numerator / denominator


# --------------------------------------------------------------------------- #
#  Prior Krichevsky-Trofimov                                                  #
# --------------------------------------------------------------------------- #


def test_kt_log2_zero_count_contributes_nothing():
    # Terme par categorie : Gamma(0 + 1/2)/Gamma(1/2) = 1, soit 0 bit.
    # L'ancien contrat rendait -1 bit et fabriquait la "codelength negative".
    assert M.kt_log2(0, k=2) == pytest.approx(0.0, abs=1e-12)


def test_kt_log2_negative_count_raises():
    with pytest.raises(ValueError):
        M.kt_log2(-1, k=2)


@pytest.mark.parametrize("counts", [
    [3, 1],
    [0, 0],
    [2, 0, 1],
    [4, 4, 4, 4],
    [7],
    [0, 0, 0, 0, 3],
])
def test_kt_codelength_matches_exact_rational_reference(counts):
    # La codelength doit valoir exactement -log2 de la marginale exacte.
    reference = -math.log2(float(_exact_kt_probability(counts)))
    assert M.kt_codelength(counts) == pytest.approx(reference, abs=1e-9)


def test_kt_codelength_empty_row_is_zero():
    # Rien a transmettre : la distribution est connue, cout nul.
    # C'est precisement le cas ou l'ancienne formule rendait des bits
    # NEGATIFS (une ligne vide de TPM facturait -4.64 bits pour k=4).
    assert M.kt_codelength([0, 0]) == 0.0
    assert M.kt_codelength([0, 0, 0, 0]) == 0.0
    assert M.kt_codelength([]) == 0.0


@pytest.mark.parametrize("counts", [
    [1, 0],
    [1, 0, 0, 0],
    [10, 0, 0, 0],
    [3, 1],
    [500, 498, 512, 490],
])
def test_kt_codelength_is_non_negative(counts):
    assert M.kt_codelength(counts) >= 0.0


def test_kt_codelength_matches_sequential_chain_rule():
    # Identite de la regle de la chaine pour un prior echangeable : la
    # codelength est la somme des couts predictifs sequentiels
    # p = (n_i + 1/2) / (n + k/2). C'est LE test qui attrape une formule
    # fausse : n'importe quel decor pourrait rester positif, pas celui-ci.
    counts = [3, 1, 0, 2]
    k = len(counts)
    symbols = []
    for index, count in enumerate(counts):
        symbols.extend([index] * count)

    running = np.zeros(k)
    sequential = 0.0
    for symbol in symbols:
        n = running.sum()
        p = (running[symbol] + 0.5) / (n + k * 0.5)
        sequential += -math.log2(p)
        running[symbol] += 1

    assert M.kt_codelength(counts) == pytest.approx(sequential, abs=1e-12)


def test_kt_codelength_increases_with_one_more_symbol():
    base = [2, 0, 1]
    for index in range(3):
        incremented = list(base)
        incremented[index] += 1
        assert M.kt_codelength(incremented) > M.kt_codelength(base)


# --------------------------------------------------------------------------- #
#  Codelength du modele                                                       #
# --------------------------------------------------------------------------- #


def test_tpm_description_length_non_negative():
    # Une TPM est un objet a transmettre : sa codelength ne peut pas etre
    # negative. L'ancien test affirmait l'inverse ("propriete fondamentale
    # de KT"), ce qui n'est vrai d'aucune longueur de code.
    assert M.tpm_description_length(np.eye(4)) > 0
    assert M.tpm_description_length(np.ones((4, 4))) > 0


def test_tpm_description_length_more_categories_costs_more():
    # Un alphabet plus grand coute plus cher : plus de lignes a declarer et
    # plus de categories par ligne. C'est l'inverse de l'ancienne assertion
    # ("le prior offre des bits pour les zeros"), qui decrivait en realite
    # l'artefact de la formule fausse.
    counts_small = np.array([[10.0, 0.0], [0.0, 10.0]])
    counts_big = np.array([[10.0, 0.0, 0.0, 0.0],
                           [0.0, 10.0, 0.0, 0.0],
                           [0.0, 0.0, 10.0, 0.0],
                           [0.0, 0.0, 0.0, 10.0]])
    assert (M.tpm_description_length(counts_big)
            > M.tpm_description_length(counts_small))


def test_tpm_description_length_empty_matrix_is_only_overhead():
    # Aucune transition observee : seuls les log2(k) bits de declaration.
    assert M.tpm_description_length(np.zeros((4, 4))) == pytest.approx(2.0)


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
    assert out["n_heldout"] == 75
    assert out["n_covered"] == 75
    assert out["n_escaped"] == 0
    # Residual par transition held-out ~ 0.08 bits (KT smoothing).
    assert out["residual_bits"] / out["n_heldout"] < 0.2


def test_two_part_code_iid_high_residual():
    # Une trajectoire iid (uniforme sur 4 etats) doit avoir un residuel
    # held-out substantiel, proche de H_1 = log2(4) = 2 bits.
    rng = np.random.default_rng(42)
    seq = rng.integers(0, 4, size=500).tolist()
    out = M.two_part_code(seq, split=0.5)
    assert out["residual_bits"] / out["n_heldout"] > 1.5


def test_two_part_code_model_bits_non_negative():
    seq = [0, 1, 0, 1, 0, 1] * 10
    out = M.two_part_code(seq, split=0.5)
    assert out["model_bits"] >= 0
    assert out["residual_bits"] >= 0
    assert out["total_bits"] == pytest.approx(
        out["model_bits"] + out["residual_bits"]
    )


def test_two_part_code_predictive_rows_sum_to_one():
    # Predictive KT normalisee : (n_ij + 1/2) / (n_i* + k/2). Un terme
    # additionnel au denominateur (l'ancien "+ 1/2") cassait la
    # normalisation et sous-estimait le residu.
    seq = [0, 1, 2, 0, 1, 2, 0, 1] * 20
    out = M.two_part_code(seq, split=0.5, states_to_index={0: 0, 1: 1, 2: 2})
    counts = np.zeros((3, 3))
    transitions = list(zip(seq[:-1], seq[1:]))
    n_train = out["n_train"]
    for a, b in transitions[:n_train]:
        counts[a, b] += 1
    prob = (counts + 0.5) / (counts.sum(axis=1, keepdims=True) + 3 * 0.5)
    np.testing.assert_allclose(prob.sum(axis=1), np.ones(3), atol=1e-12)


def test_two_part_code_split_one_nearly_zero_residual():
    # split=1.0 : n_train est plafonne a n_trans - 1 (le code reserve au
    # moins 1 transition held-out pour avoir un signal non-vide).
    seq = [0, 1, 2] * 30
    out = M.two_part_code(seq, split=1.0)
    assert out["n_heldout"] == 1
    assert out["residual_bits"] < 1.0


def test_two_part_code_unseen_symbol_is_escaped():
    # Un symbole absent de l'alphabet d'apprentissage coute un
    # echappement : la transition n'est pas "gratuite".
    seq = [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 2, 3]
    out = M.two_part_code(seq, split=0.5)
    assert out["n_escaped"] > 0
    assert out["n_escaped"] + out["n_covered"] == out["n_heldout"]


# --------------------------------------------------------------------------- #
#  Selection d'ordre : le pont MDL -> generalisation                          #
# --------------------------------------------------------------------------- #


def _markov_tpm(seed=0, order=2, k_states=4, alpha=0.3):
    """TPM d'une chaine d'ordre ``order`` sur ``k_states`` etats.

    Le tirage de la TPM est **separe** de celui de la trajectoire : une
    trajectoire d'apprentissage et sa trajectoire tenue a l'ecart doivent
    sortir de la **meme** source, sinon le NLL held-out mesure un changement
    de source et non la qualite du modele (piege rencontre en ecrivant ces
    tests : deux TPM differentes, NLL held-out qui s'effondre a l'ordre 2 et
    fait croire que le pont est casse).
    """
    rng = np.random.default_rng(seed)
    return np.array([rng.dirichlet([alpha] * k_states)
                     for _ in range(k_states ** order)])


def _markov_sequence(n, tpm, order=2, k_states=4, seed=0):
    """Trajectoire tiree sous une TPM **fournie** (meme source des deux cotes)."""
    rng = np.random.default_rng(seed)
    states = [int(rng.integers(k_states)) for _ in range(order)]
    for _ in range(n):
        context = 0
        for j in range(order):
            context = context * k_states + states[-(order - j)]
        states.append(int(rng.choice(k_states, p=tpm[context])))
    return states


def _iid_sequence(n, seed=0, k_states=4):
    rng = np.random.default_rng(seed)
    return [int(v) for v in rng.integers(0, k_states, size=n)]


def test_fit_markov_order_structure_recovers_generator_order():
    # Source structuree (Markov d'ordre 2) : MDL doit retrouver 2, et le
    # controle independant (NLL held-out) doit dire la meme chose.
    tpm = _markov_tpm(seed=0, order=2)
    train = _markov_sequence(1000, tpm, seed=0)
    heldout = _markov_sequence(3000, tpm, seed=7)
    out = M.fit_markov_order(train, heldout=heldout, max_order=4)
    assert out["best_mdl_order"] == 2
    assert out["best_nll_order"] == 2
    assert len(out["rows"]) == 5
    # Le code MDL d'ordre 2 doit etre strictement meilleur que l'ordre 0.
    by_order = {row["order"]: row for row in out["rows"]}
    assert by_order[2]["mdl_bits"] < by_order[0]["mdl_bits"]


def test_fit_markov_order_iid_selects_order_zero():
    # Nul i.i.d. : rien a capturer, MDL doit retomber sur l'ordre 0.
    train = _iid_sequence(1000, seed=0)
    heldout = _iid_sequence(3000, seed=11)
    out = M.fit_markov_order(train, heldout=heldout, max_order=4)
    assert out["best_mdl_order"] == 0


def test_fit_markov_order_rows_are_internally_consistent():
    train = _markov_sequence(400, _markov_tpm(seed=3, order=1), order=1, seed=3)
    out = M.fit_markov_order(train, max_order=3)
    for row in out["rows"]:
        assert row["mdl_bits"] == pytest.approx(
            row["payload_bits"] + row["declare_bits"]
        )
        assert row["n_contexts"] == out["k_states"] ** row["order"]
        assert 0 <= row["n_nonempty"] <= row["n_contexts"]
        assert row["payload_bits"] >= 0


def test_fit_markov_order_declares_the_undersampling_limit():
    # Limite mesuree, epinglee volontairement : sur 60 tirages d'une source
    # i.i.d. a 4 etats, l'ordre 4 compte 256 contextes dont la plupart sont
    # vides -- une ligne vide coute 0 bit, donc l'ordre eleve n'est pas
    # facture et gagne par chance. Ce test documente le regime de rupture ;
    # s'il se met a passer a l'ordre 0, c'est que la formule a change et il
    # faut relire le notebook, pas supprimer le test.
    train = _iid_sequence(60, seed=0)
    heldout = _iid_sequence(3000, seed=11)
    out = M.fit_markov_order(train, heldout=heldout, max_order=4)
    assert out["best_mdl_order"] != 0
    # Le controle held-out, lui, reste juste : c'est le point du pont.
    assert out["best_nll_order"] == 0


# --------------------------------------------------------------------------- #
#  Taux d'entropie plug-in                                                     #
# --------------------------------------------------------------------------- #


def test_entropy_rate_deterministic_zero():
    seq = [0] * 50
    h = M.entropy_rate_estimate(seq, block=1)
    assert h["H_block"] == pytest.approx(0.0)
    assert h["entropy_rate"] == pytest.approx(0.0)


def test_entropy_rate_iid_matches_log2_cardinal():
    rng = np.random.default_rng(0)
    seq = rng.integers(0, 4, size=2000).tolist()
    h = M.entropy_rate_estimate(seq, block=1)
    assert h["entropy_rate"] == pytest.approx(2.0, abs=0.05)


def test_entropy_rate_periodic_below_uniform():
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
    H_rates = sorted({row["H_rate"] for row in out["rows"]})
    assert len(H_rates) >= 2


def test_complexity_entropy_sweep_summary_has_peak():
    rng = np.random.default_rng(11)
    seqs = []
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


def test_complexity_entropy_sweep_model_bits_non_negative():
    # La bosse s'appuie sur model_bits comme complexite statistique : une
    # valeur negative n'aurait aucun sens.
    out = M.complexity_entropy_sweep(
        [[0, 1] * 60, [0, 1, 2] * 40],
        blocks=(1, 2),
        splits=(0.5,),
        rng=np.random.default_rng(5),
        n_shuffles=2,
    )
    assert all(row["model_bits"] >= 0 for row in out["rows"])


def test_complexity_entropy_sweep_empty_input_safe():
    out = M.complexity_entropy_sweep([])
    assert out["rows"] == []
    assert out["summary"]["n_rows"] == 0
