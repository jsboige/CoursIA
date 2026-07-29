"""Tests du module #7740 : valence APPRISE, transferable, distincte de p_hat.

Couvrent les trois verdicts falsifiables du banc d'essai :

1. **Transfert** — un signal neutre devient attractif par co-occurrence repetee
   avec une source pertinente, ET un signal non-conditionne reste neutre (pas de
   fuite de l'inné vers tout).
2. **Distinctness vs prediction** — la valence apprise ``pi`` monte alors que
   l'erreur de prediction ``p_hat`` est invariante : valence != prediction.
3. **Reversibilite** — la valence acquise s'eteint quand l'association est
   retiree (Rescorla-Wagner : acquisition et extinction partagent la meme regle).

Plus les proprietes mecaniques (neutre a l'init, convergence Rescorla-Wagner,
gardes de validation). numpy + pytest, CPU uniquement.
"""

import numpy as np
import pytest

from ict.learned_valence import (
    LearnedValence,
    extinction_test,
    valence_prediction_distinctness_test,
    valence_transfer_test,
)


# --- Proprietes mecaniques de LearnedValence ---


def test_initial_valence_is_neutral():
    """A l'initialisation, AUCUN signal n'est attractif (pi = 0)."""
    lv = LearnedValence(n_signals=5, lr=0.1)
    assert np.all(lv.valence_vector() == 0.0)
    assert lv.valence(0) == 0.0
    assert lv.valence(4) == 0.0


def test_conditioning_raises_valence():
    """La co-occurrence avec une source pertinente monte la valence du signal."""
    lv = LearnedValence(n_signals=3, lr=0.2)
    pre = lv.valence(1)
    lv.condition(1, source_valence=1.0, steps=10)
    post = lv.valence(1)
    assert pre == 0.0
    assert post > pre
    assert post > 0.5


def test_rescorla_wagner_converges_to_source():
    """Asymptotiquement, pi tend vers la valence de la source (Rescorla-Wagner)."""
    lv = LearnedValence(n_signals=2, lr=0.05)
    target = 0.8
    lv.condition(0, source_valence=target, steps=500)
    assert abs(lv.valence(0) - target) < 1e-6


def test_convergence_is_per_signal():
    """Conditionner le signal A ne monte pas la valence du signal B (pas de fuite)."""
    lv = LearnedValence(n_signals=3, lr=0.1)
    lv.condition(0, source_valence=1.0, steps=50)
    assert lv.valence(0) > 0.5
    assert lv.valence(1) == 0.0
    assert lv.valence(2) == 0.0


def test_extinction_decays_valence_when_presented_alone():
    """Presenter le signal seul (sans source) eteint la valence vers 0."""
    lv = LearnedValence(n_signals=2, lr=0.2)
    lv.condition(0, source_valence=1.0, steps=30)
    acquired = lv.valence(0)
    assert acquired > 0.5
    lv.condition(0, source_valence=0.0, steps=200)
    assert lv.valence(0) < 0.1


def test_attract_prob_is_clipped_to_unit():
    """attract_prob reste dans [0, 1] meme apres forte sur-conditionnement."""
    lv = LearnedValence(n_signals=1, lr=0.5)
    lv.condition(0, source_valence=1.0, steps=10)
    assert 0.0 <= lv.attract_prob(0) <= 1.0


# --- Gardes de validation ---


def test_invalid_n_signals_raises():
    with pytest.raises(ValueError):
        LearnedValence(n_signals=0)


@pytest.mark.parametrize("bad_lr", [-0.1, 0.0, 1.5])
def test_invalid_lr_raises(bad_lr):
    with pytest.raises(ValueError):
        LearnedValence(n_signals=2, lr=bad_lr)


@pytest.mark.parametrize("bad_decay", [-0.1, 1.0, 1.5])
def test_invalid_decay_raises(bad_decay):
    with pytest.raises(ValueError):
        LearnedValence(n_signals=2, decay=bad_decay)


def test_signal_idx_out_of_bounds_raises():
    lv = LearnedValence(n_signals=2)
    with pytest.raises(IndexError):
        lv.condition(5, source_valence=1.0)
    with pytest.raises(IndexError):
        lv.valence(5)


# --- Les trois verdicts falsifiables #7740 ---


def test_transfer_neutral_becomes_attractive_control_stays_neutral():
    """Verdict TRANSFERT : le neutre devient attractif, le controle reste neutre."""
    report = valence_transfer_test(
        n_signals=4, pertinent_idx=0, neutral_idx=1,
        source_valence=1.0, n_condition=50, lr=0.1,
    )
    assert report["pre_valence_neutral"] == 0.0
    assert report["post_valence_neutral"] > 0.5
    assert report["control_valence_unconditioned"] < 0.05
    assert report["transferred"] == 1.0


def test_prediction_distinctness_valence_rises_prediction_invariant():
    """Verdict DISTINCTNESS : pi monte, l'erreur p_hat ne change pas.

    predict_fn est state-invariant (1 arg : la prediction mechanique ne lit pas
    la valence) ; son erreur est donc invariante au conditionnement, et pi monte
    -> valence != prediction. Le controle negatif associe
    (``test_coupled_predictor_is_not_distinct``) prouve la reciproque : un p_hat
    re-vetu sur pi fait tomber le verdict."""
    def constant_predict_fn(signal_idx: int) -> float:
        # Le signal 1 est mal predit (erreur 0.4), invariant au conditionnement.
        return 0.4 if signal_idx == 1 else 0.1

    report = valence_prediction_distinctness_test(
        predict_fn=constant_predict_fn,
        n_signals=4, conditioned_idx=1,
        source_valence=1.0, n_condition=50, lr=0.1,
    )
    assert report["delta_valence"] > 0.3
    assert report["delta_prediction_error"] < 1e-6
    assert report["distinct"] == 1.0


def test_coupled_predictor_is_not_distinct():
    """Controle negatif : un p_hat re-vetu sur pi DOIT faire tomber le verdict.

    Le banc passe le vecteur pi_t au predicteur (>=2 args) ; un re-vetement
    parfait de la valence (``p_hat = 1 - pi``) voit son erreur suivre pi entre
    pre (pi=0 -> err=1.0) et post (pi~1 -> err~0) -> delta_err > 0 -> NON
    distinct. Sans le couplage expose, ce verdict etait satisfait par
    construction (review ai-01 #8823) ; il est desormais refutable."""
    report = valence_prediction_distinctness_test(
        predict_fn=lambda i, pi: 1.0 - pi[i],
        n_signals=4, conditioned_idx=1,
        source_valence=1.0, n_condition=50, lr=0.1,
    )
    assert report["delta_prediction_error"] > 1e-6
    assert report["distinct"] == 0.0


def test_extinction_acquired_then_reversible():
    """Verdict REVERSIBILITE : la valence acquise s'eteint sous suppression."""
    report = extinction_test(
        n_signals=4, conditioned_idx=1,
        source_valence=1.0, n_condition=50, n_extinction=200, lr=0.1,
    )
    assert report["acquired_valence"] > 0.5
    assert report["extinguished_valence"] < 0.1
    assert report["reversible"] == 1.0


def test_no_transfer_without_conditioning():
    """Sans conditionnement, AUCUN signal ne devient attractif (controle negatif)."""
    report = valence_transfer_test(
        n_signals=4, pertinent_idx=0, neutral_idx=1,
        source_valence=1.0, n_condition=0, lr=0.1,
    )
    assert report["post_valence_neutral"] < 0.05
    assert report["transferred"] == 0.0
