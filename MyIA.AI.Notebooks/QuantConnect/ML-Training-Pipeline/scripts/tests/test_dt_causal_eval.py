"""Test de non-anticipation de l'evaluation du Decision Transformer (#21187).

Deux series de prix et de features identiques jusqu'a la ligne m, divergentes
ensuite, passent par la meme chaine d'evaluation. Une chaine causale rend des
logits identiques pour toute decision qui pilote un rendement k -> k+1 avec
k <= m : cette decision ne peut lire aucune donnee posterieure a la ligne k.

Le modele n'est pas entraine : la causalite est une propriete de la chaine
(alignement des fenetres, RTG d'entree), pas des poids, et les logits suffisent
a la mesurer. Le chemin historique ``dt_positions_on_test`` sert de temoin
negatif : le test doit le voir anticiper, sinon il ne detecte rien.

validate_xrp_dt importe torch (chaine train_rl_dt) : le module passe par
``pytest.importorskip``, comme test_tranche5_metrics.py.
"""

import sys
from pathlib import Path

import numpy as np
import pandas  # noqa: F401  -- avant torch, voir la note ci-dessous
import pytest

# Sous Windows, charger torch avant pandas/pyarrow fait lever une violation
# d'acces a l'import de pyarrow, puis tuer le processus pytest plus loin, dans
# des tests pandas d'autres fichiers (test_validate_xrp_dt_foldwise). Importer
# pandas d'abord evite les deux.
torch = pytest.importorskip("torch")

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from train_rl_dt import DecisionTransformerModel, build_trajectories  # noqa: E402
from validate_xrp_dt import (  # noqa: E402
    causal_eval_series, dt_causal_positions, dt_positions_on_test,
    momentum_naked_positions, teacher_actions,
)

W = 20
C = 20
N = 200
N_FEAT = 4


class _Recorder(torch.nn.Module):
    """Delegue au modele et garde les logits de chaque appel, dans l'ordre."""

    def __init__(self, model):
        super().__init__()
        self.model = model
        self.calls = []

    def forward(self, states, actions, rtg, attention_mask=None):
        out = self.model(states, actions, rtg, attention_mask=attention_mask)
        self.calls.append((out.detach().cpu().numpy(),
                           attention_mask.detach().cpu().numpy()))
        return out


def _series(seed: int = 0):
    rng = np.random.default_rng(seed)
    prices = (100.0 * np.exp(np.cumsum(rng.normal(0.0, 0.02, N)))).astype(np.float32)
    feats = rng.normal(size=(N, N_FEAT)).astype(np.float32)
    return prices, feats


def _diverge(prices, feats, m: int, seed: int = 1):
    """Copie identique jusqu'a la ligne m incluse, differente au-dela."""
    rng = np.random.default_rng(seed)
    p2, f2 = prices.copy(), feats.copy()
    p2[m + 1:] *= np.exp(rng.normal(0.0, 0.2, N - m - 1)).astype(np.float32)
    f2[m + 1:] += rng.normal(0.0, 3.0, (N - m - 1, N_FEAT)).astype(np.float32)
    return p2, f2


def _model():
    torch.manual_seed(0)
    model = DecisionTransformerModel(state_dim=W * N_FEAT, d_model=32, nhead=4,
                                     num_layers=2, context_length=C)
    model.eval()
    return model


def _causal_logits(model, prices, feats):
    """Logits de la decision qui pilote chaque rendement (NaN sans decision)."""
    rec = _Recorder(model)
    _, first_k = dt_causal_positions(rec, prices, feats, W, C, 0.002,
                                     batch_size=64, device="cpu")
    last = np.concatenate([out[:, -1, :] for out, _ in rec.calls])
    logits = np.full((N - 1, 3), np.nan)
    logits[first_k:first_k + len(last)] = last
    return logits, first_k


def _legacy_logits(model, prices, feats):
    """Logits du chemin historique, alignes comme dans les scripts d'avant #21187."""
    trajs = build_trajectories(prices, feats, window=W, context_length=C,
                               commission=0.001)
    rec = _Recorder(model)
    dt_positions_on_test(rec, trajs, N, C, batch_size=64, device="cpu")
    flat = np.concatenate([out.reshape(-1, 3)[mask.reshape(-1).astype(bool)]
                           for out, mask in rec.calls])
    return flat[:N - 1]


@pytest.mark.parametrize("m", [4, 59, 149])
def test_causal_decisions_ignore_rows_after_their_return(m):
    model = _model()
    prices, feats = _series()
    p2, f2 = _diverge(prices, feats, m)
    a, first_k = _causal_logits(model, prices, feats)
    b, _ = _causal_logits(model, p2, f2)
    decided = np.arange(first_k, min(m + 1, N - 1))
    np.testing.assert_array_equal(a[decided], b[decided])
    # Controle positif : la perturbation atteint bien les decisions posterieures.
    later = np.arange(max(m + 3, first_k), N - 1)
    assert not np.allclose(a[later], b[later])


@pytest.mark.parametrize("m", [4, 149])
def test_legacy_path_anticipates(m):
    """Temoin negatif : sans lui, un test vert ne prouverait rien."""
    model = _model()
    prices, feats = _series()
    p2, f2 = _diverge(prices, feats, m)
    a = _legacy_logits(model, prices, feats)
    b = _legacy_logits(model, p2, f2)
    k = np.arange(0, m + 1)
    moved = int((np.abs(a[k] - b[k]).max(axis=1) > 0).sum())
    assert moved > 0


def test_alignment_first_decision_and_series():
    model = _model()
    prices, feats = _series()
    pos, first_k = dt_causal_positions(model, prices, feats, W, C, 0.002,
                                       batch_size=64, device="cpu")
    assert first_k == W + C
    assert len(pos) == N - 1
    assert not pos[:first_k].any()
    dt_pos, mom_pos, bh_pos, rets = causal_eval_series(prices, pos, first_k, W)
    n_eval = N - 1 - first_k
    assert len(dt_pos) == len(mom_pos) == len(bh_pos) == len(rets) == n_eval
    expected = np.diff(prices) / (prices[:-1] + 1e-8)
    np.testing.assert_allclose(rets, expected[first_k:])
    np.testing.assert_array_equal(mom_pos,
                                  momentum_naked_positions(prices, window=W)[first_k:N - 1])


def test_teacher_actions_match_build_trajectories():
    prices, feats = _series()
    trajs = build_trajectories(prices, feats, window=W, context_length=C,
                               commission=0.001)
    acts = teacher_actions(prices, W)
    n_traj = len(trajs["actions"])
    np.testing.assert_array_equal(trajs["actions"], acts[W:W + n_traj])
