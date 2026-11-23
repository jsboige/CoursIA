#!/usr/bin/env python3
"""
Tests for scripts/ict_pilot_transformer.py (pilote #15480).

Couvre : grille gelee (independance de l'echantillon), tokenisation jointe
(alphabet, structure bin/parite, determinisme), capture de panneaux (cles
pre/post par couche, formes), forward_patched (identite sans patch,
self-patch = identite, patch reel change les logits — le point d'entree
causal du pilote), sequences_from_bench (formes, hop, garde), train_tiny
(perte decroissante sur donnees synthetiques triviales).
CPU-only : modele 2 couches d_model 16, quelques dizaines de steps.
"""

import numpy as np
import pytest
import torch
from pathlib import Path
import sys

_scripts = str(Path(__file__).resolve().parent.parent)
if _scripts not in sys.path:
    sys.path.insert(0, _scripts)

from ict_pilot_transformer import (TokenizerConfig, TinyTransformer,
                                   TrainConfig, capture_panels,
                                   sequences_from_bench, tokenize_joint,
                                   train_tiny)


MEANS = (-0.15, 0.0, 0.15)
STD = 0.05


def _tiny_model(vocab=16, seed=0):
    return TinyTransformer(vocab=vocab, d_model=16, n_layers=2, n_heads=2,
                           d_mlp=32, max_len=64, seed=seed)


# ------------------------------------------------------------------ grille

def test_grid_gelee_independante_de_lechantillon():
    g1 = TokenizerConfig().grid(MEANS, STD)
    g2 = TokenizerConfig().grid(MEANS, STD)
    np.testing.assert_array_equal(g1, g2)
    # bornes : moyenne extreme +- 4 ecarts-types, n_bins + 1 bords
    assert g1[0] == pytest.approx(min(MEANS) - 4 * STD)
    assert g1[-1] == pytest.approx(max(MEANS) + 4 * STD)
    assert len(g1) == TokenizerConfig().n_bins + 1


# ------------------------------------------------------------- tokenisation

def test_tokenize_joint_alphabet_et_parite():
    grid = TokenizerConfig().grid(MEANS, STD)
    rng = np.random.default_rng(0)
    obs_a = rng.normal(0.0, 0.5, 500)
    obs_b = rng.integers(0, 2, 500).astype(float)
    tokens = tokenize_joint(obs_a, obs_b, grid)
    n_bins = TokenizerConfig().n_bins
    assert tokens.dtype == np.int64
    assert tokens.min() >= 0 and tokens.max() < 2 * n_bins
    # structure : bit b = parite du token, bin_a = token // 2
    np.testing.assert_array_equal(tokens % 2, (obs_b > 0.5).astype(np.int64))
    assert (tokens // 2).min() >= 0 and (tokens // 2).max() < n_bins


def test_tokenize_joint_deterministe():
    grid = TokenizerConfig().grid(MEANS, STD)
    obs_a = np.linspace(-0.5, 0.5, 64)
    obs_b = np.zeros(64)
    np.testing.assert_array_equal(tokenize_joint(obs_a, obs_b, grid),
                                  tokenize_joint(obs_a, obs_b, grid))


def test_tokenize_joint_rejette_formes_incoherentes():
    grid = TokenizerConfig().grid(MEANS, STD)
    with pytest.raises(ValueError):
        tokenize_joint(np.zeros(10), np.zeros(9), grid)
    with pytest.raises(ValueError):
        tokenize_joint(np.zeros((2, 10)), np.zeros(20), grid)


# ------------------------------------------------------------------ panneaux

def test_capture_panels_cles_et_formes():
    model = _tiny_model()
    seqs = np.zeros((5, 32), dtype=np.int64)
    panels = capture_panels(model, seqs, seq_len=32, device="cpu")
    assert set(panels) == {"L0_pre", "L0_post", "L1_pre", "L1_post"}
    for v in panels.values():
        assert v.shape == (5, 32, 16)


def test_forward_patched_identite_sans_patch():
    torch.manual_seed(0)
    model = _tiny_model()
    tok = torch.randint(0, 16, (2, 16))
    logits_ref, panels = model.forward_with_panels(tok)
    model.eval()
    with torch.no_grad():
        logits_id = model.forward_patched(tok, {})
    torch.testing.assert_close(logits_ref, logits_id)


def test_forward_patched_self_patch_identite():
    torch.manual_seed(0)
    model = _tiny_model().eval()
    tok = torch.randint(0, 16, (2, 16))
    with torch.no_grad():
        logits_ref, panels = model.forward_with_panels(tok)
        # reinjection de chaque panneau par lui-meme : identite pour tous
        for key, val in panels.items():
            logits_self = model.forward_patched(tok, {key: val.clone()})
            torch.testing.assert_close(logits_ref, logits_self)


def test_forward_patched_patch_reel_change_logits():
    torch.manual_seed(0)
    model = _tiny_model().eval()
    tok = torch.randint(0, 16, (2, 16))
    with torch.no_grad():
        logits_ref, panels = model.forward_with_panels(tok)
        mod = panels["L1_pre"].clone()
        mod[:, :, :8] = 0.0
        logits_mod = model.forward_patched(tok, {"L1_pre": mod})
    assert not torch.allclose(logits_ref, logits_mod)
    assert float((logits_ref - logits_mod).abs().max()) > 0.1


@pytest.mark.skipif(not torch.cuda.is_available(),
                    reason="CUDA indisponible (garantie testee sur GPU)")
def test_forward_patched_normalise_le_device():
    # modele sur CUDA, tokens et patches fournis sur CPU : le harnais deplace
    # lui-meme vers le device du modele (garantie du point d'entree causal).
    model = _tiny_model().to("cuda").eval()
    tok = torch.randint(0, 16, (2, 16))  # CPU
    with torch.no_grad():
        ref, panels = model.forward_with_panels(tok)
        cf = model.forward_patched(tok, {"L1_pre": panels["L1_pre"].cpu()})
    assert ref.device.type == "cuda"
    assert float((ref - cf).abs().max()) == 0.0


# ------------------------------------------------------------------ fenetres

def test_sequences_from_bench_hop():
    tokens = np.arange(100, dtype=np.int64)
    seqs = sequences_from_bench(tokens, seq_len=10, hop=10)
    assert seqs.shape == (10, 10)
    np.testing.assert_array_equal(seqs[3], tokens[30:40])
    # hop 16 < seq_len 64 : fenetres chevauchantes, contenu aligne
    tokens = np.arange(200, dtype=np.int64)
    seqs = sequences_from_bench(tokens, seq_len=64, hop=16)
    assert seqs.shape[0] == (200 - 64) // 16 + 1
    np.testing.assert_array_equal(seqs[2], tokens[32:96])


def test_sequences_from_bench_trop_court():
    with pytest.raises(ValueError):
        sequences_from_bench(np.arange(8, dtype=np.int64), seq_len=16, hop=4)


# ------------------------------------------------------------------ training

def test_train_tiny_perte_decroissante():
    torch.manual_seed(0)
    rng = np.random.default_rng(1)
    # flux avec structure : token t+1 = (token t + 1) % 16
    flux = (np.arange(4000) % 16).astype(np.int64)[None, :]
    model = _tiny_model(seed=0)
    cfg = TrainConfig(steps=120, batch=8, seq_len=24, eval_every=40)
    cfg = train_tiny(model, flux, cfg, device="cpu")
    losses = [entry[1] for entry in cfg.log]
    assert len(losses) >= 2
    assert losses[-1] < losses[0]
