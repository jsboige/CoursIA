"""Garde-fous du mode inoculation (pilote #8236, jalon 3).

Tests du CONTRAT des organes introduits par le pilote, sur cas synthetique a
verite connue par construction :

- ``trace_filename`` : suffixe ``_s{alpha}`` conditionnel — retro-compatible
  a l'octet quand alpha vaut 1 ou quand aucun clamp n'est applique ;
- ``ClampHook`` : h' = h - alpha * delta EXACT (annulation a alpha=1,
  neutralite byte-identique a alpha=0, interpolation lineaire en alpha) ;
- ``CaptureHook`` : capture le resid_post sans le modifier.

``ClampHook``/``CaptureHook`` vivent dans le script GPU et exigent torch
(CPU suffit ici). Le module est charge PAR CHEMIN : l'import package
``scripts.*`` depend du rootdir pytest (defaut connu, cf le rouge
base-inherited de ``test_sae_2b_l100_...`` sur ``fetch_sae_config``).
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from ict.sae_traces import trace_filename  # noqa: E402

_SCRIPT = Path(__file__).resolve().parent.parent / "scripts" / "extract_sae_traces.py"


def _load_script_module():
    spec = importlib.util.spec_from_file_location("extract_sae_traces_pilot", _SCRIPT)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# --- trace_filename : suffixe d'intensite conditionnel -----------------------

def test_filename_sans_clamp_scale_byte_identique():
    # alpha=1 = comportement historique : aucun suffixe, nom inchange.
    assert trace_filename("trained", 16, n_clamp=8) == \
           trace_filename("trained", 16, n_clamp=8, clamp_scale=1.0)
    assert trace_filename("trained", 16, n_clamp=8) == \
           "ict21_sae_layer16_trained_clamp8.npz"


def test_filename_suffixe_seulement_si_alpha_different_de_1():
    assert trace_filename("trained", 16, n_clamp=8, clamp_scale=0.5) == \
           "ict21_sae_layer16_trained_clamp8_s0.5.npz"
    # slug trace_filename : lower SANS points ("Qwen3.5-2B" -> "qwen35-2b"),
    # convention distincte du slug calib_ ("qwen3-5-2b") d'extract_sae_fidelity.
    assert trace_filename("trained", 12, model="Qwen/Qwen3.5-2B-Base",
                          default_model="Qwen/Qwen3.5-9B-Base", n_layers=24,
                          n_clamp=8, clamp_scale=0.25) == \
           "ict21_sae_qwen35-2b-base_layer12of24_trained_clamp8_s0.25.npz"


def test_filename_scale_sans_clamp_ne_suffixe_pas():
    # clamp_scale sans clamp_ids : aucun clamp applique, aucun suffixe — le
    # nom ne doit pas pretendre une inoculation qui n'a pas eu lieu.
    assert trace_filename("trained", 16, n_clamp=0, clamp_scale=0.5) == \
           "ict21_sae_layer16_trained.npz"


# --- ClampHook : contrat sur SAE synthetique --------------------------------

def _fake_sae(d_model=8, d_sae=16, seed=0):
    torch = pytest.importorskip("torch")
    g = torch.Generator().manual_seed(seed)
    return {
        "W_enc": torch.randn(d_sae, d_model, generator=g),
        "b_enc": torch.randn(d_sae, generator=g),
        "W_dec": torch.randn(d_sae, d_model, generator=g),
        "b_dec": None,
    }


def _expected_clamp(h, sae, ids, alpha):
    torch = pytest.importorskip("torch")
    acts = torch.relu(h @ sae["W_enc"][ids].T + sae["b_enc"][ids])
    return h - alpha * (acts @ sae["W_dec"][ids])


def test_clamp_hook_neutralite_alpha_zero():
    # alpha=0 : le hook rend la sortie ELLE-MEME (pas de copie superflue) —
    # c'est le contrat qui fonde le controle de plomberie du notebook.
    torch = pytest.importorskip("torch")
    mod = _load_script_module()
    hook = mod.ClampHook(_fake_sae(), [1, 3, 5], 0.0)
    out = torch.randn(1, 10, 8)
    assert hook(None, None, out) is out


def test_clamp_hook_annulation_exacte_alpha_un():
    torch = pytest.importorskip("torch")
    mod = _load_script_module()
    torch.manual_seed(1)
    sae = _fake_sae(seed=1)
    ids = [0, 2, 4, 6]
    hook = mod.ClampHook(sae, ids, 1.0)
    h = torch.randn(1, 12, 8)
    got = hook(None, None, h)
    assert isinstance(got, torch.Tensor)
    assert torch.allclose(got, _expected_clamp(h, sae, ids, 1.0), atol=1e-5)


def test_clamp_hook_interpolation_lineaire_en_alpha():
    # Le delta est lineaire en alpha : clamp a 0.5 = moyenne exacte du
    # residu intact et du clamp plein. Sans cette linearite, le balayage
    # d'intensite ne mesurerait pas ce qu'il pretend mesurer.
    torch = pytest.importorskip("torch")
    mod = _load_script_module()
    sae = _fake_sae(seed=2)
    ids = [1, 4, 7]
    h = torch.randn(1, 9, 8)
    half = mod.ClampHook(sae, ids, 0.5)(None, None, h)
    full = mod.ClampHook(sae, ids, 1.0)(None, None, h)
    assert torch.allclose(half, (h + full) / 2, atol=1e-5)


def test_clamp_hook_exige_w_dec():
    torch = pytest.importorskip("torch")
    mod = _load_script_module()
    sae = _fake_sae()
    sae["W_dec"] = None
    with pytest.raises(SystemExit):
        mod.ClampHook(sae, [1], 1.0)


def test_clamp_hook_sortie_tuple_preservee():
    # Le hook d'une couche dont la sortie est un tuple doit rendre un tuple
    # de meme arite, la position 0 remplacee.
    torch = pytest.importorskip("torch")
    mod = _load_script_module()
    sae = _fake_sae(seed=3)
    hook = mod.ClampHook(sae, [2], 1.0)
    h = torch.randn(1, 5, 8)
    extra = torch.randn(5, 3)
    out = hook(None, None, (h, extra))
    assert isinstance(out, tuple) and len(out) == 2
    assert out[1] is extra
    assert torch.allclose(out[0], _expected_clamp(h, sae, [2], 1.0), atol=1e-5)


# --- CaptureHook : lecture sans modification -------------------------------

def test_capture_hook_ne_modifie_pas_la_sortie():
    torch = pytest.importorskip("torch")
    mod = _load_script_module()
    cap = mod.CaptureHook()
    out = torch.randn(1, 7, 8)
    ret = cap(None, None, out)
    assert ret is out
    assert cap.hidden is not None
    assert cap.hidden.shape == (7, 8)
    assert torch.allclose(cap.hidden, out[0])


# --- random_panel_control : controle permute du panel (phase 6) -------------

def test_random_panel_meme_taille_hors_panel():
    mod = _load_script_module()
    panel = [7, 101, 4096, 21004]
    drawn = mod.random_panel_control(panel, d_sae=32768, seed=42)
    assert len(drawn) == len(panel)
    assert set(drawn).isdisjoint(panel)      # aucun id du panel differentiel
    assert all(0 <= i < 32768 for i in drawn)


def test_random_panel_seed_reproductible():
    mod = _load_script_module()
    panel = [7, 101, 4096, 21004]
    a = mod.random_panel_control(panel, 32768, seed=7)
    b = mod.random_panel_control(panel, 32768, seed=7)
    c = mod.random_panel_control(panel, 32768, seed=8)
    assert a == b                            # seed => tirage identique
    assert a != c                            # un autre seed deplace le tirage


def test_random_panel_refuse_panel_saturant():
    # Le tirage exige des candidats hors panel : un panel de la taille de
    # d_sae doit etre refuse explicitement, pas silencieusement vide.
    mod = _load_script_module()
    with pytest.raises(ValueError):
        mod.random_panel_control(list(range(10)), d_sae=10, seed=1)
