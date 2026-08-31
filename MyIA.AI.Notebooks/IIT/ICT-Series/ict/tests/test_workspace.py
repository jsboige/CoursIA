"""Tests unitaires pour ``ict.workspace`` (ICT-24, #5635 — livrable 3).

Le notebook ICT-24 a livré les Gates 22-23 avec un générateur synthétique
inline (cellule 7) où hub et ignitions sont *plantés* dans un panel AR(1).
Ces tests figent ce contrat de sanité — le hub planté doit être retrouvé
par ``workspace_candidates``, les ignitions détectées par
``ignition_events``, et la batterie event-triggered doit créditer la
dynamique plantée (contrast > 0), pas celle d'un panel sans structure.
Les tests sur les ``.npz`` committés attestent le chemin réel du notebook
(``load_traces`` -> ``differential_features`` -> ``acts_topk_panels`` ->
``concentration_series``). GPU-free, déterministes (rng seedé partout).
"""

from __future__ import annotations

from pathlib import Path

import numpy as np
import pytest

from ict import sae_traces as st
from ict import workspace as ws

TRACES_DIR = Path(__file__).resolve().parent.parent.parent / "traces"


# ---------------------------------------------------------------------------
# Générateur synthétique — miroir de la cellule 7 du notebook ICT-24
# (hub planté -> cibles à lag fixe ; ignitions = bursts >> bruit de fond)
# ---------------------------------------------------------------------------

def panel_with_hub_and_ignitions(T=1500, K=32, hub_idx=0, targets=(5, 6, 7), lag=3,
                                 hub_strength=0.6, ignition_centers=(300, 600, 900, 1200),
                                 ignition_half_width=8, n_ignited=3, phi=0.5, sigma=0.4,
                                 seed=0):
    g = np.random.default_rng(seed)
    acts = np.empty((T, K), dtype=float)
    acts[0] = np.abs(g.standard_normal(K))
    tgt = np.array(targets, dtype=int)
    for t in range(1, T):
        nxt = phi * acts[t - 1] + sigma * g.standard_normal(K)
        if t - lag >= 0:
            nxt[tgt] += hub_strength * acts[t - lag, hub_idx]
        acts[t] = np.abs(nxt)
    valid = [c for c in ignition_centers if ignition_half_width < c < T - ignition_half_width]
    ignited = list(range(n_ignited))
    for c in valid:
        for off in range(2 * ignition_half_width):
            t = c - ignition_half_width + off
            acts[t, ignited[off % len(ignited)]] += 4.0  # burst >> bruit de fond
    return acts, {"hub_idx": hub_idx, "targets": list(targets), "centers": valid}


def states_with_planted_events(T=600, centers=(120, 300, 480), window=18, seed=0):
    """États à dynamique multi-échelle dans les fenêtres plantées, iid hors fenêtres."""
    g = np.random.default_rng(seed)
    mask = np.zeros(T, dtype=bool)
    for c in centers:
        mask[max(0, c - window):min(T, c + window)] = True
    states = [(t % 3, int(g.integers(0, 2))) if mask[t] else int(g.integers(0, 4)) for t in range(T)]
    return states, list(centers)


@pytest.fixture(scope="module")
def syn_panel():
    return panel_with_hub_and_ignitions(seed=0)


# ---------------------------------------------------------------------------
# concentration_series
# ---------------------------------------------------------------------------

def test_concentration_series_uniform_panel_is_low():
    """Un panel uniforme (masse équipartie) a une concentration Gini ~ 0."""
    T, K = 400, 16
    rng = np.random.default_rng(1)
    acts = 1.0 + 1e-3 * rng.standard_normal((T, K))  # quasi-équipartition
    conc = ws.concentration_series(acts, metric="gini")
    assert conc.shape == (T,)
    assert np.isfinite(conc).all()
    assert conc.mean() < 0.05


def test_concentration_series_delta_panel_is_high():
    """Un panel delta (toute la masse sur une feature par pas) a un Gini ~ 1."""
    T, K = 400, 16
    rng = np.random.default_rng(2)
    acts = 1e-6 * rng.random((T, K))
    acts[np.arange(T), rng.integers(0, K, T)] = 1.0
    conc = ws.concentration_series(acts, metric="gini")
    assert conc.mean() > 0.9


def test_concentration_series_spikes_at_planted_ignitions(syn_panel):
    """Le Gini grimpe dans les fenêtres d'ignition (3 features portent des bursts +4)."""
    acts, info = syn_panel
    conc = ws.concentration_series(acts, metric="gini")
    hw = 8
    in_win = np.concatenate([conc[c - hw:c + hw] for c in info["centers"]])
    out_win = np.delete(conc, np.concatenate([np.arange(c - 2 * hw, c + 2 * hw)
                                              for c in info["centers"]]))
    assert in_win.mean() > out_win.mean()


# ---------------------------------------------------------------------------
# ignition_events
# ---------------------------------------------------------------------------

def test_ignition_events_detects_planted_centers(syn_panel):
    """Les événements détectés retombent sur les centres plantés (± demi-largeur)."""
    acts, info = syn_panel
    conc = ws.concentration_series(acts, metric="gini")
    thr = float(np.quantile(conc, 0.85))
    events = ws.ignition_events(conc, threshold=thr, persistence=3)
    centers = [e["center"] for e in events]
    assert len(centers) >= 1
    for planted in info["centers"]:
        assert min(abs(np.array(centers) - planted)) <= 8, (
            f"centre planté {planted} non détecté (détectés : {centers})")


def test_ignition_events_requires_persistence():
    """Un spike d'un pas (largeur 1) ne passe pas persistence=3 : c'est du bruit, pas une ignition."""
    T = 300
    conc = np.full(T, 0.2)
    conc[150] = 1.0  # spike isolé
    events = ws.ignition_events(conc, threshold=0.5, persistence=3)
    assert events == []


# ---------------------------------------------------------------------------
# lagged_influence / fanout_profile / workspace_candidates — le hub planté
# ---------------------------------------------------------------------------

def test_planted_hub_recovered_by_workspace_candidates(syn_panel):
    """Sanité centrale du notebook (cellule 7) : hub_idx est dans le top-10% fan-out."""
    acts, info = syn_panel
    infl = ws.lagged_influence(acts, max_lag=6)
    fp = ws.fanout_profile(infl["matrix"], z_threshold=2.0)
    cand = ws.workspace_candidates(fp["fanout"], top_fraction=0.1)
    assert info["hub_idx"] in cand["indices"], (
        f"hub planté {info['hub_idx']} non retrouvé dans {cand['indices']}")


def test_workspace_candidates_contract(syn_panel):
    """Contrat structurel : champs du dict, cardinal cohérent, gini borné."""
    acts, _ = syn_panel
    infl = ws.lagged_influence(acts, max_lag=6)
    fp = ws.fanout_profile(infl["matrix"], z_threshold=2.0)
    cand = ws.workspace_candidates(fp["fanout"], top_fraction=0.1)
    assert set(cand) >= {"indices", "gini", "concentrated", "n_selected"}
    assert len(cand["indices"]) == cand["n_selected"] >= 1
    assert 0.0 <= cand["gini"] <= 1.0 + 1e-9
    assert isinstance(cand["concentrated"], bool)
    fanout = np.asarray(fp["fanout"])
    assert fanout.shape == (acts.shape[1],)
    assert np.isfinite(fanout).all() and (fanout >= 0).all()


def test_shuffled_panel_kills_hub_signal(syn_panel):
    """Contrôle temps-mélangé (Gate 22) : mélanger chaque feature détruit la lag-structure,
    le hub planté ne doit plus dominer le fan-out."""
    acts, info = syn_panel
    g = np.random.default_rng(3)
    shuf = acts.copy()
    for j in range(shuf.shape[1]):
        g.shuffle(shuf[:, j])
    infl = ws.lagged_influence(shuf, max_lag=6)
    fp = ws.fanout_profile(infl["matrix"], z_threshold=2.0)
    cand = ws.workspace_candidates(fp["fanout"], top_fraction=0.1)
    assert info["hub_idx"] not in cand["indices"]


# ---------------------------------------------------------------------------
# event_triggered_battery — la dynamique plantée est créditée
# ---------------------------------------------------------------------------

def test_event_triggered_battery_credits_planted_dynamics():
    """Contrat sanité du notebook : contrast > 0 quand la dynamique est plantée aux événements."""
    states, centers = states_with_planted_events(seed=0)
    out = ws.event_triggered_battery(states, centers, window=12,
                                     rng=np.random.default_rng(11), n_shuffles=10)
    assert out["contrast"] > 0, f"contrast = {out['contrast']} : la dynamique plantée n'est pas créditée"
    assert out["n_events"] == len(centers)
    assert 0.0 <= out["fraction_credited_events"] <= 1.0


def test_event_triggered_battery_uniform_states_score_lower():
    """Contre-témoin : états iid sans structure -> contrast inférieur au planté (même fenêtrage)."""
    planted, centers = states_with_planted_events(seed=0)
    out_planted = ws.event_triggered_battery(planted, centers, window=12,
                                             rng=np.random.default_rng(11), n_shuffles=10)
    g = np.random.default_rng(4)
    uniform = [int(g.integers(0, 4)) for _ in range(600)]
    out_uniform = ws.event_triggered_battery(uniform, list(centers), window=12,
                                             rng=np.random.default_rng(11), n_shuffles=10)
    assert out_uniform["contrast"] < out_planted["contrast"]


# ---------------------------------------------------------------------------
# Chemin réel : tests sur les .npz committés (ICT-21, S4)
# ---------------------------------------------------------------------------

def _real_panel(npz_name: str, k: int) -> np.ndarray:
    traces = st.load_traces(TRACES_DIR / npz_name)
    panel = st.differential_features(traces, k=k)
    panels = st.acts_topk_panels(traces, panel)
    first = sorted(panels)[0]
    return panels[first]


def test_real_trained_trace_concentration_is_finite_and_bounded():
    """Chemin du notebook sur la trace committée trained : Gini fini, dans [0, 1]."""
    acts = _real_panel("ict21_sae_layer16_trained.npz", k=64)
    assert acts.ndim == 2 and acts.shape[1] == 64
    conc = ws.concentration_series(acts, metric="gini")
    assert conc.shape == (acts.shape[0],)
    assert np.isfinite(conc).all()
    assert (conc >= 0.0).all() and (conc <= 1.0 + 1e-9).all()


def test_real_trained_trace_fanout_is_finite():
    """Gate 22 en miniature sur la trace réelle : influence + fan-out finis, K features."""
    acts = _real_panel("ict21_sae_layer16_trained.npz", k=32)
    infl = ws.lagged_influence(acts, max_lag=3)
    fp = ws.fanout_profile(infl["matrix"], z_threshold=2.0)
    assert np.isfinite(fp["fanout"]).all()
    assert fp["fanout"].shape == (acts.shape[1],)


def test_real_control_trace_loads_same_path():
    """La trace contrôle (modèle non entraîné) passe le même chemin — prérequis du contraste Gate 22."""
    acts = _real_panel("ict21_sae_layer16_control.npz", k=64)
    assert acts.ndim == 2 and acts.shape[1] == 64
    assert np.isfinite(acts).all()
