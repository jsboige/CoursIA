"""Tests de l'adaptateur Global Workspace (ICT-24, numpy-only).

Couvrent les 6 primitives de :mod:`ict.workspace` sur des donnees synthetiques
**GPU-free**. Deux generateurs separent deux verites terrain distinctes :

1. :func:`_panel_with_hub_and_ignitions` -- **panel d'activations continues**
   (T, K) avec (a) un **hub d'influence plante** (une feature qui cause, a
   retard connu, plusieurs cibles) et (b) des **ignitions plantees** (cycle
   tournant deterministe entre quelques features, qui concentre l'activite a
   chaque pas). Outille les tests spatiaux : ``concentration_series``,
   ``ignition_events``, ``lagged_influence``, ``fanout_profile``,
   ``workspace_candidates``.

2. :func:`_states_with_planted_events` -- **suite d'etats deja discretisee**
   avec, sur les fenetres evenement, une structure **multi-echelles** (macro-cycle
   deterministe + micro-bruit, cf. ``_macro_deterministic_micro_random`` de
   ``test_synthesis``) et, sur les fenetres neutres, du bruit iid. Outille les
   tests de la batterie event-triggered.

Honestete (G.9 / Prong B) : on ne teste PAS qu'on "detecte du workspace dans
Claude" (ca, c'est le boulot du notebook sur les traces SAE de #5101) ; on teste
que l'**adaptateur** mesure correctement les phenomenes qu'on y plante, avec des
**controles negatifs** (panel sans hub, activite uniforme, etats iid) qui doivent
donner le verdict oppose.

Numpy + pytest. Le module ne depend que de numpy (et de :mod:`ict.synthesis`
pour :func:`event_triggered_battery`).
"""

import os
import sys

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import workspace as ws  # noqa: E402


# --------------------------------------------------------------------------- #
# Generateur 1 : panel d'activations continues avec hub + ignitions
# --------------------------------------------------------------------------- #
def _panel_with_hub_and_ignitions(
    T: int = 1500,
    K: int = 32,
    hub_idx: int = 0,
    targets=(5, 6, 7),
    lag: int = 3,
    hub_strength: float = 0.6,
    ignition_centers=(300, 600, 900, 1200),
    ignition_half_width: int = 8,
    n_ignited: int = 3,
    phi: float = 0.5,
    sigma: float = 0.4,
    seed: int = 0,
):
    """Panel AR(1) avec hub d'influence + fenetres d'ignition (cycle tournant).

    Retourne ``(acts, info)`` ou ``acts`` est (T, K) non-negatif et ``info``
    contient la verite terrain : ``hub_idx``, ``targets``, ``lag``,
    ``ignition_centers`` (filtrés dans [hw, T-hw]).

    Mecanisme :
    * **Baseline AR(1)** : ``a[t,k] = |phi*a[t-1,k] + noise|``.
    * **Hub plante** : ``a[t, target] += hub_strength * a[t-lag, hub_idx]`` pour
      chaque cible. Le hub est exogene (pas de parent). La lag-correlation
      ``hub -> target`` doit ressortir franchement au lag plante.
    * **Ignitions (cycle tournant)** : autour de chaque centre, a chaque pas on
      booste une seule feature parmi ``n_ignited``, en cycle ``0,1,2,0,1,2...``.
      -> a chaque pas une feature porte un burst >> bruit de fond, donc la
      concentration Gini spike fortement (ideal pour ``concentration_series`` et
      ``ignition_events``).
    """
    g = np.random.default_rng(seed)
    acts = np.empty((T, K), dtype=float)
    acts[0] = np.abs(g.standard_normal(K))
    targets_arr = np.array(targets, dtype=int)

    for t in range(1, T):
        noise = sigma * g.standard_normal(K)
        nxt = phi * acts[t - 1] + noise
        if t - lag >= 0 and len(targets_arr) > 0:
            nxt[targets_arr] += hub_strength * acts[t - lag, hub_idx]
        acts[t] = np.abs(nxt)

    # ignitions en cycle tournant (filtre les centres hors-range)
    valid_centers = [c for c in ignition_centers
                     if ignition_half_width < c < T - ignition_half_width]
    ignited = list(range(n_ignited))
    for c in valid_centers:
        lo = c - ignition_half_width
        hi = c + ignition_half_width
        for offset in range(hi - lo):
            t = lo + offset
            k_cycle = ignited[offset % len(ignited)]
            acts[t, k_cycle] += 4.0  # burst >> bruit de fond (sigma~0.4)

    info = {
        "hub_idx": hub_idx,
        "targets": list(targets),
        "lag": lag,
        "ignition_centers": valid_centers,
        "ignited_features": ignited,
    }
    return acts, info


# --------------------------------------------------------------------------- #
# Generateur 2 : suite d'etats discrete avec structure multi-echelles plantee
# --------------------------------------------------------------------------- #
def _states_with_planted_events(
    T: int = 600,
    event_centers=(120, 300, 480),
    window: int = 18,
    seed: int = 0,
):
    """Suite d'etats discrete avec verite terrain event/neutral plantee.

    Les pas HORS evenement sont du **bruit iid** sur 4 etats (pas de dynamique ->
    emergence non creditee par ``emergence_gain``). Les pas DANS une fenetre
    evenement suivent un **macro-cycle deterministe 0->1->2->0** avec un
    **micro-bruit** (bit aleatoire) -> structure multi-echelles reelle ->
    emergence creditee (exactement le motif ``_macro_deterministic_micro_random``
    de ``test_synthesis``).

    Retourne ``(states, event_centers, event_mask)``. Cette suite sert a valider
    la MECANIQUE de :func:`event_triggered_battery` (contraste per-event vs
    per-neutral via le meme ``emergence_gain``), pas a detecter du workspace reel.
    """
    g = np.random.default_rng(seed)
    event_mask = np.zeros(T, dtype=bool)
    for c in event_centers:
        lo = max(0, c - window)
        hi = min(T, c + window)
        event_mask[lo:hi] = True

    states = []
    for t in range(T):
        if event_mask[t]:
            m = t % 3  # macro-cycle deterministe
            bit = int(g.integers(0, 2))  # micro-bruit
            states.append((m, bit))
        else:
            states.append(int(g.integers(0, 4)))  # iid, pas de dynamique
    return states, list(event_centers), event_mask


# --------------------------------------------------------------------------- #
# concentration_series
# --------------------------------------------------------------------------- #
def test_concentration_series_uniform_is_near_zero():
    """Activite uniforme sur toutes les features -> Gini ~ 0 (rien de concentre)."""
    T, K = 50, 16
    acts = np.ones((T, K))
    conc = ws.concentration_series(acts, metric="gini")
    assert conc.shape == (T,)
    assert conc.mean() < 0.05, f"attendu Gini ~ 0 sur uniforme, got mean={conc.mean():.3f}"


def test_concentration_series_concentrated_is_near_one():
    """Toute l'activite sur UNE feature -> Gini ~ (K-1)/K ~ 1 (max concentration)."""
    T, K = 50, 16
    acts = np.zeros((T, K))
    acts[:, 3] = 1.0
    conc = ws.concentration_series(acts, metric="gini")
    assert conc.mean() > 0.85, f"attendu Gini ~ 1 sur concentrate, got mean={conc.mean():.3f}"


def test_concentration_series_inactive_step_is_zero():
    """Pas inactif (sum=0) -> convention 0.0 (documentee), pas de NaN."""
    acts = np.zeros((5, 8))
    acts[2] = np.array([1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0])  # un pas concentre
    conc = ws.concentration_series(acts, metric="gini")
    assert conc[0] == 0.0  # pas inactif
    assert conc[2] > 0.8  # le pas concentre
    assert np.isfinite(conc).all()


def test_concentration_series_participation_ratio_metric():
    """metric='participation_ratio' : meme sens (1=concentre) sur les deux extremes."""
    T = 10
    uniform = np.ones((T, 16))
    concentrated = np.zeros((T, 16)); concentrated[:, 0] = 1.0
    cu = ws.concentration_series(uniform, metric="participation_ratio").mean()
    cc = ws.concentration_series(concentrated, metric="participation_ratio").mean()
    assert cu < 0.2
    assert cc > 0.8


def test_concentration_series_detects_planted_ignitions():
    """Sur le panel plante : la concentration SPIKE autour des centres d'ignition."""
    acts, info = _panel_with_hub_and_ignitions(seed=1)
    conc = ws.concentration_series(acts, metric="gini")
    # concentration de base (hors ignitions)
    mask_base = np.ones(len(conc), dtype=bool)
    for c in info["ignition_centers"]:
        mask_base[max(0, c - 20):c + 20] = False
    base_level = conc[mask_base].mean()
    # concentration moyenne autour des ignitions (fenetre etroite)
    ev_levels = []
    for c in info["ignition_centers"]:
        lo, hi = max(0, c - 10), min(len(conc), c + 10)
        ev_levels.append(conc[lo:hi].mean())
    ev_level = float(np.mean(ev_levels))
    # Le contraste est reel et deterministe (seed fixe) : le baseline AR(1) en
    # demi-gaussienne est deja modement concentre (~0.42) ; le cycle d'ignition
    # le fait monter nettement (~0.52). On exige un delta > 0.05, robuste.
    assert ev_level > base_level + 0.05, (
        f"ignition devrait concentrer > base: ev={ev_level:.3f} base={base_level:.3f}"
    )


# --------------------------------------------------------------------------- #
# ignition_events
# --------------------------------------------------------------------------- #
def test_ignition_events_finds_planted_centers_within_tolerance():
    """Les ignitions plantees sont retrouvees a tolerance pres."""
    acts, info = _panel_with_hub_and_ignitions(seed=2)
    conc = ws.concentration_series(acts, metric="gini")
    thr = float(np.quantile(conc, 0.85))
    events = ws.ignition_events(conc, threshold=thr, persistence=3)
    assert len(events) > 0, "aucune ignition detectee alors qu'on en a plante"
    centers_found = [e["center"] for e in events]
    for c_true in info["ignition_centers"]:
        nearest = min(abs(c - c_true) for c in centers_found)
        assert nearest < 15, (
            f"ignition plantee a {c_true} non retrouvee (plus proche: {nearest})"
        )


def test_ignition_events_empty_on_stationary_uniform():
    """Activite uniforme : aucune ignition (concentration ~ 0 < seuil)."""
    acts = np.ones((200, 16))
    conc = ws.concentration_series(acts, metric="gini")
    events = ws.ignition_events(conc, threshold=0.3, persistence=3)
    assert events == []


def test_ignition_events_persistence_filters_isolated_spikes():
    """Un pic isole (longueur 1) doit etre filtre par persistence>=3."""
    conc = np.zeros(100)
    conc[50] = 1.0
    events = ws.ignition_events(conc, threshold=0.5, persistence=3)
    assert events == []


def test_ignition_events_persistence_one_keeps_isolated_spike():
    """Reciproque : persistence=1 garde le pic isole (comportement documente)."""
    conc = np.zeros(100)
    conc[50] = 1.0
    events = ws.ignition_events(conc, threshold=0.5, persistence=1)
    assert len(events) == 1
    assert events[0]["center"] == 50
    assert events[0]["length"] == 1


# --------------------------------------------------------------------------- #
# lagged_influence
# --------------------------------------------------------------------------- #
def test_lagged_influence_finds_planted_hub_at_planted_lag():
    """Le hub plante ressort : influence hub->cibles elevee, au bon lag."""
    acts, info = _panel_with_hub_and_ignitions(seed=3)
    infl = ws.lagged_influence(acts, max_lag=6)
    M = infl["matrix"]
    L = infl["best_lag"]
    off = M[~np.eye(M.shape[0], dtype=bool)]
    baseline = float(np.median(np.abs(off)))
    for tgt in info["targets"]:
        val = abs(M[info["hub_idx"], tgt])
        assert val > 2.0 * baseline, (
            f"influence hub->{tgt} = {val:.3f} pas > 2x mediane {baseline:.3f}"
        )
        assert L[info["hub_idx"], tgt] == info["lag"], (
            f"best lag hub->{tgt} = {L[info['hub_idx'], tgt]} != lag plante {info['lag']}"
        )


def test_lagged_influence_no_hub_in_null_panel():
    """Controle negatif : panel AR(1) sans hub -> pas d'influence dominante."""
    g = np.random.default_rng(99)
    T, K = 1500, 24
    acts = np.empty((T, K))
    acts[0] = np.abs(g.standard_normal(K))
    phi = 0.5
    for t in range(1, T):
        acts[t] = np.abs(phi * acts[t - 1] + 0.4 * g.standard_normal(K))
    infl = ws.lagged_influence(acts, max_lag=5)
    M = infl["matrix"]
    off = np.abs(M[~np.eye(K, dtype=bool)])
    med = float(np.median(off))
    mad = float(np.median(np.abs(off - med))) + 1e-9
    z = np.abs(off - med) / (1.4826 * mad)
    assert z.max() < 6.0, f"influence anormale sans hub plante: z-max={z.max():.2f}"


def test_lagged_influence_diagonal_is_zero():
    """La diagonale est nulle (un feature ne s'influence pas lui-meme ici)."""
    acts, _ = _panel_with_hub_and_ignitions(seed=4, T=500, K=12,
                                            ignition_centers=(150, 300, 400))
    M = ws.lagged_influence(acts, max_lag=3)["matrix"]
    assert np.allclose(np.diag(M), 0.0)


# --------------------------------------------------------------------------- #
# fanout_profile + workspace_candidates
# --------------------------------------------------------------------------- #
def test_fanout_profile_hub_has_disproportionate_fanout():
    """Le hub plante a un fan-out nettement superieur a la mediane."""
    acts, info = _panel_with_hub_and_ignitions(seed=5, K=32)
    infl = ws.lagged_influence(acts, max_lag=6)
    fp = ws.fanout_profile(infl["matrix"], z_threshold=2.0)
    fanout = fp["fanout"]
    med = float(np.median(fanout))
    assert fanout[info["hub_idx"]] > med, (
        f"hub fan-out={fanout[info['hub_idx']]} pas > mediane {med}"
    )


def test_workspace_candidates_includes_hub_in_top():
    """Le hub plante est dans les candidates workspace (top 10 % fan-out)."""
    acts, info = _panel_with_hub_and_ignitions(seed=6, K=32)
    infl = ws.lagged_influence(acts, max_lag=6)
    fp = ws.fanout_profile(infl["matrix"], z_threshold=2.0)
    cand = ws.workspace_candidates(fp["fanout"], top_fraction=0.1)
    assert cand["n_selected"] == max(1, int(np.ceil(0.1 * 32)))
    assert info["hub_idx"] in set(int(i) for i in cand["indices"]), (
        f"hub {info['hub_idx']} absent du top-10% {list(cand['indices'])}"
    )
    assert cand["gini"] > 0.0  # la structure hub => fanout non uniforme


def test_workspace_candidates_uniform_fanout_not_concentrated():
    """Controle negatif : fan-out uniforme -> Gini ~ 0, pas concentre."""
    fanout_uniform = np.full(32, 5.0)
    cand = ws.workspace_candidates(fanout_uniform, top_fraction=0.1)
    assert cand["gini"] < 1e-9
    assert cand["concentrated"] is False


# --------------------------------------------------------------------------- #
# event_triggered_battery (reutilise synthesis.emergence_gain VERBATIM)
# --------------------------------------------------------------------------- #
def test_event_triggered_battery_keys_and_structure():
    """La batterie retourne tous les champs documents (contraste + per-event)."""
    states, event_centers, _ = _states_with_planted_events(seed=7)
    rng = np.random.default_rng(11)
    out = ws.event_triggered_battery(states, event_centers, window=12, rng=rng, n_shuffles=8)
    for key in ("per_event", "per_neutral", "ec_gain_event", "ec_gain_neutral",
                "contrast", "fraction_credited_events", "fraction_credited_neutral",
                "n_events", "n_neutral"):
        assert key in out, f"cle manquante: {key}"
    assert out["n_events"] == len(event_centers)
    assert out["n_neutral"] == len(event_centers)  # defaut = len(events)


def test_event_triggered_battery_events_carry_more_emergence_than_neutral():
    """Gate 23 (co-location) : fenetres event (structure multi-echelles plantee)
    portent plus d'emergence creditee que les fenetres neutres (iid).

    Honnete : ce test valide la MECANIQUE de contraste de l'adaptateur (per-event
    vs per-neutral via le meme ``emergence_gain``), sur une suite d'etats avec
    verite terrain plantee (macro-cycle micro-bruite dans event, iid dans neutral).
    L'objectif n'est pas de detecter du workspace reel -- c'est l'affaire du
    notebook ICT-24 sur les traces SAE de #5101.
    """
    states, event_centers, _ = _states_with_planted_events(seed=8)
    rng_eval = np.random.default_rng(21)
    out = ws.event_triggered_battery(
        states, event_centers, window=15, rng=rng_eval, n_shuffles=8
    )
    assert out["contrast"] > 0, (
        f"contrast attendu > 0 (events portent plus d'emergence), got {out['contrast']:.4f}"
    )


def test_event_triggered_battery_explicit_neutral_centers():
    """On peut fournir explicitement les centres neutres (appariement controle)."""
    states, event_centers, _ = _states_with_planted_events(T=600, seed=9)
    # neutres : milieux entre les events (zones iid)
    neutral_centers = [60, 210, 390, 540]
    rng = np.random.default_rng(33)
    out = ws.event_triggered_battery(
        states, event_centers, window=12, rng=rng,
        n_shuffles=6, neutral=neutral_centers,
    )
    assert out["n_neutral"] == len(neutral_centers)


def test_event_triggered_battery_reproducible_with_seed():
    """Meme rng (meme etat) -> meme resultats (pas d'etat cache global)."""
    states, event_centers, _ = _states_with_planted_events(seed=10)
    out1 = ws.event_triggered_battery(
        states, event_centers, window=10,
        rng=np.random.default_rng(7), n_shuffles=5,
    )
    out2 = ws.event_triggered_battery(
        states, event_centers, window=10,
        rng=np.random.default_rng(7), n_shuffles=5,
    )
    assert out1["contrast"] == out2["contrast"]
    assert out1["fraction_credited_events"] == out2["fraction_credited_events"]


def test_event_triggered_battery_short_window_handled_gracefully():
    """Une fenetre trop courte (bords) ne fait pas crasher : branche _short."""
    states = list(range(50))  # suite triviale
    rng = np.random.default_rng(0)
    # event au bord avec window=1 -> extrait < 3 elements
    out = ws.event_triggered_battery(states, [0], window=1, rng=rng, n_shuffles=3)
    assert out["n_events"] == 1
    # le per-event est marque court (ec_gain=0 convention) -- pas de crash
