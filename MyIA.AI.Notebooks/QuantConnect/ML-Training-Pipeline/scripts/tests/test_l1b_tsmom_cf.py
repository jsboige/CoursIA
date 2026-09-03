"""Tests de `L1b_tsmom_cf` -- chaque assertion porte son controle positif.

Un test qui verifie seulement qu'une fonction "rend un nombre" ne mesure rien :
il passerait sur une implementation debranchee. Chaque bloc ci-dessous ecrit donc
l'ORDRE DE GRANDEUR attendu a cote de la mesure, et plusieurs verifient qu'une
forme volontairement corrompue est bien rejetee.
"""

import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

SCRIPTS_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS_DIR))

from L1b_tsmom_cf import (  # noqa: E402
    CF_BOUNDS,
    REBALANCE_MONTHLY,
    TARGET_VOL,
    TSTAT_LOOKBACK,
    VOL_WINDOW_YZ,
    build_positions,
    close_to_close_vol,
    compute_verdict,
    correlation_factor,
    realised_forward_vol,
    seed_view,
    sign_signal,
    tstat_signal,
    yang_zhang_vol,
)


# --------------------------------------------------------------------------
# Fabriques de series synthetiques
# --------------------------------------------------------------------------

def make_ohlc(n=600, daily_vol=0.01, drift=0.0, seed=0):
    """OHLC coherent (Low <= Open,Close <= High) tire d'un mouvement brownien."""
    rng = np.random.default_rng(seed)
    log_ret = rng.normal(drift, daily_vol, n)
    close = 100.0 * np.exp(np.cumsum(log_ret))
    prev_close = np.concatenate([[100.0], close[:-1]])
    # ouverture = saut overnight de meme echelle, puis extremes intraday
    open_ = prev_close * np.exp(rng.normal(0.0, daily_vol / 2, n))
    hi_extra = np.abs(rng.normal(0.0, daily_vol / 2, n))
    lo_extra = np.abs(rng.normal(0.0, daily_vol / 2, n))
    high = np.maximum(open_, close) * np.exp(hi_extra)
    low = np.minimum(open_, close) * np.exp(-lo_extra)
    idx = pd.bdate_range("2015-01-01", periods=n)
    return pd.DataFrame({"Open": open_, "High": high, "Low": low,
                         "Close": close, "Volume": 1e6}, index=idx)


def make_trending(n=600, slope=0.0015, noise=0.004, seed=0):
    """Serie a tendance nette : la t-stat doit y saturer."""
    rng = np.random.default_rng(seed)
    log_ret = slope + rng.normal(0.0, noise, n)
    idx = pd.bdate_range("2015-01-01", periods=n)
    return pd.Series(100.0 * np.exp(np.cumsum(log_ret)), index=idx)


# --------------------------------------------------------------------------
# Levier 2 -- Yang-Zhang
# --------------------------------------------------------------------------

def test_yang_zhang_recovers_the_injected_volatility():
    """Controle positif : la vol injectee est connue, l'estimation doit la retrouver.

    daily_vol = 1 % -> vol annualisee attendue ~= 0.01 * sqrt(252) ~= 0.159.
    Tolerance large (+/- 40 %) : Yang-Zhang agrege trois composantes dont deux
    sont ici simulees, pas mesurees sur un vrai carnet d'ordres.
    """
    df = make_ohlc(daily_vol=0.01, seed=1)
    est = yang_zhang_vol(df).dropna()
    attendu = 0.01 * np.sqrt(252)
    assert 0.6 * attendu < est.median() < 1.4 * attendu, (
        f"YZ median={est.median():.4f}, attendu ~{attendu:.4f}")


def test_yang_zhang_scales_with_volatility():
    """Controle positif d'ECART : doubler la vol doit ~doubler l'estimation.

    C'est le controle qui distingue un estimateur d'une constante : une fonction
    qui rendrait toujours 0.16 passerait le test precedent et echouerait ici.
    """
    calme = yang_zhang_vol(make_ohlc(daily_vol=0.01, seed=2)).dropna().median()
    agite = yang_zhang_vol(make_ohlc(daily_vol=0.02, seed=2)).dropna().median()
    ratio = agite / calme
    assert 1.6 < ratio < 2.4, f"ratio={ratio:.3f}, attendu ~2.0"


def test_yang_zhang_uses_the_intraday_range():
    """YZ doit differer de close-to-close : sinon les deux leviers sont le meme.

    Une implementation qui ignorerait High/Low rendrait exactement close-to-close,
    et l'ablation C-vs-B ne mesurerait rien.
    """
    df = make_ohlc(seed=3)
    yz = yang_zhang_vol(df, window=VOL_WINDOW_YZ).dropna()
    c2c = close_to_close_vol(df["Close"], window=VOL_WINDOW_YZ).dropna()
    commun = yz.index.intersection(c2c.index)
    ecart = (yz.loc[commun] - c2c.loc[commun]).abs().median()
    assert ecart > 1e-4, "YZ est indiscernable de close-to-close"


def test_realised_forward_vol_is_strictly_forward():
    """La cible du DM ne doit contenir aucune information disponible a t.

    Si le decalage etait absent, la valeur a t recouvrirait la fenetre qui la
    precede, et le "test de prevision" comparerait un estimateur a lui-meme.
    """
    df = make_ohlc(n=400, seed=4)
    fwd = realised_forward_vol(df["Close"], window=VOL_WINDOW_YZ)
    trailing = close_to_close_vol(df["Close"], window=VOL_WINDOW_YZ)
    # la cible a t doit egaler la vol trailing mesuree window jours plus tard
    aligne = trailing.shift(-VOL_WINDOW_YZ)
    pd.testing.assert_series_equal(fwd.dropna(), aligne.dropna(),
                                   check_names=False)
    assert fwd.iloc[-VOL_WINDOW_YZ:].isna().all(), (
        "les dernieres dates devraient etre NaN : leur futur n'existe pas")


# --------------------------------------------------------------------------
# Levier 1 -- signaux
# --------------------------------------------------------------------------

def test_tstat_signal_saturates_on_a_clear_trend():
    """Tendance nette -> |t| > 1 -> le signal doit saturer a +1."""
    closes = make_trending(slope=0.0015, noise=0.003, seed=5)
    sig = tstat_signal(closes).dropna()
    assert sig.iloc[-1] == pytest.approx(1.0), f"signal={sig.iloc[-1]:.4f}"


def test_tstat_signal_stays_inside_the_cap():
    for seed in (6, 7, 8):
        sig = tstat_signal(make_trending(slope=0.004, seed=seed)).dropna()
        assert sig.min() >= -1.0 and sig.max() <= 1.0


def test_tstat_signal_is_continuous_where_sign_is_binary():
    """Le point de l'article : sur une tendance FAIBLE, l'exposition se reduit.

    `sign` rend +/-1 quel que soit le niveau de preuve ; la t-stat doit rendre
    des valeurs strictement interieures. Sans cette difference, l'ablation B-vs-A
    ne mesurerait rien.
    """
    closes = make_trending(slope=0.00005, noise=0.012, seed=9)
    t = tstat_signal(closes).dropna()
    s = sign_signal(closes).dropna()
    interieurs = ((t.abs() > 1e-9) & (t.abs() < 0.999)).sum()
    assert interieurs > 0.5 * len(t), (
        f"seulement {interieurs}/{len(t)} valeurs strictement interieures")
    assert set(np.unique(s.to_numpy())) <= {-1.0, 0.0, 1.0}


def test_signals_need_a_full_lookback():
    closes = make_trending(n=TSTAT_LOOKBACK + 5, seed=10)
    assert tstat_signal(closes).iloc[:TSTAT_LOOKBACK - 1].isna().all()


# --------------------------------------------------------------------------
# Levier 3 -- facteur de correlation
# --------------------------------------------------------------------------

def _cf_on(returns: pd.DataFrame, signal_value: float = 1.0) -> float:
    signals = pd.DataFrame(signal_value, index=returns.index,
                           columns=returns.columns)
    return correlation_factor(signals, returns).dropna().median()


def test_cf_is_one_when_everything_moves_together():
    """rho_bar = 1 -> CF = sqrt(N/(1+(N-1))) = 1 : aucun benefice de diversification."""
    n, k = 400, 5
    idx = pd.bdate_range("2015-01-01", periods=n)
    base = np.random.default_rng(11).normal(0, 0.01, n)
    ret = pd.DataFrame({f"A{i}": base for i in range(k)}, index=idx)
    assert _cf_on(ret) == pytest.approx(1.0, abs=0.05)


def test_cf_approaches_sqrt_n_when_uncorrelated():
    """rho_bar = 0 -> CF = sqrt(N). Avec N=5, attendu ~2.24 (borne haute 3.0)."""
    n, k = 600, 5
    rng = np.random.default_rng(12)
    idx = pd.bdate_range("2015-01-01", periods=n)
    ret = pd.DataFrame({f"A{i}": rng.normal(0, 0.01, n) for i in range(k)},
                       index=idx)
    cf = _cf_on(ret)
    assert 1.8 < cf < 2.7, f"CF={cf:.3f}, attendu ~{np.sqrt(k):.2f}"


def test_cf_stays_inside_its_bounds():
    """Sans borne, un rho_bar proche de -1/(N-1) envoie le levier a l'infini."""
    n, k = 300, 4
    rng = np.random.default_rng(13)
    idx = pd.bdate_range("2015-01-01", periods=n)
    base = rng.normal(0, 0.01, n)
    # deux paires anti-correlees : rho_bar tres negatif
    ret = pd.DataFrame({"A0": base, "A1": -base,
                        "A2": base, "A3": -base}, index=idx)
    series = correlation_factor(
        pd.DataFrame(1.0, index=idx, columns=ret.columns), ret).dropna()
    assert series.min() >= CF_BOUNDS[0] - 1e-9
    assert series.max() <= CF_BOUNDS[1] + 1e-9
    assert len(series) > 0


def test_cf_reads_opposite_positions_as_diversification():
    """Deux actifs correles tenus en sens OPPOSES se diversifient.

    C'est ce que la ponderation par X_i X_j apporte : une correlation brute de +1
    donnerait CF = 1, alors que le portefeuille reel est neutre.
    """
    n = 400
    idx = pd.bdate_range("2015-01-01", periods=n)
    base = np.random.default_rng(14).normal(0, 0.01, n)
    ret = pd.DataFrame({"A": base, "B": base}, index=idx)
    memes = correlation_factor(
        pd.DataFrame({"A": 1.0, "B": 1.0}, index=idx), ret).dropna().median()
    opposes = correlation_factor(
        pd.DataFrame({"A": 1.0, "B": -1.0}, index=idx), ret).dropna().median()
    assert memes == pytest.approx(1.0, abs=0.05)
    assert opposes > memes + 0.2, (
        f"memes={memes:.3f} opposes={opposes:.3f} : la ponderation par signal "
        "n'est pas prise en compte")


# --------------------------------------------------------------------------
# Graines -- la regression que L1 porte encore
# --------------------------------------------------------------------------

def _fake_pre(n_symbols=20):
    idx = pd.bdate_range("2015-01-01", periods=100)
    cols = [f"S{i:02d}" for i in range(n_symbols)]
    return {"close": pd.DataFrame(1.0, index=idx, columns=cols)}


def test_seed_view_is_deterministic():
    pre = _fake_pre()
    assert seed_view(pre, 42) == seed_view(pre, 42)


def test_distinct_seeds_give_distinct_views():
    """LA regression que ce module existe pour ne pas reproduire.

    Dans `L1_tsmom.py`, le `rng` de la graine n'est jamais consomme : les quatre
    graines rendent des nombres identiques, l'ecart-type vaut 0, et la clause
    `t_stat >= 2.0` du gate rend BEATS inatteignable. Si ce test venait a passer
    avec des vues identiques, notre gate serait aussi vide que le sien.
    """
    pre = _fake_pre()
    vues = [seed_view(pre, s) for s in (0, 1, 7, 42)]
    assert len({tuple(v[0]) for v in vues}) > 1, "sous-paniers tous identiques"
    assert len({v[1] for v in vues}) > 1, "decalages d'origine tous identiques"


def test_seed_view_keeps_a_usable_panel():
    pre = _fake_pre(n_symbols=26)
    for s in (0, 1, 7, 42, 99):
        symbols, offset = seed_view(pre, s)
        assert 3 <= len(symbols) <= 26
        assert len(set(symbols)) == len(symbols), "tirage avec remise"
        assert 0 <= offset <= 40


# --------------------------------------------------------------------------
# Gate de verdict
# --------------------------------------------------------------------------

def _cfg(sharpes):
    return {"seeds": [{"net_sharpe": v} for v in sharpes]}


def _bh(sharpes):
    return {"seeds": [{"sharpe": v} for v in sharpes]}


def test_verdict_no_beats_when_delta_is_negative():
    v = compute_verdict(_cfg([0.10, 0.12, 0.09, 0.11]),
                        _bh([0.40, 0.42, 0.39, 0.41]))
    assert v["verdict"] == "NO BEATS"


def test_verdict_beats_needs_the_full_conjunction():
    """Edge large ET dispersion faible ET 3/4 graines positives."""
    v = compute_verdict(_cfg([0.80, 0.82, 0.79, 0.81]),
                        _bh([0.40, 0.42, 0.39, 0.41]))
    assert v["verdict"] == "BEATS"
    assert v["edge_sigma"] >= 2.0
    assert v["seeds_positive"] == 4


def test_verdict_inconclusive_when_dispersion_swallows_the_edge():
    """Meme delta moyen, dispersion 20x : le verdict doit basculer.

    C'est le controle qui prouve que `edge_sigma` porte quelque chose -- sans lui,
    un gate qui ne regarderait que `delta` rendrait BEATS dans les deux cas.
    """
    v = compute_verdict(_cfg([0.05, 1.60, -0.20, 1.75]),
                        _bh([0.40, 0.42, 0.39, 0.41]))
    assert v["verdict"] == "INCONCLUSIVE"
    assert v["edge_sigma"] < 2.0


def test_zero_dispersion_can_never_reach_beats():
    """Le defaut de `L1_tsmom.py`, ecrit comme un test.

    Graines identiques -> std = 0 -> edge_sigma = 0 -> BEATS impossible, quel que
    soit l'ecart. Un module dont les graines ne perturbent rien tombe ici.
    """
    v = compute_verdict(_cfg([2.0, 2.0, 2.0, 2.0]),
                        _bh([0.4, 0.4, 0.4, 0.4]))
    assert v["std_net_sharpe"] == 0.0
    assert v["edge_sigma"] == 0.0
    assert v["verdict"] != "BEATS"
    assert v["delta_sharpe"] > 1.5, (
        "l'ecart est enorme et le gate refuse quand meme : c'est exactement "
        "l'etat nominal de L1")


# --------------------------------------------------------------------------
# Frequence de rebalancement -- le parametre qui decide le verdict
# --------------------------------------------------------------------------

def _flat_pre(n=252, seed=3):
    """Un `pre` minimal ou la position EST le signal.

    La volatilite est constante et vaut exactement TARGET_VOL, donc le facteur
    d'echelle `TARGET_VOL / vol` vaut 1 : ce que `build_positions` rend est le
    signal lui-meme, non deforme. C'est ce qui rend la mesure de turnover
    ci-dessous lisible -- sur un `pre` realiste, l'effet du rebalancement serait
    melange a celui de la derive de volatilite.
    """
    rng = np.random.default_rng(seed)
    idx = pd.bdate_range("2015-01-01", periods=n)
    cols = ["AAA", "BBB"]
    sig = pd.DataFrame(rng.uniform(-1.0, 1.0, size=(n, 2)), index=idx,
                       columns=cols)
    vol = pd.DataFrame(TARGET_VOL, index=idx, columns=cols)
    fwd = pd.DataFrame(rng.normal(0.0, 0.01, size=(n, 2)), index=idx,
                       columns=cols)
    return {"tstat": sig, "c2c": vol, "fwd": fwd}, cols


_EQW_TSTAT = {"signal": "tstat", "vol": "c2c", "alloc": "eqw"}


def _mean_turnover(positions):
    """Notionnel moyen deplace par jour, toutes lignes confondues."""
    return positions.diff().abs().sum(axis=1).iloc[1:].mean()


def test_daily_rebalance_leaves_positions_untouched():
    """Controle negatif : `rebalance=1` ne doit RIEN maintenir.

    Sans lui, un bloc de hold accidentellement toujours actif passerait le test
    de constance ci-dessous sans que personne ne s'en apercoive.
    """
    pre, cols = _flat_pre()
    daily, _ = build_positions(pre, _EQW_TSTAT, cols, rebalance=1)
    pd.testing.assert_frame_equal(daily, pre["tstat"][cols], check_freq=False)


def test_monthly_rebalance_holds_positions_between_dates():
    """Sous rebalancement mensuel, la position ne bouge qu'aux dates de grille."""
    pre, cols = _flat_pre()
    held, _ = build_positions(pre, _EQW_TSTAT, cols,
                              rebalance=REBALANCE_MONTHLY)
    assert held.notna().all().all(), "aucun trou ne doit subsister apres ffill"
    for i in range(len(held)):
        anchor = (i // REBALANCE_MONTHLY) * REBALANCE_MONTHLY
        np.testing.assert_allclose(held.iloc[i].to_numpy(),
                                   held.iloc[anchor].to_numpy())
    # et la valeur tenue est bien celle du signal a la date de rebalancement
    np.testing.assert_allclose(held.iloc[0].to_numpy(),
                               pre["tstat"][cols].iloc[0].to_numpy())


def test_monthly_rebalance_divides_turnover_by_the_period():
    """Ordre de grandeur attendu : le turnover chute d'un facteur ~= la periode.

    Le signal est tire i.i.d., donc l'amplitude d'un saut ne depend pas de
    l'intervalle : en mensuel, seul 1 jour sur 21 porte un saut de meme loi
    qu'en journalier. Le rapport attendu est donc ~21, pas ~sqrt(21) (qui serait
    la reponse si le signal etait une marche aleatoire). Une implementation qui
    "tiendrait" les positions sans reduire le turnover -- par exemple en
    reinterpolant entre les dates -- tomberait ici.
    """
    pre, cols = _flat_pre()
    daily, _ = build_positions(pre, _EQW_TSTAT, cols, rebalance=1)
    held, _ = build_positions(pre, _EQW_TSTAT, cols,
                              rebalance=REBALANCE_MONTHLY)
    ratio = _mean_turnover(daily) / _mean_turnover(held)
    assert 12.0 < ratio < 32.0, f"rapport de turnover mesure : {ratio:.1f}"


def test_origin_offset_shifts_the_rebalance_calendar():
    """Le decalage tire par la graine perturbe aussi le CALENDRIER.

    Deux graines ne doivent pas seulement voir un sous-panier different : elles
    doivent aussi rebalancer des jours differents, sinon la dispersion mesuree
    sous-estime la sensibilite reelle a la date d'entree.
    """
    pre, cols = _flat_pre()
    a, _ = build_positions(pre, _EQW_TSTAT, cols, offset=0,
                           rebalance=REBALANCE_MONTHLY)
    b, _ = build_positions(pre, _EQW_TSTAT, cols, offset=5,
                           rebalance=REBALANCE_MONTHLY)
    common = a.index.intersection(b.index)
    assert len(common) > 100, "les deux vues doivent se recouvrir largement"
    diff = (a.loc[common] - b.loc[common]).abs().to_numpy().sum()
    assert diff > 1.0, (
        "positions identiques malgre un decalage de 5 jours : la grille de "
        "rebalancement ne suit pas l'origine de la vue")
