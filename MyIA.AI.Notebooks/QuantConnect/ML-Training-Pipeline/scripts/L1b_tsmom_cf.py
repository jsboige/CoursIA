"""L1b -- TSMOM-CF : time-series momentum corrige (Baltas & Kosowski, 2017).

Distillation de l'article QC research #15272 ("Improved momentum strategy on
commodities futures"), sous l'EPIC #11698 -- voir l'issue #14462 pour la lecture
analytique et le verdict de differenciation.

L'article nomme TROIS faiblesses du TSMOM traditionnel. Elles tombent une par une
sur trois lignes de notre propre baseline `L1_tsmom.py`, qui a rendu NO BEATS :

    axe          L1_tsmom.py (Moskowitz 2012)      TSMOM-CF (l'article)
    ---------    ------------------------------    ----------------------------
    signal       np.sign(past_return), binaire     t-stat 12 m capee sur [-1,+1]
    volatilite   close-to-close rolling std        Yang-Zhang OHLC (2000)
    allocation   equal-weight 1/N                  CF(rho) = sqrt(N/(1+(N-1)rho))

Ce module ne remplace pas L1 : il l'entoure d'une ABLATION a quatre configurations
qui isole la contribution de chaque correctif -- un TSMOM-CF complet qui battrait
la baseline ne dirait pas LEQUEL des trois leviers porte l'effet.

    A  sign      + close-to-close + 1/N     (= L1, controle de reproduction)
    B  t-stat    + close-to-close + 1/N     (levier 1 seul)
    C  t-stat    + Yang-Zhang     + 1/N     (leviers 1+2)
    D  t-stat    + Yang-Zhang     + CF      (TSMOM-CF complet)

Deux verdicts distincts, sur deux instruments distincts -- ils ne se remplacent
pas l'un l'autre :

  * VERDICT STRATEGIE -- gate Sharpe de la regle C : walk-forward 5 folds,
    >= 4 graines, couts de transaction, baseline buy-and-hold equal-weight,
    edge >= 2 sigma inter-graines. Rend BEATS / NO BEATS / INCONCLUSIVE.

  * VERDICT ESTIMATEUR -- test de Diebold-Mariano sur une perte de PRECISION
    (`loss_fn="mse"`), Yang-Zhang contre close-to-close, cible = volatilite
    realisee forward. C'est le seul des trois leviers qui soit une PREVISION au
    sens propre, donc le seul auquel un DM s'applique honnetement. Le DM ne dit
    RIEN de la strategie : il tranche la claim (b) de l'article, et rien d'autre.
    Un rapport de biais signe accompagne chaque estimateur, pour que le cas
    "l'ecart est porte par le biais et non par la precision" reste visible
    (cf #10938/#10956 : `loss_fn="linear"` est un controle de biais, jamais la
    jambe de precision d'un verdict).

CE QUE LES GRAINES PERTURBENT -- et pourquoi ce n'est pas ce que fait L1
-----------------------------------------------------------------------
`L1_tsmom.py:124` construit `rng = np.random.default_rng(seed)` et ne s'en sert
jamais ; sa boucle buy-and-hold (l. 233) n'en construit meme pas. Le splitter
walk-forward etant deterministe, les quatre graines de L1 rendent des nombres
IDENTIQUES : l'ecart-type inter-graines y vaut 0, donc `t_stat = delta/0 -> 0`,
donc la clause `t_stat >= 2.0` de son gate rend le verdict BEATS structurellement
inatteignable. Son gate multi-graines ne mesure rien.

Ici la graine tire une VUE du probleme, et la meme vue sert au modele et a sa
baseline (comparaison appariee) :

  * un sous-panier de PANEL_FRACTION des symboles, sans remise ;
  * un decalage d'origine de 0 a MAX_ORIGIN_OFFSET jours ouvres.

Ce sont deux perturbations de robustesse usuelles, et elles produisent une
dispersion REELLE : le sigma du gate redevient une mesure. Le defaut de L1 est
signale a part -- ce module ne le corrige pas chez lui (hors scope, cf principe 3
du CLAUDE.md : signaler le mauvais code decouvert, le traiter en sujet separe).
Les deux defauts de L1 sont mesures et suivis dans l'issue #14470.

Usage :
    python L1b_tsmom_cf.py
    python L1b_tsmom_cf.py --dry-run
    python L1b_tsmom_cf.py --seeds 0 1 7 42 99
"""

import argparse
import json
import sys
from pathlib import Path

import numpy as np
import pandas as pd

SCRIPTS_DIR = Path(__file__).resolve().parent
CHECKPOINTS_DIR = SCRIPTS_DIR.parent / "checkpoints" / "l1b_tsmom_cf"

sys.path.insert(0, str(SCRIPTS_DIR))

from panier_loader import PANIER_GROUPS, get_panier_symbols, load_panier  # noqa: E402
from walk_forward import WalkForwardSplitter  # noqa: E402
from transaction_costs import TransactionCostModel  # noqa: E402
from baselines import sharpe_from_returns  # noqa: E402
from dm_test import diebold_mariano_test  # noqa: E402

ALL_SYMBOLS = get_panier_symbols()
CRYPTO_SYMBOLS = set(PANIER_GROUPS.get("crypto", []))

# Cost models -- identiques a L1_tsmom.py, pour que la comparaison A-vs-L1 tienne.
EQUITY_COST = TransactionCostModel(
    commission_bps=1.0, bid_ask_spread_bps=2.0,
    market_impact_coeff=0.05, daily_volume=5_000_000, slippage_bps=2.0,
)
CRYPTO_COST = TransactionCostModel(
    commission_bps=2.0, bid_ask_spread_bps=3.0,
    market_impact_coeff=0.05, daily_volume=1_000_000, slippage_bps=5.0,
)

TARGET_VOL = 0.15      # volatilite annualisee cible (identique a L1)
VOL_WINDOW_YZ = 21     # fenetre Yang-Zhang -- valeur de l'article
VOL_WINDOW_C2C = 63    # fenetre close-to-close -- valeur de L1, preservee
CORR_WINDOW = 63       # ~3 mois de correlation par paires -- valeur de l'article
TSTAT_LOOKBACK = 252   # 12 mois -- valeur de l'article
CF_BOUNDS = (0.5, 3.0)
ANNUALISE = np.sqrt(252.0)

PANEL_FRACTION = 0.8     # part du panier tiree par graine
MAX_ORIGIN_OFFSET = 40   # decalage d'origine maximal, en jours ouvres
REBALANCE_MONTHLY = 21   # frequence de l'article : mensuelle (~21 jours ouvres)
REBALANCE_DAILY = 1      # frequence de L1_tsmom.py : quotidienne

CONFIGS = {
    "A_sign_c2c_eqw":  {"signal": "sign",  "vol": "c2c", "alloc": "eqw"},
    "B_tstat_c2c_eqw": {"signal": "tstat", "vol": "c2c", "alloc": "eqw"},
    "C_tstat_yz_eqw":  {"signal": "tstat", "vol": "yz",  "alloc": "eqw"},
    "D_tstat_yz_cf":   {"signal": "tstat", "vol": "yz",  "alloc": "cf"},
}


# --------------------------------------------------------------------------
# Levier 2 -- estimateurs de volatilite
# --------------------------------------------------------------------------

def yang_zhang_vol(df: pd.DataFrame, window: int = VOL_WINDOW_YZ) -> pd.Series:
    """Volatilite annualisee de Yang-Zhang (2000), a partir de l'OHLC.

    sigma_YZ^2 = sigma_OJ^2 + k * sigma_SD^2 + (1 - k) * sigma_RS^2
    k = 0.34 / (1.34 + (N+1)/(N-1))

    - sigma_OJ : saut overnight, log(open_t / close_{t-1})
    - sigma_SD : open-to-close, log(close_t / open_t)
    - sigma_RS : Rogers-Satchell (1991), insensible a la derive
    """
    o, h, low, c = df["Open"], df["High"], df["Low"], df["Close"]
    prev_c = c.shift(1)

    with np.errstate(divide="ignore", invalid="ignore"):
        log_oc_prev = np.log(o / prev_c)
        log_co = np.log(c / o)
        rs = (np.log(h / c) * np.log(h / o) + np.log(low / c) * np.log(low / o))

    var_oj = log_oc_prev.rolling(window).var(ddof=1)
    var_sd = log_co.rolling(window).var(ddof=1)
    var_rs = rs.rolling(window).mean()

    k = 0.34 / (1.34 + (window + 1.0) / (window - 1.0))
    var_yz = (var_oj + k * var_sd + (1.0 - k) * var_rs).clip(lower=0.0)
    return np.sqrt(var_yz) * ANNUALISE


def close_to_close_vol(closes: pd.Series, window: int = VOL_WINDOW_C2C) -> pd.Series:
    """Volatilite annualisee close-to-close -- l'estimateur de `L1_tsmom.py`."""
    return closes.pct_change().rolling(window).std() * ANNUALISE


def realised_forward_vol(closes: pd.Series, window: int = VOL_WINDOW_YZ) -> pd.Series:
    """Cible du DM : volatilite realisee sur les `window` jours SUIVANTS.

    Decalee de -window pour que la valeur a t soit strictement posterieure a t --
    sans ce decalage, l'estimateur se comparerait a une fenetre qui le contient,
    et l'exercice ne serait plus une prevision.
    """
    daily = closes.pct_change()
    return (daily.rolling(window).std() * ANNUALISE).shift(-window)


# --------------------------------------------------------------------------
# Levier 1 -- signaux
# --------------------------------------------------------------------------

def sign_signal(closes: pd.Series, lookback: int = TSTAT_LOOKBACK) -> pd.Series:
    """TSMOM classique : sign(rendement passe). Binaire, +/-1."""
    return np.sign(closes.pct_change(lookback))


def tstat_signal(closes: pd.Series, lookback: int = TSTAT_LOOKBACK) -> pd.Series:
    """TREND de l'article : t-stat des log-rendements quotidiens, capee sur [-1,+1].

    t = mean(r) / (std(r) / sqrt(n)) sur la fenetre. |t| > 1 sature a +/-1 ; en
    deca, la t-stat elle-meme est le signal -- l'exposition devient CONTINUE et se
    reduit quand la tendance est faiblement etablie.
    """
    log_ret = np.log(closes / closes.shift(1))
    mean = log_ret.rolling(lookback).mean()
    std = log_ret.rolling(lookback).std(ddof=1)
    with np.errstate(divide="ignore", invalid="ignore"):
        t = mean / (std / np.sqrt(float(lookback)))
    return t.clip(lower=-1.0, upper=1.0)


# --------------------------------------------------------------------------
# Levier 3 -- facteur de correlation
# --------------------------------------------------------------------------

def correlation_factor(signals: pd.DataFrame, returns: pd.DataFrame,
                       window: int = CORR_WINDOW) -> pd.Series:
    """CF(rho_bar) = sqrt(N / (1 + (N-1) rho_bar)), rho_bar ponderee par les signaux.

    rho_bar = 2 * sum_{i<j} X_i X_j rho_ij / (N (N-1)) : la correlation moyenne par
    paires PONDEREE par le produit des signaux -- deux actifs correles tenus en sens
    opposes se diversifient, et rho_bar doit le voir.

    CF monte le levier quand le panier se decorrele et le baisse quand il se
    synchronise. Borne a CF_BOUNDS : sans borne, un rho_bar proche de -1/(N-1)
    envoie le denominateur vers zero et le levier vers l'infini.
    """
    cols = [c for c in returns.columns if c in signals.columns]
    ret = returns[cols].to_numpy(dtype=float)
    sig = signals[cols].reindex(returns.index).to_numpy(dtype=float)
    n_days = ret.shape[0]
    out = np.full(n_days, np.nan)

    for t in range(window, n_days):
        win = ret[t - window:t]
        x = sig[t]
        usable = ~np.isnan(x) & (np.isfinite(win).sum(axis=0) == window)
        n_eff = int(usable.sum())
        if n_eff < 2:
            continue
        sub = win[:, usable]
        if np.any(sub.std(axis=0) < 1e-12):
            continue
        rho = np.corrcoef(sub, rowvar=False)
        xv = x[usable]
        pair = (np.outer(xv, xv) * rho)[np.triu_indices(n_eff, k=1)]
        pair = pair[np.isfinite(pair)]
        if pair.size == 0:
            continue
        rho_bar = float(2.0 * pair.sum() / (n_eff * (n_eff - 1)))
        denom = 1.0 + (n_eff - 1) * rho_bar
        out[t] = (CF_BOUNDS[1] if denom <= 1e-6
                  else float(np.clip(np.sqrt(n_eff / denom), *CF_BOUNDS)))

    return pd.Series(out, index=returns.index).ffill()


# --------------------------------------------------------------------------
# Pre-calcul -- une seule passe par symbole, reutilisee par les 4 configs
# --------------------------------------------------------------------------

def precompute(panier: dict) -> dict:
    """Signaux et volatilites des deux variantes, alignes sur un index commun."""
    symbols = [s for s in ALL_SYMBOLS if s in panier]
    frames = {"close": {}, "sign": {}, "tstat": {}, "yz": {}, "c2c": {}}
    for sym in symbols:
        df = panier[sym]
        frames["close"][sym] = df["Close"]
        frames["sign"][sym] = sign_signal(df["Close"])
        frames["tstat"][sym] = tstat_signal(df["Close"])
        frames["yz"][sym] = yang_zhang_vol(df)
        frames["c2c"][sym] = close_to_close_vol(df["Close"])

    out = {k: pd.DataFrame(v).sort_index() for k, v in frames.items()}
    index = out["close"].index
    for key in list(out):
        out[key] = out[key].reindex(index)
    # rendement du LENDEMAIN : la position de t est realisee en t+1
    out["fwd"] = out["close"].pct_change().shift(-1)
    out["daily"] = out["close"].pct_change()
    return out


def seed_view(pre: dict, seed: int) -> tuple:
    """Vue tiree par la graine : sous-panier + decalage d'origine.

    La MEME vue sert au modele et a sa baseline : la comparaison reste appariee,
    et le sigma inter-graines mesure la sensibilite au panier et a la fenetre,
    pas un bruit de tirage non partage.
    """
    rng = np.random.default_rng(seed)
    symbols = list(pre["close"].columns)
    k = max(3, int(round(PANEL_FRACTION * len(symbols))))
    chosen = sorted(rng.choice(symbols, size=k, replace=False).tolist())
    offset = int(rng.integers(0, MAX_ORIGIN_OFFSET + 1))
    return chosen, offset


# --------------------------------------------------------------------------
# Construction des positions
# --------------------------------------------------------------------------

def build_positions(pre: dict, config: dict, symbols: list,
                    offset: int = 0, rebalance: int = REBALANCE_MONTHLY) -> tuple:
    """Rend (positions, rendements_forward) pour une configuration et une vue.

    La position est `signal * (vol_cible / vol_estimee)`, clippee sur [-1, +1]
    comme dans l'article, puis multipliee par CF si l'allocation le demande.

    REBALANCEMENT -- ce parametre decide le verdict, il n'est pas cosmetique.
    Le TSMOM de Moskowitz (2012) comme celui de Baltas & Kosowski (2017) sont
    des strategies a rebalancement MENSUEL. Une position gardee telle quelle
    entre deux dates de rebalancement ne coute rien ; recalculee chaque jour,
    elle derive avec la volatilite estimee et se refacture chaque jour.
    Mesure sur notre panier (26 symboles, 5 graines, 2015-2026) : le notionnel
    deplace par jour passe de 3,5-4,6 en journalier a 0,10-0,13 en mensuel, un
    facteur 31 a 37. C'est assez pour retourner le SIGNE du Sharpe net : les memes
    quatre configurations rendent -0,43 a -0,56 en journalier et +0,35 a +0,45
    en mensuel. Le verdict contre la baseline reste NO BEATS dans les deux cas,
    mais pour deux raisons opposees -- en journalier les couts mangeaient un
    brut positif, en mensuel la strategie est simplement en dessous du
    buy-and-hold (Sharpe 1,06 sur un panier a dominante actions).
    Tester l'article a une frequence qu'il n'emploie pas ne serait pas un test
    de l'article. Le journalier reste disponible en sensibilite (--rebalance).
    """
    sig_df = pre[config["signal"]][symbols]
    vol_df = pre[config["vol"]][symbols]
    fwd = pre["fwd"][symbols]

    vol_scale = TARGET_VOL / vol_df.clip(lower=0.01)
    positions = (sig_df * vol_scale).clip(lower=-1.0, upper=1.0)

    if config["alloc"] == "cf":
        # CF depend de la COMPOSITION du panier (le N de la formule) : il se
        # recalcule sur le sous-panier de la graine, jamais sur le panier entier.
        cf = correlation_factor(sig_df, pre["daily"][symbols])
        positions = positions.mul(cf, axis=0).clip(lower=-1.0, upper=1.0)

    keep = positions.notna().any(axis=1) & fwd.notna().any(axis=1)
    positions, fwd = positions.loc[keep], fwd.loc[keep]
    if offset:
        positions, fwd = positions.iloc[offset:], fwd.iloc[offset:]

    if rebalance > 1:
        # La grille part du debut de la vue : le decalage d'origine tire par la
        # graine perturbe donc aussi le CALENDRIER de rebalancement, ce qui est
        # une sensibilite reelle et souhaitable.
        held = pd.DataFrame(np.nan, index=positions.index,
                            columns=positions.columns)
        held.iloc[::rebalance] = positions.iloc[::rebalance]
        positions = held.ffill()

    return positions, fwd


def _avg_cost_rate(symbols: list) -> float:
    """Cout unitaire moyen, en fraction du notionnel deplace (aller simple)."""
    n_crypto = sum(1 for s in symbols if s in CRYPTO_SYMBOLS)
    n_equity = len(symbols) - n_crypto
    return ((n_equity * EQUITY_COST.cost_per_trade(100)
             + n_crypto * CRYPTO_COST.cost_per_trade(100)) / max(len(symbols), 1))


def _walk_forward_returns(pos, ret, cost_rate: float,
                          n_splits: int, gap: int) -> dict:
    """Rendements OOS bruts / nets, turnover et ordres, concatenes sur les folds.

    COUT PROPORTIONNEL AU TURNBOVER -- et pourquoi ce n'est pas ce que fait L1.

    `L1_tsmom.py:158-173` compte un ordre des que la position bouge
    (`pos_changes > 0`) puis facture un aller-retour sur 100 % du notionnel :
    `trades_per_day * 2 * cost_per_trade / n_assets`. Or la position est
    `signal * vol_cible / vol_estimee` : la volatilite estimee derive tous les
    jours, donc la position bouge tous les jours, donc CHAQUE actif est facture
    tous les jours comme s'il etait entierement liquide et rachete. Mesure sur
    notre panier (config A, graine 0) : 13,5 "ordres" par jour pour 21 actifs,
    Sharpe brut +0,573 -> net -5,59. Le -5,59 ne mesure pas la strategie, il
    mesure la facturation.

    Le cout reel d'un rebalancement est proportionnel a la TAILLE du deplacement :
    `|delta position| * cout_unitaire`. C'est la convention retenue ici.

    La convention de L1 est conservee en colonne `net_l1_convention`, non pour
    l'utiliser mais pour que l'ecart reste chiffre : c'est la preuve du defaut,
    et elle appartient au dossier plutot qu'a une affirmation.
    """
    n_assets = pos.shape[1]
    gross_all, net_all, net_l1_all, turnover_all, trades_all = [], [], [], [], []

    splitter = WalkForwardSplitter(n_splits=n_splits, gap=gap)
    for _train_idx, test_idx in splitter.split(pos):
        if len(test_idx) == 0:
            continue
        p = np.nan_to_num(pos[test_idx], nan=0.0)
        r = ret[test_idx]
        gross = np.nansum(p * r, axis=1) / n_assets

        deltas = np.abs(np.diff(p, axis=0, prepend=np.zeros_like(p[0:1])))
        turnover = np.sum(deltas, axis=1)          # notionnel reellement deplace
        trades = np.sum(deltas > 1e-9, axis=1)     # nombre de lignes touchees

        net = gross - turnover * cost_rate / n_assets
        net_l1 = gross - trades * 2 * cost_rate / n_assets

        ok = ~(np.isnan(gross) | np.isnan(net))
        gross_all.extend(gross[ok].tolist())
        net_all.extend(net[ok].tolist())
        net_l1_all.extend(net_l1[ok].tolist())
        turnover_all.extend(turnover[ok].tolist())
        trades_all.extend(trades[ok].tolist())

    return {"gross": np.array(gross_all), "net": np.array(net_all),
            "net_l1": np.array(net_l1_all),
            "turnover": np.array(turnover_all), "trades": trades_all}


def run_config(pre: dict, config: dict, seeds: list, n_splits: int = 5,
               gap: int = 21, rebalance: int = REBALANCE_MONTHLY) -> dict:
    """Walk-forward multi-graines pour une configuration de l'ablation."""
    seed_results = []
    for seed in seeds:
        symbols, offset = seed_view(pre, seed)
        positions, fwd = build_positions(pre, config, symbols, offset, rebalance)
        res = _walk_forward_returns(
            positions.to_numpy(dtype=float), fwd.to_numpy(dtype=float),
            _avg_cost_rate(symbols), n_splits, gap)
        gross, net = res["gross"], res["net"]

        if len(gross) > 10:
            entry = {
                "seed": seed, "n_symbols": len(symbols), "origin_offset": offset,
                "gross_sharpe": round(float(sharpe_from_returns(pd.Series(gross))), 4),
                "net_sharpe": round(float(sharpe_from_returns(pd.Series(net))), 4),
                "net_sharpe_l1_convention": round(
                    float(sharpe_from_returns(pd.Series(res["net_l1"]))), 4),
                "net_cagr": round(float(np.prod(1 + net) ** (252 / len(net)) - 1), 4),
                "mean_daily_turnover": round(float(np.mean(res["turnover"])), 4),
                "total_trades": int(np.sum(res["trades"])), "n_oos": int(len(gross)),
            }
        else:
            entry = {"seed": seed, "n_symbols": len(symbols), "origin_offset": offset,
                     "gross_sharpe": 0.0, "net_sharpe": 0.0,
                     "net_sharpe_l1_convention": 0.0, "net_cagr": 0.0,
                     "mean_daily_turnover": 0.0, "total_trades": 0,
                     "n_oos": int(len(gross))}
        seed_results.append(entry)

    return {"config": config, "rebalance": rebalance, "seeds": seed_results}


def run_buyhold_baseline(pre: dict, seeds: list,
                         n_splits: int = 5, gap: int = 21) -> dict:
    """Buy-and-hold equal-weight, sur EXACTEMENT les vues tirees par les graines."""
    seed_results = []
    for seed in seeds:
        symbols, offset = seed_view(pre, seed)
        fwd = pre["fwd"][symbols].dropna(how="all")
        if offset:
            fwd = fwd.iloc[offset:]
        ret_arr = fwd.to_numpy(dtype=float)

        fold = []
        splitter = WalkForwardSplitter(n_splits=n_splits, gap=gap)
        for _tr, te in splitter.split(ret_arr):
            if len(te) == 0:
                continue
            port = np.nanmean(ret_arr[te], axis=1)
            fold.extend(port[~np.isnan(port)].tolist())

        arr = np.array(fold)
        sharpe = float(sharpe_from_returns(pd.Series(arr))) if len(arr) > 10 else 0.0
        seed_results.append({"seed": seed, "n_symbols": len(symbols),
                             "origin_offset": offset, "sharpe": round(sharpe, 4),
                             "n_oos": int(len(arr))})
    return {"model": "equal_weight_bh", "seeds": seed_results}


# --------------------------------------------------------------------------
# Verdicts
# --------------------------------------------------------------------------

def compute_verdict(cfg_results: dict, bh_results: dict) -> dict:
    """Gate Sharpe de la regle C -- meme forme que `L1_tsmom.compute_verdict`.

    A la difference de L1, `std_net_sharpe` y est une VRAIE dispersion : les
    graines tirent des vues distinctes (cf le docstring du module). Un
    `edge_sigma` nul signalerait donc un probleme, la ou chez L1 c'etait l'etat
    nominal.
    """
    model = [s["net_sharpe"] for s in cfg_results["seeds"]]
    base = [s["sharpe"] for s in bh_results["seeds"]]
    mean_m, mean_b = float(np.mean(model)), float(np.mean(base))
    std_m = float(np.std(model, ddof=1)) if len(model) > 1 else 0.0
    std_b = float(np.std(base, ddof=1)) if len(base) > 1 else 0.0
    delta = mean_m - mean_b
    delta_std = float(np.sqrt(std_m ** 2 + std_b ** 2))
    t_stat = delta / delta_std if delta_std > 1e-10 else 0.0
    positive = sum(1 for m, b in zip(model, base) if m > b + 0.10)

    if delta > 0.10 and t_stat >= 2.0 and positive >= max(len(model) * 3 // 4, 1):
        verdict = "BEATS"
    elif delta <= 0:
        verdict = "NO BEATS"
    else:
        verdict = "INCONCLUSIVE"

    return {"verdict": verdict,
            "mean_net_sharpe": round(mean_m, 4), "std_net_sharpe": round(std_m, 4),
            "mean_bh_sharpe": round(mean_b, 4), "std_bh_sharpe": round(std_b, 4),
            "delta_sharpe": round(delta, 4), "edge_sigma": round(t_stat, 4),
            "seeds_positive": positive, "n_seeds": len(model)}


def vol_estimator_dm(panier: dict) -> dict:
    """Verdict ESTIMATEUR : Yang-Zhang contre close-to-close, par symbole.

    Le DM se fait PAR SYMBOLE puis s'agrege : mettre bout a bout 26 series
    d'erreurs produirait une serie dont les ruptures inter-symboles ne sont pas
    de l'autocorrelation, et la correction HAC les lirait comme telles.

    Le biais signe de chaque estimateur est rapporte a cote de la precision :
    un estimateur peut gagner en MSE tout en etant systematiquement bas.
    """
    per_symbol, wins_yz, wins_c2c, inconclusive = [], 0, 0, 0
    bias_yz_all, bias_c2c_all = [], []

    for sym in [s for s in ALL_SYMBOLS if s in panier]:
        df = panier[sym]
        frame = pd.DataFrame({
            "t": realised_forward_vol(df["Close"]),
            "yz": yang_zhang_vol(df),
            "c2c": close_to_close_vol(df["Close"]),
        }).dropna()
        if len(frame) < 100:
            continue
        e_yz = (frame["yz"] - frame["t"]).to_numpy()
        e_c2c = (frame["c2c"] - frame["t"]).to_numpy()
        try:
            # horizon = VOL_WINDOW_YZ : la cible est une vol realisee a 21 jours,
            # donc les erreurs de dates voisines se recouvrent sur 20 jours. Le
            # lag de troncature HAC est fixe a ce recouvrement plutot que laisse
            # a la regle n^(1/3), qui rend 14 pour n ~ 2800 et sous-couvre la
            # dependance -- elle rendrait des p-values trop petites.
            dm = diebold_mariano_test(e_yz, e_c2c, loss_fn="mse",
                                      max_lag=VOL_WINDOW_YZ - 1,
                                      horizon=VOL_WINDOW_YZ)
        except (ValueError, ZeroDivisionError):
            continue

        bias_yz, bias_c2c = float(np.mean(e_yz)), float(np.mean(e_c2c))
        bias_yz_all.append(bias_yz)
        bias_c2c_all.append(bias_c2c)

        if dm.p_value < 0.05 and dm.mean_loss_diff < 0:
            wins_yz += 1
        elif dm.p_value < 0.05 and dm.mean_loss_diff > 0:
            wins_c2c += 1
        else:
            inconclusive += 1

        per_symbol.append({
            "symbol": sym, "n_obs": dm.n_observations,
            "lag_truncation": dm.lag_truncation,
            "dm_stat": round(dm.dm_statistic, 4),
            "p_value": round(dm.p_value, 6),
            "mean_loss_diff": float(dm.mean_loss_diff),
            "rmse_yz": round(float(np.sqrt(np.mean(e_yz ** 2))), 6),
            "rmse_c2c": round(float(np.sqrt(np.mean(e_c2c ** 2))), 6),
            "bias_yz": round(bias_yz, 6), "bias_c2c": round(bias_c2c, 6),
        })

    n = len(per_symbol)
    if n == 0:
        return {"verdict": "NO DATA", "per_symbol": []}

    if wins_yz >= max(1, n * 3 // 4):
        overall = "YANG-ZHANG PLUS PRECIS"
    elif wins_c2c >= max(1, n * 3 // 4):
        overall = "CLOSE-TO-CLOSE PLUS PRECIS"
    else:
        overall = "MIXTE / NON CONCLUANT"

    return {
        "verdict": overall, "n_symbols": n,
        "wins_yang_zhang": wins_yz, "wins_close_to_close": wins_c2c,
        "inconclusive": inconclusive,
        "median_p_value": round(float(np.median([r["p_value"] for r in per_symbol])), 6),
        "mean_bias_yang_zhang": round(float(np.mean(bias_yz_all)), 6),
        "mean_bias_close_to_close": round(float(np.mean(bias_c2c_all)), 6),
        "bias_note": ("Biais signe = mean(estimateur - realise forward). Negatif = "
                      "sous-estime la volatilite a venir. Rapporte a cote du MSE "
                      "pour que la precision ne soit pas confondue avec le biais."),
        "per_symbol": per_symbol,
    }


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--seeds", type=int, nargs="+", default=[0, 1, 7, 42],
                        help="graines walk-forward (>= 4 exigees par la regle C)")
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--gap", type=int, default=21)
    parser.add_argument("--rebalance", type=int, default=REBALANCE_MONTHLY,
                        help="periode de rebalancement en jours ouvres. 21 = "
                             "mensuel (frequence de l'article, defaut), "
                             "1 = quotidien (frequence de L1_tsmom.py).")
    parser.add_argument("--dry-run", action="store_true",
                        help="charge les donnees et sort sans backtester")
    parser.add_argument("--panier-dir", type=str, default=None,
                        help="repertoire des CSV du panier. Les donnees ne sont "
                             "pas versionnees (seul le README l'est) : depuis un "
                             "worktree, pointer le checkout principal.")
    parser.add_argument("--output", type=str, default=None)
    args = parser.parse_args()

    print("Chargement du panier anti-biais (OHLC complet requis pour Yang-Zhang)...")
    panier_dir = Path(args.panier_dir) if args.panier_dir else None
    panier = load_panier(panier_dir=panier_dir)
    usable = {s: df for s, df in panier.items()
              if {"Open", "High", "Low", "Close"} <= set(df.columns)}
    print(f"  {len(usable)}/{len(panier)} symboles avec OHLC complet")
    if usable:
        idx = next(iter(usable.values())).index
        print(f"  periode : {idx[0].date()} -> {idx[-1].date()}")

    if args.dry_run:
        print("--dry-run : sortie avant backtest.")
        return 0

    if len(usable) < 3:
        print("ERREUR : moins de 3 symboles avec OHLC complet -- rien a mesurer.\n"
              "  Les CSV du panier ne sont pas versionnes (le .gitignore ne garde\n"
              "  que le README). Passer --panier-dir <chemin du checkout principal>\n"
              "  /MyIA.AI.Notebooks/QuantConnect/datasets/panier, ou reconstruire le\n"
              "  panier avec scripts/datasets/build_panier_anti_bias.py.")
        return 2

    if len(args.seeds) < 4:
        print(f"ATTENTION : {len(args.seeds)} graine(s) -- la regle C en exige >= 4. "
              "Le verdict rendu ne satisfait pas le gate.")

    print("\nVerdict ESTIMATEUR -- Diebold-Mariano Yang-Zhang vs close-to-close")
    dm_result = vol_estimator_dm(usable)
    print(f"  {dm_result['verdict']}  "
          f"(YZ {dm_result.get('wins_yang_zhang')} / C2C {dm_result.get('wins_close_to_close')}"
          f" / nc {dm_result.get('inconclusive')} sur {dm_result.get('n_symbols')} symboles)")
    print(f"  biais moyen  YZ={dm_result.get('mean_bias_yang_zhang')}  "
          f"C2C={dm_result.get('mean_bias_close_to_close')}")

    print("\nPre-calcul des signaux et volatilites...")
    pre = precompute(usable)

    print("Baseline buy-and-hold equal-weight (memes vues que le modele)...")
    bh = run_buyhold_baseline(pre, args.seeds, args.n_splits, args.gap)
    bh_sharpes = [s["sharpe"] for s in bh["seeds"]]
    print(f"  Sharpe moyen = {np.mean(bh_sharpes):.4f} "
          f"(ecart-type inter-graines {np.std(bh_sharpes, ddof=1):.4f})")

    freq = ("mensuel" if args.rebalance == REBALANCE_MONTHLY
            else "quotidien" if args.rebalance == REBALANCE_DAILY
            else f"tous les {args.rebalance} jours ouvres")
    print(f"\nAblation -- verdict STRATEGIE par configuration"
          f" (rebalancement {freq})")
    print(f"  {'config':18s} {'brut':>8s} {'net':>8s} {'+/-':>7s} {'delta':>8s} "
          f"{'edge':>8s} {'turnover':>9s} {'net(L1)':>9s}  verdict")
    configs_out, verdicts = {}, {}
    for name, cfg in CONFIGS.items():
        res = run_config(pre, cfg, args.seeds, args.n_splits, args.gap,
                         args.rebalance)
        verdict = compute_verdict(res, bh)
        configs_out[name], verdicts[name] = res, verdict
        gross = np.mean([s["gross_sharpe"] for s in res["seeds"]])
        turn = np.mean([s["mean_daily_turnover"] for s in res["seeds"]])
        net_l1 = np.mean([s["net_sharpe_l1_convention"] for s in res["seeds"]])
        print(f"  {name:18s} {gross:+8.4f} {verdict['mean_net_sharpe']:+8.4f} "
              f"{verdict['std_net_sharpe']:7.4f} {verdict['delta_sharpe']:+8.4f} "
              f"{verdict['edge_sigma']:+7.2f}s {turn:9.3f} {net_l1:+9.4f}  "
              f"{verdict['verdict']}")
    print("  net(L1) = le meme resultat sous la facturation de L1_tsmom.py "
          "(un aller-retour plein notionnel par ligne touchee, chaque jour).")

    payload = {
        "module": "L1b_tsmom_cf",
        "source_article": "https://www.quantconnect.com/research/15272/",
        "issue": 14462, "epic": 11698,
        "seeds": args.seeds, "n_splits": args.n_splits, "gap": args.gap,
        "rebalance_days": args.rebalance,
        "seed_perturbation": {"panel_fraction": PANEL_FRACTION,
                              "max_origin_offset": MAX_ORIGIN_OFFSET},
        "buyhold": bh, "vol_estimator_dm": dm_result,
        "configs": configs_out, "verdicts": verdicts,
    }
    out = Path(args.output) if args.output else CHECKPOINTS_DIR / "l1b_results.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"\nResultats ecrits dans {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
