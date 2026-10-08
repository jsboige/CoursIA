"""M5 as a sizing layer on ETH -- strategy-grade verdict (#19725, pre-registered).

Pre-registration: issue #19725 comment 6040355929 (posted before the first
calculation; server date authoritative). Every constant below is fixed by
that comment -- no parameter search of any kind. Changing one reopens a new
experiment with a new comment, per protocol #18907 point 2.

Legs (frozen block 2022-07-01 -> 2023-12-15):
  gate      M5   : leverage from the HMM regime-switching HAR h=1 forecast
  gate      HAR  : leverage from the classic HAR h=1 forecast (M5's own
                  prediction baseline -- the comparison the precision verdict
                  already ran, now read as a strategy)
  context   RV63 : leverage from 63-day realized vol
  context   hold : constant leverage 1
  placebo   M5-5d: M5 forecast stale by 5 days (must NOT beat HAR -- a beat
                  is a leak, the verdict is voided)

Sizing rule (fixed, verbatim from the registration):
  lev_t = min(3.0, 0.60 / vol_ann_t), floored at 0 (never short),
  ret_net_t = lev_{t-1} * ret_eth_t - 0.001 * |lev_t - lev_{t-1}|
with COST = 0.001 (10 bps crypto, pr-review-discipline.md section C). The
forecast series dates a row at the day it PREDICTS (produced from data <=
the prior close, the runner's walk-forward alignment); the registration
applies lev_{t-1} to ret_t, which is one honest day of lag on top. Sharpe =
mean/std * sqrt(252) on daily net returns inside the block.

Significance: stationary block bootstrap on the PAIRED daily net returns
(geometric blocks, mean length 22 days, 2000 draws, RNG seed fixed below,
one-sided p on Sharpe(M5) - Sharpe(HAR)). This is the Sharpe analogue of
the DM test adopted by the #18907 arbitration (point 4). NO BEATS is the
mirror test: all diffs <= 0 and P(diff >= 0) < 0.05, i.e. p_leq > 0.95.

Verdict machine (per seed, then across seeds):
  BEATS       : diff > 0 on 4/4 seeds AND p_leq < 0.05 on 4/4 seeds
  NO BEATS    : diff <= 0 on 4/4 seeds AND p_leq > 0.95 on 4/4 seeds
  INCONCLUSIVE: anything else
Placebo beat -> verdict VOIDE_FUITE (leak), not a result.

The forecast series come from the published runner (hmm_regime_vol.py
--dump-series) -- this script never refits a model, it only adds the
strategy layer on top, so the treatment forecast path is identical to
the one the precision verdicts were read from (#18190 cluster revalidation).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

import numpy as np
import pandas as pd

PIPELINE_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PIPELINE_ROOT / "scripts"))

from hmm_regime_vol import load_binance_eth  # noqa: E402

# --- pre-registered constants (do not tune; see docstring) -----------------
TARGET_VOL_ANN = 0.60
LEVERAGE_CAP = 3.0
LEVERAGE_FLOOR = 0.0
COST_ONE_WAY = 0.001  # 10 bps crypto
BLOCK_START = "2022-07-01"
BLOCK_END = "2023-12-15"
SEEDS = [0, 7, 42, 99]
PLACEBO_LAG_DAYS = 5
BOOT_BLOCK_MEAN = 22
BOOT_DRAWS = 2000
BOOT_SEED = 20261007
TRADING_DAYS = 252
RV63_WINDOW = 63


def daily_log_returns() -> pd.Series:
    """ETH daily close-to-close log returns, indexed by date (panel origin
    paired with the #18190 revalidation: local Binance file)."""
    eth = load_binance_eth()
    df = eth.df["close"].resample("1D").last().dropna()
    ret = np.log(df).diff().dropna()
    ret.index = pd.to_datetime(ret.index).normalize()
    return ret[~ret.index.duplicated(keep="last")]


def annualized_vol_from_log_rv(log_rv: pd.Series) -> pd.Series:
    """log(daily RV) forecast -> annualized vol. RV is a daily variance, so
    vol_day = sqrt(exp(log_rv)) and ann = vol_day * sqrt(252)."""
    return np.sqrt(np.exp(log_rv)) * np.sqrt(TRADING_DAYS)


def leverage_series(vol_ann: pd.Series) -> pd.Series:
    lev = (TARGET_VOL_ANN / vol_ann).clip(lower=LEVERAGE_FLOOR, upper=LEVERAGE_CAP)
    return lev.dropna()


def net_returns(ret: pd.Series, lev: pd.Series) -> pd.Series:
    """Pre-registered timing: gross_t = lev_{t-1} * ret_t, cost_t =
    COST * |lev_t - lev_{t-1}| (charged the day the leverage changes)."""
    gross = lev.shift(1) * ret
    cost = COST_ONE_WAY * lev.diff().abs()
    return (gross - cost).dropna()


def _sharpe_np(x: np.ndarray) -> float:
    if len(x) < 2:
        return float("nan")
    sd = x.std(ddof=1)
    if sd == 0:
        return float("nan")
    return float(x.mean() / sd * np.sqrt(TRADING_DAYS))


def sharpe(net: pd.Series) -> float:
    return _sharpe_np(net.to_numpy())


def _stationary_indices(rng: np.random.Generator, n: int, p_jump: float) -> np.ndarray:
    """Indices of one stationary-bootstrap resample: geometric block lengths
    (mean 1/p_jump), uniform starts, circular wrap, truncated to n."""
    k = int(np.ceil(n * p_jump * 1.5)) + 4
    while True:
        lengths = rng.geometric(p_jump, size=k)
        if int(lengths.sum()) >= n:
            break
        k *= 2
    starts = rng.integers(0, n, size=k)
    out = np.concatenate(
        [np.arange(s, s + l) % n for s, l in zip(starts, lengths) if l > 0]
    )
    return out[:n]


def block_bootstrap_sharpe_diff_p(
    net_a: pd.Series, net_b: pd.Series,
    block_mean: int = BOOT_BLOCK_MEAN, draws: int = BOOT_DRAWS,
    seed: int = BOOT_SEED,
) -> tuple[float, float]:
    """One-sided p that Sharpe(a) - Sharpe(b) <= 0, stationary bootstrap on
    the paired series. Returns (p_leq0, diff_observed). Deterministic for a
    fixed seed -- same seed, same blocks for the pair."""
    idx = net_a.index.intersection(net_b.index)
    a = net_a.loc[idx].to_numpy()
    b = net_b.loc[idx].to_numpy()
    n = len(a)
    if n < block_mean * 3:
        return float("nan"), float("nan")
    diff_obs = _sharpe_np(a) - _sharpe_np(b)
    rng = np.random.default_rng(seed)
    p_jump = 1.0 / block_mean
    leq = 0
    for _ in range(draws):
        pos = _stationary_indices(rng, n, p_jump)
        sdiff = _sharpe_np(a[pos]) - _sharpe_np(b[pos])
        if sdiff <= 0:
            leq += 1
    return leq / draws, float(diff_obs)


def verdict_machine(rows: list[dict]) -> str:
    diffs = [r["sharpe_diff"] for r in rows]
    p_leq = [r["boot_p_m5_leq_har"] for r in rows]
    if all(d > 0 for d in diffs) and all(p < 0.05 for p in p_leq):
        return "BEATS"
    if all(d <= 0 for d in diffs) and all(p > 0.95 for p in p_leq):
        return "NO BEATS"
    return "INCONCLUSIVE"


def run(series_csv: Path, out: Path, full_series_out: Path | None) -> dict:
    ret = daily_log_returns()
    df = pd.read_csv(series_csv)
    eth = df[(df["coin"] == "ETH-USD") & (df["horizon"] == 1)].copy()
    eth["date"] = pd.to_datetime(eth["date"]).dt.normalize()

    # Context legs (seed-independent): RV63 vol proxy, and buy & hold.
    rv63 = (ret.rolling(RV63_WINDOW).std() * np.sqrt(TRADING_DAYS)).dropna()
    net_rv = net_returns(ret, leverage_series(rv63))
    net_hold = ret  # constant leverage 1: gross = ret, zero turnover cost

    per_seed = []
    for seed in SEEDS:
        s = eth[eth["seed"] == seed].set_index("date").sort_index()
        m5_vol = annualized_vol_from_log_rv(s["pred_regime"])
        har_vol = annualized_vol_from_log_rv(s["pred_classic"])
        placebo_vol = annualized_vol_from_log_rv(s["pred_regime"].shift(PLACEBO_LAG_DAYS))

        lev_m5 = leverage_series(m5_vol)
        lev_har = leverage_series(har_vol)
        net_m5 = net_returns(ret, lev_m5)
        net_har = net_returns(ret, lev_har)
        net_pl = net_returns(ret, leverage_series(placebo_vol))

        b = lambda x: x[(x.index >= BLOCK_START) & (x.index <= BLOCK_END)]  # noqa: E731

        p_leq, diff_m5_har = block_bootstrap_sharpe_diff_p(
            b(net_m5), b(net_har), seed=BOOT_SEED + seed)
        p_pl_leq, diff_pl_har = block_bootstrap_sharpe_diff_p(
            b(net_pl), b(net_har), seed=BOOT_SEED + seed)

        bias_m5 = float((s["pred_regime"] - s["target"]).loc[BLOCK_START:BLOCK_END].mean())
        bias_har = float((s["pred_classic"] - s["target"]).loc[BLOCK_START:BLOCK_END].mean())

        per_seed.append({
            "seed": seed,
            "sharpe_m5": sharpe(b(net_m5)),
            "sharpe_har": sharpe(b(net_har)),
            "sharpe_placebo": sharpe(b(net_pl)),
            "sharpe_rv63": sharpe(b(net_rv)),
            "sharpe_hold": sharpe(b(net_hold)),
            "sharpe_diff": diff_m5_har,
            "boot_p_m5_leq_har": p_leq,
            "placebo_diff_vs_har": diff_pl_har,
            "placebo_boot_p_leq": p_pl_leq,
            "bias_logrv_m5_block": bias_m5,
            "bias_logrv_har_block": bias_har,
            "n_days_block": int(len(b(net_m5))),
            "mean_lev_m5": float(b(lev_m5).mean()),
            "mean_lev_har": float(b(lev_har).mean()),
        })

        if full_series_out is not None:
            frame = pd.DataFrame({
                "net_m5": net_m5, "net_har": net_har, "net_placebo": net_pl,
                "lev_m5": lev_m5, "lev_har": lev_har,
            })
            frame.insert(0, "seed", seed)
            frame.to_csv(
                full_series_out, mode="a", header=not full_series_out.exists(),
                encoding="utf-8",
            )

    placebo_beats = any(
        r["placebo_diff_vs_har"] > 0 and r["placebo_boot_p_leq"] < 0.05 for r in per_seed
    )
    verdict = verdict_machine(per_seed)
    if placebo_beats:
        verdict = "VOIDE_FUITE"

    manifest = {
        "protocol": "#19725 pre-registration c.6040355929 (before first calculation)",
        "config": {
            "target_vol_ann": TARGET_VOL_ANN, "leverage_cap": LEVERAGE_CAP,
            "cost_one_way": COST_ONE_WAY, "block_start": BLOCK_START,
            "block_end": BLOCK_END, "seeds": SEEDS,
            "placebo_lag_days": PLACEBO_LAG_DAYS,
            "boot_block_mean": BOOT_BLOCK_MEAN, "boot_draws": BOOT_DRAWS,
            "boot_seed": BOOT_SEED,
        },
        "verdict": verdict,
        "placebo_beats_leak": placebo_beats,
        "per_seed": per_seed,
        "series_csv_sha256": hashlib.sha256(series_csv.read_bytes()).hexdigest(),
    }
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    print(f"verdict: {verdict}  (placebo leak: {placebo_beats})")
    for r in per_seed:
        print(
            f"  seed {r['seed']:>2}: M5 {r['sharpe_m5']:+.3f}  HAR {r['sharpe_har']:+.3f}  "
            f"diff {r['sharpe_diff']:+.3f}  p_leq {r['boot_p_m5_leq_har']:.4f}  "
            f"placebo {r['sharpe_placebo']:+.3f} (d {r['placebo_diff_vs_har']:+.3f}, p {r['placebo_boot_p_leq']:.3f})  "
            f"rv63 {r['sharpe_rv63']:+.3f}  hold {r['sharpe_hold']:+.3f}  "
            f"levM/H {r['mean_lev_m5']:.2f}/{r['mean_lev_har']:.2f}  "
            f"bias(M5/HAR) {r['bias_logrv_m5_block']:+.4f}/{r['bias_logrv_har_block']:+.4f}"
        )
    print(f"manifest -> {out}")
    return manifest


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--series-csv", type=Path, required=True,
                   help="CSV from hmm_regime_vol.py --dump-series (ETH h=1, 4 seeds)")
    p.add_argument("--out", type=Path,
                   default=PIPELINE_ROOT / "scripts/results/m5_strategy_vol_targeting.json")
    p.add_argument("--full-series-out", type=Path, default=None,
                   help="optional path for the full per-seed daily net-return series")
    args = p.parse_args(argv)
    run(args.series_csv, args.out, args.full_series_out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
