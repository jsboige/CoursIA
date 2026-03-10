"""Iteration 4 Research: Momentum lookback + allocation sensitivity.
Runs locally with yfinance to find optimal parameters before cloud backtest.
"""
import numpy as np
import pandas as pd
import yfinance as yf
from datetime import datetime

# === Configuration ===
TREND_TICKERS = ['AAPL', 'MSFT', 'GOOGL', 'AMZN', 'META', 'NVDA', 'TSLA',
                 'JPM', 'V', 'JNJ', 'UNH', 'HD', 'PG', 'MA', 'XOM']
AW_TICKERS = ['SPY', 'IEF', 'GLD', 'XLP']
AW_TARGET = {'SPY': 0.30, 'IEF': 0.30, 'GLD': 0.30, 'XLP': 0.10}
START = '2014-01-01'  # Extra warm-up for SMA200
SIM_START = '2015-01-01'
END = '2026-03-01'
FEE_BPS = 5

# === Data ===
print("Downloading data...")
all_tickers = list(set(TREND_TICKERS + AW_TICKERS))
data = yf.download(all_tickers, start=START, end=END, auto_adjust=True)
closes = data['Close'][all_tickers]
returns = closes.pct_change()
print(f"Data: {closes.shape[0]} days, {closes.shape[1]} tickers")

# === Trend Signal ===
ema20 = closes[TREND_TICKERS].ewm(span=20).mean()
ema50 = closes[TREND_TICKERS].ewm(span=50).mean()
sma200 = closes[TREND_TICKERS].rolling(200).mean()
trend_signal = ((closes[TREND_TICKERS] > sma200) & (ema20 > ema50)).astype(int)

# === Helper Functions ===
def simulate_with_fees(weights, returns, fee_bps=5):
    """Simulate portfolio with transaction costs."""
    w = weights.reindex(returns.index, method='ffill').fillna(0)
    r = returns.reindex(w.index).fillna(0)
    w = w[w.columns.intersection(r.columns)]
    r = r[w.columns]

    turnover = w.diff().abs().sum(axis=1)
    fee_drag = turnover * fee_bps / 10000
    port_ret = (w.shift(1) * r).sum(axis=1) - fee_drag
    port_ret = port_ret.loc[SIM_START:]
    equity = (1 + port_ret).cumprod()
    return port_ret, equity, turnover.loc[SIM_START:]

def calc_metrics(ret, equity, name):
    """Calculate standard metrics."""
    ann_ret = ret.mean() * 252
    ann_vol = ret.std() * np.sqrt(252)
    sharpe = ann_ret / ann_vol if ann_vol > 0 else 0
    max_dd = (equity / equity.cummax() - 1).min()
    cagr = equity.iloc[-1] ** (252 / len(equity)) - 1
    return {
        'Strategy': name,
        'Sharpe': f'{sharpe:.3f}',
        'CAGR': f'{cagr:.1%}',
        'MaxDD': f'{max_dd:.1%}',
        'AnnVol': f'{ann_vol:.1%}',
    }

def build_weights_equal(trend_sig, trend_slice=0.60, aw_slice=0.40, freq='MS'):
    """Equal-weight among bullish TrendStocks + static AllWeather."""
    tw = trend_sig.resample(freq).last().reindex(closes.index, method='ffill')
    tw = tw.loc[SIM_START:]
    idx = closes.loc[SIM_START:].index
    all_t = list(set(TREND_TICKERS + AW_TICKERS))
    weights = pd.DataFrame(0.0, index=idx, columns=all_t)
    tw_aligned = tw.reindex(idx, method='ffill')

    for date in idx:
        bullish = [t for t in TREND_TICKERS if tw_aligned.loc[date].get(t, 0) == 1]
        n = len(bullish)
        if n > 0:
            for t in bullish:
                weights.loc[date, t] += trend_slice / n
    for t in AW_TICKERS:
        weights[t] += AW_TARGET[t] * aw_slice
    return weights

def build_weights_momentum(trend_sig, lookback_days=63, trend_slice=0.60,
                           aw_slice=0.40, freq='MS'):
    """Momentum-weighted TrendStocks + static AllWeather."""
    mom = closes[TREND_TICKERS].pct_change(lookback_days)
    tw = trend_sig.resample(freq).last().reindex(closes.index, method='ffill')
    tw = tw.loc[SIM_START:]
    mom = mom.reindex(closes.index, method='ffill').loc[SIM_START:]
    idx = closes.loc[SIM_START:].index
    all_t = list(set(TREND_TICKERS + AW_TICKERS))
    weights = pd.DataFrame(0.0, index=idx, columns=all_t)
    tw_aligned = tw.reindex(idx, method='ffill')
    mom_aligned = mom.reindex(idx, method='ffill')

    for date in idx:
        bullish = [t for t in TREND_TICKERS if tw_aligned.loc[date].get(t, 0) == 1]
        n = len(bullish)
        if n > 0:
            if n > 1:
                mom_vals = {t: max(mom_aligned.loc[date].get(t, 0), 0.001)
                           for t in bullish}
                total = sum(mom_vals.values())
                for t in bullish:
                    weights.loc[date, t] += trend_slice * mom_vals[t] / total
            else:
                for t in bullish:
                    weights.loc[date, t] += trend_slice / n
    for t in AW_TICKERS:
        weights[t] += AW_TARGET[t] * aw_slice
    return weights

# === Part 1: Momentum Lookback Comparison ===
print("\n" + "="*60)
print("=== Momentum Lookback Comparison ===")
print("="*60)

lookback_results = []

# Equal-weight baseline
w_eq = build_weights_equal(trend_signal, trend_slice=0.60, aw_slice=0.40)
r_f, eq_f, to = simulate_with_fees(w_eq, returns, fee_bps=FEE_BPS)
m = calc_metrics(r_f, eq_f, 'EqualWeight (baseline)')
m['Turnover'] = f'{to.mean()*252:.1%}'
lookback_results.append(m)

# Different lookback periods
for lb_days, lb_label in [(21, '1m'), (42, '2m'), (63, '3m'), (126, '6m'), (252, '12m')]:
    w = build_weights_momentum(trend_signal, lookback_days=lb_days,
                               trend_slice=0.60, aw_slice=0.40)
    r_f, eq_f, to = simulate_with_fees(w, returns, fee_bps=FEE_BPS)
    m = calc_metrics(r_f, eq_f, f'Mom {lb_label} ({lb_days}d)')
    m['Turnover'] = f'{to.mean()*252:.1%}'
    lookback_results.append(m)

df_lb = pd.DataFrame(lookback_results)
print(df_lb.to_string(index=False))

# === Part 2: Allocation Sensitivity (with 3m momentum) ===
print("\n" + "="*60)
print("=== Allocation Sensitivity (3m momentum) ===")
print("="*60)

alloc_results = []
for trend_pct in [50, 55, 60, 65, 70, 75, 80]:
    aw_pct = 100 - trend_pct
    w = build_weights_momentum(trend_signal, lookback_days=63,
                               trend_slice=trend_pct/100, aw_slice=aw_pct/100)
    r_f, eq_f, to = simulate_with_fees(w, returns, fee_bps=FEE_BPS)
    m = calc_metrics(r_f, eq_f, f'T{trend_pct}/AW{aw_pct} Mom3m')
    m['Turnover'] = f'{to.mean()*252:.1%}'
    alloc_results.append(m)

df_alloc = pd.DataFrame(alloc_results)
print(df_alloc.to_string(index=False))

# === Part 3: Best lookback x Best allocation ===
print("\n" + "="*60)
print("=== Combined: Best lookback x allocation grid ===")
print("="*60)

combined_results = []
for lb_days, lb_label in [(21, '1m'), (63, '3m'), (126, '6m')]:
    for trend_pct in [60, 65, 70, 75]:
        aw_pct = 100 - trend_pct
        w = build_weights_momentum(trend_signal, lookback_days=lb_days,
                                   trend_slice=trend_pct/100, aw_slice=aw_pct/100)
        r_f, eq_f, to = simulate_with_fees(w, returns, fee_bps=FEE_BPS)
        m = calc_metrics(r_f, eq_f, f'T{trend_pct}/AW{aw_pct} Mom{lb_label}')
        m['Turnover'] = f'{to.mean()*252:.1%}'
        combined_results.append(m)

df_comb = pd.DataFrame(combined_results)
print(df_comb.to_string(index=False))

print("\n" + "="*60)
print("NOTE: Simulation Sharpe is typically 2-3x cloud Sharpe.")
print("Cloud v1.3 (Mom 3m, T60/AW40): Sharpe 1.130")
print("Focus on RELATIVE rankings, not absolute values.")
print("="*60)
