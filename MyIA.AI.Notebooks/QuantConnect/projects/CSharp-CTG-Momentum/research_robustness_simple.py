# CTG-Momentum : proxy Python de la strategie C# (Main.cs), fenetre figee 2015-2025
#
# Le script rejoue les regles de Main.cs sur un univers de 30 grandes capitalisations
# (proxy des constituants OEF) avec des donnees yfinance. Les indicateurs suivent les
# classes C# du projet :
#   - pente : AnnualizedExponentialSlopeIndicator (regression du log-prix sur 90 seances,
#     ((exp(pente)^252) - 1) * 100 * R^2, echelle en pourcentage) ;
#   - moyenne : ExponentialMovingAverage(150) (CustomMomentumIndicator) ;
#   - gap : GapIndicator(90), plus forte variation absolue d'une cloture a la suivante ;
#   - ATR : AverageTrueRange(20), lissage de Wilder (defaut QC) ;
#   - regime : SPY au-dessus de sa SMA(200) (MarketRegimeFilter).
# Le jeudi, 1 minute apres l'ouverture, Main.cs classe les titres prets par pente,
# garde les 20 premiers, puis filtre pente > 10, prix > EMA(150) et gap < 0,15 ; il
# vend toute ligne absente de la liste filtree, et n'achete qu'en regime Risk-ON.
# Ici, les indicateurs sont pris a la cloture de la veille et les ordres au prix
# d'ouverture du jeudi.
#
# Ecarts au C# qui restent : univers fixe de 30 titres d'aujourd'hui (biais de
# survie), pas de reajustement bimensuel des tailles de position, ni frais ni
# glissement. Le Sharpe est calcule sur les rendements hebdomadaires, sans taux sans
# risque (celui de QC en retranche un).

import numpy as np
import pandas as pd
import yfinance as yf
import warnings
from datetime import datetime
warnings.filterwarnings('ignore')

TICKERS = [
    "AAPL", "MSFT", "AMZN", "GOOGL", "META", "NVDA", "TSLA",
    "JPM", "BAC", "WFC", "GS",
    "JNJ", "UNH", "PFE", "ABT", "TMO",
    "V", "MA", "PYPL",
    "PG", "KO", "PEP", "WMT", "HD",
    "XOM", "CVX",
    "DIS", "NFLX",
    "ADBE", "CRM"
]

# Fenetre figee (meme fenetre que le carnet research_robustness.ipynb, #22273).
# yfinance exclut la date de fin : END charge jusqu'a la seance du 2025-12-31.
# Les donnees sont chargees des WARMUP_START pour que la SMA(200), l'EMA(150), la
# pente 90 j, le gap 90 j et l'ATR soient prets au premier jour de la fenetre, comme
# SetWarmUp(200) et les History(...) de Main.cs.
WARMUP_START = '2014-01-01'
START = '2015-01-01'
END = '2026-01-01'

# Parametres de Main.cs
SLOPE_WINDOW = 90          # _annualizedSlopeWindow
EMA_WINDOW = 150           # _movingAverageWindow
GAP_WINDOW = 90            # _gapWindow
ATR_WINDOW = 20            # _atrWindow
SMA_REGIME = 200           # SMA("SPY", 200)
TOP_N = 20                 # _topNStockOfSp500
MIN_SLOPE = 10.0           # _minimumAnnualizedSlope (en pourcentage)
MAX_GAP = 0.15             # _maximumGap
RISK_PER_TRADE = 0.01      # RiskPerContractOnPortfolio
INITIAL_CAPITAL = 1_000_000
SHARPE_THRESHOLD = 0.4     # critere du README du projet


def flatten(df):
    if isinstance(df.columns, pd.MultiIndex):
        df = df.copy()
        df.columns = df.columns.droplevel(1)
    return df


def exp_slope(close, window):
    """AnnualizedExponentialSlopeIndicator : OLS de log(close) sur t = 1..window."""
    logp = np.log(close.to_numpy(dtype=float))
    out = np.full(len(logp), np.nan)
    if len(logp) < window:
        return pd.Series(out, index=close.index)
    win = np.lib.stride_tricks.sliding_window_view(logp, window)
    t = np.arange(1, window + 1, dtype=float)
    tc = t - t.mean()
    yc = win - win.mean(axis=1, keepdims=True)
    slope = (yc @ tc) / (tc @ tc)
    ss_tot = (yc ** 2).sum(axis=1)
    with np.errstate(divide='ignore', invalid='ignore'):
        r2 = np.where(ss_tot > 0, slope ** 2 * (tc @ tc) / ss_tot, 0.0)
    annual = (np.exp(slope) ** 252 - 1) * 100 * r2
    out[window - 1:] = annual
    return pd.Series(out, index=close.index)


def max_drawdown(values):
    return ((values.cummax() - values) / values.cummax()).max() * 100


def weekly_sharpe(returns):
    returns = returns.dropna()
    return returns.mean() / returns.std() * np.sqrt(52) if returns.std() > 0 else 0.0


print("=" * 70)
print("CTG-Momentum : proxy Python de Main.cs (2015-2025)")
print("=" * 70)
print(f"\nFenetre {START} -> {END} (borne de fin exclue), chargement des {WARMUP_START} pour l'echauffement")
print(f"Univers : SPY + {len(TICKERS)} grandes capitalisations (proxy OEF)")

spy_all = flatten(yf.download('SPY', start=WARMUP_START, end=END, progress=False, auto_adjust=True))
data = yf.download(TICKERS, start=WARMUP_START, end=END, progress=False, group_by='ticker', auto_adjust=True)
window_mask = (spy_all.index >= START) & (spy_all.index < END)
print(f"SPY : {window_mask.sum()} seances dans la fenetre "
      f"({spy_all.index[window_mask].min().date()} -> {spy_all.index[window_mask].max().date()})")

# ==== PHASE 1 : regime de marche ====
print("\n" + "=" * 70)
print("PHASE 1 : regime de marche (SPY contre SMA 200, a la cloture)")
print("=" * 70)

spy_all['SMA_200'] = spy_all['Close'].rolling(SMA_REGIME).mean()
spy_all['Regime'] = np.where(spy_all['SMA_200'].isna(), np.nan,
                             (spy_all['Close'] > spy_all['SMA_200']).astype(float))
spy_all['Transition'] = spy_all['Regime'].diff().abs()
spy = spy_all[window_mask].copy()
print(f"\nJours sans SMA(200) dans la fenetre : {int(spy['SMA_200'].isna().sum())}")

total_days = len(spy)
risk_on_days = int((spy['Regime'] == 1).sum())
risk_off_days = int((spy['Regime'] == 0).sum())
transitions = int(spy['Transition'].sum())
risk_on_pct = 100 * risk_on_days / total_days
print(f"  Total jours : {total_days}")
print(f"  Risk-ON  (SPY > SMA200) : {risk_on_days} jours ({risk_on_pct:.1f}%)")
print(f"  Risk-OFF (SPY < SMA200) : {risk_off_days} jours ({100 * risk_off_days / total_days:.1f}%)")
print(f"  Transitions : {transitions}")
per_year = spy['Transition'].groupby(spy.index.year).sum().astype(int)
print("  Transitions par annee : " + ", ".join(f"{y}: {n}" for y, n in per_year.items()))

risk_off = spy[spy['Regime'] == 0].copy()
if not risk_off.empty:
    risk_off['Block'] = (risk_off.index.to_series().diff() > pd.Timedelta(days=5)).cumsum()
    print("\n  Periodes Risk-OFF d'au moins 10 seances")
    print("  (variation de SPY entre le premier et le dernier jour de la periode) :")
    for _, group in risk_off.groupby('Block'):
        if len(group) >= 10:
            change = 100 * (group['Close'].iloc[-1] / group['Close'].iloc[0] - 1)
            print(f"    {group.index.min().date()} -> {group.index.max().date()} "
                  f"({len(group)} seances, SPY {change:+.1f}%)")

# ==== PHASE 2 : indicateurs ====
print("\n" + "=" * 70)
print("PHASE 2 : indicateurs par action (classes C# du projet)")
print("=" * 70)

stock_data = {}
for ticker in TICKERS:
    df = flatten(data[ticker].copy()).dropna(subset=['Close'])
    if len(df) < SMA_REGIME:
        print(f"  {ticker} ecarte : {len(df)} seances")
        continue
    df['Slope'] = exp_slope(df['Close'], SLOPE_WINDOW)
    df['EMA'] = df['Close'].ewm(span=EMA_WINDOW, adjust=False, min_periods=EMA_WINDOW).mean()
    df['Gap'] = df['Close'].pct_change().abs().rolling(GAP_WINDOW - 1).max()
    tr = np.maximum(df['High'] - df['Low'],
                    np.maximum(abs(df['High'] - df['Close'].shift(1)),
                               abs(df['Low'] - df['Close'].shift(1))))
    df['ATR'] = tr.ewm(alpha=1 / ATR_WINDOW, adjust=False, min_periods=ATR_WINDOW).mean()
    # Valeurs connues a l'ouverture du jour : indicateurs de la cloture de la veille
    for col in ['Slope', 'EMA', 'Gap', 'ATR']:
        df[col + '_prev'] = df[col].shift(1)
    stock_data[ticker] = df
print(f"{len(stock_data)} actions avec indicateurs")

# ==== PHASE 3 : backtest ====
print("\n" + "=" * 70)
print("PHASE 3 : backtest (jeudi a l'ouverture, indicateurs de la veille)")
print("=" * 70)

spy_all['SMA_200_prev'] = spy_all['SMA_200'].shift(1)
thursdays = spy.index[spy.index.dayofweek == 3]
print(f"  {len(thursdays)} jeudis ({thursdays[0].date()} -> {thursdays[-1].date()})")

cash = INITIAL_CAPITAL
positions = {}
history = []
ranked_total = 0
slope_rejects = 0
ema_rejects = 0
gap_rejects = 0
empty_lists = 0

for date in thursdays:
    def price(ticker, field):
        df = stock_data[ticker]
        return df.loc[date, field] if date in df.index else np.nan

    value_open = cash + sum(n * price(t, 'Open') for t, n in positions.items()
                            if not np.isnan(price(t, 'Open')))
    risk_on = spy_all.loc[date, 'Open'] > spy_all.loc[date, 'SMA_200_prev']

    ready = []
    for ticker, df in stock_data.items():
        if date not in df.index:
            continue
        row = df.loc[date]
        if row[['Slope_prev', 'EMA_prev', 'Gap_prev', 'ATR_prev']].isna().any():
            continue
        ready.append((ticker, row))
    ready.sort(key=lambda item: item[1]['Slope_prev'], reverse=True)
    top = ready[:TOP_N]
    ranked_total += len(top)

    selected = []
    for ticker, row in top:
        if not row['Slope_prev'] > MIN_SLOPE:
            slope_rejects += 1
        elif not row['Open'] > row['EMA_prev']:
            ema_rejects += 1
        elif not row['Gap_prev'] < MAX_GAP:
            gap_rejects += 1
        else:
            selected.append((ticker, row))
    if not selected:
        empty_lists += 1
    selected_names = {t for t, _ in selected}

    # Main.cs vend toute ligne absente de la liste filtree, quel que soit le regime
    for ticker in [t for t in positions if t not in selected_names]:
        p = price(ticker, 'Open')
        if not np.isnan(p):
            cash += positions.pop(ticker) * p

    if risk_on:
        for ticker, row in selected:
            if ticker in positions:
                continue
            shares = int(np.floor(value_open * RISK_PER_TRADE / row['ATR_prev']))
            cost = shares * row['Open']
            if shares > 0 and cash > cost:
                positions[ticker] = shares
                cash -= cost

    value_close = cash + sum(n * price(t, 'Close') for t, n in positions.items()
                             if not np.isnan(price(t, 'Close')))
    history.append({'date': date, 'value': value_close, 'n_positions': len(positions)})

print(f"  Titres classes (top {TOP_N}) : {ranked_total}")
print(f"  Ecartes par la pente <= {MIN_SLOPE:g} : {slope_rejects}")
print(f"  Ecartes par le prix <= EMA({EMA_WINDOW}) : {ema_rejects}")
print(f"  Ecartes par le gap >= {MAX_GAP:g} : {gap_rejects}")
print(f"  Jeudis sans aucun titre retenu : {empty_lists} / {len(thursdays)}")

# ==== RESULTATS ====
print("\n" + "=" * 70)
print("RESULTATS SUR LA FENETRE")
print("=" * 70)

res = pd.DataFrame(history).set_index('date')
res['returns'] = res['value'].pct_change()
res.loc[res.index[0], 'returns'] = res['value'].iloc[0] / INITIAL_CAPITAL - 1
spy_w = spy_all.loc[thursdays, 'Close']
spy_ret = spy_w.pct_change()
spy_ret.iloc[0] = spy_w.iloc[0] / spy_all.loc[thursdays[0], 'Open'] - 1
spy_value = INITIAL_CAPITAL * (1 + spy_ret).cumprod()

years = (res.index[-1] - res.index[0]).days / 365.25
growth = res['value'].iloc[-1] / INITIAL_CAPITAL
total_return = (growth - 1) * 100
cagr = (growth ** (1 / years) - 1) * 100
sharpe = weekly_sharpe(res['returns'])
max_dd = max_drawdown(res['value'])
spy_growth = spy_value.iloc[-1] / INITIAL_CAPITAL
spy_cagr = (spy_growth ** (1 / years) - 1) * 100
spy_sharpe = weekly_sharpe(spy_ret)
spy_dd = max_drawdown(spy_value)

print(f"\nPeriode : {res.index[0].date()} -> {res.index[-1].date()} ({years:.2f} ans)")
print(f"\n{'':<22}{'Strategie':>12}{'SPY':>12}")
print(f"{'Rendement total':<22}{total_return:>11.2f}%{(spy_growth - 1) * 100:>11.2f}%")
print(f"{'CAGR':<22}{cagr:>11.2f}%{spy_cagr:>11.2f}%")
print(f"{'Sharpe (hebdo)':<22}{sharpe:>12.3f}{spy_sharpe:>12.3f}")
print(f"{'Pire baisse':<22}{max_dd:>11.2f}%{spy_dd:>11.2f}%")
print(f"\nNombre moyen de positions : {res['n_positions'].mean():.1f} "
      f"(maximum {res['n_positions'].max()}, jeudis sans position : {(res['n_positions'] == 0).sum()})")

# ==== STABILITE PAR SEMESTRE ====
print("\n" + "=" * 70)
print("STABILITE PAR SEMESTRE")
print("=" * 70)
print("Backtest unique decoupe en semestres : aucun parametre n'est re-estime d'un")
print("semestre a l'autre, ce n'est pas une validation walk-forward.\n")

semesters = [(datetime(y, m, 1), datetime(y + (m == 7), 1 if m == 7 else 7, 1))
             for y in range(2015, 2026) for m in (1, 7)]
print(f"{'Semestre':<20}{'Strategie':>11}{'SPY':>10}{'Ecart':>10}{'Sharpe':>9}")
print("-" * 60)
rows = []
for s, e in semesters:
    mask = (res.index >= s) & (res.index < e)
    if mask.sum() < 2:
        continue
    strat = ((1 + res.loc[mask, 'returns']).prod() - 1) * 100
    bench = ((1 + spy_ret[mask]).prod() - 1) * 100
    sem_sharpe = weekly_sharpe(res.loc[mask, 'returns'])
    label = f"{s:%Y-%m} -> {e:%Y-%m}"
    rows.append({'period': label, 'start': s, 'strategy': strat, 'spy': bench,
                 'gap': strat - bench, 'sharpe': sem_sharpe})
    print(f"{label:<20}{strat:>10.2f}%{bench:>9.2f}%{strat - bench:>9.2f}%{sem_sharpe:>9.3f}")
sem = pd.DataFrame(rows)

positive = int((sem['strategy'] > 0).sum())
beats = int((sem['gap'] > 0).sum())
worst = sem.loc[sem['strategy'].idxmin()]
best = sem.loc[sem['strategy'].idxmax()]
print(f"\nSemestres positifs : {positive} / {len(sem)}")
print(f"Semestres au-dessus de SPY : {beats} / {len(sem)}")
print(f"Ecart moyen a SPY : {sem['gap'].mean():.2f} pts")
print(f"Pire semestre : {worst['period']} ({worst['strategy']:.2f}%)")
print(f"Meilleur semestre : {best['period']} ({best['strategy']:.2f}%)")

# ==== SYNTHESE ====
print("\n" + "=" * 70)
print("SYNTHESE (valeurs calculees ci-dessus)")
print("=" * 70)

print(f"\nFiltre SMA(200) : {risk_on_pct:.1f}% du temps en Risk-ON, {transitions} transitions.")
for label, start in [("Crise COVID", datetime(2020, 1, 1)), ("Baisse 2022", datetime(2022, 1, 1))]:
    r = sem[sem['start'] == start].iloc[0]
    mask = (res.index >= start) & (res.index < datetime(start.year, 7, 1))
    dd = max_drawdown(res.loc[mask, 'value'])
    sdd = max_drawdown(spy_value[mask])
    verdict = "au-dessus de" if r['gap'] > 0 else "en dessous de"
    print(f"{label} ({r['period']}) : strategie {r['strategy']:+.2f}%, SPY {r['spy']:+.2f}% "
          f"({verdict} SPY) ; pire baisse dans le semestre {dd:.2f}% contre {sdd:.2f}% pour SPY.")
verdict_sharpe = "atteint" if sharpe >= SHARPE_THRESHOLD else "non atteint"
print(f"Critere Sharpe >= {SHARPE_THRESHOLD} : {verdict_sharpe} sur le proxy (Sharpe {sharpe:.3f}).")
compare = "au-dessus de" if sharpe > spy_sharpe else "en dessous de"
print(f"Sharpe du proxy {compare} celui de SPY sur la meme fenetre ({sharpe:.3f} contre {spy_sharpe:.3f}).")
print("\nLimites : univers de 30 titres choisis aujourd'hui (biais de survie), sans frais ni")
print("glissement, sans le reajustement bimensuel des tailles de Main.cs. Le Sharpe du")
print("backtest C# sur l'univers OEF se mesure sur QuantConnect, pas dans ce script.")
