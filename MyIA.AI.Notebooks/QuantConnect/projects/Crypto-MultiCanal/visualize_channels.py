"""
Visualisation locale des canaux ZigZag multi-echelle (macro/meso/micro).
Utilise l'algo d'enveloppe stricte avec minimisation de marge (SVM-like).
Nesting par trimming: meso vire les pivots anterieurs a macro, micro idem.
"""
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
import matplotlib.dates as mdates
from datetime import timezone
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from channel_helpers import (
    classic_chart_zigzag, find_envelope_line,
    get_line_params_time, get_channel_value_at_time
)

import yfinance as yf


def load_data(ticker, period="3y"):
    df = yf.download(ticker, period=period, interval="1d", progress=False)
    df = df.reset_index()
    if isinstance(df.columns, pd.MultiIndex):
        df.columns = [col[0] if col[1] == '' else col[0] for col in df.columns]
    df = df.rename(columns={'Date': 'time', 'Close': 'close'})
    df['time'] = pd.to_datetime(df['time'])
    if df['time'].dt.tz is None:
        df['time'] = df['time'].dt.tz_localize('UTC')
    return df


def _to_dict(series):
    if series is None or not isinstance(series, pd.Series):
        return None
    t = series.get('time')
    p = series.get('price')
    tn = series.get('time_numeric')
    if t is None or p is None or tn is None:
        return None
    return {'time': t, 'price': float(p), 'time_numeric': float(tn)}


def _get_line_mc(p1_dict, p2_dict):
    """Get (m, c) from two dict anchor points. Returns None if invalid."""
    if p1_dict is None or p2_dict is None:
        return None
    m, c = get_line_params_time(
        p1_dict['time_numeric'], p1_dict['price'],
        p2_dict['time_numeric'], p2_dict['price'])
    if m == float('inf'):
        return None
    return (m, c)


def _get_anchor_times(channel_dict):
    """Extract the 4 anchor timestamps from a channel dict, sorted chronologically.

    A channel has resistance=(p1, p2) and support=(p1, p2), so up to 4 anchors.
    Returns sorted list of time_numeric values (may have <4 if some are None).
    """
    times = []
    for side in ['resistance', 'support']:
        for p in channel_dict[side]:
            if p is not None and 'time_numeric' in p:
                times.append(p['time_numeric'])
    times.sort()
    return times


def _fit_scale(pivots_df, scale_name):
    """Fit envelope lines for one scale. Returns channel dict."""
    high_df = pivots_df[pivots_df['type'] == -1].copy()
    low_df = pivots_df[pivots_df['type'] == 1].copy()
    print(f"  {scale_name}: {len(pivots_df)} pivots ({len(high_df)}H, {len(low_df)}L)")

    ch = {'resistance': (None, None), 'support': (None, None)}
    if len(high_df) >= 2:
        r1, r2 = find_envelope_line(high_df, True, recency_alpha=3.0)
        ch['resistance'] = (_to_dict(r1), _to_dict(r2))
    if len(low_df) >= 2:
        s1, s2 = find_envelope_line(low_df, False, recency_alpha=3.0)
        ch['support'] = (_to_dict(s1), _to_dict(s2))
    return ch


def build_channels_3level(df_zz, prices_df, zigzag_threshold):
    """Build 3-level channels: macro, meso, micro.

    Algorithm (3rd-anchor nesting + recency-weighted fitting):
    1. Compute ZigZag pivots
    2. MACRO: envelope on ALL pivots (recency weighting -> convergent)
    3. MESO: pivots from macro's 3rd chronological anchor onward
    4. MICRO: pivots from meso's 3rd chronological anchor onward

    Same find_envelope_line at each scale, just windowed pivots.
    """
    pivot_list = classic_chart_zigzag(df_zz, zigzag_threshold)
    if not pivot_list or len(pivot_list) < 4:
        return None, None, None

    pivots_df = pd.DataFrame(pivot_list)
    pivots_df['time'] = pd.to_datetime(pivots_df['time'])
    if pivots_df['time'].dt.tz is None:
        pivots_df['time_numeric'] = pivots_df['time'].apply(
            lambda x: x.replace(tzinfo=timezone.utc).timestamp())
    else:
        pivots_df['time_numeric'] = pivots_df['time'].apply(lambda x: x.timestamp())

    high_df = pivots_df[pivots_df['type'] == -1].copy()
    low_df = pivots_df[pivots_df['type'] == 1].copy()

    if len(high_df) < 2 or len(low_df) < 2:
        return pivots_df, None, (high_df, low_df)

    channels = {}

    # === MACRO: all pivots ===
    channels['macro'] = _fit_scale(pivots_df, 'macro')

    # === MESO: from macro's 3rd anchor ===
    macro_anchors = _get_anchor_times(channels['macro'])
    if len(macro_anchors) >= 3:
        meso_start_t = macro_anchors[2]
    elif len(macro_anchors) >= 2:
        meso_start_t = macro_anchors[1]
    else:
        meso_start_t = pivots_df['time_numeric'].median()

    meso_pivots = pivots_df[pivots_df['time_numeric'] >= meso_start_t - 1e-9]
    channels['meso'] = _fit_scale(meso_pivots, 'meso')

    # === MICRO: from meso's 3rd anchor ===
    meso_anchors = _get_anchor_times(channels['meso'])
    if len(meso_anchors) >= 3:
        micro_start_t = meso_anchors[2]
    elif len(meso_anchors) >= 2:
        micro_start_t = meso_anchors[1]
    else:
        micro_start_t = (meso_start_t + pivots_df['time_numeric'].iloc[-1]) / 2

    micro_pivots = pivots_df[pivots_df['time_numeric'] >= micro_start_t - 1e-9]
    channels['micro'] = _fit_scale(micro_pivots, 'micro')

    # Summary
    for scale in ['macro', 'meso', 'micro']:
        ch = channels[scale]
        res_ok = ch['resistance'][0] is not None
        sup_ok = ch['support'][0] is not None
        print(f"  -> {scale}: res={'OK' if res_ok else '-'} sup={'OK' if sup_ok else '-'}")

    return pivots_df, channels, (high_df, low_df)


def plot_channel_line(ax, p1, p2, time_range, color, linestyle, label, linewidth=1.5):
    if p1 is None or p2 is None:
        return
    t1 = p1['time_numeric']
    t2 = p2['time_numeric']
    m, c = get_line_params_time(t1, p1['price'], t2, p2['price'])
    if m == float('inf'):
        return

    t_start = time_range.iloc[0]
    t_end = time_range.iloc[-1]
    t_start_num = t_start.timestamp() if hasattr(t_start, 'timestamp') else pd.Timestamp(t_start, tz='UTC').timestamp()
    t_end_num = t_end.timestamp() if hasattr(t_end, 'timestamp') else pd.Timestamp(t_end, tz='UTC').timestamp()

    t_plot_start = max(t_start_num, min(t1, t2))
    times_num = np.linspace(t_plot_start, t_end_num, 200)
    values = m * times_num + c
    times_dt = pd.to_datetime(times_num, unit='s', utc=True)

    ax.plot(times_dt, values, color=color, linestyle=linestyle,
            linewidth=linewidth, alpha=0.8, label=label)
    for p in [p1, p2]:
        pt = pd.to_datetime(p['time_numeric'], unit='s', utc=True)
        ax.plot(pt, p['price'], 'o', color=color, markersize=6)


SCALE_STYLES = {
    'macro': {'res_color': 'red', 'sup_color': 'green', 'ls': '--', 'lw': 2.5},
    'meso':  {'res_color': 'darkred', 'sup_color': 'darkgreen', 'ls': '-', 'lw': 1.8},
    'micro': {'res_color': 'orange', 'sup_color': 'teal', 'ls': '-.', 'lw': 1.2},
}


def plot_all_channels(ax, channels, time_range):
    for scale in ['macro', 'meso', 'micro']:
        if scale not in channels:
            continue
        ch = channels[scale]
        st = SCALE_STYLES[scale]
        if ch['resistance'][0] is not None:
            plot_channel_line(ax, ch['resistance'][0], ch['resistance'][1],
                              time_range, st['res_color'], st['ls'],
                              f'{scale.title()} Res', st['lw'])
        if ch['support'][0] is not None:
            plot_channel_line(ax, ch['support'][0], ch['support'][1],
                              time_range, st['sup_color'], st['ls'],
                              f'{scale.title()} Sup', st['lw'])


def visualize_asset(ticker, name, thresholds, output_dir):
    print(f"\n{'='*60}")
    print(f"Loading {name} ({ticker})...")
    df = load_data(ticker)
    df_zz = df[['time', 'close']].copy()
    print(f"  {len(df)} bars, {df['time'].iloc[0].date()} to {df['time'].iloc[-1].date()}")
    print(f"  Price range: {df['close'].min():.2f} - {df['close'].max():.2f}")

    # ZigZag pivot counts
    print(f"\nZigZag pivot counts:")
    for thresh in thresholds:
        pivots = classic_chart_zigzag(df_zz, thresh)
        n_high = sum(1 for p in pivots if p['type'] == -1)
        n_low = sum(1 for p in pivots if p['type'] == 1)
        print(f"  {thresh*100:.0f}%: {len(pivots)} pivots ({n_high} H, {n_low} L)")

    # Multi-threshold comparison with 3 channels
    fig, axes = plt.subplots(len(thresholds), 1,
                             figsize=(18, 5.5 * len(thresholds)), sharex=True)
    if len(thresholds) == 1:
        axes = [axes]

    for idx, thresh in enumerate(thresholds):
        ax = axes[idx]
        ax.plot(df['time'], df['close'], color='black', linewidth=0.8, alpha=0.7)

        print(f"\n--- ZigZag {thresh*100:.0f}% ---")
        result = build_channels_3level(df_zz, df, thresh)
        if result[1] is None:
            ax.set_title(f'{name} - ZigZag {thresh*100:.0f}% - Pas assez de pivots')
            ax.grid(True, alpha=0.3)
            continue

        piv_df, chs, (h_df, l_df) = result

        # ZigZag line + pivots
        ax.plot(piv_df['time'].values, piv_df['price'].values,
                color='blue', linewidth=0.5, alpha=0.3)
        ax.scatter(h_df['time'].values, h_df['price'].values,
                   color='red', marker='v', s=25, zorder=5, alpha=0.5)
        ax.scatter(l_df['time'].values, l_df['price'].values,
                   color='green', marker='^', s=25, zorder=5, alpha=0.5)

        # 3-level channels
        plot_all_channels(ax, chs, df['time'])

        n_piv = len(piv_df)
        status = ' | '.join(
            f"{s}:{'OK' if chs[s]['resistance'][0] or chs[s]['support'][0] else 'X'}"
            for s in ['macro', 'meso', 'micro'])
        ax.set_title(f'{name} - ZigZag {thresh*100:.0f}% ({n_piv} pivots) | {status}',
                     fontsize=11)
        ax.legend(loc='upper left', fontsize=7, ncol=2)
        ax.grid(True, alpha=0.3)

    plt.suptitle(f'{name} - Canaux 3 niveaux (enveloppe stricte + marge min)',
                 fontsize=14, y=1.01)
    plt.tight_layout()
    fname = os.path.join(output_dir, f'{ticker.replace("-", "_")}_channels.png')
    plt.savefig(fname, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"\nSaved: {fname}")

    # Zoomed view (last year) for the middle threshold
    best_thresh = thresholds[len(thresholds) // 2]
    recent_cutoff = df['time'].max() - pd.Timedelta(days=365)
    recent_df = df[df['time'] >= recent_cutoff].copy()

    fig, ax = plt.subplots(1, 1, figsize=(18, 10))
    ax.plot(recent_df['time'], recent_df['close'], color='black', linewidth=1.0, alpha=0.8)

    print(f"\n--- ZOOM 1y: ZigZag {best_thresh*100:.0f}% ---")
    result = build_channels_3level(df_zz, df, best_thresh)
    if result[1] is not None:
        piv_df, chs, (h_df, l_df) = result
        recent_piv = piv_df[piv_df['time'] >= recent_cutoff]
        recent_h = h_df[h_df['time'] >= recent_cutoff]
        recent_l = l_df[l_df['time'] >= recent_cutoff]

        if len(recent_piv) > 0:
            ax.plot(recent_piv['time'].values, recent_piv['price'].values,
                    color='blue', linewidth=0.8, alpha=0.4)
        if len(recent_h) > 0:
            ax.scatter(recent_h['time'].values, recent_h['price'].values,
                       color='red', marker='v', s=50, zorder=5)
        if len(recent_l) > 0:
            ax.scatter(recent_l['time'].values, recent_l['price'].values,
                       color='green', marker='^', s=50, zorder=5)

        plot_all_channels(ax, chs, recent_df['time'])

    ax.set_title(f'{name} - Zoom 1 an - ZigZag {best_thresh*100:.0f}% '
                 f'(Macro + Meso + Micro)', fontsize=14)
    ax.legend(loc='upper left', fontsize=9)
    ax.grid(True, alpha=0.3)
    ax.xaxis.set_major_formatter(mdates.DateFormatter('%Y-%m'))
    plt.xticks(rotation=45)
    plt.tight_layout()
    fname_zoom = os.path.join(output_dir, f'{ticker.replace("-", "_")}_channels_zoom.png')
    plt.savefig(fname_zoom, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"Saved: {fname_zoom}")


if __name__ == '__main__':
    output_dir = os.path.dirname(os.path.abspath(__file__))

    visualize_asset('BTC-USD', 'BTC/USD', [0.05, 0.08, 0.10, 0.15], output_dir)
    visualize_asset('SPY', 'SPY', [0.03, 0.05, 0.08, 0.10], output_dir)

    print("\n" + "="*60)
    print("Done. Ouvrez les images pour validation visuelle.")
