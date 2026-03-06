# channel_helpers.py - Helper functions for multi-channel strategy
import numpy as np
import pandas as pd
import math


def get_line_params_time(p1_time_num, p1_price, p2_time_num, p2_price):
    """Get slope (m) and intercept (c) for a line through two time-price points."""
    time_diff = p2_time_num - p1_time_num
    if abs(time_diff) < 1e-9:
        return float('inf'), float(p1_time_num)
    m = (p2_price - p1_price) / time_diff
    c = p1_price - m * p1_time_num
    return m, c


def check_point_position(point_time_num, point_price, m, c, check_above, epsilon=1e-9):
    """Check if a point is above/below a line defined by slope m and intercept c."""
    if m == float('inf'):
        return False
    line_y = m * point_time_num + c
    if check_above:
        return point_price >= line_y - epsilon
    else:
        return point_price <= line_y + epsilon


def calculate_weighted_sse(p1_time_num, p1_price, p2_time_num, p2_price,
                           pivots_np, time_min, time_max, weight_power=1.0):
    """Calculate weighted sum of squared errors for pivots relative to a line."""
    m, c = get_line_params_time(p1_time_num, p1_price, p2_time_num, p2_price)
    if m == float('inf'):
        return float('inf')

    if len(pivots_np) == 0:
        return 0.0

    total_wsse = 0.0
    total_weight = 0.0
    time_range = max(time_max - time_min, 1.0)

    for k in range(len(pivots_np)):
        pk_time, pk_price = pivots_np[k, 0], pivots_np[k, 1]
        if abs(pk_time - p1_time_num) < 1e-9 or abs(pk_time - p2_time_num) < 1e-9:
            continue
        normalized_time = max(0.0, (pk_time - time_min) / time_range)
        weight = normalized_time ** weight_power + 1e-9
        line_y = m * pk_time + c
        error = pk_price - line_y
        total_wsse += weight * (error ** 2)
        total_weight += weight

    return total_wsse / total_weight if total_weight > 1e-9 else 0.0


def find_best_channel_line_strict_weighted(pivots_df, all_pivots_np, is_resistance,
                                           weight_power=1.0, recent_pivot_fraction=1.0,
                                           max_violation_pct=0.2):
    """Find the best support/resistance line through pivot pairs.

    Relaxed containment: allows up to max_violation_pct of pivots to be on the
    wrong side. Lines are ranked by (violation_count, wsse) so fewer violations
    is always preferred, with WSSE as tiebreaker.
    """
    n_pivots = len(pivots_df)
    if n_pivots < 2 or len(all_pivots_np) < 1:
        return None, None

    check_df = pd.DataFrame(all_pivots_np, columns=['time_numeric', 'price'])
    check_df = check_df.sort_values('time_numeric', ascending=True)
    n_total = len(check_df)

    safe_rpf = max(0.0, min(1.0, recent_pivot_fraction))
    n_keep = max(1, math.ceil(n_total * safe_rpf))
    recent_df = check_df.tail(n_keep).copy()
    if recent_df.empty:
        return None, None

    max_violations = max(1, int(n_total * max_violation_pct))
    valid_lines = []

    for i in range(n_pivots):
        p1 = pivots_df.iloc[i]
        for j in range(i + 1, n_pivots):
            p2 = pivots_df.iloc[j]
            p1_t, p1_p = p1['time_numeric'], p1['price']
            p2_t, p2_p = p2['time_numeric'], p2['price']
            if p1_t >= p2_t:
                continue

            m, c = get_line_params_time(p1_t, p1_p, p2_t, p2_p)
            if m == float('inf'):
                continue

            # Relaxed containment: count violations
            violations = 0
            checked = 0
            for k in range(n_total):
                pk_t, pk_p = all_pivots_np[k, 0], all_pivots_np[k, 1]
                if abs(pk_t - p1_t) < 1e-9 or abs(pk_t - p2_t) < 1e-9:
                    continue
                checked += 1
                if not check_point_position(pk_t, pk_p, m, c, check_above=(not is_resistance)):
                    violations += 1
                    if violations > max_violations:
                        break

            if violations <= max_violations:
                wsse_df = recent_df[
                    (np.abs(recent_df['time_numeric'] - p1_t) > 1e-9) &
                    (np.abs(recent_df['time_numeric'] - p2_t) > 1e-9)
                ]
                wsse = 0.0
                if not wsse_df.empty:
                    wsse = calculate_weighted_sse(
                        p1_t, p1_p, p2_t, p2_p,
                        wsse_df[['time_numeric', 'price']].values,
                        wsse_df['time_numeric'].min(),
                        wsse_df['time_numeric'].max(),
                        weight_power
                    )
                if wsse != float('inf'):
                    valid_lines.append({"p1": p1, "p2": p2, "wsse": wsse,
                                       "violations": violations})

    if not valid_lines:
        return None, None

    # Prefer fewer violations, then lower WSSE
    valid_lines.sort(key=lambda x: (x['violations'], x['wsse']))
    best = valid_lines[0]
    return best['p1'], best['p2']


def classic_chart_zigzag(df, threshold_percent=0.05):
    """Classic ZigZag indicator: finds alternating high/low pivots."""
    if len(df) < 2:
        return []

    pivots = []
    first = df.iloc[0]
    last_price = float(first['close'])
    last_time = first['time']
    second = df.iloc[1]
    direction_up = float(second['close']) > last_price
    extreme_price = last_price
    extreme_time = last_time
    last_sign = 1 if direction_up else -1  # +1=Low, -1=High
    pivots.append({'time': last_time, 'price': last_price, 'type': last_sign})

    for i in range(1, len(df)):
        row = df.iloc[i]
        price = float(row['close'])
        time = row['time']

        if direction_up:
            if price > extreme_price:
                extreme_price = price
                extreme_time = time
            else:
                retrace = 1.0 - (price / extreme_price) if extreme_price != 0 else 0
                if retrace >= threshold_percent:
                    pivots.append({'time': extreme_time, 'price': extreme_price, 'type': -1})
                    direction_up = False
                    extreme_price = price
                    extreme_time = time
        else:
            if price < extreme_price:
                extreme_price = price
                extreme_time = time
            else:
                rally = (price / extreme_price) - 1.0 if extreme_price != 0 else float('inf')
                if rally >= threshold_percent:
                    pivots.append({'time': extreme_time, 'price': extreme_price, 'type': 1})
                    direction_up = True
                    extreme_price = price
                    extreme_time = time

    # Ensure alternation
    if len(pivots) > 1 and pivots[-1]['type'] == pivots[-2]['type']:
        if pivots[-1]['type'] == 1:
            if pivots[-1]['price'] < pivots[-2]['price']:
                pivots.pop(-2)
            else:
                pivots.pop(-1)
        else:
            if pivots[-1]['price'] > pivots[-2]['price']:
                pivots.pop(-2)
            else:
                pivots.pop(-1)

    # Add last unconfirmed extreme
    if pivots and pivots[-1]['type'] != (-1 if direction_up else 1):
        pivots.append({'time': extreme_time, 'price': extreme_price,
                       'type': (-1 if direction_up else 1)})

    return pivots


def get_channel_value_at_time(channel_pivots, time_numeric):
    """Get channel line value at a specific time. channel_pivots = (dict1, dict2)."""
    if not channel_pivots or channel_pivots[0] is None or channel_pivots[1] is None:
        return float('nan')
    p1, p2 = channel_pivots[0], channel_pivots[1]
    if pd.isna(p1.get('time_numeric')) or pd.isna(p2.get('time_numeric')):
        return float('nan')
    m, c = get_line_params_time(p1['time_numeric'], p1['price'],
                                p2['time_numeric'], p2['price'])
    if m == float('inf'):
        return float('nan')
    return m * time_numeric + c
