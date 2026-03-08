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


def find_envelope_line(pivots_df, is_resistance, recency_alpha=0.0,
                       max_violation_pct=0.0, check_all_pivots=None):
    """Find the tightest envelope line through any pair of same-type pivots.

    Algorithm:
    1. Try ALL pairs of same-type pivots as anchors
    2. Check containment against check_all_pivots (if provided) or same-type pivots
    3. Allow up to max_violation_pct fraction of check points to violate
    4. Score = (violations, avg_margin) — minimize violations first, then tightness

    Args:
        pivots_df: DataFrame with time_numeric, price columns (same-type pivots)
        is_resistance: True for resistance (line above), False for support (below)
        recency_alpha: 0=uniform weighting, >0=recent pivots weighted more
        max_violation_pct: fraction of check points allowed to violate (0=strict)
        check_all_pivots: optional (n,2) array of [time_numeric, price] for ALL
            pivots to check containment against. If None, checks same-type only.

    Returns:
        (p1_series, p2_series) or (None, None)
    """
    n_pivots = len(pivots_df)
    if n_pivots < 2:
        return None, None

    pivots_vals = pivots_df[['time_numeric', 'price']].values

    # Points to check containment against
    if check_all_pivots is not None:
        check_vals = check_all_pivots
    else:
        check_vals = pivots_vals
    n_check = len(check_vals)
    max_violations = max(1, int(n_check * max_violation_pct)) if max_violation_pct > 0 else 0

    best = None
    best_violations = n_check + 1
    best_margin = float('inf')

    for i in range(n_pivots):
        for j in range(i + 1, n_pivots):
            t1, p1 = pivots_vals[i]
            t2, p2 = pivots_vals[j]
            if abs(t2 - t1) < 1e-9:
                continue

            m, c = get_line_params_time(t1, p1, t2, p2)
            if m == float('inf'):
                continue

            # Check containment with violation tolerance
            violations = 0
            total_margin = 0.0
            n_checked = 0
            valid = True
            for k in range(n_check):
                pk_t, pk_p = check_vals[k]
                # Skip anchor points
                if abs(pk_t - t1) < 1e-9 or abs(pk_t - t2) < 1e-9:
                    continue
                line_val = m * pk_t + c
                if is_resistance:
                    margin = line_val - pk_p  # positive = point below line (good)
                    if margin < -1e-9:
                        violations += 1
                        if violations > max_violations:
                            valid = False
                            break
                else:
                    margin = pk_p - line_val  # positive = point above line (good)
                    if margin < -1e-9:
                        violations += 1
                        if violations > max_violations:
                            valid = False
                            break
                total_margin += margin
                n_checked += 1

            if not valid:
                continue

            avg_margin = total_margin / n_checked if n_checked > 0 else float('inf')

            # Score: minimize violations first, then minimize avg_margin (tightest)
            if (violations < best_violations or
                    (violations == best_violations and avg_margin < best_margin)):
                best_violations = violations
                best_margin = avg_margin
                best = (i, j)

    if best is None:
        return None, None
    return pivots_df.iloc[best[0]], pivots_df.iloc[best[1]]


def _check_nesting(inner_m, inner_c, outer_m, outer_c,
                   t_start, t_end, is_resistance):
    """Check that inner line stays inside outer line across the time range."""
    n_checks = 10
    for i in range(n_checks + 1):
        t = t_start + (t_end - t_start) * i / n_checks
        inner_val = inner_m * t + inner_c
        outer_val = outer_m * t + outer_c
        if is_resistance:
            # Inner resistance must be <= outer resistance
            if inner_val > outer_val + 1e-9:
                return False
        else:
            # Inner support must be >= outer support
            if inner_val < outer_val - 1e-9:
                return False
    return True


# Keep old function for backward compatibility with QC algo
def find_best_channel_line_strict_weighted(pivots_df, all_pivots_np, is_resistance,
                                           weight_power=1.0, recent_pivot_fraction=1.0,
                                           max_violation_pct=0.2):
    """Legacy: find line through pivot pairs with relaxed containment against pivots only."""
    n_pivots = len(pivots_df)
    if n_pivots < 2 or len(all_pivots_np) < 1:
        return None, None

    check_df = pd.DataFrame(all_pivots_np, columns=['time_numeric', 'price'])
    check_df = check_df.sort_values('time_numeric', ascending=True)
    n_total = len(check_df)

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

            violations = 0
            for k in range(n_total):
                pk_t, pk_p = all_pivots_np[k, 0], all_pivots_np[k, 1]
                if abs(pk_t - p1_t) < 1e-9 or abs(pk_t - p2_t) < 1e-9:
                    continue
                if not check_point_position(pk_t, pk_p, m, c, check_above=(not is_resistance)):
                    violations += 1
                    if violations > max_violations:
                        break

            if violations <= max_violations:
                # Compute average margin against all checked pivots
                total_margin = 0.0
                n_checked = 0
                for k in range(n_total):
                    pk_t, pk_p = all_pivots_np[k, 0], all_pivots_np[k, 1]
                    line_val = m * pk_t + c
                    if is_resistance:
                        total_margin += line_val - pk_p
                    else:
                        total_margin += pk_p - line_val
                    n_checked += 1
                avg_margin = total_margin / n_checked if n_checked > 0 else float('inf')
                valid_lines.append({"p1": p1, "p2": p2,
                                   "avg_margin": avg_margin,
                                   "violations": violations})

    if not valid_lines:
        return None, None

    valid_lines.sort(key=lambda x: (x['violations'], x['avg_margin']))
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
