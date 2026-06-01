# channel_helpers.py - Helper functions for multi-channel strategy
import numpy as np
import pandas as pd
import math

# --- Helper Function: Get Line Parameters ---
def get_line_params_time(p1_time_num, p1_price, p2_time_num, p2_price):
    time_diff = p2_time_num - p1_time_num
    # Use a small tolerance for time difference comparison
    if abs(time_diff) < 1e-9: return float('inf'), float(p1_time_num) # Return float('inf') for vertical line
    m = (p2_price - p1_price) / time_diff
    c = p1_price - m * p1_time_num
    return m, c

# --- Helper Function: Check Point Position Relative to Line ---
def check_point_position(point_time_num, point_price, m, c, check_above, epsilon=1e-9):
    if m == float('inf'): return False # Cannot check position relative to a vertical line this way
    line_y_at_point_x = m * point_time_num + c
    if check_above:
        return point_price >= line_y_at_point_x - epsilon
    else:
        return point_price <= line_y_at_point_x + epsilon

# --- Helper Function: Calculate Weighted SSE ---
def calculate_weighted_sse(p1_time_num, p1_price, p2_time_num, p2_price, pivots_for_sse_np, time_min_wsse, time_max_wsse, weight_power=1.0):
    m, c = get_line_params_time(p1_time_num, p1_price, p2_time_num, p2_price)
    if m == float('inf'): return float('inf')

    total_wsse = 0.0
    total_weight = 0.0
    time_range = time_max_wsse - time_min_wsse
    if time_range < 1e-9: time_range = 1.0 # Avoid division by zero if range is tiny

    if len(pivots_for_sse_np) == 0: return 0.0

    for k in range(len(pivots_for_sse_np)):
        pk_time_num, pk_price = pivots_for_sse_np[k, 0], pivots_for_sse_np[k, 1]
        # Skip the points defining the line
        if abs(pk_time_num - p1_time_num) < 1e-9 or abs(pk_time_num - p2_time_num) < 1e-9: continue

        # Calculate weight based on normalized time (ensure non-negative)
        normalized_time = max(0.0, (pk_time_num - time_min_wsse) / time_range) if time_range > 1e-9 else 0.5
        weight = normalized_time ** weight_power + 1e-9 # Add epsilon for zero weight case

        line_y_at_pk = m * pk_time_num + c
        error = pk_price - line_y_at_pk
        total_wsse += weight * (error**2)
        total_weight += weight

    return total_wsse / total_weight if total_weight > 1e-9 else 0.0

# --- Main Channel Finding Function ---
def find_best_channel_line_strict_weighted(pivots_df, all_pivots_for_check_np, is_resistance,
                                           weight_power=1.0, recent_pivot_fraction=1.0):
    strictly_valid_lines_info = []
    n_pivots = len(pivots_df)

    # Need at least 2 pivots to form a line and 1 pivot to check against
    if n_pivots < 2 or len(all_pivots_for_check_np) < 1:
        return None, None

    # Determine the pivots to use for WSSE calculation
    check_pivots_df = pd.DataFrame(all_pivots_for_check_np, columns=['time_numeric', 'price'])
    check_pivots_df = check_pivots_df.sort_values('time_numeric', ascending=True)
    n_total_check = len(check_pivots_df)

    safe_rpf = max(0.0, min(1.0, recent_pivot_fraction))
    n_keep_for_wsse = max(1, math.ceil(n_total_check * safe_rpf)) # Ensure at least 1
    recent_pivots_for_wsse_df = check_pivots_df.tail(n_keep_for_wsse).copy()

    if recent_pivots_for_wsse_df.empty: return None, None # Should not happen if n_total_check >= 1

    time_min_wsse = recent_pivots_for_wsse_df['time_numeric'].min()
    time_max_wsse = recent_pivots_for_wsse_df['time_numeric'].max()

    # Iterate through all pairs of pivots to define candidate lines
    for i in range(n_pivots):
        p1_series = pivots_df.iloc[i]
        for j in range(i + 1, n_pivots):
            p2_series = pivots_df.iloc[j]

            p1_time_num, p1_price = p1_series['time_numeric'], p1_series['price']
            p2_time_num, p2_price = p2_series['time_numeric'], p2_series['price']

            # Ensure p1 is earlier than p2
            if p1_time_num >= p2_time_num: continue

            m, c = get_line_params_time(p1_time_num, p1_price, p2_time_num, p2_price)
            if m == float('inf'): continue # Skip vertical lines

            # --- Strict Containment Check ---
            line_is_strictly_valid = True
            for k in range(n_total_check):
                pk_time_num, pk_price = all_pivots_for_check_np[k, 0], all_pivots_for_check_np[k, 1]
                # Skip the points defining the line itself
                if abs(pk_time_num - p1_time_num) < 1e-9 or abs(pk_time_num - p2_time_num) < 1e-9: continue

                # Check if the point is on the correct side of the line
                # For resistance: all points must be below or on the line (check_above = False)
                # For support:   all points must be above or on the line (check_above = True)
                if not check_point_position(pk_time_num, pk_price, m, c, check_above=(not is_resistance)):
                    line_is_strictly_valid = False
                    break # No need to check further points for this line

            # --- WSSE Calculation (if line is valid) ---
            if line_is_strictly_valid:
                # Filter the WSSE pivots to exclude the defining points
                pivots_to_calc_wsse_on_df = recent_pivots_for_wsse_df[
                    (np.abs(recent_pivots_for_wsse_df['time_numeric'] - p1_time_num) > 1e-9) &
                    (np.abs(recent_pivots_for_wsse_df['time_numeric'] - p2_time_num) > 1e-9)
                ]

                current_wsse = 0.0
                if not pivots_to_calc_wsse_on_df.empty:
                     # Recalculate min/max time for actual pivots used in WSSE
                     time_min_wsse_actual = pivots_to_calc_wsse_on_df['time_numeric'].min()
                     time_max_wsse_actual = pivots_to_calc_wsse_on_df['time_numeric'].max()
                     current_wsse = calculate_weighted_sse(p1_time_num, p1_price, p2_time_num, p2_price,
                                                           pivots_to_calc_wsse_on_df[['time_numeric', 'price']].values,
                                                           time_min_wsse_actual, time_max_wsse_actual, weight_power)

                if current_wsse != float('inf'):
                     # Store the defining pivots (as Series) and the calculated WSSE
                     strictly_valid_lines_info.append({ "p1": p1_series, "p2": p2_series, "wsse_recent": current_wsse })

    # If no strictly valid lines were found
    if not strictly_valid_lines_info:
        return None, None

    # Sort the valid lines by WSSE (ascending) and return the best pair
    strictly_valid_lines_info.sort(key=lambda x: x['wsse_recent'])
    best_line_info = strictly_valid_lines_info[0]
    return best_line_info['p1'], best_line_info['p2']

# --- ZigZag Calculation Function ---
def classic_chart_zigzag(df, thresholdPercent=0.05):
    if len(df) < 2: return []
    pivots = []
    firstBar = df.iloc[0]; lastPivotPrice = float(firstBar['close']); lastPivotTime = firstBar['time']
    secondBar = df.iloc[1]; directionUp = float(secondBar['close']) > lastPivotPrice
    currentExtremePrice = lastPivotPrice; currentExtremeTime = lastPivotTime
    lastSign = 1 if directionUp else -1 # +1 Low, -1 High
    pivots.append({'time': lastPivotTime, 'price': lastPivotPrice, 'type': lastSign})

    for i in range(1, len(df)):
        row = df.iloc[i]; price = float(row['close']); time = row['time']
        if directionUp:
            if price > currentExtremePrice:
                currentExtremePrice = price; currentExtremeTime = time
            else:
                retrace = 1.0 - (price / currentExtremePrice) if currentExtremePrice != 0 else 0
                if retrace >= thresholdPercent:
                    # Lock in High pivot (-1)
                    pivots.append({'time': currentExtremeTime, 'price': currentExtremePrice, 'type': -1})
                    directionUp = False; currentExtremePrice = price; currentExtremeTime = time
                    lastSign = -1
        else: # directionDown
            if price < currentExtremePrice:
                currentExtremePrice = price; currentExtremeTime = time
            else:
                rally = (price / currentExtremePrice) - 1.0 if currentExtremePrice != 0 else float('inf')
                if rally >= thresholdPercent:
                    # Lock in Low pivot (+1)
                    pivots.append({'time': currentExtremeTime, 'price': currentExtremePrice, 'type': 1})
                    directionUp = True; currentExtremePrice = price; currentExtremeTime = time
                    lastSign = 1

    # Ensure alternation if last pivot has same sign as the one before it
    if len(pivots) > 1 and pivots[-1]['type'] == pivots[-2]['type']:
         # Decide which one to keep based on price (keep the extreme)
         if pivots[-1]['type'] == 1: # Low pivots
             if pivots[-1]['price'] < pivots[-2]['price']: pivots.pop(-2)
             else: pivots.pop(-1)
         else: # High pivots
             if pivots[-1]['price'] > pivots[-2]['price']: pivots.pop(-2)
             else: pivots.pop(-1)

    # Add the last unconfirmed extreme as a potential pivot
    # Ensure it's different type from the last confirmed one
    if pivots and pivots[-1]['type'] != (-1 if directionUp else 1):
        pivots.append({'time': currentExtremeTime, 'price': currentExtremePrice, 'type': (-1 if directionUp else 1)})

    # Convert to list of tuples for compatibility if needed elsewhere, but dictionary list is fine
    # return [(p['time'], p['price'], p['type']) for p in pivots]
    return pivots # Return list of dictionaries

# --- Helper to get channel value at specific time ---
def get_channel_value_at_time_qc(channel_pivots, time_numeric):
    """ Gets channel value using get_line_params_time. channel_pivots is a tuple of two dicts. """
    if not channel_pivots or channel_pivots[0] is None or channel_pivots[1] is None:
        return float('nan')
    p1 = channel_pivots[0]; p2 = channel_pivots[1]
    if pd.isna(p1.get('time_numeric')) or pd.isna(p2.get('time_numeric')): return float('nan')
    m, c = get_line_params_time(p1['time_numeric'], p1['price'], p2['time_numeric'], p2['price'])
    if m == float('inf'): return float('nan')
    return m * time_numeric + c

#endregion
