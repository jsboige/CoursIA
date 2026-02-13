#region Imports and Helper Functions
from AlgorithmImports import *
import numpy as np
import pandas as pd
import math
from datetime import datetime, timedelta, timezone 
import decimal # Pour une meilleure précision si nécessaire
import traceback

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

# --- Main Algorithm Class ---
class MultiChannelStrategyAlgorithm(QCAlgorithm):

    def Initialize(self):
        # Dates, Cash, Symbole, etc. (pas de changement ici)
        self.SetStartDate(2020, 8, 9) # AJUSTÉ à la date de début du backtest log
        self.SetEndDate(2025, 4, 1)   # Garder la fin ou ajuster si besoin
        self.SetCash(10000)
        self.btc = self.AddCrypto("BTCUSDT", Resolution.Hour, Market.Binance).Symbol
        self.SetBenchmark(self.btc)
        self.SetBrokerageModel(BrokerageName.Binance, AccountType.Cash)

        # --- Paramètres GA (pas de changement) ---
        self.strategy_name = "GA_Best_Meso_Breakout_NoTrendFilt"
        self.Log(f"Initializing strategy: {self.strategy_name}")
        self.strategy_params = {
            'trade_level': 'meso', 'signal_type': 'breakout', 'trend_filter_level': 'none',
            'risk_per_trade_pct': 0.0199, 'min_channel_width_pct': 0.0062,
            'bounce_sl_type': 'pct_entry', 'bounce_sl_value': 0.0105, 'bounce_tp_type': 'rr_ratio',
            'bounce_tp_value': 2.1194, 'bounce_entry_offset': 0.0015,
            'breakout_sl_type': 'pct_level', 'breakout_sl_value': 0.0120,
            'breakout_tp_type': 'rr_ratio', 'breakout_tp_value': 2.9670
        }
        self.Log(f"Strategy Parameters (from GA): {self.strategy_params}")

        # --- Paramètres Canaux (pas de changement, mais vérifier !) ---
        self.channel_params = {
            "wp_macro_res": 2.0, "rpf_macro_res": 1.0, "wp_macro_sup": 2.0, "rpf_macro_sup": 1.0,
            "wp_meso_res" : 2.0, "rpf_meso_res" : 1.0, "wp_meso_sup" : 2.0, "rpf_meso_sup" : 1.0,
            "wp_micro_res": 2.0, "rpf_micro_res": 1.0, "wp_micro_sup": 4.0, "rpf_micro_sup": 0.30
        }
        self.Log(f"Channel Calculation Parameters: {self.channel_params} <-- !! VERIFY !!")

        # --- Seuil ZigZag (pas de changement, mais vérifier !) ---
        self.zigzag_threshold = 0.05
        self.Log(f"ZigZag Threshold: {self.zigzag_threshold} <-- !! VERIFY !!")

        # --- General Parameters & Lookbacks ---
        # *** DÉFINITION DES LOOKBACKS ICI ***
        self.lookback_days_macro = 500
        self.lookback_days_meso = 150
        self.lookback_days_micro = 50

        self.general_params = {
            "recalc_schedule": "Daily",
            # L'ancien lookback_days_algo est remplacé par lookback_days_macro pour la requête History
            # "lookback_days_algo": self.lookback_days_macro # <- Redondant si on utilise directement self.lookback_days_macro
        }
        self.Log(f"General Parameters: {self.general_params}")
        self.Log(f"Lookbacks: Macro={self.lookback_days_macro}, Meso={self.lookback_days_meso}, Micro={self.lookback_days_micro}")

        # --- Internal State ---
        self.current_channels = {
            "macro": {"resistance": (None, None), "support": (None, None)},
            "meso": {"resistance": (None, None), "support": (None, None)},
            "micro": {"resistance": (None, None), "support": (None, None)}
        }
        self.pivots_df = pd.DataFrame(); self.high_pivots_df = pd.DataFrame(); self.low_pivots_df = pd.DataFrame()
        self.all_high_pivots_np = np.array([]); self.all_low_pivots_np = np.array([])
        self.trade_tickets = []
        # Conserver self.lookback_days basé sur Macro pour la requête History initiale et Warmup
        self.lookback_days = self.lookback_days_macro

        # --- Scheduling ---
        recalc_freq = self.general_params.get("recalc_schedule", "Daily")
        if recalc_freq == "Daily":
            self.Schedule.On(self.DateRules.EveryDay(self.btc), self.TimeRules.At(0, 5), self.ScheduledRecalculation)
        elif recalc_freq == "Weekly":
            self.Schedule.On(self.DateRules.Every(DayOfWeek.Monday), self.TimeRules.At(0, 5), self.ScheduledRecalculation)

        # Warmup basé sur le plus long lookback utilisé (Macro)
        warmup_period = TimeSpan.FromDays(self.lookback_days + 10) # Marge de sécurité
        self.SetWarmUp(warmup_period)
        self.Log(f"Setting Warmup Period: {warmup_period}")
        self.first_recalc_done = False

        self.Log("Initialization complete.")

    def OnWarmUpFinished(self):
         self.Debug("Warmup finished. Initial channel calculation...")
         self.RecalculateChannels()
         self.first_recalc_done = True
         self.Log(f"Initial channels calculated. Ready to trade strategy: {self.strategy_name}")

    def ScheduledRecalculation(self):
        # self.Debug(f"Scheduled recalculation triggered at {self.Time}")
        self.RecalculateChannels()

    def OnData(self, data):
        if self.IsWarmingUp or not self.first_recalc_done: return
        if not data.ContainsKey(self.btc) or data[self.btc] is None: return

        # 1. Check for Exits (Stop Loss / Take Profit hits handled by broker simulation via OnOrderEvent)
        # We might need CheckExits primarily to cancel orders if manual intervention/logic requires it
        self.CheckExitsManualConditions(data) # Renamed to avoid confusion with SL/TP hits

        # 2. Check for Entries if not invested
        if not self.Portfolio.Invested:
             # QC positions count includes closing positions, check Quantity
             position = self.Portfolio[self.btc]
             if position.Quantity == 0: # Check if truly flat
                self.RunEntryLogic(data)
             # else: self.Debug(f"Waiting for position {position.Quantity} to close before entry check.")

    def GetHistoryAndPivots(self):
        """Gets history by BAR COUNT based on MACRO lookback, calculates ZigZag pivots, and stores them. Includes detailed data logging."""
        try:
            # *** Utilise self.lookback_days_macro défini dans Initialize ***
            history_bars_request = self.lookback_days_macro * 24 + 240 # Lookback Macro + 10 jours de marge
            end_time_request = self.Time

            self.Debug(f"GetHistoryAndPivots: Requesting {history_bars_request} hourly bars ending {end_time_request}")

            # Appel History par nombre de barres
            history_df = self.History(self.btc, history_bars_request, Resolution.Hour)

            # --- Log Initial DataFrame Info ---
            if history_df.empty:
                self.Error("GetHistoryAndPivots: History request returned no data.")
                return False
            self.Debug(f"GetHistoryAndPivots: History received shape: {history_df.shape}. Expected ~{history_bars_request} rows. Index type: {type(history_df.index)}")
            try: # Log Index Head/Tail
                 self.Debug(f"GetHistoryAndPivots: History Index Head:\n{history_df.index[:5].to_list()}")
                 self.Debug(f"GetHistoryAndPivots: History Index Tail:\n{history_df.index[-5:].to_list()}")
            except Exception as e_idx: self.Debug(f"GetHistoryAndPivots: Could not log index head/tail: {e_idx}")

            # Unstack si MultiIndex
            if isinstance(history_df.index, pd.MultiIndex):
                try:
                    if self.btc not in history_df.index.get_level_values(0):
                         self.Error(f"GetHistoryAndPivots: Symbol {self.btc} not found in MultiIndex level 0.")
                         return False
                    history_df = history_df.loc[self.btc]
                    self.Debug(f"GetHistoryAndPivots: Unstacked history. New shape: {history_df.shape}. Index type: {type(history_df.index)}")
                    try: # Relog Index
                        self.Debug(f"GetHistoryAndPivots: Unstacked Index Head:\n{history_df.index[:5].to_list()}")
                        self.Debug(f"GetHistoryAndPivots: Unstacked Index Tail:\n{history_df.index[-5:].to_list()}")
                    except Exception as e_idx2: self.Debug(f"GetHistoryAndPivots: Could not log unstacked index head/tail: {e_idx2}")
                except KeyError:
                    self.Error(f"GetHistoryAndPivots: Symbol {self.btc} not found during unstacking attempt.")
                    return False

            # Vérifier colonnes prix
            if 'close' not in history_df.columns and 'price' not in history_df.columns:
                self.Error(f"GetHistoryAndPivots: History DataFrame missing 'close' or 'price' column. Columns available: {history_df.columns}")
                return False
            price_col = 'close' if 'close' in history_df.columns else 'price'
            self.Debug(f"GetHistoryAndPivots: Using column '{price_col}' for ZigZag calculation.")

            # Reset Index et vérifier colonne 'time'
            history_df = history_df.reset_index()
            self.Debug(f"GetHistoryAndPivots: DataFrame after reset_index. Columns: {history_df.columns}")
            if 'time' not in history_df.columns:
                if 'index' in history_df.columns:
                     history_df = history_df.rename(columns={'index':'time'})
                     self.Debug("GetHistoryAndPivots: Renamed column 'index' to 'time'.")
                else:
                    self.Error(f"GetHistoryAndPivots: History DataFrame has no 'time' or 'index' column after reset_index. Columns: {history_df.columns}")
                    return False

            # Gérer Timezone vers UTC
            try:
                history_df['time'] = pd.to_datetime(history_df['time'])
                if history_df['time'].dt.tz is None:
                    history_df['time'] = history_df['time'].dt.tz_localize('UTC')
                    self.Debug("GetHistoryAndPivots: Localized naive 'time' column to UTC.")
                else:
                    history_df['time'] = history_df['time'].dt.tz_convert('UTC')
                    self.Debug("GetHistoryAndPivots: Converted timezone-aware 'time' column to UTC.")
            except Exception as e_tz:
                 self.Error(f"GetHistoryAndPivots: Error processing 'time' column timezone: {e_tz}")
                 return False

            # Préparer et logger données pour ZigZag
            df_for_zigzag = history_df[['time', price_col]].copy().rename(columns={price_col:'close'})
            self.Debug(f"GetHistoryAndPivots: Dataframe shape going into ZigZag: {df_for_zigzag.shape}")
            if not df_for_zigzag.empty:
                try:
                    self.Debug(f"GetHistoryAndPivots: Data head for ZigZag:\n{df_for_zigzag.head(5).to_string()}")
                    self.Debug(f"GetHistoryAndPivots: Data tail for ZigZag:\n{df_for_zigzag.tail(5).to_string()}")
                except Exception as e_log_df: self.Debug(f"GetHistoryAndPivots: Could not log df head/tail: {e_log_df}")
            else: self.Debug("GetHistoryAndPivots: df_for_zigzag is empty before calling classic_chart_zigzag.")

            # Calculer les pivots
            self.Debug(f"GetHistoryAndPivots: Calculating ZigZag with threshold {self.zigzag_threshold}...")
            new_pivot_list = classic_chart_zigzag(df_for_zigzag, self.zigzag_threshold)

            # --- Suite : filtrage et stockage (pas de changement) ---
            if not new_pivot_list:
                self.Debug("GetHistoryAndPivots: No pivots generated by ZigZag for this period.")
                self.pivots_df=pd.DataFrame(); self.high_pivots_df=pd.DataFrame(); self.low_pivots_df=pd.DataFrame()
                self.all_high_pivots_np=np.array([]); self.all_low_pivots_np=np.array([])
                return False

            self.pivots_df = pd.DataFrame(new_pivot_list)
            if self.pivots_df.empty:
                self.Debug("GetHistoryAndPivots: Pivot list not empty, but DataFrame is empty.")
                return False

            self.Debug(f"GetHistoryAndPivots: ZigZag generated {len(self.pivots_df)} total pivots.")
            self.pivots_df['time'] = pd.to_datetime(self.pivots_df['time'])
            if self.pivots_df['time'].dt.tz is None:
                 self.pivots_df['time_numeric'] = self.pivots_df['time'].apply(lambda x: x.replace(tzinfo=timezone.utc).timestamp())
            else:
                 self.pivots_df['time_numeric'] = self.pivots_df['time'].dt.tz_convert(timezone.utc).apply(lambda x: x.timestamp())

            self.high_pivots_df = self.pivots_df[self.pivots_df['type'] == -1].copy()
            self.low_pivots_df = self.pivots_df[self.pivots_df['type'] == +1].copy()
            num_high = len(self.high_pivots_df); num_low = len(self.low_pivots_df)
            self.Debug(f"GetHistoryAndPivots: Filtered into {num_high} High pivots and {num_low} Low pivots.")

            if num_high < 2 or num_low < 2:
                self.Debug(f"GetHistoryAndPivots: Not enough high ({num_high}<2) or low ({num_low}<2) pivots found overall.")
                return False

            self.all_high_pivots_np = self.high_pivots_df[['time_numeric', 'price']].values
            self.all_low_pivots_np = self.low_pivots_df[['time_numeric', 'price']].values
            self.Debug(f"GetHistoryAndPivots: Prepared numpy arrays: all_high_pivots_np ({len(self.all_high_pivots_np)}), all_low_pivots_np ({len(self.all_low_pivots_np)})")
            return True

        except Exception as e:
            self.Error(f"GetHistoryAndPivots: CRITICAL Error: {traceback.format_exc()}")
            self.pivots_df=pd.DataFrame(); self.high_pivots_df=pd.DataFrame(); self.low_pivots_df=pd.DataFrame()
            self.all_high_pivots_np=np.array([]); self.all_low_pivots_np=np.array([])
            return False

    def RecalculateChannels(self):
        """Recalculates Macro, Meso, and Micro channels based on latest pivots."""
        self.Debug(f"--- RecalculateChannels starting @ {self.Time} ---")
        # Tenter de récupérer les pivots frais
        can_calculate = self.GetHistoryAndPivots()

        # Vider les canaux précédents avant de recalculer (ou si le calcul échoue)
        # Important pour éviter d'utiliser des canaux obsolètes si GetHistory échoue
        for scale in self.current_channels:
            self.current_channels[scale]["resistance"] = (None, None)
            self.current_channels[scale]["support"] = (None, None)

        # Si on n'a pas pu obtenir assez de pivots de base (min 2 high, 2 low), on arrête
        if not can_calculate:
            self.Debug("RecalculateChannels: Stopping early. Failed to get sufficient base pivots from history.")
            return # Pas la peine de continuer

        self.Debug("RecalculateChannels: Proceeding with channel calculations as base pivots seem sufficient.")

        # Helper pour stocker les infos de pivot (ne pas redéfinir si déjà globale/membre)
        def get_pivot_info_qc(pivot_series):
            if pivot_series is None or not isinstance(pivot_series, pd.Series): return None
            # Utilise .get() pour éviter KeyError si une colonne manque
            time_val = pivot_series.get('time')
            price_val = pivot_series.get('price')
            time_num_val = pivot_series.get('time_numeric')
            if time_val is None or price_val is None or time_num_val is None:
                self.Debug("get_pivot_info_qc: Warning - Pivot Series missing time, price, or time_numeric.")
                return None
            return {'time': time_val, 'price': float(price_val), 'time_numeric': float(time_num_val)}

        # --- Macro Calculation ---
        macro_success = False
        self.Debug("RecalculateChannels: Calculating Macro channels...")
        try:
            # Vérifier si les DFs et NPs ne sont pas vides (sécurité additionnelle)
            # Ces vérifications devraient être vraies si can_calculate est True, mais double-check
            if not self.high_pivots_df.empty and self.all_high_pivots_np.size > 0:
                 res1_m, res2_m = find_best_channel_line_strict_weighted(
                     self.high_pivots_df, self.all_high_pivots_np, True, # Check against ALL highs
                     self.channel_params['wp_macro_res'], self.channel_params['rpf_macro_res'])
                 self.current_channels["macro"]["resistance"] = (get_pivot_info_qc(res1_m), get_pivot_info_qc(res2_m))
                 self.Debug(f"RecalculateChannels: Macro Res result - P1 found={res1_m is not None}, P2 found={res2_m is not None}")
            else: self.Debug("RecalculateChannels: Skipping Macro Res calc - No high pivots available.")

            if not self.low_pivots_df.empty and self.all_low_pivots_np.size > 0:
                 sup1_m, sup2_m = find_best_channel_line_strict_weighted(
                     self.low_pivots_df, self.all_low_pivots_np, False, # Check against ALL lows
                     self.channel_params['wp_macro_sup'], self.channel_params['rpf_macro_sup'])
                 self.current_channels["macro"]["support"] = (get_pivot_info_qc(sup1_m), get_pivot_info_qc(sup2_m))
                 self.Debug(f"RecalculateChannels: Macro Sup result - P1 found={sup1_m is not None}, P2 found={sup2_m is not None}")
            else: self.Debug("RecalculateChannels: Skipping Macro Sup calc - No low pivots available.")

            # Vérifier si les DEUX pivots de chaque ligne ont été trouvés
            if self.current_channels["macro"]["resistance"][0] is not None and \
               self.current_channels["macro"]["resistance"][1] is not None and \
               self.current_channels["macro"]["support"][0] is not None and \
               self.current_channels["macro"]["support"][1] is not None:
                macro_success = True
                self.Debug("RecalculateChannels: Macro channels successfully calculated (both Sup & Res lines complete).")
            else:
                self.Debug("RecalculateChannels: Macro channel calculation incomplete (Sup or Res line missing at least one pivot).")

        except Exception as e:
            self.Error(f"RecalculateChannels: Macro Recalc Error: {traceback.format_exc()}")
            macro_success = False # Assurer que l'échec est propagé

        # --- Meso Calculation ---
        meso_success = False
        if macro_success:
            self.Debug("RecalculateChannels: Calculating Meso channels...")
            meso_start_time = None
            # Utiliser les pivots *réellement trouvés* pour Macro
            macro_pivots_list = [p for pair in self.current_channels["macro"].values() for p in pair if p is not None]

            if len(macro_pivots_list) >= 2:
                macro_pivots_list.sort(key=lambda p: p['time'], reverse=True)
                meso_start_time = macro_pivots_list[1]['time'] # Utiliser 2ème plus récent pivot MACRO
                self.Debug(f"RecalculateChannels: Determined Meso start time: {meso_start_time}")

                if meso_start_time is not None:
                    try:
                        # Filtrer pivots APRÈS start time
                        meso_high_f = self.high_pivots_df[self.high_pivots_df['time'] >= meso_start_time].copy()
                        meso_low_f = self.low_pivots_df[self.low_pivots_df['time'] >= meso_start_time].copy()
                        num_meso_high = len(meso_high_f)
                        num_meso_low = len(meso_low_f)
                        self.Debug(f"RecalculateChannels: Pivots available for Meso (after {meso_start_time}): High={num_meso_high}, Low={num_meso_low}")

                        # Vérifier s'il y a assez de pivots DANS CETTE FENÊTRE MESO
                        if num_meso_high >= 2 and num_meso_low >= 2:
                            # Préparer les NPs pour la vérification - IMPORTANT: utiliser TOUS les pivots pour la vérification de non-croisement
                            # meso_high_np = meso_high_f[['time_numeric', 'price']].values # Pourrait être utilisé si on voulait vérifier uniquement DANS la fenêtre meso
                            # meso_low_np = meso_low_f[['time_numeric', 'price']].values

                            # Tenter de trouver les lignes Meso
                            res1_me, res2_me = find_best_channel_line_strict_weighted(
                                meso_high_f, self.all_high_pivots_np, True, # Check against ALL highs
                                self.channel_params['wp_meso_res'], self.channel_params['rpf_meso_res'])
                            self.current_channels["meso"]["resistance"] = (get_pivot_info_qc(res1_me), get_pivot_info_qc(res2_me))
                            self.Debug(f"RecalculateChannels: Meso Res result - P1 found={res1_me is not None}, P2 found={res2_me is not None}")

                            sup1_me, sup2_me = find_best_channel_line_strict_weighted(
                                meso_low_f, self.all_low_pivots_np, False, # Check against ALL lows
                                self.channel_params['wp_meso_sup'], self.channel_params['rpf_meso_sup'])
                            self.current_channels["meso"]["support"] = (get_pivot_info_qc(sup1_me), get_pivot_info_qc(sup2_me))
                            self.Debug(f"RecalculateChannels: Meso Sup result - P1 found={sup1_me is not None}, P2 found={sup2_me is not None}")

                            # Vérifier si les DEUX pivots de chaque ligne Meso ont été trouvés
                            if self.current_channels["meso"]["resistance"][0] is not None and \
                               self.current_channels["meso"]["resistance"][1] is not None and \
                               self.current_channels["meso"]["support"][0] is not None and \
                               self.current_channels["meso"]["support"][1] is not None:
                                meso_success = True
                                self.Debug("RecalculateChannels: Meso channels successfully calculated (both Sup & Res lines complete).")
                            else:
                                self.Debug("RecalculateChannels: Meso channel calculation incomplete (Sup or Res line missing at least one pivot).")
                        else:
                            self.Debug(f"RecalculateChannels: Not enough pivots for Meso calc (High<2 or Low<2) after {meso_start_time}")
                    except Exception as e:
                         self.Error(f"RecalculateChannels: Meso Recalc Error: {traceback.format_exc()}")
                         meso_success = False
                else: # meso_start_time was None
                    self.Debug("RecalculateChannels: Could not determine Meso start time (was None).")
            else: # len(macro_pivots_list) < 2
                 self.Debug("RecalculateChannels: Cannot determine Meso start time - Less than 2 valid Macro pivots found.")
        else:
            self.Debug("RecalculateChannels: Meso calculation skipped - Macro failed or incomplete.")

        # --- Micro Calculation ---
        if meso_success:
            self.Debug("RecalculateChannels: Calculating Micro channels...")
            micro_start_time = None
            meso_pivots_list = [p for pair in self.current_channels["meso"].values() for p in pair if p is not None]
            if len(meso_pivots_list) >= 2:
                meso_pivots_list.sort(key=lambda p: p['time'], reverse=True)
                micro_start_time = meso_pivots_list[1]['time'] # Utiliser 2ème plus récent pivot MESO
                self.Debug(f"RecalculateChannels: Determined Micro start time: {micro_start_time}")

                if micro_start_time is not None:
                    try:
                        micro_high_f = self.high_pivots_df[self.high_pivots_df['time'] >= micro_start_time].copy()
                        micro_low_f = self.low_pivots_df[self.low_pivots_df['time'] >= micro_start_time].copy()
                        num_micro_high = len(micro_high_f)
                        num_micro_low = len(micro_low_f)
                        self.Debug(f"RecalculateChannels: Pivots available for Micro (after {micro_start_time}): High={num_micro_high}, Low={num_micro_low}")

                        # Vérifier s'il y a assez de pivots DANS CETTE FENÊTRE MICRO
                        if num_micro_high >= 2 and num_micro_low >= 2:
                            # Encore une fois, vérifier contre TOUS les pivots par défaut
                            res1_mi, res2_mi = find_best_channel_line_strict_weighted(
                                micro_high_f, self.all_high_pivots_np, True, # Check against ALL highs
                                self.channel_params['wp_micro_res'], self.channel_params['rpf_micro_res'])
                            self.current_channels["micro"]["resistance"] = (get_pivot_info_qc(res1_mi), get_pivot_info_qc(res2_mi))
                            self.Debug(f"RecalculateChannels: Micro Res result - P1 found={res1_mi is not None}, P2 found={res2_mi is not None}")

                            sup1_mi, sup2_mi = find_best_channel_line_strict_weighted(
                                micro_low_f, self.all_low_pivots_np, False, # Check against ALL lows
                                self.channel_params['wp_micro_sup'], self.channel_params['rpf_micro_sup'])
                            self.current_channels["micro"]["support"] = (get_pivot_info_qc(sup1_mi), get_pivot_info_qc(sup2_mi))
                            self.Debug(f"RecalculateChannels: Micro Sup result - P1 found={sup1_mi is not None}, P2 found={sup2_mi is not None}")

                            # Vérifier si les DEUX pivots de chaque ligne Micro ont été trouvés
                            if self.current_channels["micro"]["resistance"][0] is not None and \
                               self.current_channels["micro"]["resistance"][1] is not None and \
                               self.current_channels["micro"]["support"][0] is not None and \
                               self.current_channels["micro"]["support"][1] is not None:
                                # micro_success = True # Pas nécessaire de suivre
                                self.Debug("RecalculateChannels: Micro channels successfully calculated (both Sup & Res lines complete).")
                                pass # Success
                            else:
                                self.Debug("RecalculateChannels: Micro channel calculation incomplete (Sup or Res line missing at least one pivot).")
                        else:
                             self.Debug(f"RecalculateChannels: Not enough pivots for Micro calc (High<2 or Low<2) after {micro_start_time}")
                    except Exception as e:
                        self.Error(f"RecalculateChannels: Micro Recalc Error: {traceback.format_exc()}")
                        # Pas besoin de changer meso_success ici
                else: # micro_start_time was None
                    self.Debug("RecalculateChannels: Could not determine Micro start time (was None).")
            else: # len(meso_pivots_list) < 2
                self.Debug("RecalculateChannels: Cannot determine Micro start time - Less than 2 valid Meso pivots found.")
        else:
            self.Debug("RecalculateChannels: Micro calculation skipped - Meso failed or incomplete.")

        self.Debug(f"--- End RecalculateChannels @ {self.Time} ---")
        # Optionnel: Plot channels
        # self.PlotChannels()
    

    def CheckTrend(self, level):
        """Checks the trend direction based on channel slopes. Returns 'up', 'down', or 'flat'."""
        channel = self.current_channels.get(level)
        if not channel: return 'flat'
        res_pivots = channel.get("resistance", (None, None))
        sup_pivots = channel.get("support", (None, None))
        if res_pivots[0] is None or sup_pivots[0] is None: return 'flat'

        try:
            m_res, _ = get_line_params_time(res_pivots[0]['time_numeric'], res_pivots[0]['price'], res_pivots[1]['time_numeric'], res_pivots[1]['price'])
            m_sup, _ = get_line_params_time(sup_pivots[0]['time_numeric'], sup_pivots[0]['price'], sup_pivots[1]['time_numeric'], sup_pivots[1]['price'])
            if m_res == float('inf') or m_sup == float('inf'): return 'flat'

            tolerance = 1e-9 # Adjust as needed
            if m_res >= -tolerance and m_sup >= -tolerance: return 'up'
            if m_res <= tolerance and m_sup <= tolerance: return 'down'
            return 'flat' # Mixed slopes or flat
        except Exception:
            return 'flat'

    def RunEntryLogic(self, data):
        """Implements the entry logic for the SINGLE selected strategy."""
        current_price = data[self.btc].Close
        current_time_num = self.Time.timestamp()

        # --- Get Parameters for the Chosen Strategy ---
        trade_level = self.strategy_params['trade_level']
        signal_type = self.strategy_params['signal_type']
        trend_filter = self.strategy_params['trend_filter_level']
        min_width_pct = self.strategy_params.get('min_channel_width_pct', 0.01)
        bounce_offset = self.strategy_params.get('bounce_entry_offset', 0.0015) # Use default if missing

        # --- Check Trend Filter (if applicable) ---
        trend_ok_long = True
        trend_ok_short = True
        if trend_filter != 'none':
            current_filter_trend = self.CheckTrend(trend_filter)
            if current_filter_trend == 'down': trend_ok_long = False
            if current_filter_trend == 'up': trend_ok_short = False
            if current_filter_trend == 'flat': # Decide how to handle flat trend filter
                 trend_ok_long = False # Example: Don't trade if filter is flat
                 trend_ok_short = False

        # --- Check Signals on the Trade Level ---
        res_pivots = self.current_channels.get(trade_level, {}).get("resistance", (None, None))
        sup_pivots = self.current_channels.get(trade_level, {}).get("support", (None, None))
        if res_pivots[0] is None or sup_pivots[0] is None:
            # self.Debug(f"Skipping entry check: {trade_level} channels not available.")
            return # Cannot trade without the primary channels

        current_res_val = get_channel_value_at_time_qc(res_pivots, current_time_num)
        current_sup_val = get_channel_value_at_time_qc(sup_pivots, current_time_num)

        if pd.isna(current_res_val) or pd.isna(current_sup_val):
             # self.Debug(f"Skipping entry check: Cannot calculate {trade_level} channel values.")
             return

        # --- Evaluate Potential Trades ---
        signal = 0 # 1 for long, -1 for short

        # 1. Check Bounce Signals (if strategy allows)
        if signal == 0 and signal_type in ['bounce', 'both']:
             channel_width = current_res_val - current_sup_val
             if channel_width >= current_price * min_width_pct: # Check width only for bounce
                 # Check Long Bounce
                 if trend_ok_long and current_price <= current_sup_val * (1 + bounce_offset):
                     signal = 1
                     sl_type = self.strategy_params['bounce_sl_type']
                     sl_value = self.strategy_params['bounce_sl_value']
                     tp_value = self.strategy_params['bounce_tp_value']
                     tag = f"Bounce {trade_level} Sup / Trend: {trend_filter}"
                     # self.Debug(f"{self.Time} - Potential LONG: {tag}")

                 # Check Short Bounce
                 elif trend_ok_short and current_price >= current_res_val * (1 - bounce_offset):
                     signal = -1
                     sl_type = self.strategy_params['bounce_sl_type']
                     sl_value = self.strategy_params['bounce_sl_value']
                     tp_value = self.strategy_params['bounce_tp_value']
                     tag = f"Bounce {trade_level} Res / Trend: {trend_filter}"
                     # self.Debug(f"{self.Time} - Potential SHORT: {tag}")

        # 2. Check Breakout Signals (if strategy allows and no bounce signal found)
        if signal == 0 and signal_type in ['breakout', 'both']:
            # Check Long Breakout
            if trend_ok_long and current_price > current_res_val: # Simple check: price closed above resistance
                 signal = 1
                 sl_type = self.strategy_params['breakout_sl_type']
                 sl_value = self.strategy_params['breakout_sl_value']
                 tp_value = self.strategy_params['breakout_tp_value']
                 tag = f"Breakout {trade_level} Res / Trend: {trend_filter}"
                 # self.Debug(f"{self.Time} - Potential LONG: {tag}")

            # Check Short Breakout
            elif trend_ok_short and current_price < current_sup_val: # Simple check: price closed below support
                 signal = -1
                 sl_type = self.strategy_params['breakout_sl_type']
                 sl_value = self.strategy_params['breakout_sl_value']
                 tp_value = self.strategy_params['breakout_tp_value']
                 tag = f"Breakout {trade_level} Sup / Trend: {trend_filter}"
                 # self.Debug(f"{self.Time} - Potential SHORT: {tag}")

        # --- Place Trade if Signal Found ---
        if signal != 0:
            # Calculate SL
            stop_price = None
            if sl_type == 'pct_entry':
                stop_price = current_price * (1 - signal * sl_value)
            elif sl_type == 'pct_level':
                level_val = current_res_val if signal == 1 else current_sup_val # Level broken/bounced from
                if not pd.isna(level_val):
                     stop_price = level_val * (1 - signal * sl_value) # Place SL beyond the level
                else: # Fallback if level value failed
                     stop_price = current_price * (1 - signal * sl_value * 1.5) # Wider fallback
                     self.Debug(f"Warning: Using fallback SL for {tag} due to invalid level value.")
            else: # Fallback default
                stop_price = current_price * (1 - signal * 0.01) # Default 1% SL

            # Calculate TP (RR Ratio based)
            target_price = None
            if stop_price is not None:
                risk_per_unit = abs(current_price - stop_price)
                if risk_per_unit > 1e-9:
                     target_price = current_price + signal * risk_per_unit * tp_value

            # Ensure TP is defined (can be None if RR logic fails)
            if target_price is None:
                 self.Debug(f"Warning: Could not calculate TP for {tag}. Trade might not have TP.")
                 # Decide: skip trade or place without TP? Let's place without TP for now.
                 # target_price = # Set a very distant default or handle differently

            # Place the actual trade
            if stop_price is not None: # Required for sizing and basic safety
                self.PlaceTrade(signal, stop_price, target_price, tag)
            else:
                 self.Error(f"Skipping trade {tag}: Could not calculate valid Stop Loss.")


    def PlaceTrade(self, direction, stop_price, target_price, tag):
        """Calculates size and places Market order with associated SL/TP orders."""
        risk_pct = self.strategy_params.get("risk_per_trade_pct", 0.01)
        available_capital = self.Portfolio.TotalPortfolioValue # Use total equity for sizing

        current_price = self.Securities[self.btc].Price
        if current_price <= 0:
             self.Error(f"Skipping trade {tag}: Current price is zero or invalid.")
             return
        if stop_price is None or pd.isna(stop_price):
             self.Error(f"Skipping trade {tag}: Invalid stop_price: {stop_price}")
             return

        # Ensure stop makes sense (e.g., below entry for long)
        if direction == 1 and stop_price >= current_price:
             self.Error(f"Skipping LONG trade {tag}: Stop Price {stop_price:.2f} is not below Entry Price {current_price:.2f}")
             return
        if direction == -1 and stop_price <= current_price:
              self.Error(f"Skipping SHORT trade {tag}: Stop Price {stop_price:.2f} is not above Entry Price {current_price:.2f}")
              return

        risk_per_unit = abs(current_price - stop_price)
        # Use a small minimum risk (e.g., 0.05% of price) to prevent division by zero if stop is extremely close
        min_risk_value = current_price * 0.0005
        if risk_per_unit < min_risk_value:
             self.Debug(f"Risk per unit ({risk_per_unit:.4f}) too small for {tag}. Adjusting SL slightly or using min risk value.")
             risk_per_unit = min_risk_value
             # Adjust stop price based on min risk, keeping directionality
             stop_price = current_price - direction * min_risk_value


        cash_to_risk = available_capital * risk_pct
        position_size = cash_to_risk / risk_per_unit

        # Calculate quantity based on position value
        position_value = position_size * current_price
        target_weight = (position_value / available_capital) if available_capital > 0 else 0
        target_weight = min(max(target_weight, -1.0), 1.0)  # Clamp to [-1, 1]
        quantity = self.CalculateOrderQuantity(self.btc, direction * target_weight)

        if quantity == 0:
            self.Log(f"Skipping trade {tag}: Calculated quantity is zero (Position Size: {position_size:.8f}, Price: {current_price:.2f}, Risk/Unit: {risk_per_unit:.4f}, Available Cap: {available_capital:.2f})")
            return

        # --- Place Orders ---
        self.LiquidateAndCancelOrders(f"New entry {tag}") # Ensure clean state

        self.Debug(f"Placing Trade: {tag} | Qty: {quantity} | Entry: ~{current_price:.2f} | SL: {stop_price:.2f} | TP: {target_price:.2f if target_price else 'None'}")

        market_ticket = self.MarketOrder(self.btc, quantity, tag=f"{tag} Entry")

        # Place SL and TP only AFTER confirming market order submission/fill
        # Use OnOrderEvent to manage this robustly. Store intended SL/TP with entry ticket info.
        if market_ticket.Status != OrderStatus.Invalid:
            # Store intended SL/TP levels associated with this entry order ID
             self.trade_tickets.append({
                 "entry_id": market_ticket.OrderId,
                 "intended_sl": stop_price,
                 "intended_tp": target_price,
                 "tag": tag,
                 "stop_id": None, # Will be set in OnOrderEvent
                 "limit_id": None, # Will be set in OnOrderEvent
                 "active": True # Flag to indicate OCO orders need placing/managing
             })
        else:
             self.Error(f"Market order {tag} failed immediately: {market_ticket.Status}")


    def CheckExitsManualConditions(self, data):
        """Placeholder for manual exit conditions NOT based on SL/TP hits
           (e.g., time-based exit, channel invalidation)."""
        # Example: If a channel used for entry becomes invalid (pivots change drastically)
        # if self.Portfolio.Invested:
        #     # Add logic here if needed
        #     pass
        pass

    def LiquidateAndCancelOrders(self, reason=""):
        """Liquidates the BTC position and cancels all open orders for BTC."""
        # Cancel pending orders first
        open_orders = self.Transactions.GetOpenOrderTickets(lambda ticket: ticket.Symbol == self.btc)
        cancelled_ids = []
        for ticket in open_orders:
            cancelled_ids.append(ticket.OrderId)
            ticket.Cancel(f"{reason}")

        # Liquidate position if held
        position = self.Portfolio[self.btc]
        if position.Invested:
            self.Liquidate(self.btc, f"{reason}")

        # Mark any tracked tickets associated with cancelled orders as inactive
        for group in self.trade_tickets:
             if (group["stop_id"] in cancelled_ids) or (group["limit_id"] in cancelled_ids) or (group["entry_id"] in cancelled_ids) :
                  group["active"] = False
        # Clean up inactive tickets
        self.trade_tickets = [group for group in self.trade_tickets if group["active"]]


    def OnOrderEvent(self, orderEvent):
         self.Log(f"{self.Time} ORDER EVENT: {orderEvent}")
         order = self.Transactions.GetOrderById(orderEvent.OrderId)
         if order is None: return # Should not happen

         tag = order.Tag
         order_id = orderEvent.OrderId

         # --- Handling Entry Order Fill ---
         if "Entry" in tag and orderEvent.Status == OrderStatus.Filled:
             for group in self.trade_tickets:
                 # Find the corresponding entry group that needs SL/TP placed
                 if group["entry_id"] == order_id and group["active"] and group["stop_id"] is None:
                     entry_qty = order.Quantity # Get the actual filled quantity
                     intended_sl = group["intended_sl"]
                     intended_tp = group["intended_tp"]

                     # Place Stop Loss order
                     if intended_sl is not None:
                          sl_ticket = self.StopMarketOrder(self.btc, -entry_qty, intended_sl, tag=f"{group['tag']} SL")
                          group["stop_id"] = sl_ticket.OrderId
                          self.Debug(f"Placed SL Order {sl_ticket.OrderId} for Entry {order_id}")

                     # Place Take Profit order
                     if intended_tp is not None:
                          # Ensure TP price is valid relative to SL and current market
                          # (Add checks if needed, e.g., TP not too close to entry)
                          tp_ticket = self.LimitOrder(self.btc, -entry_qty, intended_tp, tag=f"{group['tag']} TP")
                          group["limit_id"] = tp_ticket.OrderId
                          self.Debug(f"Placed TP Order {tp_ticket.OrderId} for Entry {order_id}")

                     if group["stop_id"] is None and group["limit_id"] is None:
                          self.Error(f"Failed to place SL and TP for filled entry {order_id}!")
                          group["active"] = False # Mark as failed/inactive

                     break # Found and processed the entry group

         # --- Handling OCO Logic for SL/TP ---
         for i in range(len(self.trade_tickets) - 1, -1, -1):
             group = self.trade_tickets[i]
             if not group["active"]: continue # Skip inactive groups

             stop_id = group.get('stop_id')
             limit_id = group.get('limit_id')

             # Check if the current event matches one of the SL/TP orders in this group
             is_stop_event = (stop_id is not None and order_id == stop_id)
             is_limit_event = (limit_id is not None and order_id == limit_id)

             if is_stop_event or is_limit_event:
                 # If either SL or TP is Filled or Cancelled, cancel the other one
                 if orderEvent.Status == OrderStatus.Filled or orderEvent.Status == OrderStatus.Cancelled:
                     other_ticket_id = limit_id if is_stop_event else stop_id
                     if other_ticket_id is not None:
                          other_ticket = self.Transactions.GetOrderTicket(other_ticket_id)
                          # Check if the other ticket exists and is still open before cancelling
                          if other_ticket is not None and not other_ticket.Status.IsClosed():
                               reason = f"SL filled ({order_id})" if is_stop_event and orderEvent.Status == OrderStatus.Filled else \
                                        f"TP filled ({order_id})" if is_limit_event and orderEvent.Status == OrderStatus.Filled else \
                                        f"Sibling order closed ({order_id})"
                               other_ticket.Cancel(reason)
                               self.Debug(f"OCO triggered: Cancelled order {other_ticket_id} due to {reason}")

                     group["active"] = False # Mark this group as inactive (trade is closed or failed)

         # Clean up inactive groups from the tracking list
         self.trade_tickets = [group for group in self.trade_tickets if group["active"]]


    def PlotChannels(self):
        """Plots current channel levels for visual debugging."""
        current_time_num = self.Time.timestamp()
        for scale in ["macro", "meso", "micro"]:
            channel = self.current_channels.get(scale, {})
            res_val = get_channel_value_at_time_qc(channel.get("resistance", (None, None)), current_time_num)
            sup_val = get_channel_value_at_time_qc(channel.get("support", (None, None)), current_time_num)
            if not pd.isna(res_val):
                self.Plot(f"Channels", f"{scale}_res", res_val)
            if not pd.isna(sup_val):
                self.Plot(f"Channels", f"{scale}_sup", sup_val)
    #     pass
