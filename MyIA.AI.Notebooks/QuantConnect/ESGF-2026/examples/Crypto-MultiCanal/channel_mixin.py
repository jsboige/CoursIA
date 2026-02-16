# channel_mixin.py - Channel calculation methods (mixin)
from AlgorithmImports import *
import numpy as np
import pandas as pd
import traceback
from datetime import timezone
from channel_helpers import *

class ChannelCalculationMixin:
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

