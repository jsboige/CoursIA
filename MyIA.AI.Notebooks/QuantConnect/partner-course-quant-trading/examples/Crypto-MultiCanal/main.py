# main.py - Multi-Channel Strategy Algorithm
from AlgorithmImports import *
import numpy as np
import pandas as pd
import traceback
from datetime import datetime, timedelta, timezone
from channel_helpers import *
from channel_mixin import ChannelCalculationMixin

class MultiChannelStrategyAlgorithm(QCAlgorithm, ChannelCalculationMixin):

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
            'trade_level': 'meso', 'signal_type': 'both', 'trend_filter_level': 'macro',
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
                 # Default TP = 2x la distance du stop-loss
                 default_tp_distance = 2.0 * abs(current_price - stop_price)
                 if signal == 1:  # Long
                     target_price = current_price + default_tp_distance
                 else:  # Short
                     target_price = current_price - default_tp_distance
                 self.Debug(f"Warning: Using default TP at {target_price:.2f} (2x SL distance)")

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
