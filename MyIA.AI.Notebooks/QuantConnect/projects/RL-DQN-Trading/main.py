#region imports
from AlgorithmImports import *
import numpy as np
from collections import deque
import random
from sklearn.neural_network import MLPRegressor
from sklearn.preprocessing import StandardScaler
from sklearn.pipeline import Pipeline
import copy
# endregion


class ReinforcementLearningTrading(QCAlgorithm):
    """
    Reinforcement Learning for Trading - v2.0.1 Improved DQN.

    Improvements over v1.0 (linear Q-function, SPY only):
    - MLPRegressor(64,32) instead of linear Q-function
    - 11 features: multi-scale momentum, RSI, Bollinger, vol regime, trend,
      flight-to-safety (TLT spread), GLD momentum, tech spread, action memory
    - Risk-adjusted reward: r - 0.5*r^2 (penalizes large losses asymmetrically)
    - Transaction cost penalty to reduce turnover
    - Multi-asset: SPY, QQQ, IWM, TLT, GLD (5 ETFs, portfolio-level allocation)
    - Actions: AGGRESSIVE (80% equities), MODERATE (50% equities), DEFENSIVE (20% equities)
    - Larger replay buffer (5000), batch training weekly
    - Epsilon decay from 0.5 to 0.05 over first 2 years (504 trading days)
    - Period: 2015-2026, Weekly rebalance

    Bug fix v2.0.1: target network only used after first monthly update.
    Separate _target_initialized flag prevents NotFittedError.

    Reference: Hands-On AI Trading with Python, QuantConnect, and AWS
    Chapter 07 - Better Hedging with Reinforcement Learning
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2026, 1, 1)
        self.set_cash(100_000)

        # Multi-asset universe
        self._symbols = {}
        for ticker in ["SPY", "QQQ", "IWM", "TLT", "GLD"]:
            self._symbols[ticker] = self.add_equity(ticker, Resolution.DAILY).symbol

        # RL hyperparameters
        self._gamma = 0.95
        self._learning_rate = 0.001
        self._epsilon = 0.5
        self._epsilon_min = 0.05
        # Decay over ~504 days (2 years of trading): 0.5 * decay^504 = 0.05 -> decay ~ 0.9978
        self._epsilon_decay = 0.9978

        # Action space: 3 portfolio allocations
        # 0 = AGGRESSIVE: 50% SPY, 20% QQQ, 10% IWM, 10% TLT, 10% GLD
        # 1 = MODERATE:   30% SPY, 15% QQQ, 5% IWM,  25% TLT, 25% GLD
        # 2 = DEFENSIVE:  10% SPY, 5%  QQQ, 0% IWM,  45% TLT, 40% GLD
        self._allocations = [
            {"SPY": 0.50, "QQQ": 0.20, "IWM": 0.10, "TLT": 0.10, "GLD": 0.10},
            {"SPY": 0.30, "QQQ": 0.15, "IWM": 0.05, "TLT": 0.25, "GLD": 0.25},
            {"SPY": 0.10, "QQQ": 0.05, "IWM": 0.00, "TLT": 0.45, "GLD": 0.40},
        ]
        self._action_names = ["AGGRESSIVE", "MODERATE", "DEFENSIVE"]
        self._n_actions = len(self._allocations)
        self._state_dim = 11  # 10 market features + 1 current action

        # Indicators per symbol for state features
        self._indicators = {}
        for ticker in ["SPY", "QQQ", "IWM", "TLT", "GLD"]:
            sym = self._symbols[ticker]
            self._indicators[ticker] = {
                "roc1":  self.roc(sym, 1,  Resolution.DAILY),
                "roc5":  self.roc(sym, 5,  Resolution.DAILY),
                "roc10": self.roc(sym, 10, Resolution.DAILY),
                "roc20": self.roc(sym, 20, Resolution.DAILY),
                "std20": self.std(sym, 20, Resolution.DAILY),
                "std60": self.std(sym, 60, Resolution.DAILY),
                "sma50": self.sma(sym, 50, Resolution.DAILY),
                "bb":    self.bb(sym, 20, 2),
            }

        # RSI for SPY (main signal)
        self._rsi_spy = self.rsi(self._symbols["SPY"], 14)

        # Warm up
        self.set_warm_up(timedelta(days=120))

        # Experience replay buffer
        self._replay_buffer = deque(maxlen=5000)

        # Q-network: MLPRegressor with 2 hidden layers (state-action -> Q-value)
        self._q_network = Pipeline([
            ("scaler", StandardScaler()),
            ("mlp", MLPRegressor(
                hidden_layer_sizes=(64, 32),
                activation="relu",
                learning_rate_init=self._learning_rate,
                max_iter=20,
                warm_start=True,
                random_state=42
            ))
        ])
        # Target network: None until first monthly copy from Q-network
        self._target_network = None
        self._network_initialized = False   # True after first fit()
        self._target_initialized = False    # True after first _update_target_network()
        self._train_count = 0

        # State tracking
        self._previous_state = None
        self._previous_action = 1  # Start MODERATE
        self._current_action = 1   # Start MODERATE
        self._total_reward = 0.0
        self._day_count = 0

        # Schedule weekly rebalance (Monday)
        self.schedule.on(
            self.date_rules.every(DayOfWeek.MONDAY),
            self.time_rules.after_market_open("SPY", 30),
            self._rebalance
        )

        # Schedule weekly training (Friday)
        self.schedule.on(
            self.date_rules.every(DayOfWeek.FRIDAY),
            self.time_rules.after_market_open("SPY", 60),
            self._train
        )

        # Update target network monthly
        self.schedule.on(
            self.date_rules.month_start("SPY"),
            self.time_rules.after_market_open("SPY", 90),
            self._update_target_network
        )

        self.log(f"RL-DQN v2.0.1 initialized: epsilon={self._epsilon}, "
                 f"state_dim={self._state_dim}, n_actions={self._n_actions}")

    def _safe_get(self, indicator, fallback=0.0):
        """Safe indicator value retrieval."""
        try:
            v = indicator.current.value
            if np.isnan(v) or np.isinf(v):
                return fallback
            return float(v)
        except Exception:
            return fallback

    def _get_spy_features(self):
        """Extract 11 market features from multi-asset indicators."""
        ind = self._indicators["SPY"]

        # 1-3. Multi-scale momentum (normalized)
        roc1  = float(np.clip(self._safe_get(ind["roc1"])  / 1.5, -3, 3))
        roc5  = float(np.clip(self._safe_get(ind["roc5"])  / 4.0, -3, 3))
        roc20 = float(np.clip(self._safe_get(ind["roc20"]) / 8.0, -3, 3))

        # 4. RSI normalized to [-1, 1]
        rsi = (self._safe_get(self._rsi_spy, 50.0) - 50.0) / 50.0

        # 5. Bollinger Band position
        bb = ind["bb"]
        try:
            upper = self._safe_get(bb.upper_band)
            lower = self._safe_get(bb.lower_band)
            mid   = self._safe_get(bb.middle_band)
            spy_price = float(self.securities[self._symbols["SPY"]].price)
            band_width = upper - lower
            if band_width > 0:
                bb_pos = float(np.clip((spy_price - mid) / (band_width / 2), -1.5, 1.5))
            else:
                bb_pos = 0.0
        except Exception:
            bb_pos = 0.0

        # 6. Volatility regime: 20d vol / 60d vol (>1 = high vol regime)
        std20 = self._safe_get(ind["std20"], 1.0)
        std60 = self._safe_get(ind["std60"], 1.0)
        vol_regime = float(np.clip(std20 / std60 - 1.0, -1.0, 2.0)) if std60 > 0 else 0.0

        # 7. Trend strength: price vs SMA50
        sma50 = self._safe_get(ind["sma50"])
        spy_price = float(self.securities[self._symbols["SPY"]].price)
        trend = float(np.clip((spy_price / sma50 - 1.0) * 10, -2.0, 2.0)) if sma50 > 0 else 0.0

        # 8. TLT vs SPY momentum spread (flight-to-safety signal)
        tlt_roc20 = self._safe_get(self._indicators["TLT"]["roc20"]) / 8.0
        spy_tlt_spread = float(np.clip(roc20 - tlt_roc20, -3, 3))

        # 9. GLD momentum (inflation/uncertainty signal)
        gld_roc20 = float(np.clip(self._safe_get(self._indicators["GLD"]["roc20"]) / 8.0, -3, 3))

        # 10. QQQ vs SPY relative momentum (tech sentiment)
        qqq_roc20 = self._safe_get(self._indicators["QQQ"]["roc20"]) / 8.0
        tech_spread = float(np.clip(qqq_roc20 - roc20, -2, 2))

        # 11. Current action (portfolio regime memory) [-0.5, 0.5]
        action_feature = float(self._current_action) / (self._n_actions - 1) - 0.5

        state = np.array([
            roc1, roc5, roc20,
            rsi,
            bb_pos,
            vol_regime,
            trend,
            spy_tlt_spread,
            gld_roc20,
            tech_spread,
            action_feature
        ], dtype=np.float32)

        return state

    def _indicators_ready(self):
        """Check that all required indicators are ready."""
        if not self._rsi_spy.is_ready:
            return False
        for ticker in ["SPY", "QQQ", "IWM", "TLT", "GLD"]:
            ind = self._indicators[ticker]
            if not (ind["roc20"].is_ready and ind["std20"].is_ready
                    and ind["std60"].is_ready and ind["sma50"].is_ready
                    and ind["bb"].is_ready):
                return False
        return True

    def _predict_q(self, network, state_a):
        """Safe single Q-value prediction."""
        try:
            return float(network.predict(state_a.reshape(1, -1))[0])
        except Exception:
            return 0.0

    def _get_q_values(self, state):
        """Get Q-values for all actions given current state (uses Q-network)."""
        if not self._network_initialized:
            return np.zeros(self._n_actions)
        q_vals = []
        for a in range(self._n_actions):
            action_enc = float(a) / (self._n_actions - 1) - 0.5
            state_a = np.append(state[:-1], action_enc).astype(np.float32)
            q_vals.append(self._predict_q(self._q_network, state_a))
        return np.array(q_vals)

    def _get_target_q(self, state_next):
        """Get max Q-value of next state.
        Uses target network when available, Q-network otherwise.
        """
        network = self._target_network if self._target_initialized else self._q_network
        q_vals = []
        for a in range(self._n_actions):
            action_enc = float(a) / (self._n_actions - 1) - 0.5
            state_a = np.append(state_next[:-1], action_enc).astype(np.float32)
            q_vals.append(self._predict_q(network, state_a))
        return max(q_vals) if q_vals else 0.0

    def _select_action(self, state):
        """Epsilon-greedy action selection."""
        if random.random() < self._epsilon:
            return random.randint(0, self._n_actions - 1)
        q_values = self._get_q_values(state)
        return int(np.argmax(q_values))

    def _calculate_reward(self, previous_action):
        """
        Risk-adjusted reward with transaction cost penalty.
        r - 0.5 * r^2 penalizes large losses more than equivalent gains.
        """
        spy_roc1 = self._safe_get(self._indicators["SPY"]["roc1"]) / 100.0

        # Approximate portfolio return using equity/bond weights
        alloc = self._allocations[previous_action]
        equity_weight = alloc["SPY"] + alloc["QQQ"] + alloc["IWM"]
        bond_weight = alloc["TLT"]
        # Bond approximately -0.3 correlated with equities on daily basis
        portfolio_return = (equity_weight * spy_roc1
                            + bond_weight * (-0.3 * spy_roc1))

        # Risk-adjusted reward: penalize large losses asymmetrically
        reward = portfolio_return - 0.5 * (portfolio_return ** 2)

        # Switching cost penalty (~2bp per rebalance)
        if self._current_action != previous_action:
            reward -= 0.0002

        return float(reward)

    def _train(self):
        """Train Q-network on a mini-batch from replay buffer."""
        if len(self._replay_buffer) < 64:
            return

        batch_size = min(128, len(self._replay_buffer))
        batch = random.sample(self._replay_buffer, batch_size)

        x_train = []
        y_train = []

        for exp in batch:
            s, a, r, s_next, done = exp
            action_enc = float(a) / (self._n_actions - 1) - 0.5
            state_a = np.append(s[:-1], action_enc).astype(np.float32)

            if done:
                target_q = r
            elif self._network_initialized:
                # Bootstrap: use target (or Q-net if target not yet ready)
                next_max_q = self._get_target_q(s_next)
                target_q = r + self._gamma * next_max_q
            else:
                target_q = r

            x_train.append(state_a)
            y_train.append(target_q)

        try:
            self._q_network.fit(np.array(x_train), np.array(y_train))
            self._network_initialized = True
            self._train_count += 1
        except Exception as e:
            self.log(f"Training error: {e}")

    def _update_target_network(self):
        """Sync target network with Q-network weights (monthly)."""
        if not self._network_initialized:
            return
        try:
            self._target_network = copy.deepcopy(self._q_network)
            self._target_initialized = True
            self.log(f"Target updated (train={self._train_count}, eps={self._epsilon:.3f})")
        except Exception as e:
            self.log(f"Target update error: {e}")

    def _rebalance(self):
        """Main RL loop: observe -> reward -> store -> act."""
        if self.is_warming_up:
            return
        if not self._indicators_ready():
            return

        current_state = self._get_state_safe()
        if current_state is None:
            return

        # Store experience
        if self._previous_state is not None:
            reward = self._calculate_reward(self._previous_action)
            self._total_reward += reward
            self._replay_buffer.append((
                self._previous_state,
                self._previous_action,
                reward,
                current_state,
                False
            ))

        # Select and execute action
        action = self._select_action(current_state)
        self._previous_action = self._current_action
        self._current_action = action

        alloc = self._allocations[action]
        for ticker, weight in alloc.items():
            self.set_holdings(self._symbols[ticker], weight)

        # Decay exploration
        self._epsilon = max(self._epsilon_min, self._epsilon * self._epsilon_decay)
        self._day_count += 1

        # Diagnostics
        q_values = self._get_q_values(current_state)
        for i, name in enumerate(self._action_names):
            self.plot("Q-Values", name, q_values[i])
        self.plot("RL", "Epsilon", self._epsilon)
        self.plot("RL", "Action", float(action))
        self.plot("RL", "CumulativeReward", self._total_reward)

        self._previous_state = current_state

        self.log(f"RL: {self._action_names[action]} | eps={self._epsilon:.3f} "
                 f"| cumRwd={self._total_reward:.4f} | train={self._train_count}")

    def _get_state_safe(self):
        """Get state with error handling."""
        try:
            return self._get_spy_features()
        except Exception as e:
            self.log(f"State error: {e}")
            return None

    def on_end_of_algorithm(self):
        final_value = self.portfolio.total_portfolio_value
        returns = (final_value - 100_000) / 100_000
        self.log(f"RL-DQN v2: Final=${final_value:,.0f}, Return={returns:.2%}, "
                 f"TotalReward={self._total_reward:.4f}, TrainSteps={self._train_count}, "
                 f"FinalEpsilon={self._epsilon:.4f}")
