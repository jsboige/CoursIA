# region imports
from AlgorithmImports import *
# endregion

class RLPortfolioAlgorithm(QCAlgorithm):
    """
    Reinforcement Learning Portfolio Strategy.

    Strategy:
    - Q-Learning agent for asset allocation decisions
    - State: Market regime (trend, volatility, momentum)
    - Actions: Allocate to different asset classes (SPY, TLT, GLD, Cash)
    - Reward: Risk-adjusted return (Sharpe-like)
    - Exploration: Epsilon-greedy with decay
    """

    def Initialize(self):
        self.SetStartDate(2020, 1, 1)
        self.SetCash(100000)

        # Assets
        self.assets = {
            'SPY': self.AddEquity("SPY", Resolution.DAILY).Symbol,
            'TLT': self.AddEquity("TLT", Resolution.DAILY).Symbol,
            'GLD': self.AddEquity("GLD", Resolution.DAILY).Symbol
        }

        # RL parameters
        self.state_size = 10  # Market features
        self.action_size = 4  # [100% SPY, 100% TLT, 100% GLD, 100% Cash]
        self.learning_rate = 0.01
        self.discount_factor = 0.95
        self.epsilon = 1.0
        self.epsilon_min = 0.01
        self.epsilon_decay = 0.995
        self.batch_size = 32
        self.memory_size = 1000

        # Q-table
        self.q_table = np.zeros((self.state_size, self.action_size))

        # Experience replay
        self.memory = []
        self.last_state = None
        self.last_action = None

        # Rebalance schedule (weekly)
        self.Schedule.On(self.DateRules.Every(DayOfWeek.Monday),
                         self.TimeRules.AfterMarketOpen("SPY", 30),
                         self.Rebalance)

        # Train weekly
        self.Schedule.On(self.DateRules.Every(DayOfWeek.Friday),
                         self.TimeRules.AfterMarketOpen("SPY", 30),
                         self.Train)

        self.rewards_history = []

    def GetState(self):
        """Get current market state."""
        # Get recent data
        spy_history = self.History(self.assets['SPY'], 60, Resolution.DAILY)
        tlt_history = self.History(self.assets['TLT'], 60, Resolution.DAILY)

        if spy_history.empty or tlt_history.empty:
            return np.zeros(self.state_size)

        spy_close = spy_history['close']
        tlt_close = tlt_history['close']

        # State features
        spy_returns = spy_close.pct_change()
        tlt_returns = tlt_close.pct_change()

        # Feature 1-2: SPY trend (EMA 20/50/200)
        ema20 = spy_close.ewm(span=20).mean().iloc[-1]
        ema50 = spy_close.ewm(span=50).mean().iloc[-1]
        ema200 = spy_close.ewm(span=200).mean().iloc[-1]
        spy_price = spy_close.iloc[-1]

        trend_short = 1 if spy_price > ema20 else 0
        trend_long = 1 if spy_price > ema200 else 0

        # Feature 3-4: Volatility regime
        spy_vol = spy_returns.rolling(20).std().iloc[-1]
        vol_threshold = spy_returns.rolling(60).std().mean()
        high_vol = 1 if spy_vol > vol_threshold else 0

        # Feature 5-6: Momentum
        momentum_5 = 1 if spy_returns.rolling(5).sum() > 0 else 0
        momentum_20 = 1 if spy_returns.rolling(20).sum() > 0 else 0

        # Feature 7-8: Flight to safety (TLT outperforming SPY)
        spy_return_20 = spy_returns.rolling(20).sum().iloc[-1]
        tlt_return_20 = tlt_returns.rolling(20).sum().iloc[-1]
        flight_to_safety = 1 if tlt_return_20 > spy_return_20 else 0

        # Feature 9-10: Market breadth (simplified)
        above_ma20 = 1 if spy_price > ema20 else 0
        above_ma50 = 1 if spy_price > ema50 else 0

        state = np.array([
            trend_short, trend_long, high_vol,
            momentum_5, momentum_20, flight_to_safety,
            above_ma20, above_ma50,
            int(self.Time.month % 4),  # Quarter
            int(self.Time.day < 10)  # Start of month
        ])

        return state

    def GetAction(self, state, training=True):
        """Epsilon-greedy action selection."""
        if training and np.random.random() < self.epsilon:
            return np.random.randint(self.action_size)
        else:
            # Convert state to index
            state_idx = int(sum(state * (2 ** np.arange(len(state))))) % self.state_size
            return np.argmax(self.q_table[state_idx])

    def GetReward(self, action, portfolio_return):
        """Calculate reward for the action."""
        # Risk-adjusted reward (penalize high volatility)
        reward = portfolio_return

        # Penalty for large drawdowns
        if len(self.rewards_history) > 5:
            recent_avg = np.mean(self.rewards_history[-5:])
            if portfolio_return < recent_avg - 0.02:
                reward -= 0.01

        return reward

    def Rebalance(self):
        """Rebalance based on Q-learning policy."""
        state = self.GetState()

        # Select action (use policy, no exploration)
        action = self.GetAction(state, training=False)

        # Execute action
        allocations = [
            [1.0, 0.0, 0.0],  # 100% SPY
            [0.0, 1.0, 0.0],  # 100% TLT
            [0.0, 0.0, 1.0],  # 100% GLD
            [0.0, 0.0, 0.0]   # 100% Cash
        ]

        spy_alloc, tlt_alloc, gld_alloc = allocations[action]

        self.SetHoldings(self.assets['SPY'], spy_alloc * 0.95)
        self.SetHoldings(self.assets['TLT'], tlt_alloc * 0.95)
        self.SetHoldings(self.assets['GLD'], gld_alloc * 0.95)

        # Store state-action for next step
        self.last_state = state
        self.last_action = action

    def Train(self):
        """Train Q-learning agent."""
        if len(self.memory) < self.batch_size:
            return

        # Sample random batch
        batch = np.random.choice(len(self.memory), self.batch_size, replace=False)

        for idx in batch:
            state, action, reward, next_state = self.memory[idx]

            # Convert to indices
            state_idx = int(sum(state * (2 ** np.arange(len(state))))) % self.state_size
            next_state_idx = int(sum(next_state * (2 ** np.arange(len(next_state))))) % self.state_size

            # Q-learning update
            current_q = self.q_table[state_idx, action]
            max_next_q = np.max(self.q_table[next_state_idx])

            new_q = current_q + self.learning_rate * (
                reward + self.discount_factor * max_next_q - current_q
            )

            self.q_table[state_idx, action] = new_q

        # Decay epsilon
        self.epsilon = max(self.epsilon_min, self.epsilon * self.epsilon_decay)

        self.Debug(f"Trained. Epsilon: {self.epsilon:.3f}")

    def OnData(self, data):
        """Track rewards for training."""
        if self.last_state is not None and self.last_action is not None:
            # Calculate portfolio return since last rebalance
            portfolio_value = self.Portfolio.TotalPortfolioValue
            if hasattr(self, 'last_value'):
                portfolio_return = (portfolio_value - self.last_value) / self.last_value
                reward = self.GetReward(self.last_action, portfolio_return)

                # Get new state
                new_state = self.GetState()

                # Store experience
                self.memory.append((self.last_state, self.last_action, reward, new_state))

                # Keep memory size limited
                if len(self.memory) > self.memory_size:
                    self.memory.pop(0)

                self.rewards_history.append(reward)

            self.last_value = portfolio_value

        # Initialize on first run
        if not hasattr(self, 'last_value'):
            self.last_value = self.Portfolio.TotalPortfolioValue
