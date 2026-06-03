#region imports
from AlgorithmImports import *
import numpy as np
from collections import deque
import random
# endregion


class ReinforcementLearningTrading(QCAlgorithm):
    """
    Reinforcement Learning for Trading using Deep Q-Network (DQN).

    This strategy demonstrates how to use reinforcement learning to train
    an agent that learns optimal trading decisions through trial and error.

    Reference: Hands-On AI Trading with Python, QuantConnect, and AWS
    Chapter 07 - Better Hedging with Reinforcement Learning

    How it works:
    1. Define state: market features (returns, volatility, position)
    2. Define actions: BUY, SELL, HOLD
    3. Define reward: portfolio return (or Sharpe-like metric)
    4. Use DQN to learn Q-values for state-action pairs
    5. Trade based on learned policy

    DQN Architecture:
    - Input: state vector (normalized features)
    - Hidden layers: learn state-action value function
    - Output: Q-values for each action

    Key RL concepts:
    - Exploration vs Exploitation: epsilon-greedy policy
    - Experience Replay: learn from past experiences
    - Target Network: stabilize learning

    Parameters:
    - lookback_days: Days for feature calculation (default: 20)
    - epsilon_start: Initial exploration rate (default: 0.3)
    - epsilon_end: Final exploration rate (default: 0.05)
    - learning_rate: Learning rate for updates (default: 0.01)
    - gamma: Discount factor for future rewards (default: 0.95)
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 1, 1)
        self.set_cash(100_000)

        self._spy = self.add_equity("SPY", Resolution.DAILY).symbol

        # RL parameters
        self._lookback_days = self.get_parameter('lookback_days', 20)
        self._epsilon = self.get_parameter('epsilon_start', 0.3)
        self._epsilon_end = self.get_parameter('epsilon_end', 0.05)
        self._epsilon_decay = 0.9995
        self._learning_rate = self.get_parameter('learning_rate', 0.01)
        self._gamma = self.get_parameter('gamma', 0.95)

        # Action space: 0=HOLD, 1=BUY, 2=SELL
        self._actions = ['HOLD', 'BUY', 'SELL']
        self._n_actions = len(self._actions)

        # State space dimensions
        # [returns_1d, returns_5d, returns_20d, volatility, position]
        self._state_dim = 5

        # Feature collection
        self._returns_window = deque(maxlen=self._lookback_days * 2)

        # Indicators for state features
        self._roc_1 = self.roc(self._spy, 1, Resolution.DAILY)
        self._roc_5 = self.roc(self._spy, 5, Resolution.DAILY)
        self._roc_20 = self.roc(self._spy, 20, Resolution.DAILY)
        self._std = self.std(self._spy, 20, Resolution.DAILY)

        # Warm up
        history = self.history[TradeBar](
            self._spy, timedelta(days=self._lookback_days * 3), Resolution.DAILY
        )
        for bar in history:
            self._roc_1.update(bar.end_time, bar.close)
            self._roc_5.update(bar.end_time, bar.close)
            self._roc_20.update(bar.end_time, bar.close)
            self._std.update(bar.end_time, bar.close)

        # Experience replay buffer
        self._replay_buffer = deque(maxlen=1000)

        # Q-network weights (simplified: linear approximator)
        self._q_weights = np.random.randn(self._state_dim, self._n_actions) * 0.1
        self._target_weights = self._q_weights.copy()

        # Tracking
        self._previous_state = None
        self._previous_action = None
        self._episode_rewards = []
        self._total_reward = 0
        self._train_count = 0

        # Schedule trading
        self.schedule.on(
            self.date_rules.every_day(self._spy),
            self.time_rules.after_market_open(self._spy, 30),
            self._trade
        )

        # Update target network periodically
        self.schedule.on(
            self.date_rules.month_start(self._spy),
            self.time_rules.after_market_open(self._spy, 60),
            self._update_target_network
        )

        self.log(f"RL Trading initialized: epsilon={self._epsilon:.2%}, gamma={self._gamma}")

    def _get_state(self):
        """
        Construct current state vector.
        """
        position = 1 if self.portfolio[self._spy].invested else 0

        state = np.array([
            self._normalize(self._roc_1.current.value, 0.01),
            self._normalize(self._roc_5.current.value, 0.03),
            self._normalize(self._roc_20.current.value, 0.05),
            self._normalize(self._std.current.value, 0.02),
            float(position)
        ])

        return state

    def _normalize(self, value, scale):
        """Normalize feature value."""
        if np.isnan(value) or np.isinf(value):
            return 0.0
        return np.clip(value / scale, -3, 3)

    def _get_q_values(self, state):
        """
        Get Q-values for all actions given state.
        """
        return np.dot(state, self._q_weights)

    def _select_action(self, state):
        """
        Select action using epsilon-greedy policy.
        """
        if random.random() < self._epsilon:
            # Exploration: random action
            return random.randint(0, self._n_actions - 1)
        else:
            # Exploitation: best action
            q_values = self._get_q_values(state)
            return np.argmax(q_values)

    def _calculate_reward(self):
        """
        Calculate reward based on portfolio performance.
        """
        # Daily return as reward
        daily_return = self._roc_1.current.value / 100

        # Position-adjusted reward
        if self.portfolio[self._spy].invested:
            reward = daily_return
        else:
            # Small penalty for holding cash (opportunity cost)
            reward = -0.0001

        return reward

    def _train_step(self, state, action, reward, next_state, done=False):
        """
        Perform one step of Q-learning update.
        """
        # Store experience
        self._replay_buffer.append({
            'state': state,
            'action': action,
            'reward': reward,
            'next_state': next_state,
            'done': done
        })

        # Sample mini-batch
        if len(self._replay_buffer) < 32:
            return

        batch = random.sample(self._replay_buffer, min(32, len(self._replay_buffer)))

        for exp in batch:
            s = exp['state']
            a = exp['action']
            r = exp['reward']
            s_next = exp['next_state']

            # Current Q-value
            current_q = np.dot(s, self._q_weights[:, a])

            # Target Q-value (using target network)
            if exp['done']:
                target = r
            else:
                next_q_values = np.dot(s_next, self._target_weights)
                target = r + self._gamma * np.max(next_q_values)

            # Update weights (gradient descent step)
            error = target - current_q
            self._q_weights[:, a] += self._learning_rate * error * s

        self._train_count += 1

    def _update_target_network(self):
        """
        Update target network with current weights.
        """
        self._target_weights = self._q_weights.copy()
        self.log(f"Target network updated (train steps: {self._train_count})")

    def _execute_action(self, action):
        """
        Execute trading action.
        """
        action_name = self._actions[action]

        if action_name == 'BUY':
            if not self.portfolio[self._spy].invested:
                self.set_holdings(self._spy, 1.0)
                self.log(f"RL Action: BUY")
        elif action_name == 'SELL':
            if self.portfolio[self._spy].invested:
                self.set_holdings(self._spy, 0.0)
                self.log(f"RL Action: SELL")
        else:  # HOLD
            self.log(f"RL Action: HOLD")

    def _trade(self):
        """
        Main trading loop.
        """
        if not self._roc_1.is_ready:
            return

        # Get current state
        current_state = self._get_state()

        # Calculate reward from previous action
        if self._previous_state is not None:
            reward = self._calculate_reward()
            self._total_reward += reward

            # Train on experience
            self._train_step(
                self._previous_state,
                self._previous_action,
                reward,
                current_state
            )

        # Select action
        action = self._select_action(current_state)

        # Execute action
        self._execute_action(action)

        # Plot Q-values
        q_values = self._get_q_values(current_state)
        for i, action_name in enumerate(self._actions):
            self.plot('Q-Values', action_name, q_values[i])

        self.plot('RL', 'Epsilon', self._epsilon)
        self.plot('RL', 'CumulativeReward', self._total_reward)

        # Update exploration rate
        self._epsilon = max(self._epsilon_end, self._epsilon * self._epsilon_decay)

        # Store for next step
        self._previous_state = current_state
        self._previous_action = action

    def on_end_of_algorithm(self):
        final_value = self.portfolio.total_portfolio_value
        returns = (final_value - 100000) / 100000

        # Action distribution
        action_counts = {'BUY': 0, 'SELL': 0, 'HOLD': 0}
        # This would need to be tracked during execution

        self.log(f"RL Trading: Final=${final_value:,.0f}, Return={returns:.2%}")
        self.log(f"Total Reward: {self._total_reward:.4f}, Train Steps: {self._train_count}")
        self.log(f"Final Epsilon: {self._epsilon:.4f}")
