"""Tests for train_dqn_rl.py -- CPU-only smoke tests."""

import sys
from pathlib import Path

import numpy as np
import pytest
import torch

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from train_dqn_rl import ReplayBuffer, TradingEnv, build_dqn


class TestTradingEnv:
    def _make_env(self, n_steps=100, n_features=5, window=10):
        prices = np.cumsum(np.random.randn(n_steps) * 0.01) + 100
        features = np.random.randn(n_steps, n_features).astype(np.float32)
        return TradingEnv(prices, features, window=window)

    def test_reset(self):
        env = self._make_env()
        state = env.reset()
        assert state is not None
        assert env.position == 0

    def test_step_hold(self):
        env = self._make_env()
        env.reset()
        state, reward, done, info = env.step(0)  # hold
        assert not done
        assert info["position"] == 0

    def test_step_buy(self):
        env = self._make_env()
        env.reset()
        state, reward, done, info = env.step(1)  # buy
        assert info["position"] == 1
        assert env.position == 1

    def test_step_sell(self):
        env = self._make_env()
        env.reset()
        state, reward, done, info = env.step(2)  # sell
        assert info["position"] == -1

    def test_episode_ends(self):
        env = self._make_env(n_steps=15, window=5)
        env.reset()
        done = False
        steps = 0
        while not done:
            _, _, done, _ = env.step(0)
            steps += 1
            if steps > 20:
                break
        assert done

    def test_state_size_property(self):
        env = self._make_env(n_features=3, window=5)
        assert env.state_size == 3 * 5 + 2

    def test_commission_deducted(self):
        env = self._make_env()
        env.reset()
        _, reward, _, info = env.step(1)  # buy
        assert reward < 0  # commission deducted


class TestBuildDQN:
    def test_forward_shape(self):
        model = build_dqn(state_size=20, hidden_size=32, n_actions=3)
        x = torch.randn(4, 20)
        out = model(x)
        assert out.shape == (4, 3)

    def test_gradient_flow(self):
        model = build_dqn(state_size=10, hidden_size=16, n_actions=3)
        x = torch.randn(2, 10)
        out = model(x)
        loss = out.sum()
        loss.backward()
        for p in model.parameters():
            assert p.grad is not None

    def test_state_dict_roundtrip(self):
        model = build_dqn(state_size=10, hidden_size=16, n_actions=3)
        sd = model.state_dict()
        model2 = build_dqn(state_size=10, hidden_size=16, n_actions=3)
        model2.load_state_dict(sd)

    def test_different_hidden_sizes(self):
        model32 = build_dqn(state_size=10, hidden_size=32)
        model128 = build_dqn(state_size=10, hidden_size=128)
        params32 = sum(p.numel() for p in model32.parameters())
        params128 = sum(p.numel() for p in model128.parameters())
        assert params128 > params32


class TestReplayBuffer:
    def test_push_and_sample(self):
        buf = ReplayBuffer(capacity=100)
        for i in range(20):
            buf.push(
                state=np.random.randn(10),
                action=np.random.randint(3),
                reward=float(np.random.randn()),
                next_state=np.random.randn(10),
                done=False,
            )
        assert len(buf) == 20
        batch = buf.sample(batch_size=8)
        assert len(batch) == 5  # states, actions, rewards, next_states, dones

    def test_capacity_limit(self):
        buf = ReplayBuffer(capacity=10)
        for i in range(50):
            buf.push(np.zeros(5), 0, 0.0, np.zeros(5), False)
        assert len(buf) == 10

    def test_sample_dtypes(self):
        buf = ReplayBuffer(capacity=50)
        for _ in range(30):
            buf.push(np.random.randn(8), 1, 0.5, np.random.randn(8), False)
        states, actions, rewards, next_states, dones = buf.sample(batch_size=5)
        assert states.dtype == np.float32
        assert actions.dtype == np.int64
        assert rewards.dtype == np.float32
