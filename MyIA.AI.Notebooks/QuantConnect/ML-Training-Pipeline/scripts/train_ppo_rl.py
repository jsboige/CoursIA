"""
Train PPO (Proximal Policy Optimization) agent for financial trading.

PPO provides stable policy updates via clipped surrogate objective, making it
more sample-efficient and stable than vanilla policy gradient for trading.

Architecture:
    - Actor-Critic with shared backbone
    - GAE (Generalized Advantage Estimation) for variance reduction
    - Clipped surrogate objective with entropy bonus
    - Walk-forward OOS validation

References:
    - Schulman et al., "Proximal Policy Optimization Algorithms" (2017)
    - Schulman et al., "High-Dimensional Continuous Control using GAE" (2016)
    - Hands-On AI Trading with Python, Pik et al., Wiley 2025

Usage:
    python train_ppo_rl.py --dry-run
    python train_ppo_rl.py --symbol SPY --episodes 500 --walk-forward
    python train_ppo_rl.py --symbol BTC-USD --seeds 0,1,7,42,99

Output:
    Checkpoints in --output-dir with metadata.json
"""

import argparse
import json
import sys
from collections import deque
from datetime import datetime
from pathlib import Path

import numpy as np
import pandas as pd
import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.distributions import Categorical

sys.path.append(str(Path(__file__).resolve().parent.parent.parent / "shared"))
from gpu_training import batch_thermal_check, get_gpu_temp, setup_amp

sys.path.append(str(Path(__file__).resolve().parent))
from baselines import oos_direction_distribution
from data_utils import generate_synthetic_data, load_data
from features import FeatureEngineer
from walk_forward import WalkForwardSplitter


# ---------------------------------------------------------------------------
# Trading Environment (reused pattern from train_dqn_rl.py)
# ---------------------------------------------------------------------------

class TradingEnv:
    """Simple trading environment for RL agent.

    Actions: 0=hold, 1=buy, 2=sell (long-only for simplicity)
    State: feature window + position info
    Reward: risk-adjusted step return minus transaction costs.
    """

    def __init__(
        self,
        prices: np.ndarray,
        features: np.ndarray,
        window: int = 20,
        commission: float = 0.001,
    ):
        self.prices = prices
        self.features = features
        self.window = window
        self.commission = commission
        self.reset()

    def reset(self) -> np.ndarray:
        self.position = 0
        self.entry_price = 0.0
        self.step_idx = self.window
        self.total_reward = 0.0
        self.done = False
        self.episode_returns = []
        return self._get_state()

    def _get_state(self) -> np.ndarray:
        feat_window = self.features[self.step_idx - self.window : self.step_idx].flatten()
        position_info = np.array([self.position, self.total_reward], dtype=np.float32)
        return np.concatenate([feat_window, position_info])

    @property
    def state_size(self) -> int:
        return self._get_state().shape[0]

    @property
    def n_actions(self) -> int:
        return 3

    def step(self, action: int) -> tuple:
        if self.done:
            return self._get_state(), 0.0, True, {}

        prev_price = self.prices[self.step_idx - 1]
        curr_price = self.prices[self.step_idx]
        price_change = (curr_price - prev_price) / prev_price

        reward = 0.0
        trade_executed = False

        if action == 1 and self.position <= 0:
            reward -= self.commission
            self.position = 1
            self.entry_price = curr_price
            trade_executed = True
        elif action == 2 and self.position >= 0:
            reward -= self.commission
            self.position = -1
            self.entry_price = curr_price
            trade_executed = True
        elif action == 0:
            pass

        reward += self.position * price_change
        self.total_reward += reward
        self.episode_returns.append(reward)
        self.step_idx += 1

        if self.step_idx >= len(self.prices) - 1:
            self.done = True

        info = {
            "position": self.position,
            "trade": trade_executed,
            "step_reward": reward,
        }
        return self._get_state(), reward, self.done, info


# ---------------------------------------------------------------------------
# Actor-Critic Network
# ---------------------------------------------------------------------------

class ActorCritic(nn.Module):
    """Shared backbone Actor-Critic for discrete action spaces."""

    def __init__(
        self,
        state_size: int,
        hidden_size: int = 256,
        n_actions: int = 3,
    ):
        super().__init__()
        self.backbone = nn.Sequential(
            nn.Linear(state_size, hidden_size),
            nn.ReLU(),
            nn.Linear(hidden_size, hidden_size),
            nn.ReLU(),
        )
        self.actor = nn.Sequential(
            nn.Linear(hidden_size, hidden_size // 2),
            nn.ReLU(),
            nn.Linear(hidden_size // 2, n_actions),
        )
        self.critic = nn.Sequential(
            nn.Linear(hidden_size, hidden_size // 2),
            nn.ReLU(),
            nn.Linear(hidden_size // 2, 1),
        )

    def forward(self, state: torch.Tensor):
        features = self.backbone(state)
        logits = self.actor(features)
        value = self.critic(features)
        return logits, value

    def get_action(self, state: torch.Tensor):
        logits, value = self.forward(state)
        dist = Categorical(logits=logits)
        action = dist.sample()
        return action, dist.log_prob(action), value.squeeze(-1), dist.entropy()

    def evaluate(self, states: torch.Tensor, actions: torch.Tensor):
        logits, value = self.forward(states)
        dist = Categorical(logits=logits)
        log_prob = dist.log_prob(actions)
        entropy = dist.entropy()
        return log_prob, value.squeeze(-1), entropy


# ---------------------------------------------------------------------------
# Rollout Buffer
# ---------------------------------------------------------------------------

class RolloutBuffer:
    """Stores transitions for PPO update."""

    def __init__(self):
        self.states = []
        self.actions = []
        self.log_probs = []
        self.rewards = []
        self.values = []
        self.dones = []

    def push(self, state, action, log_prob, reward, value, done):
        self.states.append(state)
        self.actions.append(action)
        self.log_probs.append(log_prob)
        self.rewards.append(reward)
        self.values.append(value)
        self.dones.append(done)

    def clear(self):
        self.states.clear()
        self.actions.clear()
        self.log_probs.clear()
        self.rewards.clear()
        self.values.clear()
        self.dones.clear()

    def __len__(self):
        return len(self.states)


# ---------------------------------------------------------------------------
# PPO Agent
# ---------------------------------------------------------------------------

class PPOAgent:
    """Proximal Policy Optimization agent with GAE."""

    def __init__(
        self,
        state_size: int,
        n_actions: int = 3,
        hidden_size: int = 256,
        lr: float = 3e-4,
        gamma: float = 0.99,
        gae_lambda: float = 0.95,
        clip_epsilon: float = 0.2,
        entropy_coef: float = 0.01,
        value_coef: float = 0.5,
        max_grad_norm: float = 0.5,
        ppo_epochs: int = 4,
        mini_batch_size: int = 64,
        device: str = "cpu",
    ):
        self.device = device
        self.gamma = gamma
        self.gae_lambda = gae_lambda
        self.clip_epsilon = clip_epsilon
        self.entropy_coef = entropy_coef
        self.value_coef = value_coef
        self.max_grad_norm = max_grad_norm
        self.ppo_epochs = ppo_epochs
        self.mini_batch_size = mini_batch_size

        self.model = ActorCritic(state_size, hidden_size, n_actions).to(device)
        self.optimizer = torch.optim.Adam(self.model.parameters(), lr=lr)
        self.buffer = RolloutBuffer()

    def select_action(self, state: np.ndarray):
        state_t = torch.tensor(state, dtype=torch.float32).unsqueeze(0).to(self.device)
        with torch.no_grad():
            action, log_prob, value, entropy = self.model.get_action(state_t)
        return (
            action.item(),
            log_prob.item(),
            value.item(),
            entropy.item(),
        )

    def compute_gae(self, next_value: float):
        """Compute Generalized Advantage Estimation."""
        rewards = self.buffer.rewards
        values = self.buffer.values
        dones = self.buffer.dones

        advantages = []
        gae = 0.0

        for t in reversed(range(len(rewards))):
            if t == len(rewards) - 1:
                next_val = next_value
            else:
                next_val = values[t + 1]

            delta = rewards[t] + self.gamma * next_val * (1 - dones[t]) - values[t]
            gae = delta + self.gamma * self.gae_lambda * (1 - dones[t]) * gae
            advantages.insert(0, gae)

        advantages = torch.tensor(advantages, dtype=torch.float32).to(self.device)
        returns = advantages + torch.tensor(values, dtype=torch.float32).to(self.device)
        return advantages, returns

    def update(self, next_value: float) -> dict:
        """PPO update with clipped surrogate objective."""
        advantages, returns = self.compute_gae(next_value)

        states = torch.tensor(np.array(self.buffer.states), dtype=torch.float32).to(self.device)
        actions = torch.tensor(self.buffer.actions, dtype=torch.long).to(self.device)
        old_log_probs = torch.tensor(self.buffer.log_probs, dtype=torch.float32).to(self.device)

        # Normalize advantages (guard for single-element batches)
        if len(advantages) > 1:
            advantages = (advantages - advantages.mean()) / (advantages.std() + 1e-8)

        total_loss = 0.0
        total_policy_loss = 0.0
        total_value_loss = 0.0
        total_entropy = 0.0
        n_updates = 0

        for _ in range(self.ppo_epochs):
            # Mini-batch updates
            indices = np.arange(len(states))
            np.random.shuffle(indices)

            for start in range(0, len(indices), self.mini_batch_size):
                end = start + self.mini_batch_size
                mb_idx = indices[start:end]

                mb_states = states[mb_idx]
                mb_actions = actions[mb_idx]
                mb_old_log_probs = old_log_probs[mb_idx]
                mb_advantages = advantages[mb_idx]
                mb_returns = returns[mb_idx]

                new_log_probs, values, entropy = self.model.evaluate(mb_states, mb_actions)

                # Policy loss (clipped surrogate)
                ratio = torch.exp(new_log_probs - mb_old_log_probs)
                surr1 = ratio * mb_advantages
                surr2 = torch.clamp(ratio, 1 - self.clip_epsilon, 1 + self.clip_epsilon) * mb_advantages
                policy_loss = -torch.min(surr1, surr2).mean()

                # Value loss
                value_loss = F.mse_loss(values, mb_returns)

                # Entropy bonus
                entropy_loss = -entropy.mean()

                loss = policy_loss + self.value_coef * value_loss + self.entropy_coef * entropy_loss

                self.optimizer.zero_grad()
                loss.backward()
                nn.utils.clip_grad_norm_(self.model.parameters(), self.max_grad_norm)
                self.optimizer.step()

                total_loss += loss.item()
                total_policy_loss += policy_loss.item()
                total_value_loss += value_loss.item()
                total_entropy += entropy.mean().item()
                n_updates += 1

        self.buffer.clear()

        return {
            "total_loss": round(total_loss / max(n_updates, 1), 6),
            "policy_loss": round(total_policy_loss / max(n_updates, 1), 6),
            "value_loss": round(total_value_loss / max(n_updates, 1), 6),
            "entropy": round(total_entropy / max(n_updates, 1), 6),
            "n_updates": n_updates,
        }


# ---------------------------------------------------------------------------
# Training loop
# ---------------------------------------------------------------------------

def train_ppo(
    env: TradingEnv,
    agent: PPOAgent,
    n_episodes: int = 200,
    max_steps: int = 1000,
    rollout_length: int = 2048,
    eval_every: int = 50,
    verbose: bool = True,
) -> dict:
    """Train PPO agent on trading environment."""
    episode_rewards = []
    episode_direction_accs = []
    best_reward = -float("inf")
    best_state = None

    episode = 0
    step_count = 0
    batch_n = 0

    state = env.reset()

    for step in range(rollout_length * n_episodes):
        action, log_prob, value, entropy = agent.select_action(state)
        next_state, reward, done, info = env.step(action)

        agent.buffer.push(state, action, log_prob, reward, value, float(done))
        step_count += 1
        state = next_state

        if done or step_count >= rollout_length:
            # Skip update if buffer is too small
            if len(agent.buffer) < 2:
                state = env.reset() if done else state
                step_count = 0
                if done:
                    episode += 1
                continue

            # Get next value for GAE
            if done:
                next_value = 0.0
                ep_reward = env.total_reward
                episode_rewards.append(ep_reward)

                # Direction accuracy
                rets = env.episode_returns
                if len(rets) > 1:
                    correct = sum(1 for r in rets if (r > 0 and env.position == 1)
                                  or (r < 0 and env.position == -1))
                    episode_direction_accs.append(correct / len(rets))

                if ep_reward > best_reward:
                    best_reward = ep_reward
                    best_state = {k: v.cpu().clone() for k, v in agent.model.state_dict().items()}

                state = env.reset()
                episode += 1
            else:
                state_t = torch.tensor(state, dtype=torch.float32).unsqueeze(0).to(agent.device)
                with torch.no_grad():
                    _, _, next_val, _ = agent.model.get_action(state_t)
                    next_value = next_val.item()

            update_info = agent.update(next_value)
            batch_n += 1

            if verbose and batch_n % 10 == 0:
                mean_r = np.mean(episode_rewards[-20:]) if episode_rewards else 0
                temp = get_gpu_temp() if agent.device == "cuda" else 0
                temp_str = f"  gpu={temp}C" if temp > 0 else ""
                print(f"  Batch {batch_n}  Episodes={episode}  "
                      f"MeanReward(20)={mean_r:.4f}  "
                      f"PLoss={update_info['policy_loss']:.4f}  "
                      f"VLoss={update_info['value_loss']:.6f}{temp_str}")

            if episode >= n_episodes:
                break

        # Thermal check every 50 steps
        if step % 50 == 0 and agent.device == "cuda":
            batch_thermal_check(step, check_every=50, max_temp=80, cool_sleep=30)

    # Restore best
    if best_state:
        agent.model.load_state_dict(best_state)

    return {
        "episode_rewards": episode_rewards,
        "direction_accuracies": episode_direction_accs,
        "best_reward": best_reward,
        "mean_reward": float(np.mean(episode_rewards)) if episode_rewards else 0,
        "std_reward": float(np.std(episode_rewards)) if episode_rewards else 0,
        "n_episodes": len(episode_rewards),
        "total_params": sum(p.numel() for p in agent.model.parameters()),
    }


# ---------------------------------------------------------------------------
# Evaluation
# ---------------------------------------------------------------------------

def evaluate_agent(
    env: TradingEnv,
    agent: PPOAgent,
    n_episodes: int = 10,
) -> dict:
    """Evaluate trained PPO agent deterministically."""
    rewards = []
    all_actions = []
    all_price_changes = []

    for _ in range(n_episodes):
        state = env.reset()
        ep_reward = 0
        actions = []
        price_changes = []

        while not env.done:
            state_t = torch.tensor(state, dtype=torch.float32).unsqueeze(0).to(agent.device)
            with torch.no_grad():
                logits, _ = agent.model(state_t)
                action = logits.argmax(dim=-1).item()
            next_state, reward, done, info = env.step(action)
            ep_reward += reward
            actions.append(action)

            if env.step_idx > 1:
                pc = (env.prices[env.step_idx - 1] - env.prices[env.step_idx - 2]) / env.prices[env.step_idx - 2]
                price_changes.append(pc)

            state = next_state

        rewards.append(ep_reward)
        all_actions.extend(actions)
        all_price_changes.extend(price_changes)

    # Direction accuracy
    action_directions = []
    for a in all_actions:
        if a == 1:
            action_directions.append(1)
        elif a == 2:
            action_directions.append(-1)
        else:
            action_directions.append(0)

    n_with_position = sum(1 for a in action_directions if a != 0)
    n_correct = 0
    for ad, pc in zip(action_directions, all_price_changes):
        if ad != 0 and ad * pc > 0:
            n_correct += 1

    direction_acc = n_correct / max(n_with_position, 1)

    # Action distribution
    action_counts = np.bincount(all_actions, minlength=3)
    action_dist = action_counts / max(len(all_actions), 1)

    return {
        "mean_reward": round(float(np.mean(rewards)), 6),
        "std_reward": round(float(np.std(rewards)), 6),
        "direction_accuracy": round(direction_acc, 4),
        "n_trades": n_with_position,
        "action_distribution": {
            "hold": round(float(action_dist[0]), 4),
            "buy": round(float(action_dist[1]), 4),
            "sell": round(float(action_dist[2]), 4),
        },
    }


# ---------------------------------------------------------------------------
# Walk-forward multi-seed evaluation
# ---------------------------------------------------------------------------

def run_walk_forward_multiseed(
    prices: np.ndarray,
    features: np.ndarray,
    seeds: list[int],
    n_splits: int = 5,
    gap: int = 10,
    window: int = 20,
    hidden_size: int = 256,
    n_episodes: int = 200,
    device: str = "cpu",
) -> dict:
    """Walk-forward 5-fold x multi-seed PPO evaluation."""
    assert len(seeds) >= 4

    splitter = WalkForwardSplitter(
        n_splits=n_splits, train_size=None, gap=gap, test_size=None,
    )

    all_seed_results = []

    for seed in seeds:
        np.random.seed(seed)
        torch.manual_seed(seed)

        fold_results = []
        for fold_idx, (train_idx, test_idx) in enumerate(splitter.split(prices)):
            train_prices = prices[train_idx]
            train_features = features[train_idx]
            test_prices = prices[test_idx]
            test_features = features[test_idx]

            train_env = TradingEnv(train_prices, train_features, window=window)
            agent = PPOAgent(
                state_size=train_env.state_size,
                hidden_size=hidden_size,
                device=device,
            )

            train_info = train_ppo(
                train_env, agent, n_episodes=n_episodes,
                verbose=False,
            )

            test_env = TradingEnv(test_prices, test_features, window=window)
            eval_info = evaluate_agent(test_env, agent, n_episodes=5)

            baseline = oos_direction_distribution(test_prices)

            fold_results.append({
                "fold": fold_idx,
                "train_size": len(train_idx),
                "test_size": len(test_idx),
                "train_mean_reward": train_info["mean_reward"],
                "eval": eval_info,
                "baseline": baseline,
                "edge": round(eval_info["direction_accuracy"] - baseline["majority_class_accuracy"], 4),
            })

            print(f"  Seed {seed} Fold {fold_idx}: DirAcc={eval_info['direction_accuracy']:.4f} "
                  f"Edge={fold_results[-1]['edge']:+.4f}")

        seed_dir_accs = [f["eval"]["direction_accuracy"] for f in fold_results]
        seed_edges = [f["edge"] for f in fold_results]

        all_seed_results.append({
            "seed": seed,
            "folds": fold_results,
            "mean_dir_acc": round(float(np.mean(seed_dir_accs)), 4),
            "mean_edge": round(float(np.mean(seed_edges)), 4),
        })

    # Cross-seed aggregation
    cross_dir = [r["mean_dir_acc"] for r in all_seed_results]
    cross_edge = [r["mean_edge"] for r in all_seed_results]

    mean_edge = float(np.mean(cross_edge))
    std_edge = float(np.std(cross_edge))
    beats = mean_edge >= 2 * std_edge if std_edge > 0 else mean_edge > 0

    # Per-fold summary
    n_folds_actual = min(len(r["folds"]) for r in all_seed_results)
    per_fold = []
    for f in range(n_folds_actual):
        fold_edges = [r["folds"][f]["edge"] for r in all_seed_results if f < len(r["folds"])]
        per_fold.append({
            "fold": f,
            "mean_edge": round(float(np.mean(fold_edges)), 4),
            "std_edge": round(float(np.std(fold_edges)), 4),
        })

    summary = {
        "model": "PPO",
        "n_seeds": len(seeds),
        "seeds": seeds,
        "n_splits": n_splits,
        "walk_forward": True,
        "hidden_size": hidden_size,
        "n_episodes": n_episodes,
        "cross_seed_mean_dir_acc": round(float(np.mean(cross_dir)), 4),
        "cross_seed_std_dir_acc": round(float(np.std(cross_dir)), 4),
        "cross_seed_mean_edge": round(mean_edge, 4),
        "cross_seed_std_edge": round(std_edge, 4),
        "beats_claim": bool(beats),
        "beats_criterion": (f"mean_edge({mean_edge:.4f}) >= 2*std_edge({2*std_edge:.4f})"
                            if std_edge > 0 else f"mean_edge({mean_edge:.4f}) > 0"),
        "per_fold_across_seeds": per_fold,
        "per_seed": all_seed_results,
    }

    print(f"\n=== PPO Walk-Forward {n_splits}-fold x {len(seeds)} seeds ===")
    print(f"  Cross-seed Mean DirAcc: {np.mean(cross_dir):.4f} +/- {np.std(cross_dir):.4f}")
    print(f"  Cross-seed Mean Edge:   {mean_edge:+.4f} +/- {std_edge:.4f}")
    print(f"  BEATS: {'YES' if beats else 'NO'} ({summary['beats_criterion']})")

    return summary


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="Train PPO agent for financial trading")

    # Data
    parser.add_argument("--symbol", default="SPY")
    parser.add_argument("--data-dir", default=str(
        Path(__file__).resolve().parent.parent / "datasets" / "yfinance"
    ))
    parser.add_argument("--start", default="2010-01-01")
    parser.add_argument("--end", default=None)

    # Model
    parser.add_argument("--hidden-size", type=int, default=256)
    parser.add_argument("--window", type=int, default=20, help="State lookback window")

    # Training
    parser.add_argument("--episodes", type=int, default=200)
    parser.add_argument("--rollout-length", type=int, default=2048)
    parser.add_argument("--lr", type=float, default=3e-4)
    parser.add_argument("--gamma", type=float, default=0.99)
    parser.add_argument("--gae-lambda", type=float, default=0.95)
    parser.add_argument("--clip-epsilon", type=float, default=0.2)
    parser.add_argument("--entropy-coef", type=float, default=0.01)
    parser.add_argument("--ppo-epochs", type=int, default=4)
    parser.add_argument("--mini-batch-size", type=int, default=64)
    parser.add_argument("--commission", type=float, default=0.001)

    # Evaluation
    parser.add_argument("--walk-forward", action="store_true")
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--gap", type=int, default=10)
    parser.add_argument("--seeds", type=str, default=None)
    parser.add_argument("--seed", type=int, default=42)

    # System
    parser.add_argument("--device", default="auto")
    parser.add_argument("--output-dir", default=str(
        Path(__file__).resolve().parent.parent / "outputs" / "ppo_run1"
    ))
    parser.add_argument("--dry-run", action="store_true")

    args = parser.parse_args()

    if args.device == "auto":
        device = "cuda" if torch.cuda.is_available() else "cpu"
    else:
        device = args.device

    # Load data
    if args.dry_run:
        print("DRY-RUN: Using synthetic data")
        n_days = 500
        np.random.seed(args.seed)
        synth_prices = 100 * np.cumprod(1 + np.random.randn(n_days).astype(np.float32) * 0.02)
        synth_features = np.stack([
            np.random.randn(n_days).astype(np.float32) * 0.02,
            np.random.randn(n_days).astype(np.float32) * 0.01,
            np.random.randn(n_days).astype(np.float32) * 0.005,
        ], axis=-1)
        prices = synth_prices
        features = synth_features
        args.episodes = 10
    else:
        try:
            df = load_data(args.data_dir, args.symbol, start=args.start, end=args.end)
        except FileNotFoundError:
            print(f"Data not found for {args.symbol}. Use --dry-run for testing.")
            return

        fe = FeatureEngineer()
        feat_df = fe.fit_transform(df)
        prices = df["Close"].values.astype(np.float32)
        features = feat_df.values.astype(np.float32)

    print(f"PPO Training: {args.symbol}, {len(prices)} timesteps, device={device}")
    print(f"Features: {features.shape[1]}, Hidden: {args.hidden_size}")

    output_dir = Path(args.output_dir)

    if args.walk_forward:
        seeds = [int(s.strip()) for s in args.seeds.split(",")] if args.seeds else [0, 1, 7, 42, 99]
        print(f"Walk-forward {args.n_splits}-fold x {len(seeds)} seeds")

        summary = run_walk_forward_multiseed(
            prices, features, seeds,
            n_splits=args.n_splits, gap=args.gap,
            window=args.window, hidden_size=args.hidden_size,
            n_episodes=args.episodes, device=device,
        )

        output_dir.mkdir(parents=True, exist_ok=True)
        path = output_dir / f"walkforward_ppo_{args.symbol}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        path.write_text(json.dumps(summary, indent=2, default=str), encoding="utf-8")
        print(f"Results: {path}")

    else:
        np.random.seed(args.seed)
        torch.manual_seed(args.seed)

        # Train/val/test split
        n = len(prices)
        train_end = int(n * 0.7)
        val_end = int(n * 0.85)

        train_env = TradingEnv(prices[:val_end], features[:val_end], window=args.window,
                               commission=args.commission)

        agent = PPOAgent(
            state_size=train_env.state_size,
            hidden_size=args.hidden_size,
            lr=args.lr, gamma=args.gamma,
            gae_lambda=args.gae_lambda,
            clip_epsilon=args.clip_epsilon,
            entropy_coef=args.entropy_coef,
            ppo_epochs=args.ppo_epochs,
            mini_batch_size=args.mini_batch_size,
            device=device,
        )

        print(f"Network params: {sum(p.numel() for p in agent.model.parameters()):,}")
        print(f"Training: {args.episodes} episodes, rollout={args.rollout_length}")

        train_info = train_ppo(train_env, agent, n_episodes=args.episodes,
                               rollout_length=args.rollout_length)

        # Evaluate on test set
        test_env = TradingEnv(prices[val_end:], features[val_end:], window=args.window,
                              commission=args.commission)
        eval_info = evaluate_agent(test_env, agent, n_episodes=10)

        baseline = oos_direction_distribution(prices[val_end:])

        result = {
            "symbol": args.symbol,
            "seed": args.seed,
            "train": {
                "mean_reward": train_info["mean_reward"],
                "std_reward": train_info["std_reward"],
                "best_reward": train_info["best_reward"],
                "n_episodes": train_info["n_episodes"],
                "total_params": train_info["total_params"],
            },
            "test": eval_info,
            "baseline": baseline,
            "edge_over_majority": round(
                eval_info["direction_accuracy"] - baseline["majority_class_accuracy"], 4
            ),
        }

        print(f"\n=== PPO Results ({args.symbol}) ===")
        print(f"  Train mean reward: {train_info['mean_reward']:.4f}")
        print(f"  Test DirAcc: {eval_info['direction_accuracy']:.4f}")
        print(f"  Baseline: {baseline['majority_class_accuracy']:.4f}")
        print(f"  Edge: {result['edge_over_majority']:+.4f}")
        print(f"  Actions: {eval_info['action_distribution']}")

        # Save checkpoint
        output_dir.mkdir(parents=True, exist_ok=True)
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        ckpt_dir = output_dir / ts
        ckpt_dir.mkdir(parents=True, exist_ok=True)

        torch.save(agent.model.state_dict(), ckpt_dir / "model.pt")
        (ckpt_dir / "metadata.json").write_text(
            json.dumps(result, indent=2, default=str), encoding="utf-8"
        )
        print(f"Checkpoint: {ckpt_dir}")

    if args.dry_run:
        print("DRY-RUN complete.")


if __name__ == "__main__":
    main()
