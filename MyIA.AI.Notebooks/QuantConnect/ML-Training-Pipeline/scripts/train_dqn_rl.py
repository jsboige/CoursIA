"""
Train DQN reinforcement learning agent for financial trading.

Uses OpenAI Gym-style environment with OHLCV data. The agent learns
buy/sell/hold actions to maximize cumulative reward (risk-adjusted returns).

Usage:
    # Dry-run (CPU, synthetic data, 100 steps)
    python train_dqn_rl.py --dry-run

    # Full training on yfinance SPY
    python train_dqn_rl.py --data-dir ../datasets/yfinance --symbol SPY --start 2010-01-01

    # Custom architecture
    python train_dqn_rl.py --data-dir ../datasets/yfinance --symbol SPY \
        --hidden-size 512 --num-episodes 500 --replay-size 100000

Output:
    Checkpoints in --checkpoint-dir (default: ../checkpoints/dqn/<date>/)
    metadata.json with hyperparams, episode rewards, Sharpe estimate
"""

import argparse
import json
import sys
from collections import deque
from datetime import datetime
from pathlib import Path

import numpy as np
import pandas as pd

sys.path.append(str(Path(__file__).resolve().parent.parent.parent / "shared"))
from gpu_training import (
    batch_thermal_check,
    get_gpu_temp,
    setup_amp,
    thermal_check,
)
from baselines import majority_class_baseline
from data_utils import compute_data_hash, generate_synthetic_data, load_data
from features import FeatureEngineer
from walk_forward import WalkForwardSplitter


# --- Trading Environment ---

class TradingEnv:
    """Simple trading environment for RL agent.

    Actions: 0=hold, 1=buy, 2=sell
    State: [returns, volatility, position, unrealized_pnl] window
    Reward: risk-adjusted step return (position * price_change - cost)
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
        self.position = 0  # -1, 0, 1
        self.entry_price = 0.0
        self.step_idx = self.window
        self.total_reward = 0.0
        self.done = False
        return self._get_state()

    def _get_state(self) -> np.ndarray:
        feat_window = self.features[self.step_idx - self.window : self.step_idx].flatten()
        position_info = np.array([self.position, self.total_reward], dtype=np.float32)
        return np.concatenate([feat_window, position_info])

    @property
    def state_size(self) -> int:
        feat_window = self.features[: self.window].flatten()
        return len(feat_window) + 2

    def step(self, action: int) -> tuple:
        if self.done:
            return self._get_state(), 0.0, True, {}

        prev_price = self.prices[self.step_idx - 1]
        curr_price = self.prices[self.step_idx]
        price_change = (curr_price - prev_price) / prev_price

        reward = 0.0
        trade_executed = False

        if action == 1 and self.position <= 0:  # Buy
            reward -= self.commission
            self.position = 1
            self.entry_price = curr_price
            trade_executed = True
        elif action == 2 and self.position >= 0:  # Sell
            reward -= self.commission
            self.position = -1
            self.entry_price = curr_price
            trade_executed = True

        # PnL from current position
        reward += self.position * price_change

        self.total_reward += reward
        self.step_idx += 1

        if self.step_idx >= len(self.prices) - 1:
            self.done = True

        info = {
            "position": self.position,
            "trade": trade_executed,
            "step_reward": reward,
        }
        return self._get_state(), reward, self.done, info


# --- DQN Network ---

def build_dqn(state_size: int, hidden_size: int = 256, n_actions: int = 3) -> "torch.nn.Module":
    """Build DQN network."""
    import torch
    import torch.nn as nn

    class DQN(nn.Module):
        def __init__(self, state_sz, hidden_sz, n_act):
            super().__init__()
            self.net = nn.Sequential(
                nn.Linear(state_sz, hidden_sz),
                nn.ReLU(),
                nn.Linear(hidden_sz, hidden_sz),
                nn.ReLU(),
                nn.Linear(hidden_sz, hidden_sz // 2),
                nn.ReLU(),
                nn.Linear(hidden_sz // 2, n_act),
            )

        def forward(self, x):
            return self.net(x)

    return DQN(state_size, hidden_size, n_actions)


# --- Replay Buffer ---

class ReplayBuffer:
    def __init__(self, capacity: int = 50000):
        self.buffer = deque(maxlen=capacity)

    def push(self, state, action, reward, next_state, done):
        self.buffer.append((state, action, reward, next_state, done))

    def sample(self, batch_size: int) -> tuple:
        indices = np.random.choice(len(self.buffer), min(batch_size, len(self.buffer)), replace=False)
        batch = [self.buffer[i] for i in indices]
        states, actions, rewards, next_states, dones = zip(*batch)
        return (
            np.array(states, dtype=np.float32),
            np.array(actions, dtype=np.int64),
            np.array(rewards, dtype=np.float32),
            np.array(next_states, dtype=np.float32),
            np.array(dones, dtype=np.float32),
        )

    def __len__(self):
        return len(self.buffer)


# --- Training ---

def train_dqn(
    env: TradingEnv,
    hidden_size: int = 256,
    num_episodes: int = 200,
    batch_size: int = 64,
    gamma: float = 0.99,
    lr: float = 1e-3,
    eps_start: float = 1.0,
    eps_end: float = 0.01,
    eps_decay: float = 0.995,
    replay_size: int = 50000,
    target_update: int = 10,
    device: str = "cpu",
    intermediate_save_every: int = 0,
    intermediate_save_dir: "Path | None" = None,
) -> dict:
    """Train DQN agent on trading environment."""
    import torch
    import torch.nn as nn
    import torch.optim as optim

    state_size = env.state_size
    n_actions = 3

    policy_net = build_dqn(state_size, hidden_size, n_actions).to(device)
    target_net = build_dqn(state_size, hidden_size, n_actions).to(device)
    target_net.load_state_dict(policy_net.state_dict())
    target_net.eval()

    optimizer = optim.Adam(policy_net.parameters(), lr=lr)
    buffer = ReplayBuffer(replay_size)
    criterion = nn.SmoothL1Loss()

    use_amp, grad_scaler = setup_amp()

    epsilon = eps_start
    episode_rewards = []
    episode_trades = []
    best_avg_reward = float("-inf")
    best_state = None

    for episode in range(num_episodes):
        thermal_check(max_temp=80, cool_sleep=30)
        state = env.reset()
        total_reward = 0.0
        trades = 0
        step = 0

        while True:
            # Epsilon-greedy action selection
            if np.random.random() < epsilon:
                action = np.random.randint(n_actions)
            else:
                with torch.no_grad():
                    state_t = torch.tensor(state, dtype=torch.float32).unsqueeze(0).to(device)
                    q_values = policy_net(state_t)
                    action = q_values.argmax(dim=1).item()

            next_state, reward, done, info = env.step(action)
            buffer.push(state, action, reward, next_state, float(done))
            total_reward += reward
            if info.get("trade"):
                trades += 1
            state = next_state

            # Learn from replay
            if len(buffer) >= batch_size:
                s, a, r, ns, d = buffer.sample(batch_size)
                s_t = torch.tensor(s).to(device)
                a_t = torch.tensor(a).unsqueeze(1).to(device)
                r_t = torch.tensor(r).unsqueeze(1).to(device)
                ns_t = torch.tensor(ns).to(device)
                d_t = torch.tensor(d).unsqueeze(1).to(device)

                q_values = policy_net(s_t).gather(1, a_t)
                with torch.no_grad():
                    with torch.amp.autocast("cuda", enabled=use_amp):
                        next_q = target_net(ns_t).max(1, keepdim=True)[0]
                        target_q = r_t + gamma * next_q * (1 - d_t)

                with torch.amp.autocast("cuda", enabled=use_amp):
                    loss = criterion(q_values, target_q)
                if use_amp:
                    grad_scaler.scale(loss).backward()
                    grad_scaler.unscale_(optimizer)
                    torch.nn.utils.clip_grad_norm_(policy_net.parameters(), 1.0)
                    grad_scaler.step(optimizer)
                    grad_scaler.update()
                else:
                    optimizer.zero_grad()
                    loss.backward()
                    torch.nn.utils.clip_grad_norm_(policy_net.parameters(), 1.0)
                    optimizer.step()

            step += 1
            batch_thermal_check(step, check_every=10, max_temp=80, cool_sleep=30)

            if done:
                break

        epsilon = max(eps_end, epsilon * eps_decay)
        episode_rewards.append(round(total_reward, 4))
        episode_trades.append(trades)

        # Update target network
        if (episode + 1) % target_update == 0:
            target_net.load_state_dict(policy_net.state_dict())

        # Track best model
        if len(episode_rewards) >= 10:
            avg_reward = np.mean(episode_rewards[-10:])
            if avg_reward > best_avg_reward:
                best_avg_reward = avg_reward
                best_state = {k: v.cpu().clone() for k, v in policy_net.state_dict().items()}

        if (episode + 1) % max(1, num_episodes // 5) == 0:
            recent = np.mean(episode_rewards[-10:]) if len(episode_rewards) >= 10 else np.mean(episode_rewards)
            temp = get_gpu_temp()
            temp_str = f"  GPU={temp}C" if temp > 0 else ""
            print(f"  Episode {episode+1}/{num_episodes}  reward={total_reward:.4f}  "
                  f"avg10={recent:.4f}  trades={trades}  eps={epsilon:.3f}{temp_str}")

        if (
            intermediate_save_every > 0
            and intermediate_save_dir is not None
            and best_state is not None
            and (episode + 1) % intermediate_save_every == 0
        ):
            intermediate_save_dir.mkdir(parents=True, exist_ok=True)
            torch.save(best_state, intermediate_save_dir / "best_state.pt")
            (intermediate_save_dir / "progress.json").write_text(
                json.dumps({
                    "episode": int(episode + 1),
                    "best_avg_reward_10": round(float(best_avg_reward), 4),
                    "epsilon": round(float(epsilon), 4),
                }),
                encoding="utf-8",
            )
            print(
                f"  [intermediate-save] episode={episode+1} "
                f"best_avg10={best_avg_reward:.4f} -> {intermediate_save_dir}",
                flush=True,
            )

    # Load best model
    if best_state:
        policy_net.load_state_dict(best_state)

    # Compute summary metrics
    rewards = np.array(episode_rewards)
    sharpe_estimate = rewards.mean() / (rewards.std() + 1e-8)

    metrics = {
        "total_episodes": num_episodes,
        "mean_reward": round(float(rewards.mean()), 4),
        "std_reward": round(float(rewards.std()), 4),
        "max_reward": round(float(rewards.max()), 4),
        "min_reward": round(float(rewards.min()), 4),
        "sharpe_estimate": round(float(sharpe_estimate), 4),
        "mean_trades": round(float(np.mean(episode_trades)), 1),
        "best_avg_reward_10": round(float(best_avg_reward), 4),
    }

    return {
        "model": policy_net,
        "metrics": metrics,
        "episode_rewards": [float(x) for x in episode_rewards],
        "episode_trades": [int(x) for x in episode_trades],
        "state_size": int(state_size),
        "hidden_size": int(hidden_size),
        "n_actions": int(n_actions),
    }


def evaluate_dqn(
    model: "torch.nn.Module",
    env: TradingEnv,
    device: str = "cpu",
    num_episodes: int = 10,
) -> dict:
    """Evaluate a trained DQN on a test environment (greedy policy, no exploration)."""
    import torch

    rewards = []
    trades_list = []
    model.eval()

    for _ in range(num_episodes):
        state = env.reset()
        total_reward = 0.0
        ep_trades = 0

        while True:
            with torch.no_grad():
                state_t = torch.tensor(state, dtype=torch.float32).unsqueeze(0).to(device)
                action = model(state_t).argmax(dim=1).item()

            next_state, reward, done, info = env.step(action)
            total_reward += reward
            if info.get("trade"):
                ep_trades += 1
            state = next_state

            if done:
                break

        rewards.append(total_reward)
        trades_list.append(ep_trades)

    rewards_arr = np.array(rewards)
    sharpe = float(rewards_arr.mean() / (rewards_arr.std() + 1e-8))

    return {
        "oos_mean_reward": round(float(rewards_arr.mean()), 4),
        "oos_std_reward": round(float(rewards_arr.std()), 4),
        "oos_sharpe": round(sharpe, 4),
        "oos_max_reward": round(float(rewards_arr.max()), 4),
        "oos_min_reward": round(float(rewards_arr.min()), 4),
        "oos_mean_trades": round(float(np.mean(trades_list)), 1),
        "oos_episodes": num_episodes,
    }


def train_walk_forward_dqn(
    prices: np.ndarray,
    features: np.ndarray,
    window: int = 20,
    commission: float = 0.001,
    hidden_size: int = 256,
    num_episodes: int = 200,
    batch_size: int = 64,
    gamma: float = 0.99,
    lr: float = 1e-3,
    eps_start: float = 1.0,
    eps_end: float = 0.01,
    eps_decay: float = 0.995,
    replay_size: int = 50000,
    target_update: int = 10,
    device: str = "cpu",
    n_splits: int = 5,
    train_size: int | None = None,
    test_size: int | None = None,
    gap: int = 5,
) -> dict:
    """Walk-forward DQN training with per-fold normalization and majority-class baseline.

    For each fold, trains a fresh DQN on the training window and evaluates
    the greedy policy on the test window. Aggregates OOS direction accuracy
    across all folds.
    """
    import torch

    splitter = WalkForwardSplitter(
        n_splits=n_splits, train_size=train_size, test_size=test_size, gap=gap,
    )

    fold_results = []
    oos_direction_correct = 0
    oos_direction_total = 0
    best_model = None
    best_fold_reward = float("-inf")

    for fold_idx, (train_idx, test_idx) in enumerate(splitter.split(prices)):
        if len(test_idx) == 0:
            continue

        # Per-fold train-only normalization
        train_features = features[train_idx]
        test_features = features[test_idx]
        mean = train_features.mean(axis=0)
        std = train_features.std(axis=0)
        std = np.where(std < 1e-8, 1.0, std)
        train_norm = (train_features - mean) / std
        test_norm = (test_features - mean) / std

        train_prices = prices[train_idx]
        test_prices_fold = prices[test_idx]

        # Train DQN on this fold
        env = TradingEnv(train_prices, train_norm, window=window, commission=commission)
        fold_result = train_dqn(
            env,
            hidden_size=hidden_size,
            num_episodes=num_episodes,
            batch_size=batch_size,
            gamma=gamma,
            lr=lr,
            eps_start=eps_start,
            eps_end=eps_end,
            eps_decay=eps_decay,
            replay_size=replay_size,
            target_update=target_update,
            device=device,
        )

        # Evaluate greedy policy on test fold
        test_env = TradingEnv(test_prices_fold, test_norm, window=window, commission=commission)
        oos_eval = evaluate_dqn(fold_result["model"], test_env, device=device, num_episodes=1)

        fold_results.append({
            "fold": fold_idx,
            "train_size": len(train_idx),
            "test_size": len(test_idx),
            "oos_reward": oos_eval["oos_mean_reward"],
            "in_sample_reward": fold_result["metrics"]["mean_reward"],
        })

        # Direction accuracy: did agent's test reward have correct sign vs buy-and-hold?
        test_returns = np.diff(test_prices_fold) / test_prices_fold[:-1]
        buy_hold_return = float(test_returns.sum())
        agent_return = oos_eval["oos_mean_reward"]
        if np.sign(agent_return) == np.sign(buy_hold_return):
            oos_direction_correct += 1
        oos_direction_total += 1

        # Select best fold model by in-sample reward, NOT OOS (issue #722)
        in_sample_reward = fold_result["metrics"]["mean_reward"]
        if in_sample_reward > best_fold_reward:
            best_fold_reward = in_sample_reward
            best_model = fold_result["model"]

        print(f"  Fold {fold_idx+1}/{n_splits}  oos_reward={oos_eval['oos_mean_reward']:.4f}  "
              f"train={len(train_idx)}  test={len(test_idx)}")

    oos_diracc = oos_direction_correct / max(1, oos_direction_total)

    # Majority-class baseline for direction (up vs down)
    returns = np.diff(prices) / prices[:-1]
    directions = (returns > 0).astype(int)
    y_train_proxy = directions[: len(directions) // 2]
    y_test_proxy = directions[len(directions) // 2 :]
    majority_bl = majority_class_baseline(y_train_proxy, y_test_proxy)

    return {
        "model": best_model,
        "metrics": {
            "oos_direction_accuracy": round(oos_diracc, 4),
            "majority_class_acc": majority_bl["accuracy"],
            "majority_class_freq": majority_bl["majority_freq"],
            "vs_majority_class": round(oos_diracc - majority_bl["accuracy"], 4),
            "n_wf_folds": len(fold_results),
        },
        "fold_details": fold_results,
        "history": {"fold_details": fold_results},
    }


def save_checkpoint(
    model, result: dict, hyperparams: dict, data_hash: str, checkpoint_dir: Path
) -> Path:
    """Save DQN checkpoint and metadata."""
    import torch

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    ckpt_path = checkpoint_dir / timestamp
    ckpt_path.mkdir(parents=True, exist_ok=True)

    model_file = ckpt_path / "model.pt"
    torch.save(model.state_dict(), model_file)

    metadata = {
        "timestamp": timestamp,
        "model_type": "dqn",
        "hyperparams": hyperparams,
        "metrics": result["metrics"],
        "episode_rewards": [float(x) for x in result["episode_rewards"][-50:]],
        "data_hash": data_hash,
        "architecture": {
            "state_size": int(result["state_size"]),
            "hidden_size": int(result["hidden_size"]),
            "n_actions": int(result["n_actions"]),
        },
        "files": ["model.pt", "metadata.json"],
    }
    meta_file = ckpt_path / "metadata.json"
    meta_file.write_text(json.dumps(metadata, indent=2), encoding="utf-8")

    print(f"Checkpoint saved: {ckpt_path}")
    print(f"  Metrics: {result['metrics']}")
    return ckpt_path


def main():
    parser = argparse.ArgumentParser(
        description="Train DQN RL agent for financial trading"
    )
    parser.add_argument(
        "--data-dir",
        default=str(Path(__file__).resolve().parent.parent / "datasets" / "yfinance"),
    )
    parser.add_argument("--symbol", default="SPY")
    parser.add_argument("--start")
    parser.add_argument("--end")
    parser.add_argument("--hidden-size", type=int, default=256)
    parser.add_argument("--window", type=int, default=20, help="State lookback window")
    parser.add_argument("--num-episodes", type=int, default=200)
    parser.add_argument("--batch-size", type=int, default=64)
    parser.add_argument("--gamma", type=float, default=0.99, help="Discount factor")
    parser.add_argument("--lr", type=float, default=1e-3)
    parser.add_argument("--eps-start", type=float, default=1.0, help="Initial epsilon")
    parser.add_argument("--eps-end", type=float, default=0.01, help="Final epsilon")
    parser.add_argument("--eps-decay", type=float, default=0.995)
    parser.add_argument("--replay-size", type=int, default=50000)
    parser.add_argument("--target-update", type=int, default=10)
    parser.add_argument("--commission", type=float, default=0.001, help="Trading commission")
    parser.add_argument("--lookback", type=int, default=20)
    parser.add_argument("--test-ratio", type=float, default=0.2, help="Fraction of data for OOS test set")
    parser.add_argument("--val-ratio", type=float, default=0.0, help="Fraction of training data for validation (0=disabled)")
    parser.add_argument(
        "--checkpoint-dir",
        default=str(Path(__file__).resolve().parent.parent / "checkpoints" / "dqn"),
    )
    parser.add_argument("--dry-run", action="store_true", help="Synthetic, 50 episodes")
    parser.add_argument(
        "--intermediate-save-every", type=int, default=0,
        help="Save best_state every N episodes (0 = disabled). Useful for crash-resilient long runs.",
    )
    parser.add_argument(
        "--intermediate-save-dir", default=None,
        help="Directory for intermediate best_state.pt + progress.json (defaults to checkpoint-dir/intermediate)",
    )
    parser.add_argument(
        "--advanced", action="store_true",
        help="Use advanced features (regime, momentum, statistical, price_acceleration)",
    )
    parser.add_argument(
        "--indicators", nargs="+", default=None,
        help="Specific indicators to use (overrides --advanced)",
    )
    parser.add_argument(
        "--walk-forward", action="store_true",
        help="Use walk-forward cross-validation instead of simple split",
    )
    parser.add_argument("--n-splits", type=int, default=5, help="Walk-forward splits")
    parser.add_argument("--wf-train-size", type=int, default=None, help="Walk-forward train window (None=expanding)")
    parser.add_argument("--wf-test-size", type=int, default=None, help="Walk-forward test window per fold")
    parser.add_argument("--gap", type=int, default=5, help="Gap between train and test in walk-forward")
    args = parser.parse_args()

    try:
        import torch

        device = "cuda" if torch.cuda.is_available() else "cpu"
    except ImportError:
        print("ERROR: PyTorch not installed. Run: pip install torch", file=sys.stderr)
        sys.exit(1)

    if args.dry_run:
        print("DRY-RUN: Using synthetic data (2000 rows, 10 episodes)")
        raw = generate_synthetic_data(2000)
        data_hash = "synthetic-dryrun"
        args.num_episodes = 10
    else:
        data_dir = Path(args.data_dir)
        if not data_dir.exists():
            print(f"ERROR: Data directory not found: {data_dir}", file=sys.stderr)
            sys.exit(1)
        raw = load_data(data_dir, args.symbol, args.start, args.end)
        data_hash = compute_data_hash(raw)
        print(f"Loaded {len(raw)} rows for {args.symbol}")

    if args.indicators:
        indicators = args.indicators
    elif args.advanced:
        indicators = FeatureEngineer.ALL_INDICATORS
    else:
        indicators = [
            "returns", "volatility", "volume_ratio", "ma_ratios",
            "rsi", "macd", "bollinger", "true_range_atr", "obv",
        ]

    engineer = FeatureEngineer(lookback=args.lookback, indicators=indicators)
    features_df = engineer.transform(raw, add_target=False)
    feature_cols = [c for c in features_df.columns]
    features_arr = features_df.values.astype(np.float32)

    prices = raw.loc[features_df.index, "Close"].values.astype(np.float32)

    hyperparams = {
        "model_type": "dqn",
        "hidden_size": args.hidden_size,
        "window": args.window,
        "num_episodes": args.num_episodes,
        "batch_size": args.batch_size,
        "gamma": args.gamma,
        "lr": args.lr,
        "eps_start": args.eps_start,
        "eps_end": args.eps_end,
        "eps_decay": args.eps_decay,
        "replay_size": args.replay_size,
        "target_update": args.target_update,
        "commission": args.commission,
        "lookback": args.lookback,
        "symbol": args.symbol,
        "device": device,
        "test_ratio": args.test_ratio,
    }

    # --- Walk-forward mode ---
    if args.walk_forward:
        print(f"Mode: WALK-FORWARD (n_splits={args.n_splits}, gap={args.gap})")
        hyperparams.update({
            "walk_forward": True,
            "n_splits": args.n_splits,
            "wf_train_size": args.wf_train_size,
            "wf_test_size": args.wf_test_size,
            "gap": args.gap,
        })

        wf_result = train_walk_forward_dqn(
            prices,
            features_arr,
            window=args.window,
            commission=args.commission,
            hidden_size=args.hidden_size,
            num_episodes=args.num_episodes,
            batch_size=args.batch_size,
            gamma=args.gamma,
            lr=args.lr,
            eps_start=args.eps_start,
            eps_end=args.eps_end,
            eps_decay=args.eps_decay,
            replay_size=args.replay_size,
            target_update=args.target_update,
            device=device,
            n_splits=args.n_splits,
            train_size=args.wf_train_size,
            test_size=args.wf_test_size,
            gap=args.gap,
        )

        ckpt_dir = Path(args.checkpoint_dir)
        if wf_result["model"] is not None:
            save_checkpoint(wf_result["model"], {
                "metrics": wf_result["metrics"],
                "episode_rewards": [],
                "episode_trades": [],
                "state_size": 0,
                "hidden_size": args.hidden_size,
                "n_actions": 3,
            }, hyperparams, data_hash, ckpt_dir)

        m = wf_result["metrics"]
        print(f"\nWalk-Forward OOS Results:")
        print(f"  OOS DirAcc:     {m['oos_direction_accuracy']:.4f}")
        print(f"  Majority Class: {m['majority_class_acc']:.4f} (freq={m['majority_class_freq']:.4f})")
        print(f"  vs Majority:    {m['vs_majority_class']:+.4f}")
        print(f"  Folds:          {m['n_wf_folds']}")

        if args.dry_run:
            print("DRY-RUN complete. Walk-forward pipeline validated.")
        return

    # --- Simple split mode (default) ---

    # Normalize features using training portion only (avoid lookahead bias)
    n = len(features_arr)
    train_end = int(n * (1 - args.test_ratio))
    mean = features_arr[:train_end].mean(axis=0)
    std = features_arr[:train_end].std(axis=0)
    std = np.where(std < 1e-8, 1.0, std)
    features_arr = (features_arr - mean) / std

    # Train/test split (time-series: train = first 80%, test = last 20%)
    train_prices = prices[:train_end]
    train_features = features_arr[:train_end]
    test_prices = prices[train_end:]
    test_features = features_arr[train_end:]

    print(f"Features: {len(features_df)} rows, {len(feature_cols)} columns")
    print(f"Train/test split: {len(train_prices)} train ({100*(1-args.test_ratio):.0f}%) / "
          f"{len(test_prices)} test ({100*args.test_ratio:.0f}%)")
    print(f"Device: {device}")

    env = TradingEnv(train_prices, train_features, window=args.window, commission=args.commission)
    print(f"State size: {env.state_size}, Actions: 3 (hold/buy/sell)")

    hyperparams.update({
        "train_samples": len(train_prices),
        "test_samples": len(test_prices),
    })

    intermediate_dir = None
    if args.intermediate_save_every > 0:
        intermediate_dir = (
            Path(args.intermediate_save_dir)
            if args.intermediate_save_dir
            else Path(args.checkpoint_dir) / "intermediate"
        )

    result = train_dqn(
        env,
        hidden_size=args.hidden_size,
        num_episodes=args.num_episodes,
        batch_size=args.batch_size,
        gamma=args.gamma,
        lr=args.lr,
        eps_start=args.eps_start,
        eps_end=args.eps_end,
        eps_decay=args.eps_decay,
        replay_size=args.replay_size,
        target_update=args.target_update,
        device=device,
        intermediate_save_every=args.intermediate_save_every,
        intermediate_save_dir=intermediate_dir,
    )

    ckpt_dir = Path(args.checkpoint_dir)
    save_checkpoint(result["model"], result, hyperparams, data_hash, ckpt_dir)

    # Out-of-sample evaluation on test set
    test_env = TradingEnv(test_prices, test_features, window=args.window, commission=args.commission)
    oos_metrics = evaluate_dqn(result["model"], test_env, device=device)
    result["oos_metrics"] = oos_metrics

    # Update saved metadata with OOS results
    import glob
    ckpt_subdirs = sorted(ckpt_dir.glob("*"))
    if ckpt_subdirs:
        latest_meta = ckpt_subdirs[-1] / "metadata.json"
        if latest_meta.exists():
            meta = json.loads(latest_meta.read_text(encoding="utf-8"))
            meta["oos_metrics"] = oos_metrics
            latest_meta.write_text(json.dumps(meta, indent=2), encoding="utf-8")

    o = oos_metrics
    m = result["metrics"]
    print(f"Training complete (in-sample). MeanReward={m['mean_reward']}, Sharpe~={m['sharpe_estimate']}")
    print(f"OOS evaluation.       MeanReward={o['oos_mean_reward']}, OOS Sharpe={o['oos_sharpe']}")

    if args.dry_run:
        print("DRY-RUN complete. Pipeline validated successfully.")


if __name__ == "__main__":
    main()
