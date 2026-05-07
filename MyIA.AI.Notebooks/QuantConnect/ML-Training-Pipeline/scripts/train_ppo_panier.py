"""
PPO multi-asset training for crypto panier portfolio allocation.

Trains a PPO agent to allocate across 10 crypto assets using
daily OHLCV data. Uses walk-forward evaluation with BEATS criterion.

Crypto panier: BTC, ETH, LTC, XRP, ADA, LINK, SOL, MATIC, AVAX, DOT
Data: daily OHLCV, 2020-2026.

References:
    - Schulman et al., "Proximal Policy Optimization Algorithms" (2017)
    - QC-Py-33: PPO trading notebook (single asset baseline)
    - BEATS criterion: mean_edge >= 2*std_edge across seeds

Usage:
    # Dry-run (synthetic data, 10 episodes)
    python train_ppo_panier.py --dry-run

    # Full training
    python train_ppo_panier.py --episodes 1000 --seeds 0,1,7,42

    # CPU only
    python train_ppo_panier.py --episodes 500 --device cpu
"""

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime
from pathlib import Path

import numpy as np
import pandas as pd
import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.distributions import Categorical

sys.path.insert(0, str(Path(__file__).resolve().parent))

from graph_builder import CRYPTO_PANIER_SYMBOLS, load_crypto_panier

try:
    from shared.gpu_training import batch_thermal_check, setup_amp
except ImportError:
    def batch_thermal_check(*a, **kw):
        pass
    def setup_amp():
        return False, None


# ---------------------------------------------------------------------------
# Multi-asset trading environment
# ---------------------------------------------------------------------------

class MultiAssetEnv:
    """Multi-asset crypto trading environment for RL.

    State: rolling features per asset (returns, volatility, momentum, RSI)
    Action: portfolio weights (softmax output -> target allocation)
    Reward: risk-adjusted portfolio return (Sharpe-like)

    The agent outputs allocation weights across N assets. Each step
    represents one trading day.
    """

    def __init__(
        self,
        returns: np.ndarray,
        lookback: int = 20,
        cost_bp: float = 10.0,
    ):
        self.returns = returns  # (T, N)
        self.n_assets = returns.shape[1]
        self.lookback = lookback
        self.cost_bp = cost_bp / 10000.0
        self.reset()

    def reset(self) -> np.ndarray:
        self.t = self.lookback
        self.weights = np.ones(self.n_assets) / self.n_assets
        self.portfolio_value = 1.0
        self.history = [1.0]
        return self._get_state()

    def _get_state(self) -> np.ndarray:
        t = self.t
        lb = self.lookback
        window = self.returns[t - lb:t]  # (lb, N)

        features = []
        for i in range(self.n_assets):
            asset_ret = window[:, i]
            features.append(asset_ret[-1])                           # last return
            features.append(np.std(asset_ret))                       # volatility
            features.append(np.sum(asset_ret))                       # momentum
            features.append(self._rsi(asset_ret))                    # RSI-14
            features.append(np.mean(asset_ret[-5:]))                 # 5d mean
            features.append(np.std(asset_ret[-5:]) / (np.abs(np.mean(asset_ret[-5:])) + 1e-8))  # sharpe-like

        # Add current weights
        features.extend(self.weights.tolist())
        return np.array(features, dtype=np.float32)

    @staticmethod
    def _rsi(returns: np.ndarray, period: int = 14) -> float:
        gains = np.where(returns > 0, returns, 0)
        losses = np.where(returns < 0, -returns, 0)
        avg_gain = np.mean(gains[-period:]) if len(gains) >= period else np.mean(gains)
        avg_loss = np.mean(losses[-period:]) if len(losses) >= period else np.mean(losses)
        if avg_loss < 1e-10:
            return 100.0
        rs = avg_gain / avg_loss
        return 100.0 - (100.0 / (1.0 + rs))

    def step(self, action: np.ndarray) -> tuple:
        new_weights = action / (action.sum() + 1e-10)

        # Transaction costs
        turnover = np.sum(np.abs(new_weights - self.weights))
        cost = turnover * self.cost_bp

        # Portfolio return
        if self.t < len(self.returns):
            daily_ret = np.dot(self.returns[self.t], new_weights)
        else:
            daily_ret = 0.0

        net_ret = daily_ret - cost
        self.portfolio_value *= (1.0 + net_ret)
        self.history.append(self.portfolio_value)

        # Reward: risk-adjusted return
        if len(self.history) > 20:
            recent = np.diff(np.log(np.array(self.history[-20:]) + 1e-10))
            sharpe = np.mean(recent) / (np.std(recent) + 1e-10) * np.sqrt(252)
            reward = sharpe * 0.01 + net_ret
        else:
            reward = net_ret

        self.weights = new_weights
        self.t += 1

        done = self.t >= len(self.returns)
        return self._get_state() if not done else np.zeros_like(self._get_state()), reward, done


# ---------------------------------------------------------------------------
# Actor-Critic network
# ---------------------------------------------------------------------------

class ActorCritic(nn.Module):
    """Shared backbone with actor (policy) and critic (value) heads."""

    def __init__(self, state_dim: int, n_assets: int, hidden: int = 256):
        super().__init__()
        self.backbone = nn.Sequential(
            nn.Linear(state_dim, hidden),
            nn.ReLU(),
            nn.Linear(hidden, hidden),
            nn.ReLU(),
        )
        self.actor = nn.Sequential(
            nn.Linear(hidden, n_assets),
        )
        self.critic = nn.Linear(hidden, 1)
        self._init_weights()

    def _init_weights(self):
        for m in self.modules():
            if isinstance(m, nn.Linear):
                nn.init.orthogonal_(m.weight, gain=np.sqrt(2))
                nn.init.zeros_(m.bias)

    def forward(self, x: torch.Tensor) -> tuple:
        h = self.backbone(x)
        logits = self.actor(h)
        value = self.critic(h)
        return logits, value

    def get_action(self, state: torch.Tensor, deterministic: bool = False):
        logits, value = self.forward(state)
        # Softmax over assets for portfolio weights
        probs = F.softmax(logits, dim=-1)
        dist = Categorical(probs)

        if deterministic:
            action = probs.argmax(dim=-1)
        else:
            action = dist.sample()

        return action, dist.log_prob(action), value.squeeze(-1), dist.entropy()


# ---------------------------------------------------------------------------
# PPO Agent
# ---------------------------------------------------------------------------

class PPOAgent:
    def __init__(
        self,
        state_dim: int,
        n_assets: int,
        hidden: int = 256,
        lr: float = 3e-4,
        gamma: float = 0.99,
        gae_lambda: float = 0.95,
        clip_eps: float = 0.2,
        entropy_coef: float = 0.01,
        value_coef: float = 0.5,
        ppo_epochs: int = 4,
        batch_size: int = 64,
        device: str = "cpu",
    ):
        self.device = device
        self.model = ActorCritic(state_dim, n_assets, hidden).to(device)
        self.optimizer = torch.optim.Adam(self.model.parameters(), lr=lr)

        self.gamma = gamma
        self.gae_lambda = gae_lambda
        self.clip_eps = clip_eps
        self.entropy_coef = entropy_coef
        self.value_coef = value_coef
        self.ppo_epochs = ppo_epochs
        self.batch_size = batch_size

    def select_action(self, state: np.ndarray, deterministic: bool = False):
        state_t = torch.tensor(state, dtype=torch.float32).unsqueeze(0).to(self.device)
        with torch.no_grad():
            action, log_prob, value, entropy = self.model.get_action(state_t, deterministic)
        return (
            action.item(),
            log_prob.item(),
            value.item(),
            entropy.item(),
        )

    def weights_from_action(self, action: int) -> np.ndarray:
        """Convert discrete action to portfolio weights.

        Action space: N+1 options.
        0 = equal weight, 1..N = concentrate on single asset.
        """
        w = np.zeros(self.model.actor[0].out_features)
        if action == 0:
            w[:] = 1.0 / len(w)
        else:
            w[action - 1] = 1.0
        return w

    def update(self, rollout: dict) -> dict:
        states = torch.tensor(np.array(rollout["states"]), dtype=torch.float32).to(self.device)
        actions = torch.tensor(rollout["actions"], dtype=torch.long).to(self.device)
        old_log_probs = torch.tensor(rollout["log_probs"], dtype=torch.float32).to(self.device)
        returns = torch.tensor(rollout["returns"], dtype=torch.float32).to(self.device)
        advantages = torch.tensor(rollout["advantages"], dtype=torch.float32).to(self.device)

        advantages = (advantages - advantages.mean()) / (advantages.std() + 1e-8)

        total_loss = 0.0
        n_updates = 0

        for _ in range(self.ppo_epochs):
            indices = np.random.permutation(len(states))
            for start in range(0, len(states), self.batch_size):
                idx = indices[start:start + self.batch_size]

                logits, values = self.model(states[idx])
                probs = F.softmax(logits, dim=-1)
                dist = Categorical(probs)
                new_log_probs = dist.log_prob(actions[idx])
                entropy = dist.entropy().mean()

                ratio = torch.exp(new_log_probs - old_log_probs[idx])
                surr1 = ratio * advantages[idx]
                surr2 = torch.clamp(ratio, 1 - self.clip_eps, 1 + self.clip_eps) * advantages[idx]
                actor_loss = -torch.min(surr1, surr2).mean()

                critic_loss = F.mse_loss(values.squeeze(-1), returns[idx])

                loss = actor_loss + self.value_coef * critic_loss - self.entropy_coef * entropy

                self.optimizer.zero_grad()
                loss.backward()
                nn.utils.clip_grad_norm_(self.model.parameters(), 0.5)
                self.optimizer.step()

                total_loss += loss.item()
                n_updates += 1

        return {"loss": total_loss / max(n_updates, 1)}


def compute_gae(rewards, values, dones, gamma, gae_lambda):
    """Compute GAE advantages and returns."""
    advantages = []
    returns = []
    gae = 0.0
    next_value = 0.0

    for t in reversed(range(len(rewards))):
        if dones[t]:
            next_value = 0.0
            gae = 0.0

        delta = rewards[t] + gamma * next_value * (1 - dones[t]) - values[t]
        gae = delta + gamma * gae_lambda * (1 - dones[t]) * gae
        advantages.insert(0, gae)
        returns.insert(0, gae + values[t])
        next_value = values[t]

    return advantages, returns


# ---------------------------------------------------------------------------
# Training loop
# ---------------------------------------------------------------------------

def train_episode(
    agent: PPOAgent,
    env: MultiAssetEnv,
    max_steps: int | None = None,
) -> dict:
    """Run one episode and return rollout data + metrics."""
    state = env.reset()
    rollout = {"states": [], "actions": [], "log_probs": [], "values": [], "rewards": [], "dones": []}

    total_reward = 0.0
    steps = 0
    limit = max_steps or len(env.returns)

    while steps < limit:
        action, log_prob, value, entropy = agent.select_action(state)
        weights = agent.weights_from_action(action)

        next_state, reward, done = env.step(weights)

        rollout["states"].append(state)
        rollout["actions"].append(action)
        rollout["log_probs"].append(log_prob)
        rollout["values"].append(value)
        rollout["rewards"].append(reward)
        rollout["dones"].append(float(done))

        total_reward += reward
        steps += 1
        state = next_state

        if done:
            break

    # Compute GAE
    advantages, returns = compute_gae(
        rollout["rewards"], rollout["values"], rollout["dones"],
        agent.gamma, agent.gae_lambda,
    )
    rollout["advantages"] = advantages
    rollout["returns"] = returns

    # Episode metrics
    portfolio_return = (env.portfolio_value - 1.0) * 100
    n_trades = steps

    # Buy-and-hold baseline
    bh_returns = env.returns[env.lookback:env.lookback + steps]
    if len(bh_returns) > 0:
        bh_weights = np.ones(env.n_assets) / env.n_assets
        bh_portfolio = np.cumprod(1 + bh_returns @ bh_weights)
        bh_return = (bh_portfolio[-1] - 1.0) * 100 if len(bh_portfolio) > 0 else 0.0
    else:
        bh_return = 0.0

    return {
        "rollout": rollout,
        "total_reward": total_reward,
        "portfolio_return_pct": portfolio_return,
        "buy_hold_return_pct": bh_return,
        "edge_over_bh": portfolio_return - bh_return,
        "steps": steps,
        "final_value": env.portfolio_value,
    }


def train_and_evaluate(
    returns: np.ndarray,
    n_episodes: int = 1000,
    hidden: int = 256,
    lr: float = 3e-4,
    gamma: float = 0.99,
    lookback: int = 20,
    cost_bp: float = 10.0,
    device: str = "cpu",
    train_ratio: float = 0.7,
    seed: int = 42,
) -> dict:
    """Train PPO agent on train split, evaluate on test split."""
    np.random.seed(seed)
    torch.manual_seed(seed)

    n = len(returns)
    train_end = int(n * train_ratio)

    train_returns = returns[:train_end]
    test_returns = returns[train_end:]

    env = MultiAssetEnv(train_returns, lookback=lookback, cost_bp=cost_bp)
    state_dim = len(env._get_state())

    agent = PPOAgent(
        state_dim=state_dim,
        n_assets=env.n_assets,
        hidden=hidden,
        lr=lr,
        gamma=gamma,
        device=device,
    )

    print(f"PPO panier: {env.n_assets} assets, state_dim={state_dim}, "
          f"hidden={hidden}, episodes={n_episodes}, device={device}")

    episode_log = []
    best_value = 0.0
    best_state = None

    for ep in range(n_episodes):
        result = train_episode(agent, env, max_steps=len(train_returns) - lookback)

        update_info = agent.update(result["rollout"])

        episode_log.append({
            "episode": ep,
            "reward": result["total_reward"],
            "portfolio_return": result["portfolio_return_pct"],
            "bh_return": result["buy_hold_return_pct"],
            "edge": result["edge_over_bh"],
            "steps": result["steps"],
            "final_value": result["final_value"],
            "loss": update_info["loss"],
        })

        if result["final_value"] > best_value:
            best_value = result["final_value"]
            best_state = {k: v.cpu().clone() for k, v in agent.model.state_dict().items()}

        if (ep + 1) % 100 == 0 or ep == 0:
            recent = episode_log[-min(100, len(episode_log)):]
            avg_edge = np.mean([e["edge"] for e in recent])
            avg_ret = np.mean([e["portfolio_return"] for e in recent])
            print(f"  Ep {ep+1}/{n_episodes}: Ret={avg_ret:.2f}%, "
                  f"BH-edge={avg_edge:+.2f}%, Loss={update_info['loss']:.4f}")

        # Re-reset environment for next episode
        env.reset()

    # Evaluate on test set
    if best_state is not None:
        agent.model.load_state_dict(best_state)

    test_env = MultiAssetEnv(test_returns, lookback=lookback, cost_bp=cost_bp)
    test_result = train_episode(agent, test_env, max_steps=len(test_returns) - lookback)

    # Buy-and-hold on test
    bh_rets = test_returns[lookback:lookback + test_result["steps"]]
    bh_weights = np.ones(env.n_assets) / env.n_assets
    bh_portfolio = np.cumprod(1 + bh_rets @ bh_weights)
    bh_test_return = (bh_portfolio[-1] - 1.0) * 100 if len(bh_portfolio) > 0 else 0.0

    oos_edge = test_result["portfolio_return_pct"] - bh_test_return

    metrics = {
        "train_episodes": n_episodes,
        "train_final_value": episode_log[-1]["final_value"] if episode_log else 0.0,
        "best_train_value": best_value,
        "oos_portfolio_return_pct": round(test_result["portfolio_return_pct"], 2),
        "oos_buy_hold_return_pct": round(bh_test_return, 2),
        "oos_edge_over_bh": round(oos_edge, 2),
        "seed": seed,
    }

    return {
        "metrics": metrics,
        "episode_log": episode_log,
        "model": agent.model,
    }


# ---------------------------------------------------------------------------
# Multi-seed evaluation
# ---------------------------------------------------------------------------

def run_multi_seed(
    returns: np.ndarray,
    seeds: list[int],
    n_episodes: int = 1000,
    hidden: int = 256,
    lr: float = 3e-4,
    device: str = "cpu",
    train_ratio: float = 0.7,
) -> dict:
    assert len(seeds) >= 4, f"Need >=4 seeds, got {len(seeds)}"

    results = []
    for seed in seeds:
        print(f"\n--- Seed {seed} ---")
        result = train_and_evaluate(
            returns, n_episodes=n_episodes, hidden=hidden,
            lr=lr, device=device, train_ratio=train_ratio, seed=seed,
        )
        m = result["metrics"]
        results.append({"seed": seed, "metrics": m})
        print(f"  OOS: Ret={m['oos_portfolio_return_pct']:.2f}%, "
              f"BH={m['oos_buy_hold_return_pct']:.2f}%, "
              f"Edge={m['oos_edge_over_bh']:+.2f}%")

    edges = [r["metrics"]["oos_edge_over_bh"] for r in results]
    mean_edge = np.mean(edges)
    std_edge = np.std(edges)
    beats = mean_edge >= 2 * std_edge if std_edge > 0 else mean_edge > 0

    summary = {
        "model": "ppo_panier",
        "n_seeds": len(seeds),
        "seeds": seeds,
        "n_episodes": n_episodes,
        "mean_edge": round(float(mean_edge), 4),
        "std_edge": round(float(std_edge), 4),
        "beats_claim": bool(beats),
        "beats_criterion": f"mean_edge({mean_edge:.4f}) >= 2*std_edge({2*std_edge:.4f})"
                           if std_edge > 0 else f"mean_edge({mean_edge:.4f}) > 0",
        "per_seed": results,
    }

    print(f"\n=== Multi-seed PPO Panier ({len(seeds)} seeds, {n_episodes} ep) ===")
    print(f"  Mean Edge: {mean_edge:+.4f}% +/- {std_edge:.4f}")
    print(f"  BEATS: {'YES' if beats else 'NO'} ({summary['beats_criterion']})")

    return summary


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Train PPO agent for multi-asset crypto panier allocation"
    )
    parser.add_argument("--episodes", type=int, default=1000)
    parser.add_argument("--hidden", type=int, default=256)
    parser.add_argument("--lr", type=float, default=3e-4)
    parser.add_argument("--gamma", type=float, default=0.99)
    parser.add_argument("--lookback", type=int, default=20)
    parser.add_argument("--cost-bp", type=float, default=10.0, help="Transaction cost in basis points")
    parser.add_argument("--train-ratio", type=float, default=0.7)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--seeds", type=str, default=None, help="Comma-separated seeds for multi-seed eval")
    parser.add_argument("--device", default="auto")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--output-dir",
                        default=str(Path(__file__).resolve().parent.parent / "outputs" / "ppo_panier"))
    args = parser.parse_args()

    if args.device == "auto":
        device = "cuda" if torch.cuda.is_available() else "cpu"
    else:
        device = args.device

    if args.dry_run:
        print("DRY-RUN: Synthetic crypto data (10 assets, 10 episodes)")
        np.random.seed(args.seed)
        n_days, n_assets = 500, 10
        symbols = CRYPTO_PANIER_SYMBOLS[:n_assets]
        returns = np.random.randn(n_days, n_assets).astype(np.float32) * 0.02
        args.episodes = 10
        if args.seeds is None:
            args.seeds = "0,1,7,42"
    else:
        closes = load_crypto_panier()
        symbols = list(closes.columns)
        print(f"Loaded: {len(closes)} days, {len(symbols)} assets")
        returns = closes.pct_change().dropna().values.astype(np.float32)

    if args.seeds:
        seeds = [int(s.strip()) for s in args.seeds.split(",")]
        summary = run_multi_seed(
            returns, seeds,
            n_episodes=args.episodes, hidden=args.hidden,
            lr=args.lr, device=device, train_ratio=args.train_ratio,
        )
        output_dir = Path(args.output_dir)
        output_dir.mkdir(parents=True, exist_ok=True)
        path = output_dir / f"ppo_multiseed_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        path.write_text(json.dumps(summary, indent=2, default=str), encoding="utf-8")
        print(f"Summary: {path}")
    else:
        result = train_and_evaluate(
            returns, n_episodes=args.episodes, hidden=args.hidden,
            lr=args.lr, gamma=args.gamma, lookback=args.lookback,
            cost_bp=args.cost_bp, device=device,
            train_ratio=args.train_ratio, seed=args.seed,
        )
        m = result["metrics"]
        print(f"\nResults: OOS Ret={m['oos_portfolio_return_pct']:.2f}%, "
              f"BH={m['oos_buy_hold_return_pct']:.2f}%, "
              f"Edge={m['oos_edge_over_bh']:+.2f}%")

    if args.dry_run:
        print("DRY-RUN complete.")


if __name__ == "__main__":
    main()
