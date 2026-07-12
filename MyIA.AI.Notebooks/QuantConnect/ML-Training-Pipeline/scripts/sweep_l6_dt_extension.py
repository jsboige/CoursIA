"""
L6 Decision Transformer Extension sweep for Ladder #1409.

Extends the L4 Decision Transformer (action-only) with:
  1. Dual-head architecture: action head (buy/hold/sell) + size head (0.25/0.5/1.0)
  2. Cost-aware loss: cross-entropy(action) + cross-entropy(size) + tx cost penalty
  3. Portfolio simulation with variable position sizing

Same sweep protocol as L4: 26 symbols x 4 seeds (0/1/7/42) x 5-fold walk-forward.
Verdict: BEATS / NO BEATS / INCONCLUSIVE (>= 2 sigma edge cross-seed).

L4 found BEATS 24/26 symbols with action-only DT (median AUC 0.5582).
L6 hypothesis: adding size head + cost-aware loss improves risk-adjusted returns
by reducing unnecessary trades and adapting position size to conviction.

Architecture (DualHeadDecisionTransformer):
  - StateEncoder: Linear(state_dim, d_model) + LayerNorm + GELU
  - ActionEmbedding: Embedding(3, d_model) -- buy/hold/sell
  - SizeEmbedding: Embedding(3, d_model) -- 0.25/0.5/1.0 weight
  - ReturnToGoEmbedding: Linear(1, d_model)
  - SinusoidalPositionalEncoding
  - TransformerEncoder backbone
  - Action head: Linear(d_model, 3) -- action logits
  - Size head: Linear(d_model, 3) -- size logits

Cost-aware loss:
  L = CE(action) + alpha * CE(size) + beta * E[cost_penalty]
  where cost_penalty = |position_change| * commission_bps / 10000

Usage:
    # Full sweep (26 symbols, 4 seeds, 5-fold WF) -- ~1h on RTX 3080
    python sweep_l6_dt_extension.py

    # Subset
    python sweep_l6_dt_extension.py --symbols SPY QQQ TLT GLD --seeds 0 1 7 42

    # Smoke test (CPU-safe)
    python sweep_l6_dt_extension.py --smoke

References:
    - Chen et al. (2021): "Decision Transformer: RL via Sequence Modeling"
    - arXiv:2411.17900: "Decision Transformer for Algorithmic Trading"
    - L4 results: scripts/results/l4_decision_transformer/results.json (BEATS 24/26)
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np
import pandas as pd
import torch
import torch.nn as nn
import torch.nn.functional as F

SCRIPTS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS_DIR))

from panier_loader import (
    FORBIDDEN_SYMBOLS,
    get_panier_symbols,
    load_panier,
)
from train_rl_dt import SinusoidalPositionalEncoding

sys.path.insert(0, str(SCRIPTS_DIR.parent / "shared"))
from features import FeatureEngineer

try:
    from walk_forward import WalkForwardSplitter
except ImportError:
    WalkForwardSplitter = None

# Try thermal watchdog
try:
    from gpu_training import batch_thermal_check, get_gpu_temp, setup_amp, thermal_check
except ImportError:
    # No-op fallback -- see agent instructions for thermal safety
    def batch_thermal_check(*a, **kw):
        pass

    def get_gpu_temp():
        return 0

    def setup_amp():
        return False, None

    def thermal_check(*a, **kw):
        pass

RESULTS_DIR = SCRIPTS_DIR / "results" / "l6_dt_extension"

# ---------------------------------------------------------------------------
# Size classes for position sizing
# ---------------------------------------------------------------------------
SIZE_CLASSES = [0.25, 0.5, 1.0]  # portfolio weight multipliers
SIZE_NAMES = {0: "quarter", 1: "half", 2: "full"}
ACTION_NAMES = {0: "hold", 1: "buy", 2: "sell"}


# ---------------------------------------------------------------------------
# Dual-Head Decision Transformer Model
# ---------------------------------------------------------------------------


class DualHeadDecisionTransformer(nn.Module):
    """Decision Transformer with separate action and size prediction heads.

    Extends the base DecisionTransformerModel from train_rl_dt.py with:
      - Size embedding (3 classes: 0.25, 0.5, 1.0)
      - Size prediction head (Linear)
      - Cost-aware interleaving in the sequence representation

    The interleaved sequence per timestep t is:
        [rtg_t, state_t, action_t, size_t]
    This gives 4 tokens per timestep instead of 3 in L4.

    Parameters
    ----------
    state_dim : int
        Dimension of the state vector.
    d_model : int
        Transformer model dimension.
    nhead : int
        Number of attention heads.
    num_layers : int
        Number of transformer encoder layers.
    context_length : int
        Maximum sequence (context) length.
    n_actions : int
        Number of discrete actions (default: 3 for hold/buy/sell).
    n_sizes : int
        Number of discrete size classes (default: 3 for 0.25/0.5/1.0).
    dropout : float
        Dropout rate.
    """

    def __init__(
        self,
        state_dim: int,
        d_model: int = 128,
        nhead: int = 4,
        num_layers: int = 3,
        context_length: int = 20,
        n_actions: int = 3,
        n_sizes: int = 3,
        dropout: float = 0.1,
    ):
        super().__init__()
        self.state_dim = state_dim
        self.d_model = d_model
        self.n_actions = n_actions
        self.n_sizes = n_sizes
        self.context_length = context_length

        # State encoder
        self.state_encoder = nn.Sequential(
            nn.Linear(state_dim, d_model),
            nn.LayerNorm(d_model),
            nn.GELU(),
        )

        # Action embedding (3 actions: hold=0, buy=1, sell=2)
        self.action_embedding = nn.Embedding(n_actions, d_model)

        # Size embedding (3 sizes: 0.25=0, 0.5=1, 1.0=2)
        self.size_embedding = nn.Embedding(n_sizes, d_model)

        # Return-to-go embedding
        self.rtg_embedding = nn.Sequential(
            nn.Linear(1, d_model),
            nn.GELU(),
        )

        # Positional encoding (4 tokens per timestep now)
        self.pos_encoding = SinusoidalPositionalEncoding(
            d_model, max_len=context_length * 4 + 1, dropout=dropout
        )

        # Transformer backbone
        encoder_layer = nn.TransformerEncoderLayer(
            d_model=d_model,
            nhead=nhead,
            dim_feedforward=d_model * 4,
            dropout=dropout,
            activation="gelu",
            batch_first=True,
        )
        self.transformer = nn.TransformerEncoder(
            encoder_layer, num_layers=num_layers
        )

        # Layer norm before prediction heads
        self.ln_f = nn.LayerNorm(d_model)

        # Dual prediction heads
        self.action_head = nn.Linear(d_model, n_actions)
        self.size_head = nn.Linear(d_model, n_sizes)

        self._init_weights()

    def _init_weights(self):
        """Initialize weights with small values for stable training."""
        for module in self.modules():
            if isinstance(module, nn.Linear):
                nn.init.xavier_uniform_(module.weight)
                if module.bias is not None:
                    nn.init.zeros_(module.bias)
            elif isinstance(module, nn.Embedding):
                nn.init.normal_(module.weight, mean=0.0, std=0.02)

    def forward(
        self,
        states: torch.Tensor,
        actions: torch.Tensor,
        sizes: torch.Tensor,
        rtg: torch.Tensor,
        attention_mask: torch.Tensor | None = None,
    ) -> tuple[torch.Tensor, torch.Tensor]:
        """Forward pass through Dual-Head Decision Transformer.

        Args:
            states: [B, T, state_dim] state vectors.
            actions: [B, T] action indices (long).
            sizes: [B, T] size indices (long).
            rtg: [B, T, 1] return-to-go values.
            attention_mask: [B, T] optional mask (1=attend, 0=ignore).

        Returns:
            Tuple of:
              - action_logits: [B, T, n_actions]
              - size_logits: [B, T, n_sizes]
        """
        B, T, _ = states.shape

        # Embed each modality
        state_emb = self.state_encoder(states)  # [B, T, d_model]
        action_emb = self.action_embedding(actions)  # [B, T, d_model]
        size_emb = self.size_embedding(sizes)  # [B, T, d_model]
        rtg_emb = self.rtg_embedding(rtg)  # [B, T, d_model]

        # Interleave: [rtg_0, state_0, action_0, size_0, rtg_1, ...]
        # 4 tokens per timestep
        seq_len = T * 4
        sequence = torch.zeros(B, seq_len, self.d_model, device=states.device)
        sequence[:, 0::4, :] = rtg_emb
        sequence[:, 1::4, :] = state_emb
        sequence[:, 2::4, :] = action_emb
        sequence[:, 3::4, :] = size_emb

        # Add positional encoding
        sequence = self.pos_encoding(sequence)

        # Build attention mask for interleaved sequence
        if attention_mask is not None:
            # Expand mask: each timestep has 4 tokens
            interleaved_mask = attention_mask.unsqueeze(-1).expand(-1, -1, 4)
            interleaved_mask = interleaved_mask.reshape(B, seq_len)
            src_key_padding_mask = (interleaved_mask == 0).bool()
        else:
            src_key_padding_mask = None

        # Causal mask
        causal_mask = nn.Transformer.generate_square_subsequent_mask(
            seq_len, device=states.device
        )

        # Transformer
        out = self.transformer(
            sequence,
            mask=causal_mask,
            src_key_padding_mask=src_key_padding_mask,
        )  # [B, seq_len, d_model]

        # Extract state positions (index 1 in each 4-token block)
        state_positions = out[:, 1::4, :]  # [B, T, d_model]
        state_positions = self.ln_f(state_positions)

        # Predict actions and sizes from state positions
        action_logits = self.action_head(state_positions)  # [B, T, n_actions]
        size_logits = self.size_head(state_positions)  # [B, T, n_sizes]

        return action_logits, size_logits


# ---------------------------------------------------------------------------
# Trajectory building with size labels
# ---------------------------------------------------------------------------


def build_trajectories_with_size(
    prices: np.ndarray,
    features: np.ndarray,
    window: int = 20,
    context_length: int = 20,
    commission: float = 0.0005,
) -> dict:
    """Build offline RL trajectories with size labels.

    Extends build_trajectories from train_rl_dt.py by adding a size label
    at each timestep. Size is determined by conviction (momentum strength):
      - Weak signal (< 1% move): size_class=0 (0.25 weight)
      - Medium signal (1-3% move): size_class=1 (0.50 weight)
      - Strong signal (> 3% move): size_class=2 (1.0 weight)

    Args:
        prices: [N] price array.
        features: [N, F] feature array.
        window: Lookback window for state construction.
        context_length: Number of timesteps per trajectory.
        commission: Transaction cost per trade.

    Returns:
        Dict with keys: states, actions, sizes, rtg, rewards, attention_mask
    """
    n = len(prices)

    all_states = []
    all_actions = []
    all_sizes = []
    all_rtg = []
    all_rewards = []
    all_masks = []

    # Compute returns, actions, and sizes
    position = 0.0  # continuous position
    rewards = np.zeros(n, dtype=np.float32)
    actions = np.zeros(n, dtype=np.int64)
    sizes = np.zeros(n, dtype=np.int64)

    for i in range(1, n):
        price_change = (prices[i] - prices[i - 1]) / (prices[i - 1] + 1e-8)

        # Momentum signal for trajectory generation
        if i >= window:
            past_return = (prices[i - 1] - prices[i - window]) / (
                prices[i - window] + 1e-8
            )
        else:
            past_return = 0.0

        # Determine action
        if past_return > 0.01:
            action = 1  # buy
        elif past_return < -0.01:
            action = 2  # sell
        else:
            action = 0  # hold

        # Determine size based on conviction (momentum strength)
        abs_past = abs(past_return)
        if abs_past > 0.03:
            size_class = 2  # full weight (1.0)
        elif abs_past > 0.01:
            size_class = 1  # half weight (0.5)
        else:
            size_class = 0  # quarter weight (0.25)

        # Target position from action + size
        target_position = SIZE_CLASSES[size_class]
        if action == 2:
            target_position = 0.0  # sell = flat, not short
        elif action == 0:
            target_position = position  # hold current

        # Apply commission on position changes
        reward = position * price_change
        trade_size = abs(target_position - position)
        if trade_size > 0.001:
            reward -= trade_size * commission
        position = target_position

        rewards[i] = reward
        actions[i] = action
        sizes[i] = size_class

    # Compute return-to-go
    rtg = np.zeros(n, dtype=np.float32)
    rtg[-1] = rewards[-1]
    for i in range(n - 2, -1, -1):
        rtg[i] = rewards[i] + rtg[i + 1]

    # Build trajectory segments
    start_idx = window
    end_idx = n - context_length

    if end_idx <= start_idx:
        end_idx = n - 1
        context_length = end_idx - start_idx
        if context_length <= 0:
            context_length = 1
            start_idx = max(0, n - 2)

    for t in range(start_idx, n - context_length):
        feat_window = features[t - window : t]
        if feat_window.ndim == 1:
            feat_window = feat_window.reshape(-1, 1)
        state = feat_window.flatten()

        all_states.append(state)
        all_actions.append(actions[t])
        all_sizes.append(sizes[t])
        all_rtg.append(rtg[t])
        all_rewards.append(rewards[t])
        all_masks.append(1.0)

    if len(all_states) == 0:
        feat_window = features[0:window]
        if feat_window.ndim == 1:
            feat_window = feat_window.reshape(-1, 1)
        all_states.append(feat_window.flatten())
        all_actions.append(0)
        all_sizes.append(0)
        all_rtg.append(0.0)
        all_rewards.append(0.0)
        all_masks.append(1.0)

    return {
        "states": np.array(all_states, dtype=np.float32),
        "actions": np.array(all_actions, dtype=np.int64),
        "sizes": np.array(all_sizes, dtype=np.int64),
        "rtg": np.array(all_rtg, dtype=np.float32).reshape(-1, 1),
        "rewards": np.array(all_rewards, dtype=np.float32),
        "attention_mask": np.array(all_masks, dtype=np.float32),
    }


def create_sequence_batches_with_size(
    trajectories: dict,
    context_length: int = 20,
    batch_size: int = 32,
    shuffle: bool = True,
) -> list[dict]:
    """Create fixed-length sequence batches with size labels.

    Same as create_sequence_batches from train_rl_dt.py but includes sizes.

    Returns:
        List of batch dicts with states, actions, sizes, rtg, target_actions,
        target_sizes, mask.
    """
    n = len(trajectories["states"])
    if n <= context_length:
        context_length = max(1, n - 1)
        if context_length < 1:
            return []

    sequences = []
    for i in range(n - context_length):
        seq = {
            "states": trajectories["states"][i : i + context_length],
            "actions": trajectories["actions"][i : i + context_length],
            "sizes": trajectories["sizes"][i : i + context_length],
            "rtg": trajectories["rtg"][i : i + context_length],
            "target_actions": trajectories["actions"][
                i + 1 : i + context_length + 1
            ],
            "target_sizes": trajectories["sizes"][
                i + 1 : i + context_length + 1
            ],
            "attention_mask": trajectories["attention_mask"][
                i : i + context_length
            ],
        }
        # Pad targets if needed
        for key in ("target_actions", "target_sizes"):
            if len(seq[key]) < context_length:
                pad_len = context_length - len(seq[key])
                seq[key] = np.concatenate(
                    [seq[key], np.zeros(pad_len, dtype=np.int64)]
                )
        sequences.append(seq)

    if shuffle:
        indices = np.random.permutation(len(sequences))
        sequences = [sequences[i] for i in indices]

    batches = []
    for i in range(0, len(sequences), batch_size):
        batch_seqs = sequences[i : i + batch_size]
        batch = {
            "states": torch.tensor(
                np.stack([s["states"] for s in batch_seqs]), dtype=torch.float32
            ),
            "actions": torch.tensor(
                np.stack([s["actions"] for s in batch_seqs]), dtype=torch.long
            ),
            "sizes": torch.tensor(
                np.stack([s["sizes"] for s in batch_seqs]), dtype=torch.long
            ),
            "rtg": torch.tensor(
                np.stack([s["rtg"] for s in batch_seqs]), dtype=torch.float32
            ),
            "target_actions": torch.tensor(
                np.stack([s["target_actions"] for s in batch_seqs]),
                dtype=torch.long,
            ),
            "target_sizes": torch.tensor(
                np.stack([s["target_sizes"] for s in batch_seqs]),
                dtype=torch.long,
            ),
            "attention_mask": torch.tensor(
                np.stack([s["attention_mask"] for s in batch_seqs]),
                dtype=torch.float32,
            ),
        }
        batches.append(batch)

    return batches


# ---------------------------------------------------------------------------
# Cost-aware loss
# ---------------------------------------------------------------------------


def cost_aware_loss(
    action_logits: torch.Tensor,
    size_logits: torch.Tensor,
    target_actions: torch.Tensor,
    target_sizes: torch.Tensor,
    prev_actions: torch.Tensor,
    prev_sizes: torch.Tensor,
    commission_bps: float = 5.0,
    alpha: float = 0.5,
    beta: float = 0.1,
) -> torch.Tensor:
    """Compute cost-aware dual-head loss.

    L = CE(action) + alpha * CE(size) + beta * E[cost_penalty]

    The cost penalty penalizes position changes:
      position = SIZE_CLASSES[size] if action==buy else 0 if action==sell
      cost = |new_position - old_position| * commission

    Args:
        action_logits: [B, T, 3] action predictions.
        size_logits: [B, T, 3] size predictions.
        target_actions: [B, T] ground truth actions.
        target_sizes: [B, T] ground truth sizes.
        prev_actions: [B, T] previous timestep actions (for cost calc).
        prev_sizes: [B, T] previous timestep sizes (for cost calc).
        commission_bps: Transaction cost in basis points.
        alpha: Weight for size loss relative to action loss.
        beta: Weight for cost penalty relative to action loss.

    Returns:
        Scalar loss tensor.
    """
    B, T, _ = action_logits.shape
    commission = commission_bps / 10000.0

    # Action cross-entropy
    action_ce = F.cross_entropy(
        action_logits.reshape(-1, 3), target_actions.reshape(-1)
    )

    # Size cross-entropy
    size_ce = F.cross_entropy(
        size_logits.reshape(-1, 3), target_sizes.reshape(-1)
    )

    # Cost penalty: penalize predicted position changes
    with torch.no_grad():
        pred_actions = action_logits.argmax(dim=-1)  # [B, T]
        pred_sizes = size_logits.argmax(dim=-1)  # [B, T]

        # Compute positions from predicted action+size
        size_weights = torch.tensor(
            SIZE_CLASSES, dtype=torch.float32, device=action_logits.device
        )
        pred_position = size_weights[pred_sizes]  # [B, T]
        pred_position = torch.where(
            pred_actions == 2,  # sell -> flat
            torch.zeros_like(pred_position),
            pred_position,
        )
        pred_position = torch.where(
            pred_actions == 0,  # hold -> keep previous
            torch.zeros_like(pred_position),  # placeholder, overwritten below
            pred_position,
        )

        # Previous position from prev_actions and prev_sizes
        prev_position = size_weights[prev_sizes]
        prev_position = torch.where(
            prev_actions == 2,
            torch.zeros_like(prev_position),
            prev_position,
        )

        # For hold actions, position = previous position
        # Shift prev_position by 1 to get actual previous
        hold_mask = pred_actions == 0
        # Use rolled prev_position (shift right by 1)
        prev_pos_shifted = torch.roll(prev_position, shifts=1, dims=1)
        prev_pos_shifted[:, 0] = 0.0  # no position at t=0
        pred_position = torch.where(hold_mask, prev_pos_shifted, pred_position)

        # Cost = |position_change| * commission
        position_change = pred_position - torch.roll(pred_position, shifts=1, dims=1)
        position_change[:, 0] = pred_position[:, 0]
        cost_penalty = (position_change.abs() * commission).mean()

    total_loss = action_ce + alpha * size_ce + beta * cost_penalty
    return total_loss


# ---------------------------------------------------------------------------
# Training
# ---------------------------------------------------------------------------


def train_dual_head_dt(
    trajectories: dict,
    state_dim: int,
    d_model: int = 128,
    nhead: int = 4,
    num_layers: int = 3,
    context_length: int = 20,
    epochs: int = 15,
    batch_size: int = 32,
    lr: float = 1e-4,
    weight_decay: float = 1e-4,
    dropout: float = 0.1,
    commission_bps: float = 5.0,
    alpha: float = 0.5,
    beta: float = 0.1,
    device: str = "cpu",
) -> dict:
    """Train Dual-Head Decision Transformer on offline trajectories.

    Returns:
        Dict with model and metrics.
    """
    model = DualHeadDecisionTransformer(
        state_dim=state_dim,
        d_model=d_model,
        nhead=nhead,
        num_layers=num_layers,
        context_length=context_length,
        n_actions=3,
        n_sizes=3,
        dropout=dropout,
    ).to(device)

    total_params = sum(p.numel() for p in model.parameters() if p.requires_grad)

    optimizer = torch.optim.AdamW(
        model.parameters(), lr=lr, weight_decay=weight_decay
    )
    scheduler = torch.optim.lr_scheduler.CosineAnnealingWarmRestarts(
        optimizer, T_0=10, T_mult=2
    )

    use_amp, grad_scaler = setup_amp()

    best_loss = float("inf")
    best_state = None
    n_batches_total = 0

    for epoch in range(epochs):
        thermal_check(max_temp=80, cool_sleep=30)
        model.train()

        batches = create_sequence_batches_with_size(
            trajectories,
            context_length=context_length,
            batch_size=batch_size,
            shuffle=True,
        )

        if not batches:
            continue

        epoch_loss = 0.0
        n_batches = 0

        for batch in batches:
            batch_thermal_check(n_batches, check_every=5, max_temp=80, cool_sleep=30)

            states = batch["states"].to(device)
            actions = batch["actions"].to(device)
            sizes = batch["sizes"].to(device)
            rtg = batch["rtg"].to(device)
            target_actions = batch["target_actions"].to(device)
            target_sizes = batch["target_sizes"].to(device)
            mask = batch["attention_mask"].to(device)

            # Previous actions/sizes for cost computation (roll by 1)
            prev_actions = torch.roll(actions, shifts=1, dims=1)
            prev_actions[:, 0] = 0
            prev_sizes = torch.roll(sizes, shifts=1, dims=1)
            prev_sizes[:, 0] = 0

            optimizer.zero_grad()

            with torch.amp.autocast("cuda", enabled=use_amp):
                action_logits, size_logits = model(
                    states, actions, sizes, rtg, attention_mask=mask
                )
                loss = cost_aware_loss(
                    action_logits,
                    size_logits,
                    target_actions,
                    target_sizes,
                    prev_actions,
                    prev_sizes,
                    commission_bps=commission_bps,
                    alpha=alpha,
                    beta=beta,
                )

            if use_amp:
                grad_scaler.scale(loss).backward()
                grad_scaler.unscale_(optimizer)
                torch.nn.utils.clip_grad_norm_(model.parameters(), max_norm=1.0)
                grad_scaler.step(optimizer)
                grad_scaler.update()
            else:
                loss.backward()
                torch.nn.utils.clip_grad_norm_(model.parameters(), max_norm=1.0)
                optimizer.step()

            epoch_loss += loss.item()
            n_batches += 1
            n_batches_total += 1

        scheduler.step()
        avg_loss = epoch_loss / max(n_batches, 1)

        if avg_loss < best_loss:
            best_loss = avg_loss
            best_state = {k: v.cpu().clone() for k, v in model.state_dict().items()}

    # Load best model
    if best_state:
        model.load_state_dict(best_state)
    model.eval()

    return {
        "model": model,
        "metrics": {
            "best_train_loss": round(best_loss, 6),
            "total_params": total_params,
            "epochs_trained": epochs,
        },
    }


# ---------------------------------------------------------------------------
# Portfolio simulation with variable sizing
# ---------------------------------------------------------------------------


def compute_sharpe(returns: np.ndarray, annual_factor: int = 252) -> float:
    """Annualized Sharpe ratio from daily returns."""
    if len(returns) < 10:
        return 0.0
    mean = np.mean(returns)
    std = np.std(returns)
    if std < 1e-10:
        return 0.0
    return float(mean / std * np.sqrt(annual_factor))


def simulate_dual_head_portfolio(
    prices: np.ndarray,
    actions: np.ndarray,
    sizes: np.ndarray,
    commission_bps: float = 5.0,
) -> np.ndarray:
    """Simulate portfolio returns from dual-head DT predictions.

    Actions: 0=hold, 1=buy, 2=sell.
    Sizes: 0=0.25, 1=0.5, 2=1.0 portfolio weight.
    Transaction cost in basis points per trade.

    Key difference from L4: position size varies by size prediction.
    """
    n = len(actions)
    commission = commission_bps / 10000.0
    position = 0.0
    portfolio_returns = np.zeros(n, dtype=np.float64)

    for i in range(1, n):
        price_ret = (prices[i] - prices[i - 1]) / (prices[i - 1] + 1e-8)

        if actions[i] == 1:  # buy
            target_pos = SIZE_CLASSES[sizes[i]]
        elif actions[i] == 2:  # sell -> flat
            target_pos = 0.0
        else:  # hold
            target_pos = position

        trade_cost = abs(target_pos - position) * commission
        portfolio_returns[i] = position * price_ret - trade_cost
        position = target_pos

    return portfolio_returns


# ---------------------------------------------------------------------------
# Single (symbol, seed) evaluation
# ---------------------------------------------------------------------------


def run_single_combo(
    symbol: str,
    seed: int,
    raw: pd.DataFrame,
    n_splits: int = 5,
    d_model: int = 128,
    nhead: int = 4,
    num_layers: int = 3,
    context_length: int = 20,
    epochs_per_fold: int = 15,
    window: int = 20,
    lookback: int = 20,
    commission_bps: float = 5.0,
    alpha: float = 0.5,
    beta: float = 0.1,
    device: str = "cpu",
) -> dict:
    """Run walk-forward dual-head DT training for one (symbol, seed) combo.

    Returns dict with:
        sharpe_dt: annualized Sharpe from dual-head DT portfolio
        sharpe_bh: annualized Sharpe from buy-and-hold
        delta_sharpe: sharpe_dt - sharpe_bh
        auc_dt: direction accuracy
        n_folds: number of completed folds
        n_trades: total trades across folds
        size_distribution: distribution of predicted sizes
    """
    np.random.seed(seed)
    torch.manual_seed(seed)

    # Determine commission rate based on asset class
    is_crypto = any(
        c in symbol.upper() for c in ["BTC", "ETH", "LTC", "XRP", "BCH"]
    )
    effective_commission = commission_bps * 2 if is_crypto else commission_bps

    # Feature engineering
    indicators = [
        "returns",
        "volatility",
        "volume_ratio",
        "ma_ratios",
        "rsi",
        "macd",
        "bollinger",
        "true_range_atr",
        "obv",
    ]
    engineer = FeatureEngineer(lookback=lookback, indicators=indicators)
    features_df = engineer.transform(raw, add_target=False)
    features_arr = features_df.values.astype(np.float32)
    prices = raw.loc[features_df.index, "Close"].values.astype(np.float32)

    n = len(prices)
    if n < 500:
        return {"error": f"insufficient data ({n} rows)"}

    # Walk-forward split
    if WalkForwardSplitter is None:
        return {"error": "WalkForwardSplitter not available"}

    splitter = WalkForwardSplitter(
        n_splits=n_splits,
        train_size=max(252, n // (n_splits + 1)),
        test_size=max(63, n // (n_splits * 3)),
        gap=24,
    )

    fold_deltas = []
    fold_auc = []
    fold_trades = []
    all_dt_rets = []
    all_bh_rets = []
    all_sizes = []

    for fold_idx, (train_idx, test_idx) in enumerate(
        splitter.split(np.arange(n))
    ):
        if len(test_idx) < context_length + window + 10:
            continue

        # Normalize features on train only
        train_feat = features_arr[train_idx]
        mean = train_feat.mean(axis=0)
        std = train_feat.std(axis=0)
        std = np.where(std < 1e-8, 1.0, std)

        train_features_norm = (features_arr[train_idx] - mean) / std
        test_features_norm = (features_arr[test_idx] - mean) / std

        train_prices = prices[train_idx]
        test_prices = prices[test_idx]

        # Build trajectories with size labels
        train_trajs = build_trajectories_with_size(
            train_prices,
            train_features_norm,
            window=window,
            context_length=context_length,
            commission=effective_commission / 10000.0,
        )

        if len(train_trajs["states"]) <= context_length:
            continue

        state_dim = train_trajs["states"].shape[1]

        # Train dual-head DT
        result = train_dual_head_dt(
            train_trajs,
            state_dim=state_dim,
            d_model=d_model,
            nhead=nhead,
            num_layers=num_layers,
            context_length=context_length,
            epochs=epochs_per_fold,
            batch_size=32,
            lr=1e-4,
            commission_bps=effective_commission,
            alpha=alpha,
            beta=beta,
            device=device,
        )
        model = result["model"]

        # Build test trajectories
        test_trajs = build_trajectories_with_size(
            test_prices,
            test_features_norm,
            window=window,
            context_length=context_length,
            commission=effective_commission / 10000.0,
        )

        if len(test_trajs["states"]) <= context_length:
            continue

        # Predict on test set
        model.eval()
        with torch.no_grad():
            batches = create_sequence_batches_with_size(
                test_trajs,
                context_length=context_length,
                batch_size=64,
                shuffle=False,
            )
            all_action_preds = []
            all_size_preds = []
            for batch in batches:
                states = batch["states"].to(device)
                actions = batch["actions"].to(device)
                sizes = batch["sizes"].to(device)
                rtg = batch["rtg"].to(device)
                mask = batch["attention_mask"].to(device)

                action_logits, size_logits = model(
                    states, actions, sizes, rtg, attention_mask=mask
                )
                action_preds = action_logits.argmax(dim=-1)[:, -1].cpu().numpy()
                size_preds = size_logits.argmax(dim=-1)[:, -1].cpu().numpy()
                all_action_preds.extend(action_preds.tolist())
                all_size_preds.extend(size_preds.tolist())

        # Align predictions with test prices
        n_preds = len(all_action_preds)
        if n_preds < 10:
            continue

        test_prices_subset = test_prices[window : window + n_preds]

        if len(test_prices_subset) < n_preds:
            n_preds = len(test_prices_subset)
            all_action_preds = all_action_preds[:n_preds]
            all_size_preds = all_size_preds[:n_preds]
        test_prices_subset = test_prices_subset[:n_preds]

        # Simulate dual-head DT portfolio
        dt_rets = simulate_dual_head_portfolio(
            test_prices_subset,
            np.array(all_action_preds, dtype=np.int64),
            np.array(all_size_preds, dtype=np.int64),
            commission_bps=effective_commission,
        )

        # Buy-and-hold returns
        bh_rets = np.diff(test_prices_subset) / (
            test_prices_subset[:-1] + 1e-8
        )
        bh_rets = np.concatenate([[0.0], bh_rets])

        min_len = min(len(dt_rets), len(bh_rets))
        all_dt_rets.extend(dt_rets[:min_len].tolist())
        all_bh_rets.extend(bh_rets[:min_len].tolist())

        # Per-fold metrics
        fold_sharpe_dt = compute_sharpe(dt_rets[:min_len])
        fold_sharpe_bh = compute_sharpe(bh_rets[:min_len])
        fold_deltas.append(fold_sharpe_dt - fold_sharpe_bh)

        # Direction accuracy
        actual_dir = (np.diff(test_prices_subset[:min_len]) > 0).astype(int)
        pred_dir = np.array(all_action_preds[: len(actual_dir)])
        if len(pred_dir) >= len(actual_dir):
            pred_dir = pred_dir[: len(actual_dir)]
            correct = (pred_dir == 1) == (actual_dir == 1)
            fold_auc.append(
                float(correct.mean()) if len(correct) > 0 else 0.5
            )
        else:
            fold_auc.append(0.5)

        # Track size distribution and trades
        all_sizes.extend(all_size_preds[:min_len])
        fold_trades.append(
            int(np.sum(np.diff(all_action_preds[:min_len]) != 0))
        )

    if not fold_deltas:
        return {"error": "no valid folds completed"}

    # Aggregate across folds
    sharpe_dt = compute_sharpe(np.array(all_dt_rets))
    sharpe_bh = compute_sharpe(np.array(all_bh_rets))

    # Size distribution
    size_arr = np.array(all_sizes)
    size_dist = {
        str(SIZE_CLASSES[i]): int(np.sum(size_arr == i))
        for i in range(len(SIZE_CLASSES))
    }

    return {
        "sharpe_dt": round(sharpe_dt, 4),
        "sharpe_bh": round(sharpe_bh, 4),
        "delta_sharpe": round(sharpe_dt - sharpe_bh, 4),
        "mean_fold_delta": round(float(np.mean(fold_deltas)), 4),
        "std_fold_delta": round(float(np.std(fold_deltas)), 4),
        "mean_auc": round(float(np.mean(fold_auc)), 4),
        "n_folds": len(fold_deltas),
        "n_trades": sum(fold_trades),
        "size_distribution": size_dist,
        "commission_bps": effective_commission,
        "fold_deltas": [round(d, 4) for d in fold_deltas],
    }


# ---------------------------------------------------------------------------
# Main sweep
# ---------------------------------------------------------------------------


def main():
    parser = argparse.ArgumentParser(
        description="L6 Decision Transformer Extension sweep (dual-head + cost-aware)"
    )
    parser.add_argument(
        "--symbols",
        nargs="+",
        default=None,
        help="Symbols to test (default: full panier)",
    )
    parser.add_argument(
        "--seeds",
        nargs="+",
        type=int,
        default=[0, 1, 7, 42],
        help="Random seeds (default: 0 1 7 42)",
    )
    parser.add_argument(
        "--n-splits", type=int, default=5, help="Walk-forward folds"
    )
    parser.add_argument(
        "--epochs-per-fold",
        type=int,
        default=15,
        help="Training epochs per WF fold",
    )
    parser.add_argument("--d-model", type=int, default=128)
    parser.add_argument("--nhead", type=int, default=4)
    parser.add_argument("--num-layers", type=int, default=3)
    parser.add_argument("--context-length", type=int, default=20)
    parser.add_argument("--window", type=int, default=20)
    parser.add_argument("--lookback", type=int, default=20)
    parser.add_argument(
        "--commission-bps",
        type=float,
        default=5.0,
        help="Transaction cost in basis points (doubled for crypto)",
    )
    parser.add_argument(
        "--alpha",
        type=float,
        default=0.5,
        help="Weight for size loss (default: 0.5)",
    )
    parser.add_argument(
        "--beta",
        type=float,
        default=0.1,
        help="Weight for cost penalty (default: 0.1)",
    )
    parser.add_argument(
        "--smoke",
        action="store_true",
        help="Quick test: 2 symbols, 2 seeds, 2 epochs",
    )
    parser.add_argument(
        "--output", type=str, default=None, help="Output path for results JSON"
    )
    parser.add_argument(
        "--no-auto-fetch",
        action="store_true",
        help="Skip yfinance fallback for missing panier symbols "
             "(default: auto-fetch on, see PR #1726)",
    )
    args = parser.parse_args()

    # Device
    device = "cuda" if torch.cuda.is_available() else "cpu"
    print(f"Device: {device} | torch {torch.__version__}")

    # Verify thermal watchdog
    temp = get_gpu_temp()
    if device == "cuda" and temp == 0:
        print(
            "WARNING: gpu_training watchdog not active (temp=0). "
            "GPU thermal protection is in no-op fallback mode."
        )
    elif device == "cuda":
        print(f"GPU temperature: {temp}C (watchdog active, max=80C)")

    # Symbols
    if args.symbols:
        symbols = args.symbols
    else:
        symbols = get_panier_symbols()
    symbols = [s for s in symbols if s not in FORBIDDEN_SYMBOLS]

    # Smoke test override
    if args.smoke:
        symbols = symbols[:2]
        args.seeds = args.seeds[:2]
        args.epochs_per_fold = 2
        args.n_splits = 2
        print("SMOKE MODE: 2 symbols, 2 seeds, 2 epochs, 2 folds")

    seeds = args.seeds
    n_combos = len(symbols) * len(seeds)
    print(f"Sweep: {len(symbols)} symbols x {len(seeds)} seeds = {n_combos} combos")
    print(
        f"  WF folds={args.n_splits}, epochs/fold={args.epochs_per_fold}, "
        f"commission={args.commission_bps}bps (2x crypto)"
    )
    print(
        f"  alpha={args.alpha} (size weight), beta={args.beta} (cost penalty)"
    )
    print(f"  Architecture: DualHeadDT (d={args.d_model}, h={args.nhead}, "
          f"L={args.num_layers}, ctx={args.context_length})")

    # Load panier (auto_fetch missing CSVs via yfinance unless --no-auto-fetch)
    panier = load_panier(start="2015-01-01", auto_fetch=not args.no_auto_fetch)
    loaded_symbols = [s for s in symbols if s in panier]
    if len(loaded_symbols) < len(symbols):
        missing = [s for s in symbols if s not in panier]
        print(f"WARNING: {len(missing)} symbols not in panier: {missing}")
    symbols = loaded_symbols

    print(
        f"Loaded panier: {len(symbols)} symbols, "
        f"{len(next(iter(panier.values())))} days"
    )

    # Run sweep
    t0 = time.time()
    symbol_seed_results = {}
    combo_idx = 0

    for symbol in symbols:
        raw = panier[symbol]
        symbol_seed_results[symbol] = {}

        for seed in seeds:
            combo_idx += 1
            print(
                f"[{combo_idx}/{n_combos}] {symbol} seed={seed} ",
                end="",
                flush=True,
            )

            try:
                result = run_single_combo(
                    symbol=symbol,
                    seed=seed,
                    raw=raw,
                    n_splits=args.n_splits,
                    d_model=args.d_model,
                    nhead=args.nhead,
                    num_layers=args.num_layers,
                    context_length=args.context_length,
                    epochs_per_fold=args.epochs_per_fold,
                    window=args.window,
                    lookback=args.lookback,
                    commission_bps=args.commission_bps,
                    alpha=args.alpha,
                    beta=args.beta,
                    device=device,
                )

                if "error" in result:
                    print(f"ERROR: {result['error']}")
                else:
                    d = result["delta_sharpe"]
                    s = result["sharpe_dt"]
                    auc = result["mean_auc"]
                    nf = result["n_folds"]
                    nt = result["n_trades"]
                    sd = result.get("size_distribution", {})
                    print(
                        f"dSharpe={d:+.4f} dtSharpe={s:.4f} auc={auc:.4f} "
                        f"folds={nf} trades={nt} sizes={sd}"
                    )
                    symbol_seed_results[symbol][seed] = result

            except Exception as e:
                print(f"EXCEPTION: {e}")
                symbol_seed_results[symbol][seed] = {"error": str(e)}

    # Multi-seed edge evaluation per symbol
    edges = []
    for symbol in symbols:
        seed_results = symbol_seed_results.get(symbol, {})
        deltas = [
            r["delta_sharpe"]
            for r in seed_results.values()
            if "delta_sharpe" in r
        ]

        if len(deltas) < 2:
            mean_d = deltas[0] if deltas else 0.0
            std_d = 0.0
            sigma = 0.0
        else:
            mean_d = float(np.mean(deltas))
            std_d = float(np.std(deltas))
            sigma = mean_d / std_d if std_d > 1e-10 else 0.0

        aucs = [
            r["mean_auc"]
            for r in seed_results.values()
            if "mean_auc" in r
        ]

        # Aggregate size distribution across seeds
        agg_sizes = {}
        for r in seed_results.values():
            if "size_distribution" in r:
                for k, v in r["size_distribution"].items():
                    agg_sizes[k] = agg_sizes.get(k, 0) + v

        edges.append(
            {
                "symbol": symbol,
                "mean_delta": round(mean_d, 4),
                "std_delta": round(std_d, 4),
                "sigma_edge": round(sigma, 4),
                "is_signal": sigma >= 2.0 and mean_d > 0,
                "n_seeds": len(deltas),
                "mean_auc": (
                    round(float(np.mean(aucs)), 4) if aucs else 0.0
                ),
                "size_distribution_agg": agg_sizes,
                "seed_details": {
                    str(s): {
                        "delta_sharpe": r.get("delta_sharpe"),
                        "sharpe_dt": r.get("sharpe_dt"),
                        "n_folds": r.get("n_folds"),
                        "n_trades": r.get("n_trades"),
                        "size_distribution": r.get("size_distribution"),
                    }
                    for s, r in seed_results.items()
                    if "delta_sharpe" in r
                },
            }
        )

    # Verdict
    n_signal = sum(1 for e in edges if e["is_signal"])
    median_auc = (
        float(np.median([e["mean_auc"] for e in edges])) if edges else 0.0
    )
    median_delta = (
        float(np.median([e["mean_delta"] for e in edges])) if edges else 0.0
    )

    if n_signal >= len(edges) * 0.5 and median_auc > 0.52:
        verdict = "BEATS"
    elif n_signal > 0 and median_auc > 0.50:
        verdict = "INCONCLUSIVE"
    else:
        verdict = "NO BEATS"

    elapsed = time.time() - t0

    output = {
        "ladder": "L6",
        "description": "Dual-Head DT Extension (action+size, cost-aware)",
        "verdict": verdict,
        "n_signal": n_signal,
        "n_cells": len(edges),
        "median_auc": round(median_auc, 4),
        "median_delta_sharpe": round(median_delta, 4),
        "edges": edges,
        "n_combos": n_combos,
        "elapsed_s": round(elapsed, 2),
        "device": device,
        "smoke": args.smoke,
        "config": {
            "model": "DualHeadDecisionTransformer",
            "d_model": args.d_model,
            "nhead": args.nhead,
            "num_layers": args.num_layers,
            "context_length": args.context_length,
            "window": args.window,
            "epochs_per_fold": args.epochs_per_fold,
            "n_splits": args.n_splits,
            "seeds": seeds,
            "commission_bps": args.commission_bps,
            "commission_crypto_multiplier": 2.0,
            "alpha": args.alpha,
            "beta": args.beta,
            "size_classes": SIZE_CLASSES,
            "action_classes": list(ACTION_NAMES.values()),
        },
        "comparison_with_l4": {
            "l4_verdict": "BEATS",
            "l4_n_signal": 24,
            "l4_n_cells": 26,
            "l4_median_auc": 0.5582,
            "l6_improvement_hypothesis": (
                "Size head reduces unnecessary full-size trades; "
                "cost penalty discourages churning"
            ),
        },
    }

    # Save
    out_path = Path(args.output) if args.output else RESULTS_DIR / "results.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(
        json.dumps(output, indent=2, default=str), encoding="utf-8"
    )

    print(f"\n{'='*60}")
    print(f"L6 Dual-Head DT sweep: {n_combos} combos in {elapsed:.0f}s")
    print(
        f"VERDICT: {verdict} (signal cells {n_signal}/{len(edges)}, "
        f"median AUC {median_auc:.4f}, median delta {median_delta:+.4f})"
    )
    print(f"Saved: {out_path}")


if __name__ == "__main__":
    main()
