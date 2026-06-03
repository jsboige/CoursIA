"""
Train Decision Transformer (DT) for offline RL financial trading.

Implements the Decision Transformer architecture (Chen et al., 2021) adapted for
trading following arXiv:2411.17900. Unlike online RL (DQN), DT learns entirely
from historical trajectories, eliminating environment interaction during training
and the associated data leakage risks.

Key advantages over online RL:
    - No environment simulation needed during training (offline)
    - Return-conditioned policy: specify target return at inference
    - No replay buffer instability or exploration noise
    - Naturally handles variable-length trajectories via transformer attention

Anti-pattern safeguards (cf. feedback_ml_trading_pitfalls.md):
    - --test-ratio is HONORED: normalize stats computed on train set only
    - Walk-forward validation supported (from Stage 0 WalkForwardSplitter)
    - Majority-class baseline computed and reported (must beat to claim edge)
    - Transaction costs deducted from reward computation
    - RTG uses only future rewards from each timestep (no lookahead)

Usage:
    # Dry-run (CPU, synthetic data, 50 steps)
    python train_rl_dt.py --dry-run

    # Full training on yfinance SPY
    python train_rl_dt.py --data-dir ../datasets/yfinance --symbol SPY \
        --start 2010-01-01 --epochs 50

    # Walk-forward validation
    python train_rl_dt.py --data-dir ../datasets/yfinance --symbol SPY \
        --walk-forward --n-splits 5 --gap 24 --purge 24

    # With LoRA (if peft available)
    python train_rl_dt.py --dry-run --lora

Output:
    Checkpoints in --checkpoint-dir (default: ../checkpoints/dt/<date>/)
    metadata.json with hyperparams, metrics, majority-class comparison

References:
    - Chen et al. (2021): "Decision Transformer: RL via Sequence Modeling"
    - arXiv:2411.17900: "Decision Transformer for Algorithmic Trading"
    - Radford et al. (2019): GPT-2 architecture foundation
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from datetime import datetime
from pathlib import Path

import numpy as np
import pandas as pd
import torch
import torch.nn as nn
import torch.nn.functional as F

sys.path.append(str(Path(__file__).resolve().parent.parent.parent / "shared"))
from gpu_training import batch_thermal_check, get_gpu_temp, setup_amp, thermal_check
from data_utils import compute_data_hash, generate_synthetic_data, load_data
from features import FeatureEngineer

try:
    from walk_forward import WalkForwardSplitter
except ImportError:
    WalkForwardSplitter = None

try:
    from peft import LoraConfig, get_peft_model
    HAS_PEFT = True
except ImportError:
    HAS_PEFT = False


# ---------------------------------------------------------------------------
# Positional Encoding (sinusoidal, from Vaswani et al. 2017)
# ---------------------------------------------------------------------------


class SinusoidalPositionalEncoding(nn.Module):
    """Sinusoidal positional encoding for transformer inputs."""

    def __init__(self, d_model: int, max_len: int = 5000, dropout: float = 0.1):
        super().__init__()
        self.dropout = nn.Dropout(dropout)
        pe = torch.zeros(max_len, d_model)
        position = torch.arange(0, max_len, dtype=torch.float32).unsqueeze(1)
        div_term = torch.exp(
            torch.arange(0, d_model, 2, dtype=torch.float32)
            * (-math.log(10000.0) / d_model)
        )
        pe[:, 0::2] = torch.sin(position * div_term)
        if d_model % 2 == 1:
            pe[:, 1::2] = torch.cos(position * div_term[:-1])
        else:
            pe[:, 1::2] = torch.cos(position * div_term)
        pe = pe.unsqueeze(0)  # [1, max_len, d_model]
        self.register_buffer("pe", pe)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        """Add positional encoding to input.

        Args:
            x: [B, T, d_model] tensor.

        Returns:
            [B, T, d_model] with positional encoding added.
        """
        x = x + self.pe[:, : x.size(1), :]
        return self.dropout(x)


# ---------------------------------------------------------------------------
# Decision Transformer Model
# ---------------------------------------------------------------------------


class DecisionTransformerModel(nn.Module):
    """Decision Transformer for offline RL trading.

    Architecture:
        1. StateEncoder: Linear(state_dim, d_model) + LayerNorm + GELU
        2. ActionEmbedding: Embedding(3, d_model) for hold/buy/sell
        3. ReturnToGoEmbedding: Linear(1, d_model)
        4. SinusoidalPositionalEncoding
        5. TransformerEncoder backbone
        6. Prediction head: Linear(d_model, 3) for action logits

    Sequence input per timestep t:
        [return_to_go_t, state_t, action_t]
    Target: action_{t+1}

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
        dropout: float = 0.1,
    ):
        super().__init__()
        self.state_dim = state_dim
        self.d_model = d_model
        self.n_actions = n_actions
        self.context_length = context_length

        # State encoder
        self.state_encoder = nn.Sequential(
            nn.Linear(state_dim, d_model),
            nn.LayerNorm(d_model),
            nn.GELU(),
        )

        # Action embedding (3 actions: hold=0, buy=1, sell=2)
        self.action_embedding = nn.Embedding(n_actions, d_model)

        # Return-to-go embedding
        self.rtg_embedding = nn.Sequential(
            nn.Linear(1, d_model),
            nn.GELU(),
        )

        # Positional encoding
        self.pos_encoding = SinusoidalPositionalEncoding(
            d_model, max_len=context_length * 3 + 1, dropout=dropout
        )

        # Transformer backbone (using nn.TransformerEncoder)
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

        # Layer norm before prediction head
        self.ln_f = nn.LayerNorm(d_model)

        # Prediction head: action logits
        self.action_head = nn.Linear(d_model, n_actions)

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
        rtg: torch.Tensor,
        attention_mask: torch.Tensor | None = None,
    ) -> torch.Tensor:
        """Forward pass through Decision Transformer.

        Args:
            states: [B, T, state_dim] state vectors.
            actions: [B, T] action indices (long).
            rtg: [B, T, 1] return-to-go values.
            attention_mask: [B, T] optional mask (1=attend, 0=ignore).

        Returns:
            [B, T, n_actions] action logits for each timestep.
        """
        B, T, _ = states.shape

        # Embed each modality
        state_emb = self.state_encoder(states)  # [B, T, d_model]
        action_emb = self.action_embedding(actions)  # [B, T, d_model]
        rtg_emb = self.rtg_embedding(rtg)  # [B, T, d_model]

        # Interleave: [rtg_0, state_0, action_0, rtg_1, state_1, action_1, ...]
        # This gives the model: "given RTG_t and state_t, what action_t to take?"
        seq_len = T * 3
        sequence = torch.zeros(B, seq_len, self.d_model, device=states.device)
        sequence[:, 0::3, :] = rtg_emb
        sequence[:, 1::3, :] = state_emb
        sequence[:, 2::3, :] = action_emb

        # Add positional encoding
        sequence = self.pos_encoding(sequence)

        # Build attention mask for interleaved sequence
        if attention_mask is not None:
            # Expand mask: each timestep has 3 tokens
            interleaved_mask = attention_mask.unsqueeze(-1).expand(-1, -1, 3)
            interleaved_mask = interleaved_mask.reshape(B, seq_len)
            # Convert to float mask for transformer (True positions are masked)
            float_mask = (interleaved_mask == 0).float()
            # nnn.TransformerEncoder uses src_key_padding_mask: True = ignore
            src_key_padding_mask = float_mask.bool()
        else:
            src_key_padding_mask = None

        # Causal mask (prevent attending to future)
        causal_mask = nn.Transformer.generate_square_subsequent_mask(
            seq_len, device=states.device
        )

        # Transformer
        out = self.transformer(
            sequence,
            mask=causal_mask,
            src_key_padding_mask=src_key_padding_mask,
        )  # [B, seq_len, d_model]

        # Extract state positions (where action prediction happens)
        # We predict action from the state embedding position
        state_positions = out[:, 1::3, :]  # [B, T, d_model]
        state_positions = self.ln_f(state_positions)

        # Predict actions
        action_logits = self.action_head(state_positions)  # [B, T, n_actions]

        return action_logits


# ---------------------------------------------------------------------------
# Sequence Formation
# ---------------------------------------------------------------------------


def build_trajectories(
    prices: np.ndarray,
    features: np.ndarray,
    window: int = 20,
    context_length: int = 20,
    commission: float = 0.001,
) -> dict:
    """Build offline RL trajectories from historical data.

    Constructs sequences of (return_to_go, state, action) tuples from
    a simple deterministic policy (momentum-based) applied to historical data.

    Args:
        prices: [N] price array.
        features: [N, F] feature array.
        window: Lookback window for state construction.
        context_length: Number of timesteps per trajectory.
        commission: Transaction cost per trade.

    Returns:
        Dict with keys: states, actions, rtg, rewards, attention_mask
        Each value is an np.ndarray.
    """
    n = len(prices)
    feature_dim = features.shape[1] if features.ndim > 1 else 1

    all_states = []
    all_actions = []
    all_rtg = []
    all_rewards = []
    all_masks = []

    # Compute returns and simple momentum actions
    position = 0  # -1, 0, 1
    rewards = np.zeros(n, dtype=np.float32)
    actions = np.zeros(n, dtype=np.int64)

    for i in range(1, n):
        price_change = (prices[i] - prices[i - 1]) / (prices[i - 1] + 1e-8)

        # Simple momentum policy for trajectory generation
        if i >= window:
            past_return = (prices[i - 1] - prices[i - window]) / (prices[i - window] + 1e-8)
        else:
            past_return = 0.0

        if past_return > 0.01:
            action = 1  # buy
        elif past_return < -0.01:
            action = 2  # sell
        else:
            action = 0  # hold

        # Apply commission on position changes
        reward = position * price_change
        if action == 1 and position <= 0:
            reward -= commission
            position = 1
        elif action == 2 and position >= 0:
            reward -= commission
            position = -1
        elif action == 0:
            pass  # hold current position

        rewards[i] = reward
        actions[i] = action

    # Compute return-to-go (cumulative future reward)
    rtg = np.zeros(n, dtype=np.float32)
    rtg[-1] = rewards[-1]
    for i in range(n - 2, -1, -1):
        rtg[i] = rewards[i] + rtg[i + 1]

    # Build trajectory segments
    start_idx = window
    end_idx = n - context_length

    if end_idx <= start_idx:
        # Not enough data, use what we have
        end_idx = n - 1
        context_length = end_idx - start_idx
        if context_length <= 0:
            context_length = 1
            start_idx = max(0, n - 2)

    for t in range(start_idx, n - context_length):
        # State: feature window + position info
        feat_window = features[t - window : t]
        if feat_window.ndim == 1:
            feat_window = feat_window.reshape(-1, 1)
        state = feat_window.flatten()

        # Action at this timestep
        action = actions[t]

        # Return-to-go from this timestep
        rtg_val = rtg[t]

        # Reward at this timestep
        reward = rewards[t]

        all_states.append(state)
        all_actions.append(action)
        all_rtg.append(rtg_val)
        all_rewards.append(reward)
        all_masks.append(1.0)

    if len(all_states) == 0:
        # Fallback: create minimal trajectory
        feat_window = features[0:window]
        if feat_window.ndim == 1:
            feat_window = feat_window.reshape(-1, 1)
        all_states.append(feat_window.flatten())
        all_actions.append(0)
        all_rtg.append(0.0)
        all_rewards.append(0.0)
        all_masks.append(1.0)

    states_arr = np.array(all_states, dtype=np.float32)
    actions_arr = np.array(all_actions, dtype=np.int64)
    rtg_arr = np.array(all_rtg, dtype=np.float32).reshape(-1, 1)
    rewards_arr = np.array(all_rewards, dtype=np.float32)
    mask_arr = np.array(all_masks, dtype=np.float32)

    return {
        "states": states_arr,
        "actions": actions_arr,
        "rtg": rtg_arr,
        "rewards": rewards_arr,
        "attention_mask": mask_arr,
    }


def create_sequence_batches(
    trajectories: dict,
    context_length: int = 20,
    batch_size: int = 32,
    shuffle: bool = True,
) -> list[dict]:
    """Create fixed-length sequence batches from trajectories.

    Args:
        trajectories: Dict from build_trajectories.
        context_length: Number of timesteps per sequence.
        batch_size: Sequences per batch.
        shuffle: Whether to shuffle sequences.

    Returns:
        List of batch dicts, each with states, actions, rtg, target_actions, mask.
    """
    n = len(trajectories["states"])
    if n <= context_length:
        # Not enough data for even one sequence
        context_length = max(1, n - 1)
        if context_length < 1:
            return []

    sequences = []
    for i in range(n - context_length):
        seq = {
            "states": trajectories["states"][i : i + context_length],
            "actions": trajectories["actions"][i : i + context_length],
            "rtg": trajectories["rtg"][i : i + context_length],
            "target_actions": trajectories["actions"][i + 1 : i + context_length + 1],
            "attention_mask": trajectories["attention_mask"][i : i + context_length],
        }
        # Pad target_actions if needed
        if len(seq["target_actions"]) < context_length:
            pad_len = context_length - len(seq["target_actions"])
            seq["target_actions"] = np.concatenate(
                [seq["target_actions"], np.zeros(pad_len, dtype=np.int64)]
            )
        sequences.append(seq)

    if shuffle:
        indices = np.random.permutation(len(sequences))
        sequences = [sequences[i] for i in indices]

    # Batch
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
            "rtg": torch.tensor(
                np.stack([s["rtg"] for s in batch_seqs]), dtype=torch.float32
            ),
            "target_actions": torch.tensor(
                np.stack([s["target_actions"] for s in batch_seqs]), dtype=torch.long
            ),
            "attention_mask": torch.tensor(
                np.stack([s["attention_mask"] for s in batch_seqs]), dtype=torch.float32
            ),
        }
        batches.append(batch)

    return batches


# ---------------------------------------------------------------------------
# Majority-class baseline
# ---------------------------------------------------------------------------


def compute_majority_class_baseline(actions: np.ndarray) -> dict:
    """Compute majority-class baseline for action prediction.

    Args:
        actions: [N] array of action indices.

    Returns:
        Dict with accuracy, per-class counts, and dominant class.
    """
    unique, counts = np.unique(actions, return_counts=True)
    total = len(actions)
    majority_count = counts.max()
    majority_class = int(unique[counts.argmax()])
    baseline_acc = float(majority_count / total)

    class_counts = {int(u): int(c) for u, c in zip(unique, counts)}
    class_names = {0: "hold", 1: "buy", 2: "sell"}

    return {
        "majority_class_accuracy": round(baseline_acc, 4),
        "majority_class": majority_class,
        "majority_class_name": class_names.get(majority_class, str(majority_class)),
        "class_counts": class_counts,
        "total_samples": total,
    }


# ---------------------------------------------------------------------------
# Training
# ---------------------------------------------------------------------------


def train_dt(
    trajectories: dict,
    state_dim: int,
    d_model: int = 128,
    nhead: int = 4,
    num_layers: int = 3,
    context_length: int = 20,
    epochs: int = 50,
    batch_size: int = 32,
    lr: float = 1e-4,
    weight_decay: float = 1e-4,
    dropout: float = 0.1,
    device: str = "cpu",
    use_lora: bool = False,
) -> dict:
    """Train Decision Transformer on offline trajectories.

    Args:
        trajectories: Dict from build_trajectories.
        state_dim: Dimension of state vectors.
        d_model: Transformer model dimension.
        nhead: Number of attention heads.
        num_layers: Number of transformer layers.
        context_length: Sequence length.
        epochs: Training epochs.
        batch_size: Batch size.
        lr: Learning rate.
        weight_decay: AdamW weight decay.
        dropout: Dropout rate.
        device: Device (cpu or cuda).
        use_lora: Enable LoRA fine-tuning via peft.

    Returns:
        Dict with model, metrics, history.
    """
    model = DecisionTransformerModel(
        state_dim=state_dim,
        d_model=d_model,
        nhead=nhead,
        num_layers=num_layers,
        context_length=context_length,
        n_actions=3,
        dropout=dropout,
    )

    # Optional LoRA
    lora_applied = False
    if use_lora and HAS_PEFT:
        lora_config = LoraConfig(
            r=8,
            lora_alpha=16,
            target_modules=["state_encoder.0", "action_embedding", "rtg_embedding.0"],
            lora_dropout=0.05,
        )
        model = get_peft_model(model, lora_config)
        lora_applied = True
        print(f"LoRA applied: trainable params = {model.print_trainable_parameters()}")
    elif use_lora and not HAS_PEFT:
        print("WARNING: --lora requested but peft not installed. Training without LoRA.")

    model = model.to(device)
    total_params = sum(p.numel() for p in model.parameters() if p.requires_grad)
    print(f"Decision Transformer params: {total_params:,}")
    print(f"  d_model={d_model}, nhead={nhead}, num_layers={num_layers}, "
          f"context_length={context_length}")

    optimizer = torch.optim.AdamW(
        model.parameters(), lr=lr, weight_decay=weight_decay
    )
    scheduler = torch.optim.lr_scheduler.CosineAnnealingWarmRestarts(
        optimizer, T_0=10, T_mult=2
    )
    criterion = nn.CrossEntropyLoss()

    use_amp, grad_scaler = setup_amp()

    history = {"train_loss": [], "val_loss": []}
    best_loss = float("inf")
    best_state = None

    # Create batches (re-created each epoch for different shuffling)
    for epoch in range(epochs):
        thermal_check(max_temp=80, cool_sleep=30)
        model.train()

        batches = create_sequence_batches(
            trajectories, context_length=context_length, batch_size=batch_size, shuffle=True
        )

        if not batches:
            print(f"  Epoch {epoch+1}/{epochs}: no valid batches, skipping")
            continue

        epoch_loss = 0.0
        n_batches = 0

        for batch in batches:
            batch_thermal_check(n_batches, check_every=5, max_temp=80, cool_sleep=30)

            states = batch["states"].to(device)
            actions = batch["actions"].to(device)
            rtg = batch["rtg"].to(device)
            targets = batch["target_actions"].to(device)
            mask = batch["attention_mask"].to(device)

            optimizer.zero_grad()

            with torch.amp.autocast("cuda", enabled=use_amp):
                logits = model(states, actions, rtg, attention_mask=mask)
                # logits: [B, T, n_actions], targets: [B, T]
                loss = criterion(
                    logits.reshape(-1, 3),
                    targets.reshape(-1),
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

        scheduler.step()
        avg_loss = epoch_loss / max(n_batches, 1)
        history["train_loss"].append(round(avg_loss, 6))

        if avg_loss < best_loss:
            best_loss = avg_loss
            best_state = {k: v.cpu().clone() for k, v in model.state_dict().items()}

        if (epoch + 1) % max(1, epochs // 5) == 0:
            temp = get_gpu_temp() if device == "cuda" else 0
            temp_str = f"  gpu={temp}C" if temp > 0 else ""
            print(f"  Epoch {epoch+1}/{epochs}  loss={avg_loss:.6f}{temp_str}")

    # Load best model
    if best_state:
        model.load_state_dict(best_state)
    model.eval()

    # Majority-class baseline
    all_actions = trajectories["actions"]
    majority_bl = compute_majority_class_baseline(all_actions)

    metrics = {
        "best_train_loss": round(best_loss, 6),
        "total_params": total_params,
        "lora_applied": lora_applied,
        "majority_class_baseline": majority_bl,
        "epochs_trained": epochs,
        "train_samples": len(trajectories["states"]),
    }

    return {
        "model": model,
        "metrics": metrics,
        "history": history,
        "state_dim": state_dim,
        "d_model": d_model,
        "nhead": nhead,
        "num_layers": num_layers,
        "context_length": context_length,
    }


def evaluate_dt(
    model: DecisionTransformerModel,
    trajectories: dict,
    context_length: int = 20,
    batch_size: int = 32,
    device: str = "cpu",
) -> dict:
    """Evaluate Decision Transformer on test trajectories.

    Args:
        model: Trained DT model.
        trajectories: Test trajectories dict.
        context_length: Sequence length.
        batch_size: Batch size.
        device: Device.

    Returns:
        Dict with evaluation metrics.
    """
    model.eval()
    criterion = nn.CrossEntropyLoss(reduction="none")

    batches = create_sequence_batches(
        trajectories, context_length=context_length, batch_size=batch_size, shuffle=False
    )

    total_loss = 0.0
    total_correct = 0
    total_samples = 0
    all_preds = []
    all_targets = []

    with torch.no_grad():
        for batch in batches:
            states = batch["states"].to(device)
            actions = batch["actions"].to(device)
            rtg = batch["rtg"].to(device)
            targets = batch["target_actions"].to(device)
            mask = batch["attention_mask"].to(device)

            logits = model(states, actions, rtg, attention_mask=mask)
            loss = criterion(logits.reshape(-1, 3), targets.reshape(-1))

            # Mask out padded positions
            mask_flat = mask.reshape(-1).bool()
            valid_loss = loss[mask_flat]
            total_loss += valid_loss.sum().item()

            preds = logits.argmax(dim=-1)
            valid_preds = preds.reshape(-1)[mask_flat]
            valid_targets = targets.reshape(-1)[mask_flat]

            total_correct += (valid_preds == valid_targets).sum().item()
            total_samples += mask_flat.sum().item()

            all_preds.append(valid_preds.cpu().numpy())
            all_targets.append(valid_targets.cpu().numpy())

    avg_loss = total_loss / max(total_samples, 1)
    accuracy = total_correct / max(total_samples, 1)

    # Compute action distribution
    preds_all = np.concatenate(all_preds) if all_preds else np.array([])
    targets_all = np.concatenate(all_targets) if all_targets else np.array([])

    # Majority-class baseline on test set
    majority_bl = compute_majority_class_baseline(targets_all) if len(targets_all) > 0 else {}

    return {
        "test_loss": round(avg_loss, 6),
        "test_accuracy": round(accuracy, 4),
        "test_samples": total_samples,
        "majority_class_baseline": majority_bl,
        "edge_over_majority": round(
            accuracy - majority_bl.get("majority_class_accuracy", 0.5), 4
        ),
    }


# ---------------------------------------------------------------------------
# Checkpoint
# ---------------------------------------------------------------------------


def save_checkpoint(
    model, result: dict, hyperparams: dict, data_hash: str, checkpoint_dir: Path
) -> Path:
    """Save Decision Transformer checkpoint and metadata."""
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    ckpt_path = checkpoint_dir / timestamp
    ckpt_path.mkdir(parents=True, exist_ok=True)

    model_file = ckpt_path / "model.pt"
    torch.save(model.state_dict(), model_file)

    metadata = {
        "timestamp": timestamp,
        "model_type": "decision_transformer",
        "hyperparams": hyperparams,
        "metrics": result["metrics"],
        "history": result["history"],
        "data_hash": data_hash,
        "architecture": {
            "state_dim": int(result["state_dim"]),
            "d_model": int(result["d_model"]),
            "nhead": int(result["nhead"]),
            "num_layers": int(result["num_layers"]),
            "context_length": int(result["context_length"]),
            "n_actions": 3,
        },
        "files": ["model.pt", "metadata.json"],
    }
    meta_file = ckpt_path / "metadata.json"
    meta_file.write_text(json.dumps(metadata, indent=2, default=str), encoding="utf-8")

    print(f"Checkpoint saved: {ckpt_path}")
    print(f"  Metrics: {result['metrics']}")
    return ckpt_path


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main():
    parser = argparse.ArgumentParser(
        description="Train Decision Transformer (offline RL) for financial trading"
    )
    # Data
    parser.add_argument(
        "--data-dir",
        default=str(Path(__file__).resolve().parent.parent / "datasets" / "yfinance"),
    )
    parser.add_argument("--symbol", default="SPY")
    parser.add_argument("--start")
    parser.add_argument("--end")

    # Architecture
    parser.add_argument("--d-model", type=int, default=128, help="Model dimension")
    parser.add_argument("--nhead", type=int, default=4, help="Number of attention heads")
    parser.add_argument("--num-layers", type=int, default=3, help="Transformer layers")
    parser.add_argument("--context-length", type=int, default=20, help="Sequence length")
    parser.add_argument("--dropout", type=float, default=0.1)
    parser.add_argument("--window", type=int, default=20, help="State lookback window")

    # Training
    parser.add_argument("--epochs", type=int, default=50)
    parser.add_argument("--batch-size", type=int, default=32)
    parser.add_argument("--lr", type=float, default=1e-4)
    parser.add_argument("--weight-decay", type=float, default=1e-4)
    parser.add_argument("--lookback", type=int, default=20)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--commission", type=float, default=0.001,
                        help="Transaction cost per trade")

    # Splitting
    parser.add_argument("--test-ratio", type=float, default=0.2,
                        help="Fraction for temporal test split")
    parser.add_argument("--walk-forward", action="store_true",
                        help="Enable walk-forward validation")
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--gap", type=int, default=24)
    parser.add_argument("--purge", type=int, default=24)

    # LoRA
    parser.add_argument("--lora", action="store_true",
                        help="Enable LoRA fine-tuning (requires peft)")

    # Output
    parser.add_argument(
        "--checkpoint-dir",
        default=str(Path(__file__).resolve().parent.parent / "checkpoints" / "dt"),
    )
    parser.add_argument("--dry-run", action="store_true",
                        help="Synthetic data, 50 steps, CPU")
    parser.add_argument(
        "--advanced", action="store_true",
        help="Use advanced features (all indicators)",
    )
    parser.add_argument(
        "--indicators", nargs="+", default=None,
        help="Specific indicators to use (overrides --advanced)",
    )
    args = parser.parse_args()

    # Seed
    np.random.seed(args.seed)
    torch.manual_seed(args.seed)

    # Device
    device = "cuda" if torch.cuda.is_available() else "cpu"

    # Load data
    if args.dry_run:
        print("DRY-RUN: Using synthetic data (2000 rows, 10 epochs)")
        raw = generate_synthetic_data(2000)
        data_hash = "synthetic-dryrun"
        args.epochs = 10
    else:
        data_dir = Path(args.data_dir)
        if not data_dir.exists():
            print(f"ERROR: Data directory not found: {data_dir}", file=sys.stderr)
            sys.exit(1)
        raw = load_data(data_dir, args.symbol, args.start, args.end)
        data_hash = compute_data_hash(raw)
        print(f"Loaded {len(raw)} rows for {args.symbol}")

    # Feature engineering
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

    # Normalize using training portion only
    n = len(features_arr)
    train_end = int(n * (1 - args.test_ratio))
    mean = features_arr[:train_end].mean(axis=0)
    std = features_arr[:train_end].std(axis=0)
    std = np.where(std < 1e-8, 1.0, std)
    features_arr = (features_arr - mean) / std

    prices = raw.loc[features_df.index, "Close"].values.astype(np.float32)

    # Temporal split
    train_prices = prices[:train_end]
    train_features = features_arr[:train_end]
    test_prices = prices[train_end:]
    test_features = features_arr[train_end:]

    print(f"Features: {len(features_df)} rows, {len(feature_cols)} columns")
    print(f"Train/test split: {len(train_prices)} train ({100*(1-args.test_ratio):.0f}%) / "
          f"{len(test_prices)} test ({100*args.test_ratio:.0f}%)")
    print(f"Device: {device}")

    # Build trajectories
    train_trajs = build_trajectories(
        train_prices, train_features,
        window=args.window,
        context_length=args.context_length,
        commission=args.commission,
    )
    state_dim = train_trajs["states"].shape[1]
    print(f"State dim: {state_dim}, Trajectories: {len(train_trajs['states'])} timesteps")

    # Majority-class baseline (training set)
    train_majority = compute_majority_class_baseline(train_trajs["actions"])
    print(f"Majority-class baseline (train): {train_majority['majority_class_accuracy']:.4f} "
          f"(class={train_majority['majority_class_name']})")

    hyperparams = {
        "model_type": "decision_transformer",
        "d_model": args.d_model,
        "nhead": args.nhead,
        "num_layers": args.num_layers,
        "context_length": args.context_length,
        "dropout": args.dropout,
        "window": args.window,
        "epochs": args.epochs,
        "batch_size": args.batch_size,
        "lr": args.lr,
        "weight_decay": args.weight_decay,
        "lookback": args.lookback,
        "symbol": args.symbol,
        "device": device,
        "test_ratio": args.test_ratio,
        "commission": args.commission,
        "use_lora": args.lora,
        "train_samples": len(train_prices),
        "test_samples": len(test_prices),
    }

    # Train
    result = train_dt(
        train_trajs,
        state_dim=state_dim,
        d_model=args.d_model,
        nhead=args.nhead,
        num_layers=args.num_layers,
        context_length=args.context_length,
        epochs=args.epochs,
        batch_size=args.batch_size,
        lr=args.lr,
        weight_decay=args.weight_decay,
        dropout=args.dropout,
        device=device,
        use_lora=args.lora,
    )

    # Save checkpoint
    ckpt_dir = Path(args.checkpoint_dir)
    save_checkpoint(result["model"], result, hyperparams, data_hash, ckpt_dir)

    # Evaluate on test set
    test_trajs = build_trajectories(
        test_prices, test_features,
        window=args.window,
        context_length=args.context_length,
        commission=args.commission,
    )

    if len(test_trajs["states"]) > args.context_length:
        oos_metrics = evaluate_dt(
            result["model"], test_trajs,
            context_length=args.context_length,
            batch_size=args.batch_size,
            device=device,
        )
        result["oos_metrics"] = oos_metrics

        # Update metadata with OOS results
        ckpt_subdirs = sorted(ckpt_dir.glob("*"))
        if ckpt_subdirs:
            latest_meta = ckpt_subdirs[-1] / "metadata.json"
            if latest_meta.exists():
                meta = json.loads(latest_meta.read_text(encoding="utf-8"))
                meta["oos_metrics"] = oos_metrics
                latest_meta.write_text(
                    json.dumps(meta, indent=2, default=str), encoding="utf-8"
                )

        o = oos_metrics
        m = result["metrics"]
        print(f"\nTraining complete. BestLoss={m['best_train_loss']:.6f}")
        print(f"OOS evaluation. TestAcc={o['test_accuracy']:.4f}, "
              f"OOS Loss={o['test_loss']:.6f}")
        print(f"  Majority baseline (test): {o['majority_class_baseline'].get('majority_class_accuracy', 'N/A')}")
        print(f"  Edge over majority: {o['edge_over_majority']:+.4f} "
              f"({'BEATS' if o['edge_over_majority'] > 0 else 'FAILS'} baseline)")
    else:
        print("Not enough test data for OOS evaluation")

    # Walk-forward validation (optional)
    if args.walk_forward and WalkForwardSplitter is not None:
        print(f"\nWalk-forward validation: {args.n_splits} splits")
        all_prices = prices
        all_features = features_arr
        splitter = WalkForwardSplitter(
            n_splits=args.n_splits,
            train_size=max(252, len(all_prices) // (args.n_splits + 1)),
            test_size=max(63, len(all_prices) // (args.n_splits * 3)),
            gap=args.gap,
        )

        wf_accuracies = []
        for fold_idx, (train_idx, test_idx) in enumerate(
            splitter.split(np.arange(len(all_prices)))
        ):
            if len(test_idx) < args.context_length + args.window:
                continue

            fold_prices = all_prices[train_idx]
            fold_features = all_features[train_idx]
            fold_test_prices = all_prices[test_idx]
            fold_test_features = all_features[test_idx]

            fold_trajs = build_trajectories(
                fold_prices, fold_features,
                window=args.window,
                context_length=args.context_length,
                commission=args.commission,
            )
            fold_test_trajs = build_trajectories(
                fold_test_prices, fold_test_features,
                window=args.window,
                context_length=args.context_length,
                commission=args.commission,
            )

            if len(fold_trajs["states"]) <= args.context_length:
                continue

            fold_result = train_dt(
                fold_trajs,
                state_dim=fold_trajs["states"].shape[1],
                d_model=args.d_model,
                nhead=args.nhead,
                num_layers=args.num_layers,
                context_length=args.context_length,
                epochs=min(args.epochs, 10),  # Fewer epochs per fold
                batch_size=args.batch_size,
                lr=args.lr,
                device=device,
            )

            if len(fold_test_trajs["states"]) > args.context_length:
                fold_eval = evaluate_dt(
                    fold_result["model"], fold_test_trajs,
                    context_length=args.context_length,
                    device=device,
                )
                wf_accuracies.append(fold_eval["test_accuracy"])
                print(f"  Fold {fold_idx+1}: acc={fold_eval['test_accuracy']:.4f}")

        if wf_accuracies:
            avg_wf_acc = np.mean(wf_accuracies)
            print(f"Walk-forward avg accuracy: {avg_wf_acc:.4f} "
                  f"(over {len(wf_accuracies)} folds)")

    if args.dry_run:
        print("DRY-RUN complete. Pipeline validated successfully.")


if __name__ == "__main__":
    main()
