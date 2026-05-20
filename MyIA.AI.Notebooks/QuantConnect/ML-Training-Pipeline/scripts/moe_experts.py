"""
Mixture-of-Experts (MoE) with regime-aware routing for financial prediction.

Each market regime (bull/bear/neutral/volatile) gets its own expert model.
A router classifies the current regime and delegates prediction to the
corresponding expert. This specialization makes each expert's task simpler
than a single model trying to learn all regimes simultaneously.

Architecture:
    1. Regime detector → label each timestep
    2. Per-regime expert (LSTM/GRU/MLP) trained only on its regime's data
    3. Router dispatches new samples to the appropriate expert
    4. Ensemble combines experts with optional gating

Used by:
    - Issue #754 Phase B: MoE+régimes approach to beat majority baseline
    - Walk-forward training with regime-aware expert specialization
    - eval_moe.py for backtesting regime-conditioned strategies

References:
    - Jacobs et al. (1991), "Adaptive Mixtures of Local Experts"
    - Fedus et al. (2022), "A Review of Sparse Expert Models in Deep Learning"
    - Hands-On AI Trading, Pik et al., Wiley 2025 — regime-aware strategies
"""

from __future__ import annotations

import numpy as np
import pandas as pd
from dataclasses import dataclass, field
from typing import Protocol
import logging

log = logging.getLogger(__name__)


# ---------------------------------------------------------------------------
# Expert protocol — any model implementing fit/predict
# ---------------------------------------------------------------------------

class ExpertModel(Protocol):
    """Minimal interface for an expert model."""

    def fit(self, X: np.ndarray, y: np.ndarray) -> "ExpertModel": ...

    def predict(self, X: np.ndarray) -> np.ndarray: ...

    def predict_proba(self, X: np.ndarray) -> np.ndarray: ...


@dataclass
class ExpertConfig:
    """Configuration for a single regime expert."""

    regime: str
    model_type: str = "mlp"
    hidden_sizes: tuple[int, ...] = (64, 32)
    max_iter: int = 200
    random_state: int = 42
    extra: dict | None = None


@dataclass
class MoEConfig:
    """Configuration for the MoE router + experts."""

    regimes: list[str] = field(
        default_factory=lambda: ["bull", "bear", "neutral", "volatile"]
    )
    expert_type: str = "mlp"
    hidden_sizes: tuple[int, ...] = (64, 32)
    max_iter: int = 200
    min_samples_per_expert: int = 50
    fallback_regime: str = "neutral"
    random_state: int = 42
    regime_method: str = "price"
    seq_len: int = 20
    d_model: int = 64
    nhead: int = 4
    num_layers: int = 2
    dropout: float = 0.1
    batch_size: int = 32
    learning_rate: float = 1e-3
    device: str = "cpu"


# ---------------------------------------------------------------------------
# PyTorch expert wrapper — sklearn-compatible LSTM/Transformer experts
# ---------------------------------------------------------------------------


class _PytorchExpertWrapper:
    """Wraps a PyTorch LSTM or Transformer as an sklearn-compatible expert.

    Internally reshapes flat (N, D) input into sequences (N, seq_len, D//seq_len)
    if needed, or uses a simple sliding window over flat features.
    """

    def __init__(
        self,
        model_type: str = "lstm",
        hidden_size: int = 64,
        max_iter: int = 200,
        seq_len: int = 20,
        d_model: int = 64,
        nhead: int = 4,
        num_layers: int = 2,
        dropout: float = 0.1,
        batch_size: int = 32,
        learning_rate: float = 1e-3,
        device: str = "cpu",
        random_state: int = 42,
    ):
        self.model_type = model_type
        self.hidden_size = hidden_size
        self.max_iter = max_iter
        self.seq_len = seq_len
        self.d_model = d_model
        self.nhead = nhead
        self.num_layers = num_layers
        self.dropout = dropout
        self.batch_size = batch_size
        self.learning_rate = learning_rate
        self.device = device
        self.random_state = random_state
        self._model = None
        self._scaler_mean = None
        self._scaler_std = None

    def _build_model(self, input_size: int):
        import torch
        import torch.nn as nn

        rng = torch.Generator()
        rng.manual_seed(self.random_state)

        if self.model_type == "lstm":
            class _LSTMExpert(nn.Module):
                def __init__(self_, inp_sz, hid_sz, n_lyr, drop):
                    super().__init__()
                    self_.rnn = nn.LSTM(
                        input_size=inp_sz,
                        hidden_size=hid_sz,
                        num_layers=n_lyr,
                        batch_first=True,
                        dropout=drop if n_lyr > 1 else 0.0,
                    )
                    self_.head = nn.Sequential(
                        nn.Linear(hid_sz, 32),
                        nn.ReLU(),
                        nn.Dropout(drop),
                        nn.Linear(32, 2),
                    )

                def forward(self_, x):
                    out, _ = self_.rnn(x)
                    return self_.head(out[:, -1, :])

            return _LSTMExpert(input_size, self.hidden_size, self.num_layers, self.dropout)

        else:  # transformer
            class _TransformerExpert(nn.Module):
                def __init__(self_, inp_sz, d_mod, n_heads, n_lyr, drop, seq_l):
                    super().__init__()
                    self_.input_proj = nn.Linear(inp_sz, d_mod)

                    # Sinusoidal positional encoding
                    pe = np.zeros((seq_l, d_mod))
                    pos = np.arange(0, seq_l).reshape(-1, 1)
                    div = np.exp(np.arange(0, d_mod, 2) * -(np.log(10000.0) / d_mod))
                    pe[:, 0::2] = np.sin(pos * div)
                    pe[:, 1::2] = np.cos(pos * div[:d_mod // 2])
                    self_.register_buffer("pos_enc", torch.tensor(pe.astype(np.float32)))

                    enc_layer = nn.TransformerEncoderLayer(
                        d_model=d_mod,
                        nhead=n_heads,
                        dim_feedforward=d_mod * 4,
                        dropout=drop,
                        batch_first=True,
                        activation="gelu",
                    )
                    self_.encoder = nn.TransformerEncoder(enc_layer, num_layers=n_lyr)
                    self_.head = nn.Sequential(
                        nn.LayerNorm(d_mod),
                        nn.Linear(d_mod, 32),
                        nn.GELU(),
                        nn.Dropout(drop),
                        nn.Linear(32, 2),
                    )

                def forward(self_, x):
                    h = self_.input_proj(x) + self_.pos_enc[:x.size(1)]
                    h = self_.encoder(h)
                    return self_.head(h[:, -1, :])

            return _TransformerExpert(
                input_size, self.d_model, self.nhead, self.num_layers,
                self.dropout, self.seq_len,
            )

    def _make_sequences(self, X: np.ndarray) -> np.ndarray:
        """Reshape flat features into sequences using sliding window."""
        n_samples, n_features = X.shape
        seq_len = min(self.seq_len, n_samples)

        if n_samples <= seq_len:
            # Not enough samples for sliding window — tile and use as 1-step
            return X.reshape(n_samples, 1, n_features)

        seqs = np.zeros((n_samples - seq_len + 1, seq_len, n_features), dtype=np.float32)
        for i in range(n_samples - seq_len + 1):
            seqs[i] = X[i:i + seq_len]
        return seqs

    def fit(self, X: np.ndarray, y: np.ndarray) -> "_PytorchExpertWrapper":
        import torch
        import torch.nn as nn

        torch.manual_seed(self.random_state)

        # Normalize
        self._scaler_mean = X.mean(axis=0, keepdims=True)
        self._scaler_std = np.where(X.std(axis=0) < 1e-8, 1.0, X.std(axis=0, keepdims=True))
        X_norm = (X - self._scaler_mean) / self._scaler_std

        # Build sequences
        X_seq = self._make_sequences(X_norm)

        # Align targets — trim the first (seq_len-1) to match sequence count
        trim = len(X) - len(X_seq)
        y_aligned = y[trim:]

        X_t = torch.tensor(X_seq, dtype=torch.float32, device=self.device)
        y_t = torch.tensor(y_aligned, dtype=torch.long, device=self.device)

        # Split into train/val for early stopping
        n_val = max(1, int(len(X_t) * 0.15))
        n_train = len(X_t) - n_val
        X_train, X_val = X_t[:n_train], X_t[n_train:]
        y_train, y_val = y_t[:n_train], y_t[n_train:]

        n_features = X_seq.shape[2]
        self._model = self._build_model(n_features).to(self.device)

        optimizer = torch.optim.Adam(
            self._model.parameters(), lr=self.learning_rate, weight_decay=1e-4,
        )
        loss_fn = nn.CrossEntropyLoss()

        train_dataset = torch.utils.data.TensorDataset(X_train, y_train)
        train_loader = torch.utils.data.DataLoader(
            train_dataset, batch_size=self.batch_size, shuffle=True,
        )

        # Early stopping with patience
        best_val_loss = float("inf")
        patience = 10
        patience_counter = 0
        best_state = None

        self._model.train()
        for epoch in range(self.max_iter):
            for xb, yb in train_loader:
                optimizer.zero_grad()
                logits = self._model(xb)
                loss = loss_fn(logits, yb)
                loss.backward()
                optimizer.step()

            # Validation check for early stopping
            if n_val > 0 and (epoch + 1) % 5 == 0:
                self._model.eval()
                with torch.no_grad():
                    val_logits = self._model(X_val)
                    val_loss = loss_fn(val_logits, y_val).item()
                self._model.train()

                if val_loss < best_val_loss:
                    best_val_loss = val_loss
                    patience_counter = 0
                    best_state = {k: v.clone() for k, v in self._model.state_dict().items()}
                else:
                    patience_counter += 1
                    if patience_counter >= patience:
                        log.debug(
                            f"Early stopping at epoch {epoch+1}/{self.max_iter} "
                            f"(val_loss={val_loss:.4f})"
                        )
                        break

        # Restore best weights
        if best_state is not None:
            self._model.load_state_dict(best_state)

        return self

    def _prepare_input(self, X: np.ndarray) -> "torch.Tensor":
        import torch

        X_norm = (X - self._scaler_mean) / self._scaler_std
        X_seq = self._make_sequences(X_norm)
        return torch.tensor(X_seq, dtype=torch.float32, device=self.device)

    def predict(self, X: np.ndarray) -> np.ndarray:
        import torch

        trim = len(X) - len(self._make_sequences((X - self._scaler_mean) / self._scaler_std))
        self._model.eval()
        with torch.no_grad():
            logits = self._model(self._prepare_input(X))
            preds = logits.argmax(dim=1).cpu().numpy()

        # Pad front with zeros for trimmed samples
        if trim > 0:
            preds = np.concatenate([np.zeros(trim, dtype=int), preds])
        return preds[:len(X)]

    def predict_proba(self, X: np.ndarray) -> np.ndarray:
        import torch
        import torch.nn.functional as F

        trim = len(X) - len(self._make_sequences((X - self._scaler_mean) / self._scaler_std))
        self._model.eval()
        with torch.no_grad():
            logits = self._model(self._prepare_input(X))
            proba = F.softmax(logits, dim=1).cpu().numpy()

        if trim > 0:
            pad = np.ones((trim, 2), dtype=np.float32) * 0.5
            proba = np.concatenate([pad, proba], axis=0)
        return proba[:len(X)]


# ---------------------------------------------------------------------------
# Expert factory — create models per architecture
# ---------------------------------------------------------------------------

def create_expert(config: ExpertConfig) -> ExpertModel:
    """Create an expert model from config.

    Supports: mlp, lstm, transformer.
    """
    from sklearn.neural_network import MLPClassifier
    from sklearn.preprocessing import StandardScaler
    from sklearn.pipeline import Pipeline

    if config.model_type == "mlp":
        return Pipeline([
            ("scaler", StandardScaler()),
            ("clf", MLPClassifier(
                hidden_layer_sizes=config.hidden_sizes,
                max_iter=config.max_iter,
                random_state=config.random_state,
                early_stopping=True,
                validation_fraction=0.15,
            )),
        ])

    if config.model_type in ("lstm", "transformer"):
        return _create_pytorch_expert(config)

    raise ValueError(
        f"Unknown model type: {config.model_type}. "
        f"Available: mlp, lstm, transformer"
    )


def _create_pytorch_expert(config: ExpertConfig) -> "_PytorchExpertWrapper":
    """Create a PyTorch-based expert (LSTM or Transformer)."""
    import torch

    torch.manual_seed(config.random_state)

    extra = config.extra or {}
    return _PytorchExpertWrapper(
        model_type=config.model_type,
        hidden_size=extra.get("hidden_size", config.hidden_sizes[0]),
        max_iter=config.max_iter,
        seq_len=extra.get("seq_len", 20),
        d_model=extra.get("d_model", 64),
        nhead=extra.get("nhead", 4),
        num_layers=extra.get("num_layers", 2),
        dropout=extra.get("dropout", 0.1),
        batch_size=extra.get("batch_size", 32),
        learning_rate=extra.get("learning_rate", 1e-3),
        device=extra.get("device", "cpu"),
        random_state=config.random_state,
    )


# ---------------------------------------------------------------------------
# MoE Router
# ---------------------------------------------------------------------------

@dataclass
class ExpertStats:
    """Training statistics for a single expert."""

    regime: str
    n_train: int = 0
    n_test: int = 0
    train_accuracy: float = 0.0
    test_accuracy: float = 0.0
    fitted: bool = False


class MoERouter:
    """Mixture-of-Experts with regime-aware routing.

    Workflow:
        1. Call fit() with features, labels, and regime labels
        2. Each regime gets its own expert model trained on regime-filtered data
        3. Call predict() — routes each sample to its regime's expert
        4. Call predict_proba() — same routing with probability outputs

    Parameters
    ----------
    config : MoEConfig
        Router and expert configuration.
    """

    def __init__(self, config: MoEConfig | None = None):
        self.config = config or MoEConfig()
        self._experts: dict[str, ExpertModel] = {}
        self._stats: dict[str, ExpertStats] = {}
        self._regime_names: list[str] = []
        self._fitted = False

    @property
    def regimes(self) -> list[str]:
        """List of regimes with trained experts."""
        return list(self._experts.keys())

    @property
    def stats(self) -> dict[str, ExpertStats]:
        """Per-expert training statistics."""
        return dict(self._stats)

    def _make_expert(self, regime: str) -> ExpertModel:
        extra = None
        if self.config.expert_type in ("lstm", "transformer"):
            extra = {
                "hidden_size": self.config.hidden_sizes[0] if self.config.hidden_sizes else 64,
                "seq_len": self.config.seq_len,
                "d_model": self.config.d_model,
                "nhead": self.config.nhead,
                "num_layers": self.config.num_layers,
                "dropout": self.config.dropout,
                "batch_size": self.config.batch_size,
                "learning_rate": self.config.learning_rate,
                "device": self.config.device,
            }
        cfg = ExpertConfig(
            regime=regime,
            model_type=self.config.expert_type,
            hidden_sizes=self.config.hidden_sizes,
            max_iter=self.config.max_iter,
            random_state=self.config.random_state,
            extra=extra,
        )
        return create_expert(cfg)

    def fit(
        self,
        X: np.ndarray,
        y: np.ndarray,
        regime_labels: np.ndarray | pd.Series,
    ) -> "MoERouter":
        """Train one expert per regime.

        Parameters
        ----------
        X : np.ndarray, shape (N, D)
            Feature matrix.
        y : np.ndarray, shape (N,)
            Target labels.
        regime_labels : array-like, shape (N,)
            Regime label for each sample.

        Returns
        -------
        self
        """
        regime_labels = np.asarray(regime_labels)
        unique_regimes = np.unique(regime_labels)
        self._regime_names = list(unique_regimes)
        self._experts.clear()
        self._stats.clear()

        for regime in unique_regimes:
            mask = regime_labels == regime
            X_regime = X[mask]
            y_regime = y[mask]
            n_samples = len(X_regime)

            if n_samples < self.config.min_samples_per_expert:
                log.warning(
                    f"Regime '{regime}': only {n_samples} samples "
                    f"(min={self.config.min_samples_per_expert}), skipping"
                )
                self._stats[regime] = ExpertStats(
                    regime=regime, n_train=n_samples, fitted=False
                )
                continue

            expert = self._make_expert(regime)
            try:
                expert.fit(X_regime, y_regime)
                train_acc = float(np.mean(expert.predict(X_regime) == y_regime))
                self._experts[regime] = expert
                self._stats[regime] = ExpertStats(
                    regime=regime,
                    n_train=n_samples,
                    train_accuracy=train_acc,
                    fitted=True,
                )
                log.info(
                    f"Expert '{regime}': trained on {n_samples} samples, "
                    f"train_acc={train_acc:.3f}"
                )
            except Exception as e:
                log.error(f"Expert '{regime}' training failed: {e}")
                self._stats[regime] = ExpertStats(
                    regime=regime, n_train=n_samples, fitted=False
                )

        n_fitted = sum(1 for s in self._stats.values() if s.fitted)
        log.info(
            f"MoE fitted: {n_fitted}/{len(unique_regimes)} experts trained"
        )
        self._fitted = True
        return self

    def _resolve_expert(self, regime: str) -> ExpertModel | None:
        """Get expert for regime, falling back to fallback_regime."""
        if regime in self._experts:
            return self._experts[regime]
        if self.config.fallback_regime in self._experts:
            return self._experts[self.config.fallback_regime]
        if self._experts:
            return next(iter(self._experts.values()))
        return None

    def predict(
        self,
        X: np.ndarray,
        regime_labels: np.ndarray | pd.Series,
    ) -> np.ndarray:
        """Predict using regime-routed experts.

        Parameters
        ----------
        X : np.ndarray, shape (N, D)
            Feature matrix.
        regime_labels : array-like, shape (N,)
            Regime label for each sample.

        Returns
        -------
        np.ndarray of predicted labels, shape (N,).
        """
        regime_labels = np.asarray(regime_labels)
        predictions = np.zeros(len(X), dtype=int)

        for regime in np.unique(regime_labels):
            mask = regime_labels == regime
            expert = self._resolve_expert(regime)
            if expert is not None:
                predictions[mask] = expert.predict(X[mask])
            else:
                predictions[mask] = 0

        return predictions

    def predict_proba(
        self,
        X: np.ndarray,
        regime_labels: np.ndarray | pd.Series,
    ) -> np.ndarray:
        """Predict probabilities using regime-routed experts.

        Parameters
        ----------
        X : np.ndarray, shape (N, D)
            Feature matrix.
        regime_labels : array-like, shape (N,)
            Regime label for each sample.

        Returns
        -------
        np.ndarray of probabilities, shape (N, n_classes).
        """
        regime_labels = np.asarray(regime_labels)
        all_proba = None

        for regime in np.unique(regime_labels):
            mask = regime_labels == regime
            expert = self._resolve_expert(regime)
            if expert is not None:
                proba = expert.predict_proba(X[mask])
            else:
                n_classes = max(2, len(set(int(v) for v in regime_labels)))
                proba = np.ones((mask.sum(), n_classes)) / n_classes

            if all_proba is None:
                all_proba = np.zeros((len(X), proba.shape[1]))
            all_proba[mask] = proba

        return all_proba

    def evaluate(
        self,
        X: np.ndarray,
        y: np.ndarray,
        regime_labels: np.ndarray | pd.Series,
    ) -> dict:
        """Evaluate MoE performance with per-regime breakdown.

        Returns
        -------
        dict with overall + per-regime accuracy, sample counts.
        """
        regime_labels = np.asarray(regime_labels)
        predictions = self.predict(X, regime_labels)
        overall_acc = float(np.mean(predictions == y))

        per_regime = {}
        for regime in np.unique(regime_labels):
            mask = regime_labels == regime
            if mask.sum() > 0:
                regime_acc = float(np.mean(predictions[mask] == y[mask]))
                per_regime[regime] = {
                    "accuracy": regime_acc,
                    "n_samples": int(mask.sum()),
                    "n_correct": int(np.sum(predictions[mask] == y[mask])),
                }
                if regime in self._stats:
                    self._stats[regime].n_test = int(mask.sum())
                    self._stats[regime].test_accuracy = regime_acc

        return {
            "overall_accuracy": overall_acc,
            "n_samples": len(X),
            "n_regimes": len(per_regime),
            "per_regime": per_regime,
            "experts_fitted": sum(1 for s in self._stats.values() if s.fitted),
        }


# ---------------------------------------------------------------------------
# Walk-forward MoE training
# ---------------------------------------------------------------------------

def train_moe_walk_forward(
    features: np.ndarray,
    targets: np.ndarray,
    regime_labels: np.ndarray | pd.Series,
    n_folds: int = 5,
    config: MoEConfig | None = None,
) -> list[dict]:
    """Walk-forward MoE training with expanding window.

    For each fold:
    1. Train experts on expanding window up to fold boundary
    2. Predict on out-of-sample fold period
    3. Record per-regime and overall accuracy

    Parameters
    ----------
    features : np.ndarray, shape (N, D)
        Feature matrix.
    targets : np.ndarray, shape (N,)
        Target labels.
    regime_labels : array-like, shape (N,)
        Regime labels for each sample.
    n_folds : int
        Number of walk-forward folds.
    config : MoEConfig, optional
        MoE configuration. Uses defaults if None.

    Returns
    -------
    list of dicts, one per fold, with train/test indices, accuracy, stats.
    """
    regime_labels = np.asarray(regime_labels)
    n = len(features)
    fold_size = n // (n_folds + 1)
    results = []

    for fold in range(n_folds):
        train_end = fold_size * (fold + 1)
        test_end = min(train_end + fold_size, n)

        if test_end <= train_end:
            break

        X_train, y_train = features[:train_end], targets[:train_end]
        X_test, y_test = features[train_end:test_end], targets[train_end:test_end]
        regime_train = regime_labels[:train_end]
        regime_test = regime_labels[train_end:test_end]

        router = MoERouter(config)
        router.fit(X_train, y_train, regime_train)

        eval_result = router.evaluate(X_test, y_test, regime_test)
        results.append({
            "fold": fold,
            "train_end": train_end,
            "test_end": test_end,
            "n_train": train_end,
            "n_test": test_end - train_end,
            **eval_result,
        })

        log.info(
            f"Fold {fold}: train={train_end}, test={test_end - train_end}, "
            f"acc={eval_result['overall_accuracy']:.3f}"
        )

    return results
