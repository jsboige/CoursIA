# Stage 7: Decision Transformer (Offline RL for Trading)

Decision Transformer applied to algorithmic trading, following arXiv:2411.17900.
Unlike online RL (DQN, PPO), DT learns entirely from historical trajectories
without environment interaction, eliminating exploration noise and replay
buffer instability.

## Why Decision Transformer > Online RL for Trading

| Issue | Online RL (DQN/PPO) | Decision Transformer |
|-------|---------------------|---------------------|
| Data leakage | Environment sim can leak future info | Purely offline, no sim needed |
| Exploration | Random actions waste capital | No exploration, learns from data |
| Training stability | Replay buffer, moving targets | Stable supervised-style training |
| Inference control | Policy is fixed | Return-conditioned (specify target) |
| Overfitting risk | High (sim != reality) | Lower (learns from real trajectories) |
| Sample efficiency | Needs millions of steps | Learns from available history |

## Architecture

```
Input Sequence (per timestep t):
    [RTG_t, State_t, Action_t, RTG_{t+1}, State_{t+1}, Action_{t+1}, ...]
           |         |         |              |              |
           v         v         v              v              v
     +----------+ +--------+ +-----------+ +----------+ +--------+
     | RTG Emb  | | State  | | Action    | | RTG Emb  | | State  |
     | Linear   | | Encode | | Embedding | | Linear   | | Encode |
     | (1->d)   | | (S->d) | | (3->d)    | | (1->d)   | | (S->d) |
     +----+-----+ +---+----+ +-----+-----+ +----+-----+ +---+----+
          |           |            |              |           |
          +-----------+------------+              +-----------+------+
                      |                                        |
                      v                                        v
              +-------+-------+                     +---------+--------+
              | Pos Encoding  |                     | Pos Encoding     |
              | (sinusoidal)  |                     | (sinusoidal)     |
              +-------+-------+                     +---------+--------+
                      |                                        |
                      +--------------------+-------------------+
                                           |
                                           v
                              +------------+-----------+
                              |  Transformer Encoder   |
                              |  (d_model, nhead, L)   |
                              |  + Causal Mask         |
                              +------------+-----------+
                                           |
                                           v
                              +------------+-----------+
                              |  LayerNorm             |
                              +------------+-----------+
                                           |
                                           v
                              +------------+-----------+
                              |  Action Head           |
                              |  Linear(d -> 3)        |
                              |  (hold/buy/sell logits)|
                              +------------------------+
```

### Components

| Component | Description | Default |
|-----------|-------------|---------|
| StateEncoder | Linear(state_dim, d_model) + LayerNorm + GELU | d_model=128 |
| ActionEmbedding | Embedding(3, d_model) | 3 actions: hold/buy/sell |
| ReturnToGoEmbedding | Linear(1, d_model) + GELU | Scalar RTG -> d_model |
| PositionalEncoding | Sinusoidal (Vaswani 2017) | max_len=60+1 |
| TransformerEncoder | nn.TransformerEncoder layers | nhead=4, num_layers=3 |
| ActionHead | Linear(d_model, 3) | Action logits |

## GPT-2 Initialization Rationale

The transformer backbone follows GPT-2-style architecture (causal attention,
pre-norm) rather than BERT-style (bidirectional). This is critical because:

1. **Causality**: Trading decisions must not see future prices. The causal mask
   enforces temporal ordering just like language modeling.
2. **Autoregressive**: Predict next action given past (RTG, state, action) tuples,
   analogous to predicting next token given previous tokens.
3. **Return-conditioned**: By conditioning on return-to-go, the model can be
   steered toward desired performance levels at inference time.

## LoRA for Parameter-Efficient Fine-Tuning

When `--lora` flag is set and `peft` library is available:

- LoRA rank: 8, alpha: 16
- Target modules: StateEncoder, ActionEmbedding, RTGEmbedding
- Dropout: 0.05
- Reduces trainable parameters by ~90% for fine-tuning on new assets

## Sequence Construction

Each training sample is a sequence of `context_length` timesteps:

```python
# For each timestep t in the trajectory:
RTG_t = sum(rewards[t:])         # Return-to-go (cumulative future reward)
State_t = features[t-W:t].flatten()  # State window (W lookback)
Action_t = action_labels[t]      # Action taken (0=hold, 1=buy, 2=sell)

# Interleaved input: [RTG_0, State_0, Action_0, RTG_1, State_1, Action_1, ...]
# Target: Action_{t+1} at each state position
```

RTG is computed backward from the end of the trajectory, ensuring no lookahead
bias. The model learns: "given this return-to-go target and current state,
what action should I take?"

## CLI Usage

```bash
# Dry-run (CPU, synthetic data, 50 steps)
python scripts/train_rl_dt.py --dry-run

# Full training on yfinance SPY
python scripts/train_rl_dt.py --data-dir ../datasets/yfinance --symbol SPY \
    --start 2010-01-01 --epochs 50

# Custom architecture
python scripts/train_rl_dt.py --data-dir ../datasets/yfinance --symbol SPY \
    --d-model 256 --nhead 8 --num-layers 4 --context-length 30

# Walk-forward validation
python scripts/train_rl_dt.py --data-dir ../datasets/yfinance --symbol SPY \
    --walk-forward --n-splits 5 --gap 24

# With LoRA fine-tuning
python scripts/train_rl_dt.py --dry-run --lora

# Custom transaction costs
python scripts/train_rl_dt.py --data-dir ../datasets/yfinance --symbol SPY \
    --commission 0.002

# Evaluate a checkpoint
python scripts/eval_rl_dt.py --checkpoint checkpoints/dt/20260505_120000
python scripts/eval_rl_dt.py --dry-run
```

## Anti-Pattern Safeguards

All scripts enforce (consistent with Stage 0 discipline):

1. **Test ratio honored**: `--test-ratio` defaults to 0.2, actual ratio reported
2. **Train-only normalization**: Z-stats computed on training set only
3. **Majority-class baseline**: Always computed and reported
4. **Transaction costs**: Applied via `--commission` flag
5. **Thermal watchdog**: `batch_thermal_check()` every 5 batches, MAX_TEMP=80C
6. **AMP**: Automatic Mixed Precision when CUDA available
7. **Gradient clipping**: max_norm=1.0

## Output Format

Checkpoints saved to `--checkpoint-dir` (default: `checkpoints/dt/`):

```
checkpoints/dt/
  20260505_120000/
    model.pt          # PyTorch state dict
    metadata.json     # hyperparams, metrics, architecture, data_hash
```

### Metrics Reported

- `best_train_loss`: Cross-entropy loss on training sequences
- `majority_class_baseline`: Frequency of most common action (must beat this)
- `test_accuracy`: Action prediction accuracy on held-out test set
- `edge_over_majority`: test_accuracy - majority_class_accuracy
- `sharpe`: Annualized Sharpe ratio from simulated returns
- `max_drawdown`: Maximum drawdown from cumulative returns
- `n_trades`: Number of position changes (for cost analysis)
- `gross_sharpe` / `net_sharpe`: Before/after transaction costs

## Performance Expectations

| Configuration | CPU Time | GPU Time | Params |
|--------------|----------|----------|--------|
| Dry-run (d=32, 1L) | ~5s | ~1s | ~5K |
| Default (d=128, 3L) | ~3min | ~30s | ~200K |
| Large (d=256, 4L) | ~10min | ~1min | ~800K |
| Large + LoRA | ~10min | ~1min | ~80K trainable |

CPU-only mode is fully supported. AMP auto-enables on CUDA. The thermal
watchdog prevents GPU overheating on sustained training runs.

## Tests

16 tests in `tests/test_train_rl_dt.py`, all CPU-only:

| # | Test | Category |
|---|------|----------|
| 1 | StateEncoder shape | Architecture |
| 2 | ActionEmbedding shape | Architecture |
| 3 | RTGEmbedding shape | Architecture |
| 4 | PositionalEncoding output | Architecture |
| 5 | DT forward pass shape | Architecture |
| 6 | DT forward with mask | Architecture |
| 7 | Sequence formation length | Data pipeline |
| 8 | RTG monotonicity | Data pipeline |
| 9 | Gradient flow | Training |
| 10 | Save/load roundtrip | Checkpoint |
| 11 | Dry-run completes | Integration |
| 12 | Temporal split no leakage | Anti-bias |
| 13 | No lookahead in RTG | Anti-bias |
| 14 | Transaction costs applied | Costs |
| 15 | Majority baseline reported | Baseline |
| 16 | Checkpoint metadata | Checkpoint |
| + | Walk-forward splits (opt) | Validation |

## References

- Chen et al. (2021): "Decision Transformer: Reinforcement Learning via Sequence Modeling" (NeurIPS)
- arXiv:2411.17900: "Decision Transformer for Algorithmic Trading"
- Vaswani et al. (2017): "Attention Is All You Need" (Transformer architecture)
- Hu et al. (2022): "LoRA: Low-Rank Adaptation of Large Language Models"
- Lopez de Prado (2018): "Advances in Financial Machine Learning" (Walk-forward, purged CV)
