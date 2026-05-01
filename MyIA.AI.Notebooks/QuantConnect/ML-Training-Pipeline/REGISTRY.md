# Checkpoint Registry

Auto-generated: 2026-05-01 13:14

Total checkpoints: 13

## dqn

Checkpoints: 3

### 20260501_120415 [OK]

- Data hash: `17cb43b404e3ddf1`
- Metrics: best_avg_reward_10=2.2865, max_reward=3.0876, mean_reward=1.0177, mean_trades=749.3, min_reward=-1.8051, sharpe_estimate=0.8921
- Architecture: hidden_size=256, n_actions=3, state_size=242
- Config: device=cuda, hidden_size=256, num_episodes=50, symbol=SPY
- Files: metadata.json, model.pt

### 20260501_112641 [OK]

- Data hash: `17cb43b404e3ddf1`
- Metrics: best_avg_reward_10=-0.1559, max_reward=0.9312, mean_reward=-0.5358, mean_trades=739.6, min_reward=-1.5861, sharpe_estimate=-0.8096
- Architecture: hidden_size=32, n_actions=3, state_size=242
- Config: device=cpu, hidden_size=32, num_episodes=20, symbol=SPY
- Files: metadata.json, model.pt

### 20260501_111005 [OK]

- Data hash: `synthetic-dryrun`
- Metrics: best_avg_reward_10=-0.0017, max_reward=0.1665, mean_reward=-0.0017, mean_trades=44.1, min_reward=-0.2395, sharpe_estimate=-0.0134
- Architecture: hidden_size=256, n_actions=3, state_size=242
- Config: device=cpu, hidden_size=256, num_episodes=10, symbol=SPY
- Files: metadata.json, model.pt

## lstm

Checkpoints: 3

### 20260501_113924 [OK]

- Data hash: `17cb43b404e3ddf1`
- Metrics: best_val_loss=0.000144, direction_accuracy=0.4848, direction_accuracy_significant=0.4957, epochs_trained=30, mae=0.008986, mse=0.000147
- Architecture: hidden_size=256, input_size=15, num_layers=3
- Config: device=cuda, epochs=30, hidden_size=256, num_layers=3, symbol=SPY
- Files: metadata.json, model.pt

### 20260501_111103 [OK]

- Data hash: `17cb43b404e3ddf1`
- Metrics: best_val_loss=0.00015, direction_accuracy=0.5149, direction_accuracy_significant=0.5014, epochs_trained=5, mae=0.009063, mse=0.000153
- Architecture: hidden_size=64, input_size=15, num_layers=1
- Config: device=cpu, epochs=5, hidden_size=64, num_layers=1, symbol=SPY
- Files: metadata.json, model.pt

### 20260501_110937 [OK]

- Data hash: `synthetic-dryrun`
- Metrics: best_val_loss=0.000261, direction_accuracy=0.5, direction_accuracy_significant=0.5139, epochs_trained=2, mae=0.013328, mse=0.000265
- Architecture: hidden_size=128, input_size=15, num_layers=2
- Config: device=cpu, epochs=2, hidden_size=128, num_layers=2, symbol=SPY
- Files: metadata.json, model.pt

## rf

Checkpoints: 4

### 20260501_113900 [OK]

- Data hash: `17cb43b404e3ddf1`
- Metrics: accuracy=0.4966, f1=0.4958, precision=0.505, recall=0.4966, test_samples=441, train_samples=1764
- Config: symbol=SPY
- Files: metadata.json, model.joblib

### 20260501_111041 [OK]

- Data hash: `17cb43b404e3ddf1`
- Metrics: accuracy=0.4966, f1=0.4958, precision=0.505, recall=0.4966, test_samples=441, train_samples=1764
- Config: symbol=SPY
- Files: metadata.json, model.joblib

### 20260501_111026 [OK]

- Data hash: `synthetic-dryrun`
- Metrics: accuracy=0.3933, f1=0.3951, precision=0.4033, recall=0.3933, test_samples=89, train_samples=352
- Config: symbol=SPY
- Files: metadata.json, model.joblib

### 20260501_110930 [OK]

- Data hash: `synthetic-dryrun`
- Metrics: accuracy=0.3933, f1=0.3951, precision=0.4033, recall=0.3933, test_samples=89, train_samples=352
- Config: symbol=SPY
- Files: metadata.json, model.joblib

## transformer

Checkpoints: 3

### 20260501_113923 [OK]

- Data hash: `17cb43b404e3ddf1`
- Metrics: best_val_loss=7.3e-05, direction_accuracy=0.4872, direction_accuracy_significant=0.5071, epochs_trained=30, mae=0.009084, mse=0.000149
- Architecture: d_model=128, input_size=17, nhead=8, num_layers=4
- Config: d_model=128, device=cuda, epochs=30, nhead=8, num_layers=4, symbol=SPY
- Files: metadata.json, model.pt

### 20260501_111130 [OK]

- Data hash: `17cb43b404e3ddf1`
- Metrics: best_val_loss=9.9e-05, direction_accuracy=0.4714, direction_accuracy_significant=0.468, epochs_trained=5, mae=0.011033, mse=0.0002
- Architecture: d_model=64, input_size=17, nhead=4, num_layers=2
- Config: d_model=64, device=cpu, epochs=5, nhead=4, num_layers=2, symbol=SPY
- Files: metadata.json, model.pt

### 20260501_110947 [OK]

- Data hash: `synthetic-dryrun`
- Metrics: best_val_loss=0.000252, direction_accuracy=0.4762, direction_accuracy_significant=0.4722, epochs_trained=2, mae=0.018693, mse=0.000542
- Architecture: d_model=128, input_size=17, nhead=4, num_layers=4
- Config: d_model=128, device=cpu, epochs=2, nhead=4, num_layers=4, symbol=SPY
- Files: metadata.json, model.pt
