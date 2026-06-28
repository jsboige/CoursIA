# Crypto LSTM Prediction

**Status**: 🔄 Research Phase - Based on HandsOnAITrading Book

## Description

Deep Learning model for cryptocurrency price prediction using LSTM (Long Short-Term Memory) networks with advanced architecture.

### Key Features

- **DLinear Architecture** (AAAI 2023): Ultra-simple decomposition + linear layers
  - SeriesDecomposition block (moving average trend/seasonal split)
  - No attention mechanism (~10K parameters)
  - SOTA performance on time series forecasting

- **PyTorch Implementation**: Full deep learning stack
  - Custom Dataset and DataLoader
  - SeriesDecomposition module
  - DLinear model (trend + seasonal forecasting)

- **Target**: BTCUSDT price prediction

## Architecture

```
Input → SeriesDecomposition → [Trend, Seasonal] → DLinear → Prediction
         (Moving Avg)
```

### DLinear Model Components

1. **SeriesDecomposition**: Decomposes time series into trend and seasonal components
2. **Trend Linear Layer**: Projects trend features
3. **Seasonal Linear Layer**: Projects seasonal features
4. **Reconstruction**: Combines trend + seasonal predictions

## Files

- `main.py`: QC algorithm with PyTorch model integration
- `research.ipynb`: Research notebook with model training and evaluation
- `config.json`: Project configuration

## Reference

- **Paper**: "Are Transformers Effective for Time Series Forecasting?" (AAAI 2023)
- **Book**: Hands-On AI Trading (Chapter on Deep Learning)
- **Related Notebook**: QC-Py-22-Deep-Learning-LSTM.ipynb

## Status

This is a research/exploration project. Backtesting results and performance metrics to be determined.

---

**Note**: Crypto markets are highly volatile. This strategy is for educational purposes.
