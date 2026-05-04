# QuantConnect Python Notebooks

Supports de cours pour l'apprentissage du trading algorithmique avec QuantConnect LEAN.

> **Note** : Ces notebooks sont des supports de cours a lire sur GitHub ou en local.
> Pour executer les backtests, copiez le code dans un projet [QuantConnect Cloud](https://www.quantconnect.com/lab).

---

## Phase 1 : Fondations LEAN (QC-Py-01 a 04)

| Notebook | Contenu |
|----------|---------|
| [QC-Py-01-Setup](QC-Py-01-Setup.ipynb) | Compte QC, premier backtest, architecture LEAN |
| [QC-Py-02-Platform-Fundamentals](QC-Py-02-Platform-Fundamentals.ipynb) | QCAlgorithm lifecycle, Initialize/OnData |
| [QC-Py-03-Data-Management](QC-Py-03-Data-Management.ipynb) | History API, consolidators, multi-timeframe |
| [QC-Py-04-Research-Workflow](QC-Py-04-Research-Workflow.ipynb) | QuantBook, pandas, notebook vers algorithme |

## Phase 2 : Classes d'actifs (QC-Py-05 a 10)

| Notebook | Contenu |
|----------|---------|
| [QC-Py-05-Universe-Selection](QC-Py-05-Universe-Selection.ipynb) | Univers dynamiques, filtres fondamentaux |
| [QC-Py-06-Options-Trading](QC-Py-06-Options-Trading.ipynb) | Chaines d'options, greeks, strategies couvertes |
| [QC-Py-07-Futures-Forex](QC-Py-07-Futures-Forex.ipynb) | Contrats a terme, devises, hedging |
| [QC-Py-08-Multi-Asset-Strategies](QC-Py-08-Multi-Asset-Strategies.ipynb) | Portefeuilles multi-classes d'actifs |
| [QC-Py-09-Order-Types](QC-Py-09-Order-Types.ipynb) | Market, limit, stop, trailing, combo orders |
| [QC-Py-10-Risk-Portfolio-Management](QC-Py-10-Risk-Portfolio-Management.ipynb) | Risk management, position sizing, drawdown |

## Phase 3 : Analyse et Strategie (QC-Py-11 a 17)

| Notebook | Contenu |
|----------|---------|
| [QC-Py-11-Technical-Indicators](QC-Py-11-Technical-Indicators.ipynb) | Indicateurs techniques, indicateurs custom |
| [QC-Py-12-Backtesting-Analysis](QC-Py-12-Backtesting-Analysis.ipynb) | Mesures de performance, Sharpe, drawdown |
| [QC-Py-13-Alpha-Models](QC-Py-13-Alpha-Models.ipynb) | Framework Alpha, signaux, combinaison |
| [QC-Py-14-Portfolio-Construction-Execution](QC-Py-14-Portfolio-Construction-Execution.ipynb) | Construction portefeuille, execution |
| [QC-Py-15-Parameter-Optimization](QC-Py-15-Parameter-Optimization.ipynb) | Optimization, grid search, walk-forward |
| [QC-Py-16-Alternative-Data](QC-Py-16-Alternative-Data.ipynb) | donnees alternatives, sentiment, fundamentals |
| [QC-Py-17-Sentiment-Analysis](QC-Py-17-Sentiment-Analysis.ipynb) | NLP, analyse sentiment, signaux textuels |

## Phase 4 : Machine Learning (QC-Py-18 a 28)

| Notebook | Contenu |
|----------|---------|
| [QC-Py-18-ML-Features-Engineering](QC-Py-18-ML-Features-Engineering.ipynb) | Feature engineering pour trading |
| [QC-Py-19-ML-Supervised-Classification](QC-Py-19-ML-Supervised-Classification.ipynb) | Classification, signaux d'achat/vente |
| [QC-Py-20-ML-Regression-Prediction](QC-Py-20-ML-Regression-Prediction.ipynb) | Regression, prediction de prix |
| [QC-Py-21-Portfolio-Optimization-ML](QC-Py-21-Portfolio-Optimization-ML.ipynb) | Optimisation ML de portefeuille |
| [QC-Py-22-Deep-Learning-LSTM](QC-Py-22-Deep-Learning-LSTM.ipynb) | Reseaux LSTM pour series temporelles |
| [QC-Py-23-Attention-Transformers](QC-Py-23-Attention-Transformers.ipynb) | Transformers, attention mechanism |
| [QC-Py-24-Autoencoders-Anomaly](QC-Py-24-Autoencoders-Anomaly.ipynb) | Detection d'anomalies, autoencodeurs |
| [QC-Py-25-Reinforcement-Learning](QC-Py-25-Reinforcement-Learning.ipynb) | RL, DQN, environnement trading |
| [QC-Py-26-LLM-Trading-Signals](QC-Py-26-LLM-Trading-Signals.ipynb) | LLM pour signaux de trading |
| [QC-Py-27-Production-Deployment](QC-Py-27-Production-Deployment.ipynb) | Deploiement live, monitoring |
| [QC-Py-28-Market-Regime-Detection](QC-Py-28-Market-Regime-Detection.ipynb) | Detection de regimes de marche |

## Entrainement ML (QC-Py-30 a 32)

Notebooks d'entrainement de modeles avec checkpoints GPU.

| Notebook | Modele | Sortie |
|----------|--------|--------|
| [QC-Py-30-LSTM-Training](QC-Py-30-LSTM-Training.ipynb) | LSTM | Checkpoint PyTorch |
| [QC-Py-31-Transformer-Training](QC-Py-31-Transformer-Training.ipynb) | Transformer | Checkpoint PyTorch |
| [QC-Py-32-RL-DQN-Trading](QC-Py-32-RL-DQN-Trading.ipynb) | DQN | Checkpoint PyTorch |

## Paper Trading (QC-Py-40 a 41)

| Notebook | Courtier |
|----------|----------|
| [QC-Py-40-PaperTrading-Binance](QC-Py-40-PaperTrading-Binance.ipynb) | Binance |
| [QC-Py-41-PaperTrading-IBKR](QC-Py-41-PaperTrading-IBKR.ipynb) | Interactive Brokers |

## Strategies Cloud (QC-Py-Cloud-*)

Notebooks de recherche et strategies executees sur QuantConnect Cloud.

| Notebook | Strategie |
|----------|-----------|
| [QC-Py-Cloud-01-FinBERT-Sentiment](QC-Py-Cloud-01-FinBERT-Sentiment.ipynb) | NLP FinBERT sentiment |
| [QC-Py-Cloud-01-RiskParity-Composite](QC-Py-Cloud-01-RiskParity-Composite.ipynb) | Risk Parite composite |
| [QC-Py-Cloud-02-ML-Classification](QC-Py-Cloud-02-ML-Classification.ipynb) | ML classification |
| [QC-Py-Cloud-02-SectorRotation-Momentum](QC-Py-Cloud-02-SectorRotation-Momentum.ipynb) | Rotation sectorielle |
| [QC-Py-Cloud-03-DualMomentum](QC-Py-Cloud-03-DualMomentum.ipynb) | Dual Momentum |
| [QC-Py-Cloud-03-Risk-Parity](QC-Py-Cloud-03-Risk-Parity.ipynb) | Risk Parite |
| [QC-Py-Cloud-04-MeanReversion](QC-Py-Cloud-04-MeanReversion.ipynb) | Mean Reversion |
| [QC-Py-Cloud-04-RL-DQN-Trading](QC-Py-Cloud-04-RL-DQN-Trading.ipynb) | RL DQN |
| [QC-Py-Cloud-05-MLP-Forecasting](QC-Py-Cloud-05-MLP-Forecasting.ipynb) | MLP Forecasting |
| [QC-Py-Cloud-05-RegimeSwitching](QC-Py-Cloud-05-RegimeSwitching.ipynb) | Regime Switching |
| [QC-Py-Cloud-06-VolTargeting](QC-Py-Cloud-06-VolTargeting.ipynb) | Volatility Targeting |

## Utilitaires

| Notebook | Usage |
|----------|-------|
| [QC-Py-Dataset-Workflow](QC-Py-Dataset-Workflow.ipynb) | Workflow de gestion des datasets QC |

---

**Navigation** : [README principal](../README.md) | [Livre de reference](https://www.hands-on-ai-trading.com/)
