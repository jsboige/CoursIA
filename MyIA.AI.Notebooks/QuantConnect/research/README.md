# Standalone Research Notebooks

Independent research using local data (yfinance, pandas, sklearn). No QuantConnect Cloud required.

## Notebooks

| Notebook | Topic | Type | Data Source |
|----------|-------|------|-------------|
| `research_btc_ml.ipynb` | BTC ML prediction features | (c) Standalone | yfinance |
| `research_composite_ff_aw.ipynb` | FamaFrench + AllWeather composite | (c) Standalone | yfinance |
| `research_composite_mom_regime.ipynb` | Momentum + Regime composite | (c) Standalone | yfinance |
| `research_m11ef_ensemble.ipynb` | Ensemble methods | (c) Standalone | yfinance |
| `research_m12_har_rv_j.ipynb` | HAR-RV-J volatility model | (c) Standalone | yfinance |
| `research_quality_lowvol.ipynb` | Quality + Low Vol factor | (c) Standalone | yfinance |
| `research_risk_parity.ipynb` | Risk parity allocation | (c) Standalone | yfinance |
| `research_rl_grpo.ipynb` | RL GRPO trading agent | (c) Standalone | yfinance |
| `research_rl_intro.ipynb` | RL introduction | (c) Standalone | yfinance |
| `research_rl_multi_asset.ipynb` | RL multi-asset allocation | (c) Standalone | yfinance |
| `research_rl_ppo.ipynb` | PPO trading agent | (c) Standalone | yfinance |
| `research_rl_reward_shaping.ipynb` | RL reward shaping | (c) Standalone | yfinance |
| `research_rl_tactical_overlay.ipynb` | RL tactical overlay | (c) Standalone | yfinance |
| `research_vrp_putwrite.ipynb` | VRP put-write strategy | (c) Standalone | yfinance |

All 14 notebooks are type **(c) standalone research**. Executable locally with `pip install yfinance pandas matplotlib scikit-learn`.

---

## Conclusion / Prochaines étapes

### Ce que vous avez appris

Ces **14 notebooks standalone** sont le **laboratoire local** de la série QuantConnect : ils ne nécessitent **pas** de compte QC Cloud ni de données payantes — `yfinance` (données gratuites) + `pandas` / `scikit-learn` suffisent. Ils illustrent deux familles de recherche :

- **Recherche factorielle & allocation** (HAR-RV-J vol, FamaFrench + AllWeather composite, Momentum + Regime, Quality/LowVol, Risk Parity, VRP put-write) — on apprend que les modèles de volatilité et d'allocation robuste sont reproductibles en local sur données publiques, et que les composites (M12, M11ef) sont les briques des stratégies *Robuste* du catalogue.
- **Recherche Reinforcement Learning** (intro, PPO, GRPO, reward shaping, multi-asset, tactical overlay) — on apprend que le RL trading se prototypé localement avant tout déploiement QC Cloud, et que le *reward shaping* est le levier le plus sensible (un reward mal spécifié fige la policy).

Le fil rouge : **l'indépendance de la plateforme**. Ces notebooks prouvent que l'idéation et la validation ML peuvent se faire hors QC Cloud ; le cloud n'est requis que pour le backtest haute-fidélité sur données natives.

### Prochaines étapes

1. **Installer l'environnement local** : `pip install yfinance pandas matplotlib scikit-learn` puis ouvrir un notebook dans `jupyter`.
2. **Commencer par l'intro RL** : `research_rl_intro.ipynb` avant les avancés (PPO, GRPO, reward shaping).
3. **Reproduire un keeper** : `research_m12_har_rv_j.ipynb` (modèle de volatilité HAR-RV-J, un des 4 KEEPERS du curriculum ML-V2).
4. **Tester le reward shaping** : `research_rl_reward_shaping.ipynb` — modifier la fonction de reward et observer l'impact sur la policy convergée.
5. **Combiner en composite** : `research_composite_mom_regime.ipynb` montre comment assembler Momentum + Regime en une stratégie multi-signal.
6. **Déployer le meilleur sur QC Cloud** : une fois une idée validée en local, la porter en `main.py` dans `../projects/` pour un backtest réaliste avec coûts de transaction.

> **Rappel honnête** : les données `yfinance` (gratuites) ont des limitations (ajustements, splits, profondeur historique) par rapport aux données QC natives. Un edge confirmé en local doit être **re-validé** sur QC Cloud avant toute conclusion de robustesse.
