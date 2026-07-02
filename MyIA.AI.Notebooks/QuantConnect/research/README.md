# Standalone Research Notebooks

Independent research using local data (yfinance, pandas, sklearn). No QuantConnect Cloud required.

## Notebooks

| Notebook | Topic | Type | Data Source |
|----------|-------|------|-------------|
| `research_btc_ml.ipynb` | BTC ML prediction features | (c) Standalone | yfinance |
| `research_composite_ff_aw.ipynb` | FamaFrench + AllWeather composite | (c) Standalone | yfinance |
| `research_composite_mom_regime.ipynb` | Momentum + Regime composite | (c) Standalone | yfinance |
| `research_m11ef_ensemble.ipynb` | Ensemble methods | (c) Standalone | yfinance |
| `research_m12_har_rv_j.ipynb` | HAR-RV-J volatility model (hourly) | (c) Standalone | yfinance |
| `research_m12_har_rv_j_minute.ipynb` | M12-HF : variante minute (QuantBook QC Cloud) | (c) Standalone | QC Cloud crypto |
| `research_m12_hf_btc_local.ipynb` | M12-HF : verdict BTC minute vs hourly (local) | (c) Standalone | BTC tick Bitstamp |
| `research_m12_hf_dm_test.ipynb` | M12-HF : test de significativité Diebold-Mariano | (c) Standalone | BTC tick Bitstamp |
| `research_quality_lowvol.ipynb` | Quality + Low Vol factor | (c) Standalone | yfinance |
| `research_risk_parity.ipynb` | Risk parity allocation | (c) Standalone | yfinance |
| `research_rl_grpo.ipynb` | RL GRPO trading agent | (c) Standalone | yfinance |
| `research_rl_intro.ipynb` | RL introduction | (c) Standalone | yfinance |
| `research_rl_multi_asset.ipynb` | RL multi-asset allocation | (c) Standalone | yfinance |
| `research_rl_ppo.ipynb` | PPO trading agent | (c) Standalone | yfinance |
| `research_rl_reward_shaping.ipynb` | RL reward shaping | (c) Standalone | yfinance |
| `research_rl_tactical_overlay.ipynb` | RL tactical overlay | (c) Standalone | yfinance |
| `research_vrp_putwrite.ipynb` | VRP put-write strategy | (c) Standalone | yfinance |

All 17 notebooks are type **(c) standalone research**. La plupart s'exécutent localement avec `pip install yfinance pandas matplotlib scikit-learn` ; la famille M12-HF (3 notebooks) utilise des données tick BTC Bitstamp possédées (agrégées en minute localement), et la variante `_minute` est un QuantBook à exécuter sur QC Cloud.

---

## Conclusion / Prochaines étapes

### Ce que vous avez appris

Ces **17 notebooks standalone** sont le **laboratoire local** de la série QuantConnect : ils ne nécessitent **pas** de compte QC Cloud ni de données payantes — `yfinance` (données gratuites) + `pandas` / `scikit-learn` suffisent (la famille M12-HF utilise des données tick BTC possédées). Ils illustrent deux familles de recherche :

- **Recherche factorielle & allocation** (HAR-RV-J vol, FamaFrench + AllWeather composite, Momentum + Regime, Quality/LowVol, Risk Parity, VRP put-write) — on apprend que les modèles de volatilité et d'allocation robuste sont reproductibles en local sur données publiques, et que les composites (M12, M11ef) sont les briques des stratégies *Robuste* du catalogue. **Verdict honnête M12-HF** (`research_m12_hf_btc_local.ipynb` + `research_m12_hf_dm_test.ipynb`) : l'estimation de la realized variance en minute **bat** celle en hourly (delta médian +0.548, MSE minute ~moitié hourly), statistiquement validée par un test de Diebold-Mariano (HAC, p≈0.000) et un block-bootstrap dont l'IC95 est entièrement négatif. La cause du gain est cependant la **fréquence d'échantillonnage** (qualité de l'estimateur RV, Andersen-Bollerslev-Diebold 2003), **pas** la composante de jump — HAR-Classic sans jump montre le même gain. Leçon méthodologique : la résolution hourly (24 bars/jour) est trop bruitée pour le vol-targeting Kelly ; la minute (1440 bars/jour) l'est beaucoup moins.
- **Recherche Reinforcement Learning** (intro, PPO, GRPO, reward shaping, multi-asset, tactical overlay) — on apprend que le RL trading se prototypé localement avant tout déploiement QC Cloud, et que le *reward shaping* est le levier le plus sensible (un reward mal spécifié fige la policy). **Leçon d'intégrité #3360** : diviser la reward portfolio-level par le nombre d'actifs (`reward / N_ASSETS`) détruit le signal du critic per-asset → la policy gèle près de l'uniforme → l'argmax collapse vers Buy (fingerprint buy-and-hold, Sharpe 0.657 identique au collapse PPO). Corrigé : la reward portfolio complète alimente chaque transition per-asset (cohérence #3359/#3360). Verdict ré-évalué honnête après fix : NO BEATS (A2C Sharpe 0.000, SAC −0.063 sur univers non-FAANG) — pour la bonne raison.

Le fil rouge : **l'indépendance de la plateforme**. Ces notebooks prouvent que l'idéation et la validation ML peuvent se faire hors QC Cloud ; le cloud n'est requis que pour le backtest haute-fidélité sur données natives.

### Prochaines étapes

1. **Installer l'environnement local** : `pip install yfinance pandas matplotlib scikit-learn` puis ouvrir un notebook dans `jupyter`.
2. **Commencer par l'intro RL** : `research_rl_intro.ipynb` avant les avancés (PPO, GRPO, reward shaping).
3. **Reproduire un keeper** : `research_m12_har_rv_j.ipynb` (modèle de volatilité HAR-RV-J, un des 4 KEEPERS du curriculum ML-V2).
4. **Tester le reward shaping** : `research_rl_reward_shaping.ipynb` — modifier la fonction de reward et observer l'impact sur la policy convergée.
5. **Combiner en composite** : `research_composite_mom_regime.ipynb` montre comment assembler Momentum + Regime en une stratégie multi-signal.
6. **Déployer le meilleur sur QC Cloud** : une fois une idée validée en local, la porter en `main.py` dans `../projects/` pour un backtest réaliste avec coûts de transaction.

> **Rappel honnête** : les données `yfinance` (gratuites) ont des limitations (ajustements, splits, profondeur historique) par rapport aux données QC natives. Un edge confirmé en local doit être **re-validé** sur QC Cloud avant toute conclusion de robustesse.
