<!-- CATALOG-STATUS
series: QuantConnect-research
pedagogical_count: 0
breakdown: 
maturity: 
-->

# Notebooks de recherche standalone

Recherche indépendante utilisant des données locales (yfinance, pandas, sklearn). La majorité des notebooks s'exécutent en local sans QuantConnect Cloud ; les notebooks des familles M11/M12 (`research_btc_ml`, `research_m11ef_ensemble`, `research_m12_har_rv_j`, `research_m12_har_rv_j_minute`) chargent leurs données crypto via `QuantBook` QC Cloud (type (b), signalés dans le tableau ci-dessous).

## Comment lire ce README

- **Vous voulez une carte du dossier** : la colonne « Ce qu'on y apprend » de la table ci-dessous
  dit, pour chaque carnet, la question qu'il tranche et le verdict qu'il publie.
- **Vous débutez** : `intraday_volume_periodicity.ipynb` est la seule illustration entièrement
  synthétique — elle ne demande ni compte QuantConnect ni données téléchargées.
- **Vous cherchez un résultat publiable** : commencez par les carnets qui portent un verdict
  explicite (`NO BEATS`, `INCONCLUSIVE`) — la colonne le nomme, et la section [Ce que vous avez
  appris](#ce-que-vous-avez-appris) dit ce que chaque famille en tire.
- **Vous voulez la famille volatilité haute fréquence** : les carnets M12 forment une paire —
  l'estimation, puis le test qui la valide.
- **Vous devez choisir votre environnement** : la colonne « Type » sépare les carnets locaux des
  carnets QuantBook ; la [Conclusion](#conclusion--prochaines-etapes) donne la commande
  d'installation locale.
- Les nombres d'inventaire vivent dans le bloc `CATALOG-STATUS` et le catalogue généré ; ce README
  ne les recopie pas.

## Parcours principal

| Notebook | Ce qu'on y apprend | Type | Source de données |
|----------|-------|------|-------------------|
| `intraday_volume_periodicity.ipynb` | Periodicite intraday du volume (illustration pedagogique CPU-only) | (c) Standalone | simulation synthetique (numpy) |
| `research_btc_ml.ipynb` | Caractéristiques de prédiction ML BTC | (b) QuantBook QC Cloud | QC Cloud crypto (BTCUSDT Binance) |
| `research_composite_ff_aw.ipynb` | Composite FamaFrench + AllWeather | (c) Standalone | yfinance |
| `research_composite_mom_regime.ipynb` | Composite Momentum + Régime | (c) Standalone | yfinance |
| `research_day_of_week.ipynb` | Effet jour de la semaine (DOW, calendrier) — verdict NO BEATS net de coûts | (c) Standalone | yfinance (SPY/QQQ/EFA) |
| `research_fifty_two_week_high.ipynb` | Effet plus-haut 52 sem (George–Hwang 2004) : cross-section 20 grandes caps, verdict NO BEATS net de coûts | (c) Standalone | yfinance |
| `research_idio_vol_anomaly.ipynb` | Anomalie de volatilité idiosyncratique (IVOL) : backtest long-short, verdict INCONCLUSIVE | (c) Standalone | panier local CSV (SPY + 14 ETF) |
| `research_iv_rank_strike_clusters.ipynb` | Facteurs IV-Rank et strike-availability (article QC #18766, verdicts NO-BEATS) | (c) Standalone | yfinance (VIX/SPY) + resultats QC Cloud mesures |
| `research_m11ef_ensemble.ipynb` | Méthodes d'ensemble | (b) QuantBook QC Cloud | QC Cloud crypto (Bitstamp/Coinbase) |
| `research_m12_har_rv_j.ipynb` | Modèle de volatilité HAR-RV-J (horaire) | (b) QuantBook QC Cloud | QC Cloud crypto (Hour) |
| `research_m12_har_rv_j_minute.ipynb` | M12-HF : variante minute (QuantBook QC Cloud) | (b) QuantBook QC Cloud | QC Cloud crypto (Minute, non exécuté) |
| `research_m12_hf_btc_local.ipynb` | M12-HF : verdict BTC minute vs hourly (local) | (c) Standalone | BTC tick Bitstamp |
| `research_m12_hf_dm_test.ipynb` | M12-HF : test de significativité Diebold-Mariano | (c) Standalone | BTC tick Bitstamp |
| `research_month_of_year.ipynb` | Saisonnalité mensuelle (effet de mois / « January effect », calendrier) — verdict NO BEATS net de coûts | (c) Standalone | yfinance (SPY/QQQ/EFA) |
| `research_quality_lowvol.ipynb` | Facteur Quality + Low Vol | (c) Standalone | yfinance |
| `research_regime_pairs.ipynb` | Pairs trading a changement de regime (Vasicek 2-regime + filtre de Hamilton, article QC #21678) : confrontation OOS au z-score classique, verdict INCONCLUSIVE net de 10 bps | (c) Standalone | yfinance (49 grandes caps S&P 500) |
| `research_risk_parity.ipynb` | Allocation risk parity | (c) Standalone | yfinance |
| `research_turn_of_month.ipynb` | Effet de calendrier turn of the month (brut, net de coûts, walk-forward + DM, verdict NO BEATS) | (c) Standalone | yfinance (SPY/QQQ/EFA) |
| `research_rl_grpo.ipynb` | Agent de trading RL GRPO | (c) Standalone | yfinance |
| `research_rl_intro.ipynb` | Introduction au RL | (c) Standalone | yfinance |
| `research_rl_multi_asset.ipynb` | Allocation multi-actifs RL | (c) Standalone | yfinance |
| `research_rl_ppo.ipynb` | Agent de trading PPO | (c) Standalone | yfinance |
| `research_rl_reward_shaping.ipynb` | Reward shaping RL | (c) Standalone | yfinance |
| `research_rl_tactical_overlay.ipynb` | Overlay tactique RL | (c) Standalone | yfinance |
| `research_vrp_putwrite.ipynb` | Stratégie VRP put-write | (c) Standalone | yfinance |

Sur l'ensemble de la série, la **majorité est de type (c) standalone research** (exécution locale avec `pip install yfinance pandas matplotlib scikit-learn` ; la famille M12-HF utilise des données tick BTC Bitstamp possédées agrégées en minute localement) ; le reste est de type (b), research lié au quantbook QC Cloud (`research_btc_ml`, `research_m11ef_ensemble`, `research_m12_har_rv_j` exécutés, et la variante `_minute` qui instancie `QuantBook` sans outputs committés — à exécuter sur QC Cloud). Le décompte par type se lit dans le tableau ci-dessus ; les totaux relèvent de la régénération du catalogue.

## Approfondissements

| Fil | Carnets | Ce qu'on y apprend |
|---|---|---|
| Effets de calendrier | `research_day_of_week`, `research_month_of_year`, `research_turn_of_month` | trois anomalies calendaires testées de la même façon — brut, net de coûts, walk-forward et test de significativité — et trois verdicts négatifs, ce qui est le résultat |
| Facteurs et allocation | `research_fifty_two_week_high`, `research_idio_vol_anomaly`, `research_quality_lowvol`, `research_risk_parity`, `research_composite_ff_aw`, `research_composite_mom_regime`, `research_regime_pairs`, `research_vrp_putwrite` | un facteur se teste en cross-section et net de frais ; un composite assemble des briques mesurées séparément au lieu d'empiler des signaux non validés |
| Volatilité et haute fréquence | `research_m12_har_rv_j`, `research_m12_har_rv_j_minute`, `research_m12_hf_btc_local`, `research_m12_hf_dm_test` | la chaîne complète : estimer la variance réalisée, la décomposer, puis établir par un test de significativité que le gain vient de l'estimation et non du décor |
| Reinforcement learning | `research_rl_intro`, `research_rl_ppo`, `research_rl_grpo`, `research_rl_reward_shaping`, `research_rl_multi_asset`, `research_rl_tactical_overlay` | le RL se prototype localement ; la spécification de la récompense décide de la politique convergée, et un verdict négatif se publie comme un autre |
| Lecture méthodologique | section [Ce que vous avez appris](#ce-que-vous-avez-appris) | pourquoi un edge mesuré mais non significatif reste `INCONCLUSIVE`, et pourquoi une moyenne d'experts corrélés dilue au lieu de diversifier |

Pour prolonger hors du dossier : le parcours de cours [QC-Py](../Python/README.md), le pipeline
d'entraînement [ML-Training-Pipeline](../ML-Training-Pipeline/README.md), les stratégies portées en
`main.py` dans [`projects/`](../projects/), et les companions pédagogiques de
[`Python/research/`](../Python/research/README.md).

---

## Conclusion / Prochaines étapes

### Ce que vous avez appris

Ces notebooks sont le **laboratoire de recherche** de la série QuantConnect. La **majorité (16/20) sont standalone** et s'exécutent en local avec `yfinance` (données gratuites) + `pandas` / `scikit-learn` (la famille M12-HF utilise des données tick BTC possédées) ; les notebooks des familles M11/M12 (btc_ml, m11ef_ensemble, m12_har_rv_j, m12_har_rv_j_minute) chargent leurs données crypto via `QuantBook` QC Cloud (type (b)). Ils illustrent deux familles de recherche :

- **Recherche factorielle & allocation** (HAR-RV-J vol, FamaFrench + AllWeather composite, Momentum + Regime, Quality/LowVol, Risk Parity, VRP put-write, anomalie de volatilité idiosyncratique (IVOL)) — on apprend que les modèles de volatilité et d'allocation robuste sont reproductibles en local sur données publiques, et que les composites (M12, M11ef) sont les briques des stratégies *Robuste* du catalogue. **Verdict honnête M12-HF** (`research_m12_hf_btc_local.ipynb` + `research_m12_hf_dm_test.ipynb`) : l'estimation de la realized variance en minute **bat** celle en hourly (delta médian +0.548, MSE minute ~moitié hourly), statistiquement validée par un test de Diebold-Mariano (HAC, p≈0.000) et un block-bootstrap dont l'IC95 est entièrement négatif. La cause du gain est cependant la **fréquence d'échantillonnage** (qualité de l'estimateur RV, Andersen-Bollerslev-Diebold 2003), **pas** la composante de jump — HAR-Classic sans jump montre le même gain. Leçon méthodologique : la résolution hourly (24 bars/jour) est trop bruitée pour le vol-targeting Kelly ; la minute (1440 bars/jour) l'est beaucoup moins. Le carnet `research_idio_vol_anomaly.ipynb` montre le cas symétrique d'un edge **mesuré mais non significatif** : Sharpe long-short net +0.18 sur 132 mois, mais t de Newey-West p=0.45 et test de randomisation p=0.16 (100 permutations) — le verdict INCONCLUSIVE est conservé tel quel plutôt que présenté comme un gain.
- **Recherche Reinforcement Learning** (intro, PPO, GRPO, reward shaping, multi-asset, tactical overlay) — on apprend que le RL trading se prototypé localement avant tout déploiement QC Cloud, et que le *reward shaping* est le levier le plus sensible (un reward mal spécifié fige la policy). **Leçon d'intégrité #3360** : diviser la reward portfolio-level par le nombre d'actifs (`reward / N_ASSETS`) détruit le signal du critic per-asset → la policy gèle près de l'uniforme → l'argmax collapse vers Buy (fingerprint buy-and-hold, Sharpe 0.657 identique au collapse PPO). Corrigé : la reward portfolio complète alimente chaque transition per-asset (cohérence #3359/#3360). Verdict ré-évalué honnête après fix : NO BEATS (A2C Sharpe 0.000, SAC −0.063 sur univers non-FAANG) — pour la bonne raison.

Le fil rouge : **l'indépendance de la plateforme**. Ces notebooks prouvent que l'idéation et la validation ML peuvent se faire hors QC Cloud pour la majorité des sujets (16/20 standalone) ; QC Cloud devient nécessaire dès que la recherche porte sur des données crypto natives (les notebooks M11/M12 qui instancient `QuantBook`), et reste la porte d'entrée du backtest haute-fidélité sur données natives.

### Prochaines étapes

1. **Installer l'environnement local** : `pip install yfinance pandas matplotlib scikit-learn` puis ouvrir un notebook dans `jupyter`.
2. **Commencer par l'intro RL** : `research_rl_intro.ipynb` avant les avancés (PPO, GRPO, reward shaping).
3. **Reproduire un keeper** : `research_m12_har_rv_j.ipynb` (modèle de volatilité HAR-RV-J, un des 4 KEEPERS du curriculum ML-V2).
4. **Tester le reward shaping** : `research_rl_reward_shaping.ipynb` — modifier la fonction de reward et observer l'impact sur la policy convergée.
5. **Combiner en composite** : `research_composite_mom_regime.ipynb` montre comment assembler Momentum + Regime en une stratégie multi-signal.
6. **Déployer le meilleur sur QC Cloud** : une fois une idée validée en local, la porter en `main.py` dans `../projects/` pour un backtest réaliste avec coûts de transaction.

> **Rappel honnête** : les données `yfinance` (gratuites) ont des limitations (ajustements, splits, profondeur historique) par rapport aux données QC natives. Un edge confirmé en local doit être **re-validé** sur QC Cloud avant toute conclusion de robustesse.
