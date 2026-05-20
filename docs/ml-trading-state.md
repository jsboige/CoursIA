# ML Trading — Etat consolide

Document de reference des **lecons trans-iteration** sur le ML applique au trading. Les **chiffres par iteration** (Sharpe, DirAcc per coin, per seed) sont dans `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/REGISTRY.md` + `docs/M<N>_*.md` + QC Cloud — ne pas dupliquer ici.

## Pattern central empirique (verifie sur ~17 modeles)

Apres M5-M17 + MoE + M8 SOTA sweep (96 runs sur 4 architectures de sequence), le pattern qui se degage :

1. **La direction / return est quasi-imprevisible.** Meme les architectures SOTA 2026 (TFT, Mamba, iTransformer, PatchTST) sur 96 runs (BTC/ETH × h1/5/10 × 4 seeds) ne battent pas la majority class baseline. Le DirAcc plateaute autour de la frequence des up-days du dataset (e.g. 0.5786 sur SPY = freq up-days 2015-2024).
2. **La volatilite EST previsible.** Les 2 seuls BEATS de toute la serie sont des previsionnistes de variance realisee :
   - **M12 HAR-RV-J** : BEATS cluster-wide, p=7.9e-7, 64/84
   - **M15 LSTM h=32** : BEATS etroit, p=0.0188, 52/84 (h=64/128 = overfitting, NO BEATS confirme)
3. **La parcimonie gagne.** HAR Classic (Corsi 2009, 3 regresseurs) bat tout ce qu'on lui empile. M12 le bat avec UN seul ajout discipline (split jump continu vs discontinu). Composer (M17 = M12+M16) DILUE le signal.
4. **Les couts de transaction tuent les edges.** M11f montre que l'edge Kelly K60 survit a 50 bps puis se dissout a 100 bps. Sharpe brut sans couts = mensonge.

Ce pattern est aligne avec *Hands-On AI Trading* (Broad et al., 2025) : ne pas predire la direction, l'edge est dans le sizing / regime / risque / qualite d'execution ; la vol est l'objet previsible.

## Erreur conceptuelle a NE PAS reproduire : regression log-RV != classification direction

Cause racine des 0 BEATS M5/M6/M7/M8/MoE : on entraine en regression log realized variance (MSE) et on evalue en direction (DirAcc binaire). Ces deux signaux sont faiblement correles :

- Vol haute peut preceder up OU down (asymetrique selon regime)
- Vol future est persistante (autoregressive) -> HAR est tres competitif
- Direction des log-returns est ~0 en moyenne, presque indistinguable de bruit

**Smoking gun typique** (audit M8 tft_BTC_USD_h1) :
```
Epoch 250/250  train=0.000929  val=0.000894
Metrics: mse=0.00054, direction_accuracy_step1=0.4833,
         majority_class_baseline=0.5076, edge_over_majority=-0.0243
```
MSE excellent en regression. DirAcc inferieur a la baseline majoritaire. Le modele a appris a predire la vol, on lui demande la direction : echec garanti.

**Metriques honnetes par tache** :

| Tache | Bon metrique | Metriques piege |
|-------|--------------|-----------------|
| Vol forecast | MSE log-RV vs HAR/GARCH | DirAcc (irrelevant) |
| Direction | DirAcc vs majority + walk-forward + >=4 seeds + edge >= 2sigma | MSE (signal trop faible) |
| Trading strategy | **Sharpe out-of-sample 5y+** + MaxDD + transaction costs | In-sample CAGR, single backtest |

**A abandonner** : ajouter d'autres architectures sequence-to-one log-RV pour la direction (DLinear, NLinear, PatchTST variants...). Le pattern est sature.

**A poursuivre** :
- Vol forecast pour position sizing (pas direction) : GARCH(1,1), HAR(1,5,22), HAR-RV-Kelly
- Vol-targeting strategy : target vol annualisee (e.g. 15%), scale exposure inversely to forecast vol
- Regime detection HMM : binary state (calm/volatile), gate les positions selon etat
- Multi-asset universe : pas juste BTC/ETH univariate. Inclure SPY/EFA/EEM/TLT/GLD/DBC
- Risk parity / vol parity : equiponderer en risque, pas en capital

## Les 7 disciplines obligatoires (audit PR ML/trading)

Tout training ou evaluation ML applique au trading qui ne respecte pas ces 7 disciplines est INVALIDE et ses metriques doivent etre ignorees.

1. **Walk-forward validation** : split temporel rolling, jamais random. Purged k-fold CV (Lopez de Prado) pour modeles batch. Pas de shuffle de series temporelles.
2. **Baseline majoritaire systematique** : tout report DirAcc compare a `freq(up_days)` du dataset. Si DirAcc <= freq(up_days), modele inutile.
3. **Out-of-sample strict** : `--test-ratio` honore, metriques de production calculees sur test holdout uniquement. Normalization stats train-only. Env RL split aussi.
4. **FinTSB regimes** : evaluer sur 4 regimes distincts (uptrend / downtrend / volatility / black swan). Sharpe global = moyenne ponderee. Reference : [TongjiFinLab/FinTSB](https://github.com/TongjiFinLab/FinTSB).
5. **Transaction costs explicites** : modele bid-ask + market impact dans tout backtest. QC `BrokerageModel` coherent avec eval local.
6. **Anti-survivorship bias** : pas de panier "stocks survivants" (CRSP/Norgate ideal, sinon documenter le biais). **Pas de FAANG** (cf section datasets).
7. **Anti-data-snooping** : log des hypotheses tentees, deflated Sharpe pour comptes exhaustifs. Pas de "j'ai trouve une strategie parmi 10000" sans correction Bonferroni / deflated Sharpe.

**Audit PR : ces 7 points doivent etre visibles dans le body ou refusable CHANGES_REQUESTED** (cf [.claude/rules/pr-review-discipline.md](../.claude/rules/pr-review-discipline.md) section C).

**Consequences observees en cas de non-respect** :
- DirAcc plateauent a freq(up_days) sans qu'on s'en rende compte (LSTM/Transformer 0.5795 = freq SPY) — metrique trompeuse, succes apparent qui n'apprend rien
- Sharpe in-sample 2.4454 sur DQN qui n'a jamais vu test set (incident historique)
- Live trading qui s'ecroule (PolyBench 2026 : 5/7 LLM SOTA perdent en live capital reel)
- Plus de temps perdu a exploiter des resultats faux qu'a fixer la methodo en amont

## Politique datasets — anti-biais

**INTERDIT en training** :
- **FAANG / Mag7** : AAPL, MSFT, GOOG, AMZN, NVDA, TSLA, META. Tickers x10 sur 10 ans, modele entraine dessus apprend "ca monte" = majority class predictor. Confirme par incident pedagogique 2026-05-04 (LSTM/Transformer plateau DirAcc 0.5786 = freq up-days SPY).
- Single-asset stocks isoles sans contexte sectoriel.
- Yahoo Finance sans controle survivorship pour panier large (CRSP preferable mais payant).

**AUTORISE en training (panier anti-biais 26 symboles)** :

| Categorie | Symboles | Justification |
|-----------|----------|---------------|
| Crypto multi-exchange long | BTC/USD multi-source (Bitstamp/Coinbase/Kraken), BTC/EUR/JPY/KRW, ETH, LTC, XRP | Pas de survivor bias, marche 24/7, plusieurs regimes complets |
| Indices equilibres | SPY, RSP (S&P equal-weight), IWM, VIX | Moins biaises que cap-weighted seul, VIX = distribution opposee |
| Sectors S&P (10) | XLF, XLE, XLK, XLV, XLY, XLP, XLI, XLU, XLB, XLRE | Rotation, cross-sector dynamics, ideal GNN |
| Bonds (3) | TLT (20+y), IEF (10y), SHY (1-3y) | Correlation inversee actions, regime taux |
| Commodities (3) | GLD, USO, DBA | Souvent mean-reverting, contraste equity |
| International (2) | EFA (Europe), EEM (emerging) | Test out-of-distribution hors-USA |
| Forex | EUR/USD, GBP/USD, USD/JPY, AUD/USD | Faible biais directionnel haussier |

**Datasets historiques disponibles** : crypto multi-exchange CSV.gz format CryptoDataDownload, Bitstamp BTC/USD horaire 2014-08-09 -> 2024-08-08 (10 ans, le plus precieux : couvre bull 2017, crash 2018, sideways 2019, bull 2020-21, crash 2022, recovery 2023-24). Path local des datasets sur disque ai-01 : voir le memory file local de l'agent (gitignored).

Datasets s'arretent ~aout 2024. Pour periode recente : completer via Binance API ou yfinance, stitching avec validation coherence OHLC sur chevauchement 1 mois.

## Recommandation datasets QC (jugement 2026-05-14)

**NON** pour nourrir plus de DL directionnel ou de nouvelles archis de sequence — echec regle (M8, 96 runs). Plus de donnee n'inverse pas un resultat structurel.

**OUI conditionnel** pour UNE chose : donnee **minute/5-min crypto QC** pour estimer une RV haute-frequence. Renforce l'INPUT de M12/M15h32 (nos 2 succes), ameliore le split jump/continu (bipower variation sensible a la frequence), et a une valeur economique directe si on porte M12 vers options/risk-parity/vol-targeting.

**Ordre de levier** :
- A. Consolider M12 vers production (Phase B QC Cloud, deja en cours po-2024, 0 QCCC). Levier #1.
- B. Apres validation Phase B : acheter donnee minute crypto QC pour les 7 coins -> lancer M12-HF (high-freq RV). Seul achat signe.
- C. Ne PAS acheter pour etendre l'univers d'actifs ni donnee alternative tant que le coeur vol n'est pas en prod.

**Verdict** : 0 QCCC maintenant (finir Phase B M12). Achat minute crypto QC SEULEMENT apres verdict A/B M12 positif. Jamais d'achat pour relancer du DL directionnel.

## Reference livre

*Hands-On AI Trading* (Pik, Chan, Broad, Sun, Singh, Wiley 2025) — https://www.hands-on-ai-trading.com/

Le livre documente precisement les ecueils ci-dessus et les bonnes pratiques (vol forecasting, regime gating, Kelly capped, multi-asset). A relire en cas de doute methodo. Repo exemples : https://github.com/QuantConnect/HandsOnAITradingBook (cf section "Livre de reference" de [quantconnect.md](quantconnect.md)).

## Pointeurs cross-doc

- Infrastructure QC + MCP + backtest : [docs/quantconnect.md](quantconnect.md)
- Env Conda ML training + GPU wrapper : [docs/kernels-runtime.md](kernels-runtime.md)
- Historique training par iteration : `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/REGISTRY.md` + `docs/M<N>_*.md`
- Regles audit PR ML : [.claude/rules/pr-review-discipline.md](../.claude/rules/pr-review-discipline.md) section C
