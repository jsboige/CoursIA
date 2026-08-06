# ARCHIVE - ML-DeepLearning (Ridge regression LSTM proxy)

**Status** : ARCHIVED (substance pédagogique préservée)
**Date d'archive** : 2026-07-21
**Sharpe** : Aucun backtest QC Cloud exécuté
**Issue de reference** : #7575 (bug-class `PREEXISTING_UNEXEC` quantbooks sans `config.json`)

## Strategy Summary

Stratégie de prédiction de direction (up/down/flat) sur 3 ETFs US
(SPY, QQQ, IWM) via une régression Ridge (`sklearn.linear_model.Ridge`)
utilisée comme **proxy** d'un LSTM, selon le pattern de
*Hands-On AI Trading* (chapitre 13.6, "LSTM proxy pattern").

Architecture :
- Input : rendements open-close décalés (lag features) sur SPY/QQQ/IWM
- Hidden : Ridge regression avec régularisation L2
- Output : direction next-day (up/down/flat), classification 3-classes
- Univers : SPY (S&P 500), QQQ (Nasdaq-100), IWM (Russell 2000)
- Rebalance : Weekly

Mécanisme : features de rendement lagged → Ridge → classe prédite →
position long/short/cash selon signal.

## Notes d'infrastructure

- **QC Cloud** : jamais déployé. Le `config.json` est absent du repo,
  le README confirme "Not yet deployed. Copy files to a new QC Cloud
  project to run."
- **Note de transparence** : le README lui-même précise "uses
  sklearn Ridge, not a real neural network (LSTM proxy pattern
  from Hands-On AI Trading)". Pas de LSTM effectif dans `main.py`.
- **quantbook.ipynb** : 2/12 cellules non-exécutées — substance
  préservée dans `main.py` (172 lignes, `MLDeepLearningAlgorithm`).

## Verdict

**INTRINSIC** (substance pédagogique, jamais déployé) :
- Le projet est un **squelette fonctionnel** du pattern "LSTM proxy
  via Ridge" (substitution pédagogique d'un réseau de neurones par
  un modèle linéaire).
- Pas de backtest QC, pas de Sharpe documenté.
- L'absence de `config.json` confirme que le projet n'a jamais été
  promu en projet QC Cloud opérationnel.

À conserver comme **référence pédagogique** pour le pattern LSTM
proxy (substitution modèle non-linéaire par modèle linéaire dans un
sandbox Lean/QC) — **pas comme source d'alpha live**.

## Leçons retenues

1. **Le "LSTM proxy pattern" est explicite et transparent** :
   le README mentionne clairement que `sklearn Ridge` n'est pas
   un vrai réseau de neurones. Pattern transférable : on peut
   *toujours* approximer un modèle non-linéaire par un modèle
   linéaire en première itération, pour valider le pipeline
   end-to-end avant d'investir dans le LSTM.
2. **Univers 3-ETF (SPY/QQQ/IWM)** : univers cross-section
   classique US equities. Le choix weekly rebalance réduit le
   turnover (et les frais) au prix d'un signal potentiellement
   stale.
3. **Le scaffolding Ridge proxy n'est pas l'alpha** : sans
   backtest, le projet est une **démonstration de pattern
   d'implémentation** (comment coder le proxy), pas une
   stratégie déployable.

## Fichiers

- `main.py` (6.9 KB) — `MLDeepLearningAlgorithm` (172 lignes)
- `quantbook.ipynb` (196 KB) — exploration QuantBook (2/12 cells unexec)
- `README.md` — Description + avertissement explicite "LSTM proxy
  pattern"

## References

- #7575 (issue parent) — bug-class `PREEXISTING_UNEXEC` quantbooks
- *Hands-On AI Trading* (Jared Broad), chapitre 13.6 — LSTM proxy
  pattern via modèle linéaire
- `scripts/quantconnect/audit_quantbooks_unexec.py` — détecteur
