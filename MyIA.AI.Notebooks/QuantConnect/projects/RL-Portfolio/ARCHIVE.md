# ARCHIVE - RL-Portfolio (Reinforcement Learning portfolio template)

**Status** : ARCHIVED (substance pédagogique préservée, template/squelette)
**Date d'archive** : 2026-07-21
**Sharpe** : Aucun backtest QC Cloud exécuté
**Issue de reference** : #7575 (bug-class `PREEXISTING_UNEXEC` quantbooks sans `config.json`)

## Strategy Summary

Stratégie de reinforcement learning (RL) sur allocation de portfolio
multi-actifs via **Q-Learning tabulaire** (et non DQN/PPO), avec
état markovien sur régime de marché.

Architecture :
- **State (10 dimensions)** : trend court/long (EMA20/200),
  volatilité régime, momentum (5j/20j), flight-to-safety
  (TLT outperforming SPY), market breadth (au-dessus MA20/50),
  trimestre calendaire, début de mois.
- **Actions (4)** : [100% SPY, 100% TLT, 100% GLD, 100% Cash].
- **Reward** : portfolio return ajusté risk (Sharpe-like avec
  pénalité drawdown -1 % si portfolio_return < moyenne_5j - 2 %).
- **Exploration** : ε-greedy avec decay (ε₀=1.0 → ε_min=0.01, decay=0.995).
- **Apprentissage** : Q-table (10×4), update standard
  `Q(s,a) ← Q(s,a) + α[r + γ·max_a'Q(s',a') - Q(s,a)]`,
  learning_rate=0.01, discount_factor=0.95.
- **Experience replay** : mémoire (1000 transitions), batch=32.
- **Univers** : SPY (S&P 500), TLT (20Y Treasury), GLD (Gold).
- **Rebalance** : Weekly (lundi 30min après open SPY).
- **Train** : Weekly (vendredi 30min après open SPY).

## Notes d'infrastructure

- **QC Cloud** : jamais déployé. Le `config.json` est absent du repo,
  le README confirme "Template/skeleton project — Not yet deployed.
  Copy files to a new QC Cloud project to run."
- **Q-Learning tabulaire, pas DQN** : la Q-table est de taille fixe
  (state_size=10, action_size=4), mise à jour par Q-learning
  classique. Ce n'est **pas** un réseau de neurones — c'est un
  lookup table. Le scaffolding est un **proxy pédagogique** du RL
  moderne (DQN, PPO).
- **quantbook.ipynb** : 7/10 cellules non-exécutées — substance
  pédagogique préservée dans `main.py` (217 lignes,
  `RLPortfolioAlgorithm`) + `README.md`.

## Verdict

**INTRINSIC** (substance pédagogique, jamais déployé) :
- Le projet est un **squelette fonctionnel** du pattern
  Q-Learning appliqué à l'allocation de portfolio.
- Le `main.py` implémente bien la boucle `state → action →
  reward → next_state → update Q-table`, mais sans backtest
  QuantConnect, **il n'y a aucune mesure d'edge**.
- L'absence de `config.json` confirme que le projet n'a jamais
  été promu en projet QC Cloud opérationnel.
- **Limite pédagogique** : Q-Learning tabulaire sur état à
  10 dimensions est **un jouet** comparé à un vrai RL de
  portfolio (DQN continu, PPO avec fonction de valeur, etc.).
  Utile pour comprendre la boucle, insuffisant pour produire
  de l'alpha.

À conserver comme **référence pédagogique** pour la boucle
RL classique (state/action/reward/Q-update) appliquée à
l'allocation d'actifs — **pas comme source d'alpha live**.

## Leçons retenues

1. **Q-Learning tabulaire ≠ RL moderne** : le pattern implémenté
   ici est la version 1990 du RL (lookup table). Le RL moderne
   (DQN, PPO, SAC) utilise des réseaux de neurones pour
   approximer la Q-function ou la policy. Pour un usage
   pédagogique, c'est un bon point d'entrée ; pour un usage
   opérationnel, il faut passer à une lib spécialisée
   (`stable-baselines3`, `Ray RLlib`).
2. **Epsilon-greedy avec decay** : pattern d'exploration
   standard. ε₀=1.0 (full random au début) → ε_min=0.01
   (quasi-greedy en fin d'apprentissage). Decay=0.995 = ~140
   épisodes pour atteindre ε_min. Adapter à la fréquence de
   re-train (ici weekly = ~9 ans pour converger sur 2015-2024).
3. **State discret à 10 dimensions** : choix conservateur
   (chaque feature est binaire ou catégorielle). Permet la
   Q-table tabulaire. Un état continu demanderait une
   **discrétisation** ou un approximateur (réseau neuronal).
4. **Le RL de portfolio sans backtest est un exercice de
   code, pas une stratégie** : la boucle est correcte, mais
   sans mesure d'edge, on ne sait pas si elle apprend
   quoi que ce soit d'utile. **À backtester avant tout
   usage opérationnel**.

## Fichiers

- `main.py` (8.2 KB) — `RLPortfolioAlgorithm` (217 lignes)
- `quantbook.ipynb` (41 KB) — exploration QuantBook (7/10 cells unexec)
- `README.md` — Description + avertissement "Template/skeleton
  project"

## References

- #7575 (issue parent) — bug-class `PREEXISTING_UNEXEC` quantbooks
- Sutton & Barto (2018), *"Reinforcement Learning: An Introduction"*,
  chapitre 6 (Q-Learning)
- `scripts/quantconnect/audit_quantbooks_unexec.py` — détecteur
- `stable-baselines3` : library RL moderne recommandée pour aller
  au-delà du Q-Learning tabulaire