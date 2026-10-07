# RL Options Hedging (Ch07-01)

**Hands-On AI Trading**, Chapter 7-01 — Deep Hedging with Reinforcement Learning — portage suivi par [#18902](https://github.com/jsboige/CoursIA/issues/18902).

## Ce que fait le projet

Un agent de renforcement (PPO) apprend à couvrir une position **courte d'un call ATM de 30 jours sur SPY**, rebalancée chaque séance. Sa politique est comparée à la référence du marché — la **couverture delta de Black-Scholes quotidienne** — sur la **variance** et la **queue (CVaR 95 %)** du P&L de couverture, avec et sans frais (5 bps sur le notionnel échangé), sur des régimes de volatilité contrastés : calme (12 %), 2020 (35 %), 2022 (25 %).

## Conception (plan d'origine du stub, exécuté avec deux adaptations mesurées — cf. Enseignements)

- **Option** : call européen ATM (K = S₀), 30 jours calendaires ≈ 21 séances.
- **État** (5) : moneyness S/K−1, temps restant τ, delta BS, gamma BS (×10²), position de couverture courante.
- **Action** : ratio de couverture continu a ∈ [0, 1] — on détient h = a·δ_BS parts de sous-jacent. **a = 1 constant reproduit exactement la couverture delta** : la baseline est un point spécial de l'espace des politiques.
- **Récompense** : P&L terminal de couverture (prime − payoff + P&L de couverture − frais), normalisé, échelle O(1).
- **Simulation** : GBM, pas quotidien, trois régimes de vol. Plan d'origine : mesure neutre au risque (μ = 0) ; **exécuté** en mesure physique (μ = 8 %/an, dérive du sous-jacent) pour l'entraînement **et** la simulation d'évaluation — sous μ = 0 le gradient de politique s'annule (4/8 seeds effondrées, mesuré ; cf. Enseignements ci-dessous).
- **Entraînement** : PPO (stable-baselines3), 8 seeds, 120 000 pas, réseau 64×64, sans frais ; les frais n'entrent qu'à l'évaluation, des deux côtés de la comparaison.

## Fichiers

- `research.ipynb` — recherche locale exécutée : pricing BS, simulation des trois régimes, environnement gymnasium, sanity checks, entraînement PPO multi-seed, évaluation RL contre delta (variance + CVaR 95 %, avec/sans frais), verdict, export de la politique.
- `rl_policy.py` — poids exportés du notebook (MLP en numpy pur, sans torch) consommés par l'algorithme QC.
- `main.py` — algorithme QuantConnect : **double comptabilité** — le livre « delta » et le livre « rl » couvrent la même short call réelle (chaîne d'options SPY) ; seuls diffèrent leurs chemins de couverture ; frais comptés par livre comme dans le notebook.

## Résultats (notebook, 2 000 trajectoires nouvelles par régime, 8 seeds)

| Régime | Frais | std P&L delta | std P&L RL (moy. 8 seeds) | std RL (meilleure seed) | CVaR 95 % delta | CVaR 95 % RL (moy.) |
| --- | --- | --- | --- | --- | --- | --- |
| calme 12 % | 0 | 0,573 | 1,272 | 0,790 | −1,26 | −3,60 |
| calme 12 % | 5 bps | 0,570 | 1,272 | 0,785 | −1,37 | −3,66 |
| 2020 35 % | 0 | 1,691 | 3,724 | 2,292 | −3,88 | −10,94 |
| 2020 35 % | 5 bps | 1,689 | 3,723 | 2,285 | −3,98 | −10,99 |
| 2022 25 % | 0 | 1,194 | 2,539 | 1,556 | −2,60 | −7,05 |
| 2022 25 % | 5 bps | 1,192 | 2,538 | 1,550 | −2,70 | −7,11 |

P&L par trajectoire de 21 séances, en dollars pour un spot initial de 100 $. 2 000 trajectoires nouvelles par régime, mesure physique (dérive 8 %/an), 8 seeds PPO.

## Verdict

**NO BEATS — net et mesuré.** La couverture delta BS quotidienne n'est battue par **aucune** des 8 seeds, dans **aucun** régime, avec **ou sans** frais : la meilleure seed reste +30 à +38 % au-dessus de l'écart-type du P&L delta selon le régime (calme 12 % : +37,8 % ; 2020 35 % : +35,5 % ; 2022 25 % : +30,3 %), la moyenne inter-seeds est ~2,2×, et la CVaR 95 % du RL est ~2,8× plus profonde. Les frais (5 bps) ne changent rien au classement (~0,03 %) : les deux politiques échangent trop peu pour que les frais décident.

Trois enseignements documentés dans le notebook : (1) sous mesure neutre au risque, E[P&L] = 0 pour toute politique — le gradient de politique s'annule et l'entraînement est sans signal (4/8 seeds effondrées, mesuré) ; l'entraînement passe donc en mesure physique, comme le livre qui apprend sur des données réelles dérivées ; (2) le clip de l'action à sa borne laisse un gradient nul — reparamétrage [-1, 1] ; (3) malgré ces corrections, 3/8 seeds restent proches de la politique non couverte : le PPO à récompense terminale est structurellement fragile sur ce problème. La suite naturelle (non couverte) : objectif risque-aversion dans la récompense (Kolm & Ritter 2019) ou Q-learning par pas (Halperin 2020).

## Projet QC

| Champ | Valeur |
| --- | --- |
| Project ID | 30800109 |
| Organization | Trading Firm QC-Course |
| Nom | RL-Options-Hedging-Ch07 |
| Fenêtres | 2018-2024 (complet) · 2020 · 2022 · 2018-2019 (calme) |
| Capital initial | $1 000 000 |

## Références

- Hands-On AI Trading, chapitre 07-01 (Better Hedging with Reinforcement Learning) — code de référence : `QuantConnect/HandsOnAITradingBook`, dossier `07` (politique PPO 3→256→256, entraînement du modèle de delta).
- Kolm & Ritter (2019), "Deep Hedging: Learning to Simulate Equity Options".
- Halperin (2020), "QLBS: Q-Learner in the Black-Scholes World".
