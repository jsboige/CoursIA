# MeanReversion

**Classe d'actifs :** ETF sectoriels américains
**ID projet Cloud :** Aucun (local uniquement)

## Description

Stratégie de retour à la moyenne à court terme sur 11 ETF sectoriels GICS (XLK, XLF, XLE, XLV, XLI, XLY, XLP, XLU, XLB, XLRE, XLC).
Chaque jour à 10:00 (New York), elle achète les ETF les plus survendus (RSI(14) < 40) dont le rendement sur trois mois n'est pas inférieur de plus de 10 points à celui de SPY. Au plus 4 positions à 25 % chacune.
Sortie : RSI > 65, 15 jours de détention, ou stop-loss à −10 %.

Filtre de régime SMA200 sur SPY : en marché baissier, les nouvelles positions prennent 12,5 % au lieu de 25 % ; les positions ouvertes ne sont pas soldées.
Un ETF qui a moins de 63 séances d'historique (XLRE fin 2015, XLC en 2018) reçoit un rendement nul sur trois mois.

## Comment lancer

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/MeanReversion"`
```bash
lean backtest --project .
```

**QC Cloud :** pas de projet cloud persistant. Les backtests ci-dessous ont tourné dans des projets de mesure ; copier `main.py` dans un nouveau projet QC Cloud pour relancer.

**Paramètres** (#23199) :

| Paramètre | Valeurs | Défaut |
|-----------|---------|--------|
| `mode` | `strategy` (la stratégie) ; `spy` (SPY 100 % détenu) ; `6040` (SPY 60 % / BND 40 %) ; `ew11` (les ETF sectoriels de l'univers à poids égal, parmi ceux qui cotent) | `strategy` |
| `start_date`, `end_date` | dates `AAAA-MM-JJ` | `2015-01-01`, `2024-12-31` |

Les trois modes de référence se rééquilibrent le premier jour de bourse du mois, 30 minutes après l'ouverture, à l'heure du scan de la stratégie. Le graphique `shadow` trace la valeur du portefeuille à chaque ouverture de séance du SPY. C'est l'entrée du calcul de significativité (`Paradox46Benchmarks/significance.py`). La statistique d'exécution `reentries` compte les ETF re-sélectionnés le jour même de leur sortie.

## Correction de l'exécution (#23199)

Le scan quotidien traitait d'abord les sorties par `self.liquidate(symbol)`, puis cherchait les entrées. Un ETF qui venait de sortir pouvait être re-sélectionné le jour même si son RSI restait sous 40, ce qui arrive souvent après un stop ou une sortie à 15 jours. Il recevait alors `self.set_holdings(symbol, w)`. En résolution journalière, les deux ordres se remplissent à la clôture. `set_holdings`, calculé contre la position pas encore vendue, n'envoyait que l'écart : la ligne finissait à quelques parts, ou à découvert, alors que la stratégie la comptait comme une position pleine pendant 15 jours.

Le rejeu des ordres du backtest publié jusqu'ici (`ad190cab96bc`, #20346) l'a mesuré : **37 re-entrées du même jour**. Dans 35 cas, la vente est suivie d'un rachat, et dans **29** d'entre eux ce rachat ne porte que sur 7 à 70 parts (XLF le 2015-01-29 : 1606 parts vendues, 21 rachetées). Dans les **2** autres cas, la cible était inférieure à la position, `set_holdings` a vendu en plus de la liquidation, et la ligne est passée à découvert (XLE le 2018-10-30, XLF le 2020-03-02) ; ces positions courtes sont restées ouvertes sur 7 dates de remplissage. Relancé le 2026-10-29, le code d'avant le correctif refait exactement ce journal, ordre par ordre (704 ordres, mêmes statistiques).

Une sortie suivie d'une re-entrée du même ETF le même jour ne passe plus d'ordre de liquidation : seul `set_holdings(symbol, w)` part, et la ligne finit à `w`. Les règles de signal (RSI, force relative, filtre SMA200, stop, durée) ne changent pas. Au rejeu des ordres, le code corrigé n'a **aucune vente-rachat du même jour et aucune position courte** sur les deux fenêtres. Chaque ligne encore détenue après un ordre pèse au moins 11,6 % du portefeuille, pour des cibles de 12,5 % et 25 %. La statistique `reentries` vaut 45 sur w1 et 6 sur w2.

## Métriques du backtest

Backtests QC Cloud du 2026-10-29, capital de départ 100 000, frais de courtage modélisés par Lean. Chaque ligne est un run du code corrigé (`main.py` sha256 `8a3399323c43`), avec le `mode` indiqué. Résultats lus après `completed: true`.

**w1 : 2015-01-01 → 2024-12-31** (2516 dates négociables)

| Bras | Sharpe QC | CAGR | Drawdown max | PSR | Profit net | Ordres |
|------|-----------|------|--------------|-----|------------|--------|
| **`strategy`** | **0.584** | **10.20 %** | **19.5 %** | 4.7 % | 164.2 % | 667 |
| `spy` (référence) | 0.533 | 12.97 % | 33.7 % | 3.0 % | 238.9 % | 1 |
| `6040` (référence) | 0.442 | 8.41 % | 21.7 % | 1.5 % | 124.4 % | 201 |
| `ew11` (diagnostic) | 0.438 | 10.66 % | 36.1 % | 1.4 % | 175.5 % | 615 |

**w2 : 2025-01-01 → 2026-07-01** (374 dates négociables, dernière séance le 2026-06-30)

| Bras | Sharpe QC | CAGR | Drawdown max | PSR | Profit net | Ordres |
|------|-----------|------|--------------|-----|------------|--------|
| **`strategy`** | **0.179** | **7.70 %** | **8.0 %** | 10.7 % | 11.8 % | 98 |
| `spy` (référence) | 0.665 | 18.96 % | 18.7 % | 27.5 % | 29.7 % | 2 |
| `6040` (référence) | 0.59 | 13.37 % | 11.2 % | 24.7 % | 20.7 % | 30 |
| `ew11` (diagnostic) | 0.632 | 15.84 % | 14.9 % | 26.7 % | 24.6 % | 107 |

Le Sharpe de QC retire un taux sans risque. Les tests ci-dessous utilisent un Sharpe à taux nul, calculé sur les rendements journaliers du graphique `shadow`.

**Significativité** (Ledoit-Wolf, bootstrap stationnaire, Newey-West). La correction de Holm porte d'un côté sur les deux références du verdict, de l'autre sur le diagnostic :

| Fenêtre | Comparaison | Sharpe à taux nul (stratégie / bras) | p de Holm, écart de Sharpe (Ledoit-Wolf ; bootstrap) |
|---------|-------------|---------------------------------------|------------------------------------------------------|
| w1 | vs `spy` | 0.97 / 0.79 | 1.0 ; 1.0 |
| w1 | vs `6040` | 0.97 / 0.81 | 1.0 ; 1.0 |
| w1 | vs `ew11` | 0.97 / 0.69 | 0.41 ; 0.41 |
| w2 | vs `spy` | 0.82 / 1.05 | 1.0 ; 1.0 |
| w2 | vs `6040` | 0.82 / 1.21 | 1.0 ; 1.0 |
| w2 | vs `ew11` | 0.82 / 1.15 | 1.0 ; 1.0 |

## Verdict : NO BEATS hors échantillon (2025-2026), INCONCLUSIVE dans l'échantillon (2015-2024)

Le protocole (#23012, repris dans #23199) donne BEATS seulement si le Sharpe dépasse celui du SPY détenu **et** que l'écart reste significatif après Holm contre les deux références. Il donne NO BEATS si le Sharpe est inférieur à celui du SPY détenu, et INCONCLUSIVE sinon. Les paramètres v5.x ont été choisis sur 2015-2024 (historique du docstring de `main.py`) : w1 est dans l'échantillon, son verdict n'est qu'indicatif. C'est w2, hors échantillon, qui tranche.

- **w2 (2025 → mi-2026) : NO BEATS.** Sharpe 0.179 contre 0.665 pour SPY détenu, CAGR 7,7 % contre 19,0 %. Le drawdown est plus faible (8,0 % contre 18,7 %), mais le Sharpe à taux nul reste lui aussi sous celui des trois bras (0,82 contre 1,05 pour SPY).
- **w1 (2015-2024) : INCONCLUSIVE.** Sharpe 0.584 contre 0.533 pour SPY détenu, mais l'écart n'est pas significatif après Holm (p = 1,0 contre les deux références). La stratégie rend moins que SPY (CAGR 10,2 % contre 13,0 %). Son Sharpe vient d'une volatilité plus faible : elle ne détient le plus souvent que deux lignes (médiane au rejeu des ordres), et son drawdown est de 19,5 % contre 33,7 %.

**Ce que mesure le diagnostic `ew11`.** Les onze ETF à poids égal ont sur w1 un Sharpe à taux nul de 0,69, contre 0,97 pour la stratégie. L'écart n'est pas significatif après Holm (p = 0,41). Sur w2, la stratégie est sous l'univers à poids égal (0,82 contre 1,15), sans écart significatif non plus.

**Ce qui change par rapport aux chiffres publiés.** Le backtest `ad190cab96bc` (#20346) donnait un Sharpe de 0,675, un CAGR de 10,42 % et un drawdown de 11,1 % sur 2015-2024. Une partie de ses entrées n'avait pas eu lieu : 29 re-entrées ne détenaient qu'un résidu de 7 à 70 parts, 2 autres étaient à découvert, et le livre était moins investi que la stratégie ne le prévoit. Corrigé, il a un Sharpe de 0,584 et un drawdown de 19,5 %. Ce backtest ne reproduisait déjà pas les chiffres du docstring pour la v5.2 (Sharpe 0,810). Pas de re-réglage des paramètres : un ajustement rétrospectif serait du surapprentissage (EPIC #9768).

Avant #20346, le code plantait le 2018-09-11 sur une erreur d'index (XLC, trop jeune pour la garde d'historique) : il ne pouvait produire aucune métrique sur sa fenêtre codée. Les chiffres que ce README citait auparavant (sweep #1621, Sharpe −0,082, verdict BROKEN ; reproduction QuantBook du code v4.0, Sharpe 0,365) ne portent pas sur le code v5.2.

## Fichiers

- `main.py` - Stratégie (v5.2, retour à la moyenne sur ETF sectoriels ; re-entrée du même jour corrigée par #23199, modes de référence)
- `research.ipynb` - Recherche : pivot stocks -> ETF sectoriels, hypothèses H1-H8 (RSI, stop-loss, période de détention...)
- `quantbook.ipynb` - Reproduction QuantBook de l'analyse exploratoire sur les ETF sectoriels (données natives QC)

## Références

- Jegadeesh (1990), « Evidence of Predictable Behavior of Security Returns »
- De Bondt & Thaler (1985), « Does the Stock Market Overreact? »
