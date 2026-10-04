# Markov-Regime-Detection-Index-Options

**Classe d'actifs :** Indice S&P 500 (SPX) et options sur indice
**ID projet Cloud :** `37338052`

## Description

Port de l'exemple **06/04/03 — Index Options** du livre *Hands-On AI Trading with Python, QuantConnect, and AWS* (Jared Broad et al., Wiley, 2025), dépôt [QuantConnect/HandsOnAITradingBook](https://github.com/QuantConnect/HandsOnAITradingBook) au commit `e025f21`.

Même modèle de régime et même expression en straddle que [06/04/02](../Markov-Regime-Detection-Equity-Options/), déplacés sur les **options d'indice SPX**. La raison donnée par le livre : l'exercice européen, le règlement en espèces et l'absence d'exercice anticipé — un straddle vendeur ne peut donc pas être assigné avant l'échéance, ce qui est précisément le mode de défaillance que la variante sur options d'action doit traiter par une branche d'assignation explicite.

| Régime détecté | Position ouverte |
|---|---|
| Volatilité basse (régime 0) | **straddle vendeur**, échéance la plus proche |
| Volatilité haute (régime 1) | **straddle acheteur**, échéance la plus lointaine |

## Ce qui diffère de la variante sur options d'action, et que le livre garde

- Le **déclencheur de rollover** est temporel (`expiry - now < min_expiry`) et non piloté par l'assignation, parce qu'un straddle d'indice n'est jamais assigné de façon anticipée.
- `liquidate()` **sans argument** vide tout le portefeuille — l'appel du livre — au lieu de parcourir les contrats un à un.
- Le capital de départ est **1 000 000** (le livre) et non 100 000 : le multiplicateur d'un contrat d'indice est bien plus élevé que celui d'une option sur action.

## Fidélité au livre, et écarts déclarés

Le modèle, la table des régimes, le filtre d'échéance, la construction du straddle et la branche de rollover sont **ceux du livre**. Cinq écarts sont déclarés — quatre gardes que le livre laisse implicites, et un réglage de courtage qui déplace la mesure :

1. **Longueur de série avant l'ajustement** — le livre ajuste ce qu'il a ; sous ~100 points l'ajustement diverge ou lève.
2. **Liste d'échéances vide** — le livre garde déjà cette garde, le portage la conserve.
3. **`try/except` autour de l'ajustement**, avec un compteur publié en statistique d'exécution.
4. **Paramètres** `start_year`, `end_year`, `cash`, `lookback_years`, dont les valeurs par défaut sont **celles du livre** (2019, 2024, 1 000 000, 3).
5. **Modèle de courtage** — le livre n'en règle aucun. Le portage fixe Interactive Brokers sur compte sur marge, sans quoi un straddle vendeur d'indice serait refusé faute de pouvoir d'achat. Les frais appliqués sont donc ceux d'Interactive Brokers et non ceux du modèle par défaut de QuantConnect : des cinq écarts, c'est le seul qui **déplace la mesure** au lieu d'éviter une levée.

Les quatre premiers sont des gardes ; le cinquième est un réglage. Le repère de performance est en outre fixé à l'indice SPX, là où QuantConnect prend SPY par défaut : le ratio de Sharpe n'en dépend pas, mais l'alpha et le bêta rapportés, si.

Le diff structurel des appels `self.*` entre le `main.py` du livre et ce portage ne contient **que des ajouts** — aucun appel du livre n'a été retiré.

## Comment lancer

**QC Cloud :** projet `37338052`. Paramètres : `start_year`/`end_year` (défaut 2019/2024), `cash` (défaut 1 000 000), `lookback_years` (défaut 3), `min_expiry`/`max_expiry`/`min_hold_period` (défaut 180/365/7), `quantity` (défaut 1).
**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Markov-Regime-Detection-Index-Options"`

## Métriques de backtest

Fenêtre du livre : 2019-01-01 → 2024-01-01, capital 1 000 000 (valeur du livre). Rejeu par le MCP QC, projet `37338052`, backtest `book-window-2019-2024`. Chiffres repris de `measures/qc_statistics.json`, où ils sont écrits depuis la plateforme.

| Métrique | Valeur |
|---|---|
| Sharpe Ratio | **−1,832** |
| CAGR (`Compounding Annual Return`) | **−3,568 %** |
| Pire baisse (`Drawdown`) | **20,700 %** |
| Probabilistic Sharpe Ratio | 0,000 % |
| Profit net | **−16,602 %** (−167 190 $) |
| Ordres | 470 |
| Frais | 470 $ |
| Rotation de portefeuille | 0,78 % |
| Alpha / Bêta | −0,039 / −0,082 |
| Taux de réussite | 44 % (56 % de pertes) |

Compteurs d'exécution du portage : 98 bascules de régime, **67 straddles vendeurs et 51 acheteurs**, 49 rollovers, 0 échec d'ajustement, **32 listes d'échéances vides**. Contrairement à la variante sur actions, la garde n°2 a servi : sur 32 journées planifiées, le filtre 180-365 jours a vidé la liste des échéances SPX et la stratégie est restée sans position ce jour-là. L'ajustement, lui, n'a jamais échoué — et il n'y a pas de compteur d'assignation, puisqu'un straddle d'indice européen n'en subit pas.

À noter que le modèle penche côté vendeur (67 contre 51) : le régime « basse volatilité » domine légèrement la fenêtre. L'ajustement porte sur les rendements **passés**, sur une fenêtre glissante de trois ans — le portage ne prend pas les régimes en avance, il les constate.

### Comparaison à SPX détenu, même période

| Bras | Sharpe | CAGR | Pire baisse | Rendement total |
|---|---|---|---|---|
| 06/04/03 (ce projet) | −1,832 | −3,568 % | 20,700 % | **−16,602 %** |
| SPX détenu | 0,610 | +13,92 % | — | **+91,89 %** |

Le chiffre de SPX est mesuré hors QuantConnect (cours de l'indice `^GSPC` du 2018-12-28 au 2023-12-29, soit les 1259 séances de la fenêtre ; SPX est un indice de cours, sans dividendes). Alpha et bêta rapportés par la plateforme contre ce même repère : −0,039 et −0,082, cohérents avec un repère nettement positif.

**Verdict : `NO BEATS`.** Le portage reproduit la mécanique du livre — 118 straddles ouverts, aucun échec d'ajustement — et cette mécanique perd : −16,6 % contre +91,9 % pour l'indice détenu, à fenêtre et capital égaux.

### Période hors échantillon

Fenêtre 2024-01-01 → 2026-01-01 (502 séances), capital 1 000 000, mêmes règles — la fenêtre se déplace par les paramètres `start_year`/`end_year`, sans bifurcation de code.

| Métrique | Valeur |
|---|---|
| Sharpe Ratio | **−2,635** |
| CAGR (`Compounding Annual Return`) | **−2,400 %** |
| Pire baisse (`Drawdown`) | **7,100 %** |
| Probabilistic Sharpe Ratio | 0,000 % |
| Profit net | **−4,750 %** (−48 516 $) |
| Ordres | 126 |
| Frais | 126 $ |
| Rotation de portefeuille | 0,60 % |
| Alpha / Bêta | −0,052 / −0,133 |
| Taux de réussite | 52 % |

Compteurs d'exécution : 28 bascules de régime, 21 straddles vendeurs et 11 acheteurs, 25 rollovers, 0 échec d'ajustement, 20 listes d'échéances vides. Le penchement vendeur s'accentue hors échantillon (21 contre 11) : le régime « basse volatilité » domine la fenêtre 2024-2026, et le taux de réussite monte à 52 % — mais les pertes des straddles vendeurs dans un marché qui monte de plus de 40 % suffisent à emporter le résultat.

| Bras | Sharpe | Rendement total |
|---|---|---|
| 06/04/03, hors échantillon | −2,635 | **−4,750 %** |
| SPX détenu, hors échantillon | 1,140 | **+43,52 %** |

**Verdict hors échantillon : `NO BEATS`.** Comme pour la variante sur actions, la fenêtre 2024-2026 est un marché haussier fort : le pire terrain pour un straddle vendeur.

## Voir aussi

- [BOOK_MAPPING.md](../../BOOK_MAPPING.md) — inventaire du livre, lignes 04/03
- [Markov-Regime-Detection](../Markov-Regime-Detection/) — exemple 04/01, rotation SPY/TLT
- [Markov-Regime-Detection-Equity-Options](../Markov-Regime-Detection-Equity-Options/) — exemple 04/02, mêmes règles sur SPY
