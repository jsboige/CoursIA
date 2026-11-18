# Markov-Regime-Detection-Equity-Options

**Classe d'actifs :** Actions américaines (SPY) et options sur action
**ID projet Cloud :** `37338046`

## Description

Port de l'exemple **06/04/02 — Equity Options** du livre *Hands-On AI Trading with Python, QuantConnect, and AWS* (Jared Broad et al., Wiley, 2025), dépôt [QuantConnect/HandsOnAITradingBook](https://github.com/QuantConnect/HandsOnAITradingBook) au commit `e025f21`.

Le même modèle que [06/04/01](../Markov-Regime-Detection/) — `MarkovRegression` de statsmodels, `k_regimes=2`, `switching_variance=True` sur les rendements glissants de SPY — mais l'avis est exprimé **en options** plutôt qu'en rotation d'actifs :

| Régime détecté | Position ouverte |
|---|---|
| Volatilité basse (régime 0) | **straddle vendeur** (short straddle), échéance la plus proche |
| Volatilité haute (régime 1) | **straddle acheteur** (long straddle), échéance la plus lointaine |

Les deux jambes sont au strike le plus proche du sous-jacent. Le filtre d'échéance du livre est conservé : `min_expiry` 180 jours, `max_expiry` 365 jours, `min_hold_period` 7 jours.

## Fidélité au livre, et écarts déclarés

Le modèle, la table des régimes, le filtre d'échéance, la construction du straddle et le gestionnaire d'assignation sont **ceux du livre**. Cinq écarts sont déclarés — quatre gardes que le livre laisse implicites, son code étant du code d'enseignement qui laisse plusieurs appels lever, et un réglage de courtage qui déplace la mesure :

1. **Longueur de série avant l'ajustement** — le livre ajuste ce qu'il a ; sous ~100 points l'ajustement diverge ou lève.
2. **Liste d'échéances vide** — le livre appelle `min()`/`max()` sur une liste que le filtre peut rendre vide.
3. **`try/except` autour de l'ajustement**, avec un compteur publié en statistique d'exécution, au lieu de laisser le gestionnaire planifié mourir pour la journée.
4. **Paramètres** `start_year`, `end_year`, `cash`, `lookback_years`, dont les valeurs par défaut sont **celles du livre** (2019, 2024, 100 000, 3) : la fenêtre du livre se rejoue à l'identique et une fenêtre hors échantillon ne demande aucune bifurcation de code.
5. **Modèle de courtage** — le livre n'en règle aucun. Le portage fixe Interactive Brokers sur compte sur marge, sans quoi un straddle vendeur de cette taille serait refusé faute de pouvoir d'achat. Les frais appliqués sont donc ceux d'Interactive Brokers et non ceux du modèle par défaut de QuantConnect : des cinq écarts, c'est le seul qui **déplace la mesure** au lieu d'éviter une levée.

Les quatre premiers sont des gardes ; le cinquième est un réglage. Le repère de performance est en outre fixé au sous-jacent — pour cette variante c'est déjà le repère par défaut de QuantConnect, l'appel n'y change rien.

Le diff structurel des appels `self.*` entre le `main.py` du livre et ce portage ne contient **que des ajouts** — aucun appel du livre n'a été retiré.

## Comment lancer

**QC Cloud :** projet `37338046`. Paramètres : `start_year`/`end_year` (défaut 2019/2024), `cash` (défaut 100 000), `lookback_years` (défaut 3), `min_expiry`/`max_expiry`/`min_hold_period` (défaut 180/365/7), `quantity` (défaut 1).
**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Markov-Regime-Detection-Equity-Options"`

## Métriques de backtest

Fenêtre du livre : 2019-01-01 → 2024-01-01, capital 100 000 (valeur du livre). Rejeu par le MCP QC, projet `37338046`, backtest `book-window-2019-2024`. Chiffres repris de `measures/qc_statistics.json`, où ils sont écrits depuis la plateforme.

| Métrique | Valeur |
|---|---|
| Sharpe Ratio | **−2,188** |
| CAGR (`Compounding Annual Return`) | **−6,808 %** |
| Pire baisse (`Drawdown`) | **33,100 %** |
| Probabilistic Sharpe Ratio | 0,000 % |
| Profit net | **−29,698 %** (−28 048 $) |
| Ordres | 430 |
| Frais | 430 $ |
| Rotation de portefeuille | 0,77 % |
| Alpha / Bêta | −0,06 / −0,089 |
| Taux de réussite | 37 % (63 % de pertes) |

Compteurs d'exécution du portage : 107 bascules de régime, **54 straddles vendeurs et 54 acheteurs**, 0 échec d'ajustement, 0 chaîne d'options vide, 0 assignation. Les gardes déclarées plus haut n'ont donc pas servi : la stratégie a bien ouvert 108 straddles, et c'est le résultat qui est négatif.

À noter que le modèle alterne (54 vendeurs, 54 acheteurs) : il ne reste pas bloqué d'un côté. L'ajustement porte sur les rendements **passés**, sur une fenêtre glissante de trois ans — le portage ne prend pas les régimes en avance, il les constate.

### Comparaison à SPY détenu, même période

| Bras | Sharpe | CAGR | Pire baisse | Rendement total |
|---|---|---|---|---|
| 06/04/02 (ce projet) | −2,188 | −6,808 % | 33,100 % | **−29,698 %** |
| SPY détenu | 0,796 | +15,61 % | — | **+106,16 %** |

Le chiffre de SPY est mesuré hors QuantConnect (rendement total, dividendes réinvestis, sur `SPY` du 2019-01-02 au 2023-12-29, soit les 4,99 années de la fenêtre). Alpha et bêta rapportés par la plateforme contre ce même repère : −0,06 et −0,089, cohérents avec un repère nettement positif.

**Verdict : `NO BEATS`.** Le portage reproduit la mécanique du livre — 108 straddles ouverts, aucune garde déclenchée — et cette mécanique perd : −29,7 % contre +106,2 % pour le sous-jacent détenu, à fenêtre et capital égaux.

### Période hors échantillon

Fenêtre 2024-01-01 → 2026-01-01 (502 séances), capital 100 000, mêmes règles — la fenêtre se déplace par les paramètres `start_year`/`end_year`, sans bifurcation de code. Le backtest `oos-2024-2026` porte `parameterSet: {'start_year': 2024, 'end_year': 2026}` et 502 dates négociables : les paramètres sont appliqués, pas seulement enregistrés.

| Métrique | Valeur |
|---|---|
| Sharpe Ratio | **−1,850** |
| CAGR (`Compounding Annual Return`) | **−2,475 %** |
| Pire baisse (`Drawdown`) | **7,500 %** |
| Probabilistic Sharpe Ratio | 0,000 % |
| Profit net | **−4,895 %** (−6 177 $) |
| Ordres | 90 |
| Frais | 90 $ |
| Rotation de portefeuille | 0,46 % |
| Alpha / Bêta | −0,044 / −0,205 |
| Taux de réussite | 45 % |

Compteurs d'exécution : 22 bascules de régime, 12 straddles vendeurs et 11 acheteurs, 0 échec d'ajustement, 0 chaîne vide, 0 assignation. Même profil qu'en fenêtre du livre, en plus court : le modèle alterne, les gardes ne servent pas, et le résultat reste négatif.

| Bras | Sharpe | Rendement total |
|---|---|---|
| 06/04/02, hors échantillon | −1,850 | **−4,895 %** |
| SPY détenu, hors échantillon | 1,282 | **+47,84 %** |

**Verdict hors échantillon : `NO BEATS`.** La fenêtre 2024-2026 est un marché haussier fort (+47,8 % pour SPY) : c'est le pire terrain pour un straddle vendeur et le modèle n'a pas basculé assez souvent côté acheteur pour le compenser.

## Voir aussi

- [BOOK_MAPPING.md](../../BOOK_MAPPING.md) — inventaire du livre, lignes 04/02
- [Markov-Regime-Detection](../Markov-Regime-Detection/) — exemple 04/01, rotation SPY/TLT
- [Markov-Regime-Detection-Index-Options](../Markov-Regime-Detection-Index-Options/) — exemple 04/03, mêmes règles sur SPX
