# Crypto-ShortTermReversion

Retour à la moyenne court terme sur BTCUSDT — candidat crypto de la ligue de stratégies (#19821), idée « retour à la moyenne à court terme, qui devrait se décorréler d'une tendance ». Mesuré sous règle pré-inscrite (#21129) : verdict **NO BEATS**.

## La règle

RSI(2) de Wilder < 10 → achat de 95 % du cash ; sortie RSI(2) > 60 ou garde temporelle de 10 séances. Sans filtre de tendance : le canon actions de Connors garde une SMA200, mais la question posée est la décorrélation des stratégies de tendance déjà mesurées — le filtre est écarté a priori. La garde temporelle borne le couteau qui tombe. Aucun paramètre réglé sur les données : les défauts (2/10/60, garde 10) sont ceux du canon.

Compte Binance cash en USDT, frais du modèle de courtier Binance, barres journalières BTCUSDT (7 jours sur 7).

## Mesure (QC Cloud, 2026-10-16, projet 37939451)

Règle pré-inscrite sur #21129 avant le premier backtest. SHA du code mesuré : `a008bb4dcd` (empreinte sha256 du `main.py` : `7d22b22c5f0eb66f` ; le SHA gelé à la pré-inscription `6a8ad18111` ne différait que par un nom d'énum Lean, `WILDER` → `WILDERS`, règle inchangée). Fenêtre 2018-01-01 → 2026-09-25 ; première barre BTCUSDT Binance disponible sur QC relevée : **2018-05-02** (3 070 séances, 3 069 rendements communs). Statistique : différence de Sharpe (taux sans risque nul, annualisée sur 365 jours) contre BTC détenu sans frais, bootstrap circulaire par blocs de 21 jours, 10 000 tirages, graine 18921 ; une seule comparaison, la correction de Holm est l'identité.

| Run | Sharpe | CAGR | Pire baisse |
|---|---|---|---|
| `base` | 0,106 | −2,4 % | −57,1 % |
| BTC détenu | 0,742 | +30,3 % | −76,6 % |

| Différence de Sharpe | Écart | IC 95 % | p Holm | 2018-2020 | 2021-2023 | 2024 → 2026-09 |
|---|---|---|---|---|---|---|
| `base` − BTC | −0,529 | [−1,059 ; −0,003] | 0,976 | −1,028 | −0,359 | −0,504 |

**Verdict : NO BEATS** — la différence est négative et non significative, et les trois sous-périodes sont négatives. Conformément à la règle pré-inscrite, la grille de paramètres et le run à frais doublés ne sont pas lancés (ils ne peuvent plus changer un verdict non significatif).

312 ordres sur la fenêtre. Statistiques QC descriptives : Sharpe QC 0,016, PSR 0,18 %.

## Ce que la mesure ne dit pas

- La pire baisse de la règle (−57,1 %) est meilleure que celle du BTC détenu (−76,6 %) : la règle passe l'essentiel du temps en liquidités et coupe les krachs par absence, pas par skill — le Sharpe net de cette inactivité est négatif.
- La décorrélation visée existe mécaniquement (la règle n'entre que sur survente), mais elle ne vaut rien sans rendement : le candidat n'entre pas dans la matrice de la ligue comme stratégie suivie.
- Une variante avec filtre de tendance (canon actions complet) n'a pas été mesurée : ce serait une autre règle, à pré-inscrire séparément si la question se pose.

Traces (graphique shadow, producteur du verdict avec empreintes) : `QC-traces/21129-crypto-shortterm-reversion/`, hors dépôt.

See #21129 · Part of #19821
