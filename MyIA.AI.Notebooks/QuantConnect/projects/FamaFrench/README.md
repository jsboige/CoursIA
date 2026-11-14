# FamaFrench

**Asset class:** US Factor ETFs
**Cloud project ID:** None (local only)

## Description

Factor ETF rotation strategy using risk-adjusted momentum (12m-1m return / 63d realized volatility) with skip-month.
Universe of 5 Fama-French factor ETFs: VLUE (value), MTUM (momentum), SIZE (size), QUAL (quality), USMV (low-vol).

SMA200 regime filter on SPY: in bear markets, rotates to USMV as risk-off asset.
Dynamic top_n selection (all factors with positive score). Per-position stop-loss at -12%.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/FamaFrench"`
```bash
lean backtest --project .
```

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics (2015-2026)

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.540 |
| CAGR | 12.1% |
| Max Drawdown | 24.2% |
| Net Return | +258% |
| Rebalance | Monthly |

Note d'écart : le `Net Return | +258%` ci-dessus est le rendement net du run long de l'auteur ; le `Net +109%` de la docstring `v3.0` (`main.py`) est le rendement net de la **fenêtre alignée 2018-2025** (table ci-dessous, CAGR 11.111 % ⇒ `1.11111^7 − 1 = 109.07 %`). Les deux chiffres décrivent des fenêtres différentes, ils ne se contredisent pas. Fenêtre de cette première table : l'en-tête dit 2015-2026, le paragraphe d'interprétation ci-dessous dit « 2015-2024 » — l'écart est signalé, non tranché ici (aucun identifiant de backtest auteur n'est cité pour le départager).

### Aligned baseline (2018-2025)

Standardized #1630 backbone run (QC Cloud project `33251801`, backtest `697e96af`).

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.445 |
| CAGR | 11.111% |
| Max Drawdown | 24.100% |
| Probabilistic Sharpe Ratio | 11.9% |
| Tradeable dates | 1761 |

Interprétation : le run aligné donne un Sharpe de 0,445 (troisième meilleur socle sans ML, proche des 0,454 de GlobalMacro-Regime) et un CAGR de 11,1 % (deuxième après les 14,1 % de HAR-RV-J-Kelly). La v3.0 antérieure de l'auteur indiquait un Sharpe de 0,540 et une pire baisse de 24,2 %, mais sa fenêtre exacte reste indéterminée ci-dessus ; le run aligné indique une pire baisse de 24,1 %. Ces chiffres historiques portent sur des périodes différentes qui se chevauchent : ils ne démontrent ni la robustesse de la stratégie ni l'absence de surajustement à une période. La rotation combine momentum ajusté du risque, filtre SMA200, repli sur USMV et stop par position ; elle illustre ces mécanismes plutôt qu'une exposition factorielle statique.

Le chiffre historique de 0,684 pour le composite est conservé comme résultat rapporté : il ne démontre pas que le framework apporte de la valeur par rapport à cette rotation autonome, car l'identité des fenêtres, des implémentations et du protocole de comparaison n'est pas établie par ces chiffres. La [mesure du composite](../Framework_Composite_FamaFrenchAllWeather/README.md#mesure-19621--no-beats) conclut elle-même à `NO BEATS` et ne démontre pas d'apport de Sharpe de sa tranche factorielle. Le test de ligue ci-dessous compare la stratégie autonome à SPY et au 60/40 : `INCONCLUSIVE` sur 2018–2025 et `NO BEATS` sur la courte fenêtre 2025–2026. La promotion Tier 4 → 2 (Historique) rappelle le classement antérieur. `totalOrders = 0` était un artefact d'extraction du wrapper ; le contrôle ultérieur ci-dessous compte 249 ordres.

## Demi-séances (#20286)

Quand le 3 juillet tombe un lundi, c'est à la fois le premier jour de cotation du mois et une demi-séance qui ferme à 13:00, heure de New York : en 2017 et en 2023 sur les fenêtres ci-dessus. Sur la tranche de clôture d'une demi-séance, `history()` rend environ 21 barres journalières de moins que demandé (mesuré dans #20286 sur un autre projet). `_risk_adjusted_momentum` demandait `lookback + 5` barres et rejetait le titre sous `lookback`. Il restait moins de deux scores, et `rebalance` sortait sans rien écrire dans le journal. Ces mois-là passaient sans rééquilibrage : juillet 2023 sur 2018-2024, juillet 2017 et juillet 2023 sur 2015-2024.

Correctif dans `main.py` : `_risk_adjusted_momentum` demande le double de barres et garde les `lookback + 5` dernières. Sur une séance pleine, ce sont les mêmes barres qu'avant. Aucune ligne du journal ne montre l'historique court : la cause se déduit du code, et le retour des mois manquants avec ce seul changement la confirme.

Mesure sur les nœuds QC, frais de courtage inclus, protocole fixé avant les backtests ([#20286, c.6115594357](https://github.com/jsboige/CoursIA/issues/20286#issuecomment-6115594357)) :

| Fenêtre | Variante | Mois rééquilibrés | Sharpe | CAGR | Pire baisse | Ordres | Backtest |
|---|---|---|---|---|---|---|---|
| 2018-01-01 → 2025-01-01 (codée) | avant | 83 / 84 | 0.446 | 11.098 % | 24.2 % | 250 | `ae3857d1a5eb25ee984ac54265df672e` |
| | après | 84 / 84 | 0.446 | 11.096 % | 24.2 % | 253 | `72edd9f1cfb074417703e764df4e9c6e` |
| 2015-01-01 → 2024-12-31 | avant | 118 / 120 | 0.555 | 11.838 % | 24.1 % | 313 | `39e54720fe0ee2e49c11b5245d2afd98` |
| | après | 120 / 120 | 0.555 | 11.836 % | 24.1 % | 313 | `54a8fcab145eab2557865b9cceb8f062` |
| 2025-01-01 → 2026-07-10 (hors échantillon) | avant | 19 / 19 | 0.524 | 14.234 % | 14.5 % | 66 | `7da7535966e9266b2a5ba2600dd49d78` |
| | après | 19 / 19 | 0.524 | 14.234 % | 14.5 % | 66 | `137d3bd124123133eb4d4426e3599d7e` |

Sharpe calculé par QC, taux sans risque inclus. Les quatre prédictions fixées d'avance ont tenu :

- les rééquilibrages des lundis 3 juillet reviennent ;
- avant le premier de ces lundis, les ordres sont identiques (date, titre, quantité) ; sur 2015-2024, le 2016-07-01, les mêmes ordres partent dans un autre ordre de soumission ;
- les dates de rééquilibrage sont celles d'avant, plus les lundis ;
- hors échantillon, aucun mois ne commence par une demi-séance, et les deux variantes sont identiques au centime.

L'effet est minime. Le rééquilibrage du 2017-07-03 n'envoie aucun ordre, et celui du 2023-07-03 en envoie deux, sur SIZE et USMV. Les écarts suivants viennent de ces deux ajustements. L'écart de Sharpe est nul au millième, sous le seuil de 0.05 fixé d'avance, et les chiffres publiés plus haut ne sont pas réécrits. Ce n'est pas un verdict de stratégie : il s'agit de la correction d'un défaut, mesurée sur des fenêtres déjà vues.

## Verdict de ligue (#25615)

Mesure de la rotation de facteurs contre les deux références de la ligue — **SPY détenu** et
**60/40** (SPY 60 % / BND 40 %, rééquilibré en début de mois) — sur les deux fenêtres du
protocole. Tous les chiffres proviennent de QC Cloud (projet `39232628`), lus à
`completed: true` le 2026-11-11.

### Contrôle d'innocuité

Le code actuel est rejoué le même jour dans un projet séparé (témoin `39232629`). Le mode
`strategy` du code modifié reproduit les ordres et les statistiques QC du témoin **au centime**
: 249 ordres, Sharpe 0.446, CAGR 11.084 %, pire baisse 24.2 %, net 108.821 %, equity
$208 821.43, frais −$575.11, volume $4 209 471.51. Le paramètre `mode`, la trace `shadow` et le
compteur `invalid_orders` ne modifient pas le comportement du mode `strategy`.

### Fenêtre 1 — 2018-01-01 → 2025-01-01 (dans l'échantillon, 1761 séances)

| Mode | Sharpe QC | CAGR | Pire baisse | Net | Ordres | Backtest |
|---|---|---|---|---|---|---|
| strategy | 0.446 | 11.084 % | 24.2 % | +108.82 % | 249 | `7a099a68` |
| SPY détenu | 0.464 | 12.807 % | 33.6 % | +132.60 % | 1 | `5c880591` |
| 60/40 | 0.354 | 8.293 % | 21.7 % | +74.73 % | 145 | `7de755d1` |

### Fenêtre 2 — 2025-01-01 → 2026-07-31 (hors échantillon, 395 séances)

La fin effective, lue sur la trace, est le 2026-07-31 : la fenêtre n'est pas rognée par la
coupure de fin des nœuds QC. Elle ne couvre qu'environ 19 mois — sa puissance statistique est
faible, et c'est dit dès le protocole.

| Mode | Sharpe QC | CAGR | Pire baisse | Net | Ordres | Backtest |
|---|---|---|---|---|---|---|
| strategy | 0.406 | 12.083 % | 14.5 % | +19.75 % | 68 | `af0b87f2` |
| SPY détenu | 0.561 | 16.351 % | 18.7 % | +27.03 % | 2 | `88b38ddc` |
| 60/40 | 0.444 | 11.228 % | 11.1 % | +18.31 % | 29 | `2807bbc3` |

### Significativité (taux sans risque nul)

`Paradox46Benchmarks/significance.py`, sur les traces `shadow` journalières (contrat #18923).
Le Sharpe est annualisé par racine de 252, taux sans risque nul : il ne recopie pas le Sharpe
QC, qui retranche le taux. Correction de Holm sur les six p-valeurs de chaque fenêtre.

**Fenêtre 1** — Sharpe 0-rate : strategy **0.7495**, SPY détenu 0.7215, 60/40 0.7201.

| Contre | Écart de Sharpe | p Ledoit-Wolf | p de Holm |
|---|---|---|---|
| SPY détenu | +0.028 | 0.861 | 1.000 |
| 60/40 | +0.029 | 0.870 | 1.000 |

**Fenêtre 2** — Sharpe 0-rate : strategy **0.874**, SPY détenu 0.972, 60/40 1.066.

| Contre | Écart de Sharpe | p Ledoit-Wolf | p de Holm |
|---|---|---|---|
| SPY détenu | −0.098 | 0.815 | 1.000 |
| 60/40 | −0.192 | 0.640 | 1.000 |

### Verdict

- **Fenêtre 1 : `INCONCLUSIVE`.** L'écart de Sharpe est positif contre les deux références,
  mais sa p de Holm (Ledoit-Wolf) vaut 1.000, très au-dessus de 0.05 : le `BEATS` n'est pas
  atteint. Le Sharpe ponctuel de la stratégie n'est pas inférieur à celui de SPY détenu : le
  `NO BEATS` non plus.
- **Fenêtre 2 : `NO BEATS`.** Le Sharpe ponctuel de la stratégie est inférieur à celui de SPY
  détenu (0.874 < 0.972), et l'écart est négatif contre les deux références, sans être
  significatif sur 19 mois.

### Lecture

Le registre `docs/qc/qc-strategies-status.md` classait la rotation *Needs-improvement* sur une
seule mesure (Sharpe QC 0.445 sur 2018-2025). Ce verdict l'affine : la rotation ne bat pas SPY
détenu sur la fenêtre codée — l'écart de Sharpe est de l'ordre du bruit — et elle reste en
deçà en hors-échantillon. Le filtre SMA200 et le repli sur USMV améliorent la pire baisse
(24.2 % contre 33.6 % en fenêtre 1), pas le Sharpe. Ce n'est pas un verdict de suppression :
c'est la mesure manquante, posée sur les deux fenêtres du protocole et contre les deux
références de la ligue.

## Files

- `main.py` - Strategy (v3, risk-adjusted momentum with skip-month)
- `research.ipynb` - Factor analysis and signal robustness tests
- `quantbook.ipynb` - Reproduction QuantBook de l'analyse exploratoire sur les donnees natives QC (validation pre-backtest)

## References

- Fama & French (1993), "Common risk factors in the returns on stocks and bonds"
- Barroso & Santa-Clara (2015), "Momentum has its moments"
