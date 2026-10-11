# Framework_Composite_EMATrend

**Classe d'actifs :** Actions US (Mag7 + méga-capitalisations)
**Cloud project ID :** 28911253

## Description

Composite framework combinant EMA-Cross-Alpha (5 actions tech/Mag7, rééquilibrage
quotidien) avec TrendStocks-Alpha (15 méga-capitalisations diversifiées, rééquilibrage
hebdomadaire) via le QC Algorithm Framework. Allocation cible : EMA70/Trend30
(configuration gagnante du sweep).

Chevauchement d'univers : les 5 actions Mag7 (AAPL, MSFT, GOOGL, AMZN, NVDA) sont
présentes dans les deux stratégies. Le modèle de construction de portefeuille
(`MultiStrategyPCM`) attribue une part du capital à chaque alpha, puis additionne les deux
parts sur ces cinq titres. C'est le mode `intent`, par défaut depuis #19759.

**Défaut corrigé par #19759.** Avant d'appeler `determine_target_percent`, le
`PortfolioConstructionModel` de Lean ne garde que l'insight actif le plus récent de chaque
symbole. EMACross émet chaque jour sur ses cinq titres, TrendStocks une fois par semaine sur
ses quinze. Avant #19759, les parts ne s'additionnaient donc jamais : sur les cinq titres
communs, la cible suivait le dernier alpha à avoir émis. TrendStocks l'emportait dans 602
des 3502 appels mesurés. D'après le code, chacun de ces cinq titres passait alors de la part
d'EMACross (70 % répartis sur ses titres haussiers, soit 0,14 quand les cinq le sont) à
celle de TrendStocks (30 % répartis sur ses titres haussiers, jusqu'à quinze), puis y
revenait à l'émission suivante d'EMACross. La rotation mesurée vaut 74,7 fois le
portefeuille par an, contre 14,4 sous `intent`, et les frais environ 2,6 % de la valeur du
portefeuille par an, contre 0,5 %.

Ce comportement reste disponible sous `mode` = `base` pour reproduire les chiffres
antérieurs. Sous `intent`, le modèle reconstruit les cibles à partir de l'insight actif le
plus récent de chaque couple (symbole, alpha), puis les additionne par symbole.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Framework_Composite_EMATrend"`
**QC Cloud :** Déployé comme projet 28911253 (IBKR margin, backtest direct).

## Mesure #19759 : `NO BEATS`

Backtests QC Cloud du 2026-10-07, du 2015-01-02 au 2026-07-09 (2894 séances), frais du
courtier Interactive Brokers. Le protocole et la règle de verdict ont été fixés avant tout
calcul ([#19759](https://github.com/jsboige/CoursIA/issues/19759), même règle que #19740).
Le Sharpe est calculé à taux sans risque nul sur la valeur du portefeuille à chaque
clôture, par une analyse hors dépôt ; il diffère donc du Sharpe affiché par QC, qui
retranche un taux sans risque.

| Version | Sharpe | CAGR | Pire baisse | Rotation par an | Exposition brute moyenne |
|---------|--------|------|-------------|-----------------|--------------------------|
| `intent` (défaut) | 1,20 | 27,1 % | −36,3 % | 14,4 | 0,93 |
| `base` (code avant #19759) | 0,95 | 17,0 % | −28,0 % | 74,7 | 0,82 |
| EMACross seul (`ema`) | 1,19 | 30,8 % | −37,4 % | 14,6 | 0,91 |
| TrendStocks seul (`trend`) | 0,98 | 17,7 % | −33,7 % | 14,5 | 0,99 |
| SPY détenu (`spy`) | 0,83 | 13,8 % | −33,7 % | 0,09 | 1,00 |
| 60 % SPY / 40 % IEF (`sixty40`) | 0,88 | 8,9 % | −21,1 % | 0,29 | 1,00 |

**Verdict.** Il est `NO BEATS` pour `base` comme pour `intent` : aucun écart de Sharpe avec
les références n'est significatif. La différence est testée par bootstrap circulaire par
blocs de 21 séances (10 000 tirages, correction de Holm sur les deux références).

| Candidate | Écart avec SPY [IC 95 %] | Écart avec le 60/40 [IC 95 %] | p Holm (SPY / 60/40) |
|-----------|--------------------------|-------------------------------|----------------------|
| `intent` | +0,37 [−0,03 ; +0,76] | +0,32 [−0,11 ; +0,75] | 0,069 / 0,074 |
| `base` | +0,13 [−0,29 ; +0,52] | +0,07 [−0,38 ; +0,52] | 0,57 / 0,57 |

`intent` s'approche du seuil sans le franchir. Ses écarts sont positifs sur les trois
sous-périodes, mais l'essentiel tient à 2015-2018 : +0,96 contre SPY, puis +0,11 sur
2019-2022 et +0,07 sur 2023 → 2026-07. La grille de paramètres et le run à frais doublés
n'étaient prévus que pour une candidate significative : ils n'ont pas été lancés.

**Apport de chaque tranche.** Sous `intent`, l'écart de Sharpe avec EMACross seul vaut
+0,00 [−0,10 ; +0,12], et la corrélation hebdomadaire des rendements vaut 0,985 : le
composite se comporte comme EMACross seul, avec un CAGR plus bas. Avec TrendStocks seul,
l'écart vaut +0,22 [−0,17 ; +0,58]. Sous `base`, l'écart avec EMACross seul vaut −0,24
[−0,49 ; −0,01] : la rotation forcée coûtait du Sharpe. Ces écarts sont descriptifs, hors
correction de Holm.

**Choix du défaut.** `intent` est la conception annoncée par le projet : le docstring de
`MultiStrategyPCM` et ce README décrivent l'addition des parts. `base` faisait tourner le
portefeuille cinq fois plus vite pour un Sharpe plus bas. Ni l'une ni l'autre ne bat les
références : le changement de défaut rend le projet conforme à sa description, il ne crée
pas d'avantage démontré.

**Limites.**
- La tranche EMACross ne porte que cinq valeurs de la Mag7, choisies en connaissant la
  décennie. NVDA fournit à elle seule 44 % du résultat des positions fermées sous `intent`
  (47 % sous `ema`). Ce biais favorisait les candidates, ce qui renforce le `NO BEATS`.
- Les backtests demandaient une fin au 2026-09-30. L'organisation QC utilisée retient les
  90 derniers jours et a ramené la fin au 2026-07-09, sans erreur. Toutes les versions ont
  tourné dans la même organisation : les comparaisons portent sur les mêmes séances.
- La statistique `PCM calls with Trend on EMA tickers` vaut 602 sous `base` comme sous
  `intent` : elle compte les insights reçus par `determine_target_percent`, avant la
  reconstruction. La reconstruction se lit dans la rotation et dans les ordres sur les dix titres
  propres à TrendStocks (de 622 à 875 par titre sous `base`, de 238 à 284 sous `intent`).

## Chiffres antérieurs à #19759

Les deux sections ci-dessous datent d'avant la mesure ; elles sont conservées pour
l'historique.

**Lecture corrigée par #19759.**
- **Baseline alignée.** Le run `readme` (`base` sur 2018-01-01 → 2025-01-01, 1760 séances)
  la reproduit : Sharpe QC 0,614, CAGR 16,73 %, pire baisse 27,9 %, 8396 ordres. Le PSR
  diffère (8,95 % contre 19,8 %) ; la cause n'a pas été mesurée. Ces chiffres mesuraient le
  code `base`, dont les parts ne s'additionnaient pas sur les titres communs.
- **« Le MultiStrategyPCM combine additivement les poids. »** C'était faux sous `base` ;
  c'est vrai sous `intent`.

### Métriques de backtest

| Métrique | Catalogue 2015-2025 | Alignée 2018-2025 |
|----------|---------------------|-------------------|
| Sharpe Ratio | 0.741 | **0.611** |
| CAGR | — | 16.670 % |
| Max Drawdown | 28.0 % | 27.9 % |
| PSR | 27.4 % | 19.8 % |

Backtest catalogue (décennie complète 2015-2025, EMA70/Trend30) = Sharpe 0.741
(la docstring annonçait 0.867 → réel 0.741, −14 %). Voir `docs/qc/qc-comparative-backtests.md`.

### Baseline alignée (2018-2025)

Vérifiée sur la fenêtre alignée cohorte (2018-01-01 → 2025-01-01, 1761 dates
tradables), même configuration gagnante EMA70/Trend30 :

- **Sharpe 0.611** (backtest `3095a263d5bd30df181ec002c0a52b72`, projet 28911253)
- CAGR 16.670 %, MaxDD 27.9 %, PSR 19.8 %

**Verdict : survit à l'alignement avec une baisse modérée** (0.741 → 0.611, −18 %) — pas
un effondrement de sur-ajustement de période. Il perd une partie du pré-ramp Mag7 2015-2017
et absorbe le drawdown Mag7 de 2022, mais le signal tendance tient. Sur la fenêtre alignée,
c'est le **backbone COMP (composite-framework) au Sharpe le plus élevé vérifié à ce jour**
(devance composite-c2-equityfactor 0.574, FamaFrenchAllWeather 0.338,
composite-c1-multiasset 0.258). Promu Tier 4 (Untested) → Tier 2 (Historique).

**Caveat de survivance Mag7 :** le sleeve EMA est 100 % Mag7, le Sharpe est donc en partie
un artefact de la surperformance Mag7 sur la décennie backtestée. Le Sharpe le plus élevé
ne se confond pas avec la constitution la plus robuste : composite-c2-equityfactor
(0.574, diversifié factoriellement sur 25 actions) est le leader COMP le plus défendable
constitution-par-constitution, tandis qu'EMATrend est celui au Sharpe le plus élevé mais
concentré Mag7. Voir Key-finding #36 dans `docs/qc/qc-comparative-backtests.md`.

## Fichiers

- `main.py` — Stratégie (composite EMA70/Trend30, alignée 2018-2025 ; paramètres `mode`, `start`, `end`, `fee_mult` et grille depuis #19759)
- `alpha_models.py` — EMACrossAlpha + TrendStocksAlpha
- `portfolio_construction.py` — MultiStrategyPCM (blend d'allocation alpha)
- `quantbook.ipynb` — QuantBook de recherche du composite (sweep d'allocation cellule 12 : EMA70/Trend30 élu, Sharpe 0.497)
- `quantbook_composite_research.ipynb` — QuantBook pré-composite (corrélation des signaux EMA-Cross × TrendStocks)
