# Framework Composite - FamaFrench + AllWeather

## Description

Stratégie composite combinant deux approches complémentaires via le QuantConnect Algorithm Framework :

1. **FamaFrench (tranche 20 %)** : Rotation d'ETF factoriels (VLUE, MTUM, SIZE, QUAL, USMV)
   - Momentum ajusté du risque : rendement sur 12 mois hors dernier mois (`lookback` = 252 séances, 21 séances écartées), divisé par la volatilité réalisée annualisée sur 63 séances (`vol_window`)
   - Skip-month (exclure le dernier mois pour éviter le retournement court terme)
   - Tous les facteurs à score positif, à poids égaux ; si aucun score n'est positif, USMV seul
   - Seul le signe du score décide. Diviser par une volatilité positive ne change pas ce signe : la sélection est celle du momentum brut, et `vol_window` n'a aucun effet sur les ordres (mesuré : le point de grille `vol_window` 126 reproduit `intent` à l'identique)
   - Signal émis le premier jour de bourse de chaque mois

2. **AllWeather (tranche 80 %)** : Allocation statique multi-actifs (SPY 30 %, IEF 30 %, GLD 30 %, XLP 10 %)
   - Portefeuille « All Weather » inspiré de Ray Dalio (simplifié, sans TLT)
   - Signal émis le premier jour de bourse de chaque mois

Le modèle de construction de portefeuille (`MultiStrategyPCM`) répartit le capital entre les deux tranches et rééquilibre tous les 31 jours. Le code ne contient ni seuil de dérive ni sélection des deux meilleurs facteurs.

## Principe de conception clé

**PAS de chevauchement entre univers** : ETF factoriels (facteurs actions) vs actifs traditionnels (actions/obligations/or). Cela crée une vraie diversification :
- FamaFrench : exposition aux facteurs actions (value, momentum, size, quality, low-vol)
- AllWeather : allocation macro (actions, obligations, or, défensif)

**Important** : FamaFrench utilise le momentum ajusté du risque UNIQUEMENT (pas de filtre SMA200). AllWeather gère la défense via son allocation statique. C'est le mode `intent`, par défaut depuis #19621.

**Défaut corrigé par #19621.** `alpha_models.py` contient aussi un filtre de régime sur la SMA200 de SPY, qui contredit ce principe. Avant #19621, ce filtre n'était jamais créé : SPY n'appartient pas à l'univers de la tranche FamaFrench, et la tranche n'émettait donc aucun signal. Elle restait en liquide pendant tout le backtest, et le composite valait 80 % d'AllWeather et 20 % de liquide. Ce comportement reste disponible sous `mode` = `base` pour reproduire les chiffres antérieurs ; `mode` = `sma` rend le filtre effectif.

## Fichiers

- `main.py` : Configuration de l'algorithme avec CompositeAlpha et MultiStrategyPCM
- `alpha_models.py` : Classes FamaFrenchAlpha et AllWeatherAlpha
- `portfolio_construction.py` : MultiStrategyPCM pour l'allocation de capital par stratégie
- `quantbook.ipynb` : Notebook de recherche avec analyse de backtest

## Performance

### Mesure #19621 : `NO BEATS`

Backtests QC Cloud du 2026-10-07, du 2015-01-02 au 2026-09-25 (2949 séances), frais du courtier Interactive Brokers. Le protocole et la règle de verdict ont été fixés avant tout calcul ([#19621](https://github.com/jsboige/CoursIA/issues/19621)). Le Sharpe est calculé à taux sans risque nul sur la valeur du portefeuille à chaque clôture, par une analyse hors dépôt ; il diffère donc du Sharpe affiché par QC, qui retranche un taux sans risque.

| Version | Sharpe | CAGR | Pire baisse | Rotation par an | Ordres sur les ETF factoriels |
|---------|--------|------|-------------|-----------------|-------------------------------|
| `intent` (défaut) | 1,02 | 9,6 % | −17,6 % | 0,79 | 232 |
| `base` (code avant #19621) | 1,03 | 7,0 % | −13,2 % | 0,33 | 0 |
| `sma` (filtre SMA200 effectif) | 1,01 | 9,4 % | −17,2 % | 1,09 | 243 |
| AllWeather seul (`base`, 0 / 1) | 1,03 | 8,8 % | −16,2 % | 0,43 | 0 |
| SPY détenu (`spy`) | 0,83 | 13,9 % | −33,7 % | 0,09 | — |
| 60 % SPY / 40 % IEF (`sixty40`) | 0,87 | 8,8 % | −21,1 % | 0,28 | — |

**Verdict.** Il est `NO BEATS` pour `base` comme pour `intent` : aucun écart de Sharpe avec les références n'est significatif. La différence est testée par bootstrap circulaire par blocs de 21 séances (10 000 tirages, correction de Holm sur les deux références).

| Candidate | Écart avec SPY [IC 95 %] | Écart avec le 60/40 [IC 95 %] | p Holm |
|-----------|--------------------------|-------------------------------|--------|
| `intent` | +0,19 [−0,13 ; +0,48] | +0,15 [−0,10 ; +0,39] | 0,22 |
| `base` | +0,20 [−0,25 ; +0,59] | +0,16 [−0,20 ; +0,49] | 0,37 |

Les autres conditions du `BEATS` tiennent :
- l'écart reste positif à frais doublés ;
- il est positif sur au moins deux des trois sous-périodes (2015-2018, 2019-2022, 2023 → 2026-09) ;
- il est positif sur les cinq points de la grille (part factorielle 10 % et 40 %, `lookback` 189 et 315, `vol_window` 126 ; ce dernier point est inerte, voir la description).

Sur près de douze ans, l'avance du composite reste indiscernable du bruit.

**Apport de la tranche factorielle.** L'écart de Sharpe `intent` − AllWeather seul vaut −0,01 [−0,14 ; +0,14], et `sma` − AllWeather seul −0,02 [−0,15 ; +0,12]. Active, la tranche relève le rendement annuel d'environ 0,8 point et la pire baisse de 1,4 point, sans changer le Sharpe. Sous `base`, l'écart est −0,002 : 20 % de liquide ne change pas un Sharpe calculé à taux sans risque nul.

**Choix du défaut.** `intent` est la conception annoncée par le projet. `sma` ajoute de la rotation (1,09 contre 0,79 par an) pour un Sharpe qui n'est pas meilleur. `base` laisse un cinquième du capital en liquide. Ni `intent` ni `sma` ne bat les références : le changement de défaut rend le projet conforme à sa description, il ne crée pas d'avantage mesuré.

**Limite.** La fenêtre de mesure est incluse dans celle du balayage d'allocation (2010-2026) : il n'y a pas de période hors échantillon. Ce défaut favorisait la candidate, ce qui renforce le `NO BEATS`.

### Chiffres antérieurs à #19621

Les tableaux ci-dessous datent d'avant la mesure ; ils sont conservés pour l'historique.

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | 0.588 |
| CAGR | 9.9 % |
| Max Drawdown | 17.1 % |
| Période | 2010-2026 |

Fenêtre #1630 standardisée (2018-01-01 à 2025-01-01, 1761 dates tradables), backtestée sur QC Cloud avec les frais du courtier post-#2801.

| Métrique | Headline README (sweep 2010-2026) | Catalogue (2015-2025) | Alignée (2018-2025) |
|----------|-----------------------------------|-----------------------|---------------------|
| Sharpe | 0.588 | 0.472 | 0.338 |
| CAGR | 9.9 % | 7.226 % | 6.578 % |
| MaxDD | 17.1 % | 13.1 % | 13.1 % |
| PSR | — | 35.0 % | 22.9 % |

Backtest aligné `e9ac7c66` (1761 dates tradables) / backtest catalogue `70415edc` (`FF20_AW80_2015_2025_extended`, 2766 dates) / chiffre « OOS » 2023-2026 (Sharpe 0.684, PSR 87.5 %) `b08c8956`, sur 835 dates seulement. Le `totalOrders=0` lu alors venait de l'extraction du wrapper MCP : le run `orig` de #19621 compte 343 ordres, tous sur la tranche AllWeather. Le projet avait été promu du Tier 4 (Untested) au Tier 2 (Historique).

**Lecture corrigée par #19621.**
- **Fenêtre alignée.** Le run `orig` (`base` sur 2018-01-01 → 2025-01-01) reproduit la ligne alignée : Sharpe QC 0,341, CAGR 6,57 %, pire baisse 13,1 %, avec 0 ordre sur les ETF factoriels. Ces chiffres mesuraient déjà la tranche inerte. L'explication donnée jusqu'ici (« le sleeve AllWeather tire le composite sous la rotation FamaFrench ») ne tient donc pas : il n'y avait pas de rotation FamaFrench, seulement 20 % de liquide.
- **Statut du registre.** Le 87,5 % du registre est le PSR de ce petit échantillon, pas une mesure contre une référence.
- **Balayage 2010-2026.** Sa pire baisse (17,1 %) et la hausse du CAGR avec la part factorielle ressemblent à une tranche active (`intent` −17,6 %, `sma` −17,2 %), pas à la tranche inerte (−13,2 %). Hypothèse non vérifiée : le balayage a été produit par une version antérieure du code.

| Allocation | Sharpe | CAGR | Max DD |
|------------|--------|------|--------|
| FF20/AW80 | 0.588 | 9.9 % | 17.1 % |
| FF40/AW60 | 0.564 | 10.5 % | 19.3 % |
| FF50/AW50 | 0.539 | 10.8 % | 21.7 % |
| FF60/AW40 | 0.512 | 11.2 % | 24.1 % |

| Stratégie | Sharpe | CAGR | Max DD |
|-----------|--------|------|--------|
| FamaFrench v3.0 | 0.540 | 12.1 % | 24.2 % |
| AllWeather | 0.667 | 9.3 % | 16.4 % |
| Composite (FF20/AW80) | 0.588 | 9.9 % | 17.1 % |

## Paramètres

| Paramètre | Défaut | Description |
|-----------|--------|-------------|
| `mode` | `intent` | `intent` : tranche FamaFrench sans filtre de régime · `base` : code avant #19621 (tranche inerte) · `sma` : filtre SMA200 de SPY effectif · `spy`, `sixty40` : références détenues, rééquilibrées le premier jour de bourse du mois |
| `ff_allocation` | 0.20 | Tranche FamaFrench (0.20 = 20 %) |
| `aw_allocation` | 0.80 | Tranche AllWeather (0.80 = 80 %) |
| `lookback` | 252 | Horizon du momentum, en séances |
| `vol_window` | 63 | Fenêtre de la volatilité réalisée, en séances (sans effet sur les ordres, voir la description) |
| `start`, `end` | 2018-01-01, 2025-01-01 | Dates du backtest (`AAAA-MM-JJ`) |
| `fee_mult` | 1 | Multiplicateur des frais du courtier (2 = frais doublés) |

Le graphique `shadow` porte la valeur du portefeuille à chaque clôture, les frais cumulés et la rotation cumulée (contrat du rejeu en ombre, #18923). Les statistiques d'exécution `Orders <ETF>` comptent les ordres exécutés par ETF.

## Période de backtest

Par défaut 2018-01-01 à 2025-01-01. La mesure #19621 porte sur 2015-01-01 à 2026-09-25 ; le balayage d'allocation antérieur couvrait 2010-01-01 à 2026-03-10.

## Déploiement

- **Project ID** : 28882145
- **Organization** : Jean-Sylvain Boige (Researcher PAID)
- **Statut** : ✅ Déployé et backtesté

## Références

- **FamaFrench** : Rotation d'ETF factoriels avec momentum ajusté du risque
- **AllWeather** : Allocation statique multi-actifs (sans TLT)
- **SESSION5_PATTERNS.md** : Guide pédagogique AlphaModel Framework
