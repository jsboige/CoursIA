# Cloud-MeanReversion-Sectors

**Classe d'actifs :** Actions (ETF sectoriels GICS)

**ID projet Cloud :** 30822855

## Description

Stratégie de retour à la moyenne basée sur le RSI(14) sur 11 ETF sectoriels GICS (XLK, XLF, XLE, XLV, XLI, XLY, XLP, XLU, XLB, XLRE, XLC). Trois variantes de sophistication croissante : v1 utilise des signaux bruts de survente/surachat du RSI ; v2 ajoute un filtre de régime SMA200 (ne trader qu'en marché haussier) ; v3 incorpore une règle de stop-loss à 8 %. Scan quotidien 30 minutes après l'ouverture du marché. Brokerage Interactive Brokers (frais réels), benchmark SPY.

La variante v1, la seule mesurée ici, achète les ETF dont le RSI(14) passe sous 35, les plus survendus d'abord, au plus trois lignes à 1/3 du portefeuille chacune. Elle sort au-dessus de 55 ou après 20 séances de détention.

## Comment exécuter

### Lean CLI

```bash
lean backtest --algorithm Cloud-MeanReversion-Sectors/main.py
```

### QC Cloud

Projet 30822855. Téléverser `main.py`, compiler et lancer un backtest. Le paramètre `version` (`v1`/`v2`/`v3`) choisit la variante ; sans paramètre, le code prend `v1`. Période par défaut : **2018-01-01 → 2025-01-01** (alignée sur la baseline cross-stratégie #1630).

**Paramètres de mesure** (#23257) :

| Paramètre | Valeurs | Défaut |
|-----------|---------|--------|
| `mode` | `strategy` (la stratégie) ; `spy` (SPY 100 % détenu) ; `6040` (SPY 60 % / BND 40 %) ; `ew11` (les ETF sectoriels de l'univers à poids égal, parmi ceux qui cotent) | `strategy` |
| `fix` | `on` (exécution corrigée, ci-dessous) ; `off` (code d'avant #23257, pour le contrôle) | `on` |
| `start_date`, `end_date` | dates `AAAA-MM-JJ` | `2018-01-01`, `2025-01-01` |

Les trois modes de référence se rééquilibrent le premier jour de bourse du mois, 30 minutes après l'ouverture, à l'heure du scan de la stratégie. Le graphique `shadow` trace la valeur du portefeuille à chaque ouverture de séance du SPY. C'est l'entrée du calcul de significativité (`Paradox46Benchmarks/significance.py`). Trois statistiques d'exécution sont relevées :

- `reentries` compte les ETF re-sélectionnés le jour même de leur sortie (durée, ou stop en v3 avec `fix=off`). Avec `fix=on`, une sortie sur stop exclut l'ETF des candidats du jour ;
- `short_days` compte les ouvertures où une ligne est courte ;
- `max_gross` donne l'exposition brute maximale lue à l'ouverture.

## Correction de l'exécution (#23257)

Le scan quotidien traitait d'abord les sorties par `self.liquidate(symbol)`, puis cherchait les entrées. Un ETF qui sortait après ses 20 séances de détention en restant sous 35 de RSI était re-sélectionné le jour même et recevait `self.set_holdings(symbol, 1/3)`. En résolution journalière, les deux ordres se remplissent à la clôture. `set_holdings`, calculé contre la position pas encore vendue, n'envoyait que l'écart : la ligne finissait à quelques parts. La stratégie la comptait pourtant comme une position pleine pendant 20 séances, et la place restait prise. Le même défaut a été corrigé sur `projects/MeanReversion` (#23199).

Le rejeu des ordres du code d'origine en compte **8 sur 2018-2024**, et chaque fois la ligne finit entre 0,5 % et 8,2 % du portefeuille au lieu de 33 % :

| Date | ETF | Parts vendues | Parts rachetées | Poids de la ligne après |
|------|-----|---------------|-----------------|-------------------------|
| 2018-12-26 | XLE | 1583 | 82 | 1,7 % |
| 2019-06-03 | XLE | 1530 | 32 | 0,7 % |
| 2020-03-24 | XLE | 1890 | 512 | 8,2 % |
| 2020-10-07 | XLE | 2074 | 200 | 3,0 % |
| 2022-10-04 | XLRE | 1041 | 40 | 1,2 % |
| 2023-10-04 | XLP | 589 | 16 | 0,9 % |
| 2023-10-20 | XLRE | 1249 | 29 | 0,8 % |
| 2023-12-08 | XLE | 1032 | 17 | 0,5 % |

Sur 2025 → mi-2026, il y en a deux : XLY le 2026-03-16 (4 parts gardées sur 340) et XLF le 2026-03-17 (15 sur 771). Aucune ne passe à découvert.

**Correctif.** Les sorties sont liquidées une fois les entrées connues. Un ETF re-sélectionné le jour de sa sortie ne reçoit plus que `set_holdings(symbol, 1/3)`, et la ligne finit à 1/3. Les seuils, le filtre de régime et la cadence ne changent pas. En v3, une sortie sur stop est liquidée et exclue des candidats du jour : le même ETF ne peut pas être racheté immédiatement. Cette distinction est nécessaire pour que le stop ne devienne pas un renforcement. Au rejeu des ordres de la variante v1, le code corrigé n'a **aucune vente-rachat du même jour et aucune position courte** sur les deux fenêtres. Chaque ligne encore détenue après un ordre pèse au moins 31 % du portefeuille, et le code corrigé passe huit ordres de moins (265 contre 273).

**Contrôle d'innocuité.** Le code de `main` (sha256 `6cda5ec4b0c7`) et le code instrumenté avec `fix=off` ont tourné le même jour sur la même fenêtre. Ils produisent les mêmes 273 ordres (date, symbole, quantité) et les mêmes statistiques QC. L'instrumentation ne change donc rien aux ordres. Le backtest publié le 2026-08-14 a les mêmes 273 ordres en date, symbole et sens. Par rapport au run du 2026-08-14, les quantités diffèrent de quelques parts sur 257 des 273 ordres, et le Sharpe passe de 0,067 à 0,069. La cause de ces écarts entre deux runs du même code n'est pas isolée ici. L'égalité exacte du contrôle porte seulement sur les deux runs lancés le même jour, pas sur la reproductibilité entre dates d'exécution.

**L'exposition brute dépasse encore 1.** Elle atteint 1,039 avec le correctif, contre 1,032 avec le code d'origine. Ce dépassement n'est pas introduit par le correctif. À la lecture du code, il vient des nouvelles lignes, dimensionnées à 1/3 de la valeur du portefeuille alors que les lignes détenues ne sont jamais ramenées à 1/3. Cette explication n'a pas été mesurée date par date.

**Contrôle de la sortie sur stop.** En v3, conserver seulement la cible après un stop pouvait renforcer la ligne au lieu de la solder. Le mode corrigé exclut maintenant le titre stoppé des candidats du jour, avant leur classement ; la place peut être prise par un autre ETF. Les sorties par durée conservent la ré-entrée normale. Le mode `fix=off` conserve le comportement d'origine, y compris ce défaut. Les seuils de stop ne changent pas, mais son effet est rétabli : il s'agit d'un changement de comportement v3, pas d'une simple clarification.

Le code complété (sha256 `ff72ef038902`) a été compilé puis exécuté sur QC Cloud le 2026-10-29, projet 38620750. Deux runs terminés sur 2018-01-01 → 2025-01-01 : témoin v1 `ab01508b8e6af4a02396bfba8da0e352` (Sharpe 0,162, CAGR 5,644 %, MaxDD 41,0 %, 265 ordres, aucune séance courte), et v3 `fc9f80a1b77166b0e0abca00c96ed76d` (Sharpe 0,252, CAGR 6,187 %, MaxDD 10,9 %, 434 ordres, aucune séance courte, exposition brute maximale 1,019). Le témoin v1 retrouve les statistiques du tableau ; cette comparaison n'isole pas l'effet du correctif v3, faute de bras v3 avant correctif sur la même fenêtre. Aucun verdict de performance v3 n'en est déduit. Les tests locaux exécutent la méthode du fichier source : stop sans rachat, place réutilisée, sorties par durée et signal, invariance v1/v2 et fidélité de `fix=off` sur un chemin synthétique. Leur modèle simplifié de remplissage ne remplace pas Lean.

## Métriques du backtest

Backtests QC Cloud du 2026-10-29, `version=v1`, capital de départ 100 000, frais de courtage modélisés par Lean. Le code instrumenté porte le sha256 `9b9a01006f3a`. Résultats lus après `completed: true`.

**w1 : 2018-01-01 → 2025-01-01** (1761 séances, du 2018-01-02 au 2024-12-31)

| Bras | Sharpe QC | CAGR | Drawdown max | PSR | Profit net | Ordres |
|------|-----------|------|--------------|-----|------------|--------|
| **`strategy`** (corrigé) | **0.162** | **5.64 %** | **41.0 %** | 0.38 % | 46.9 % | 265 |
| `strategy`, `fix=off` (code d'origine) | 0.069 | 3.79 % | 41.7 % | 0.15 % | 29.8 % | 273 |
| `spy` (référence) | 0.496 | 13.58 % | 33.7 % | 4.54 % | 144.0 % | 3 |
| `6040` (référence) | 0.378 | 8.66 % | 21.7 % | 2.16 % | 78.9 % | 147 |
| `ew11` (diagnostic) | 0.393 | 10.91 % | 36.0 % | 2.36 % | 106.5 % | 459 |

**w2 : 2025-01-01 → 2026-07-01** (373 séances, du 2025-01-02 au 2026-06-30)

| Bras | Sharpe QC | CAGR | Drawdown max | PSR | Profit net | Ordres |
|------|-----------|------|--------------|-----|------------|--------|
| **`strategy`** (corrigé) | **0.418** | **11.92 %** | **7.7 %** | 17.0 % | 18.4 % | 52 |
| `strategy`, `fix=off` (code d'origine) | 0.307 | 9.97 % | 7.2 % | 13.4 % | 15.3 % | 54 |
| `spy` (référence) | 0.665 | 18.96 % | 18.7 % | 27.5 % | 29.7 % | 2 |
| `6040` (référence) | 0.59 | 13.37 % | 11.2 % | 24.7 % | 20.7 % | 30 |
| `ew11` (diagnostic) | 0.632 | 15.84 % | 14.9 % | 26.7 % | 24.6 % | 107 |

Le Sharpe de QC retire un taux sans risque. Les tests ci-dessous utilisent un Sharpe à taux nul, calculé sur les rendements journaliers du graphique `shadow`.

**Significativité** (Ledoit-Wolf, bootstrap stationnaire, Newey-West). La correction de Holm porte d'un côté sur les deux références du verdict, de l'autre sur le diagnostic :

| Fenêtre | Comparaison | Sharpe à taux nul (stratégie / bras) | p de Holm, écart de Sharpe (Ledoit-Wolf ; bootstrap) |
|---------|-------------|---------------------------------------|------------------------------------------------------|
| w1 | vs `spy` | 0.40 / 0.76 | 0.64 ; 0.64 |
| w1 | vs `6040` | 0.40 / 0.75 | 0.64 ; 0.64 |
| w1 | vs `ew11` | 0.40 / 0.65 | 0.60 ; 0.60 |
| w2 | vs `spy` | 0.93 / 1.05 | 1.0 ; 1.0 |
| w2 | vs `6040` | 0.93 / 1.21 | 1.0 ; 1.0 |
| w2 | vs `ew11` | 0.93 / 1.15 | 1.0 ; 1.0 |

## Verdict : NO BEATS sur les deux fenêtres

Le protocole (#23012, repris dans #23257) donne BEATS seulement si le Sharpe dépasse celui du SPY détenu **et** que l'écart reste significatif après Holm contre les deux références. Il donne NO BEATS si le Sharpe est inférieur à celui du SPY détenu, et INCONCLUSIVE sinon. Les paramètres de la v1 datent d'avant l'alignement de 2018 : w1 est dans l'échantillon de tout réglage, et son verdict n'est qu'indicatif. C'est w2, hors échantillon, qui tranche.

- **w2 (2025 → mi-2026) : NO BEATS.** Sharpe 0.418 contre 0.665 pour SPY détenu, et CAGR de 11,9 % contre 19,0 %. Le drawdown est plus faible (7,7 % contre 18,7 %), mais le Sharpe à taux nul reste sous celui des trois bras (0,93 contre 1,05 pour SPY). Avec 373 séances, la puissance du test est faible.
- **w1 (2018-2024) : NO BEATS.** Sharpe 0.162 contre 0.496 pour SPY détenu. La stratégie rend 5,6 % par an contre 13,6 % pour SPY, pour un drawdown plus profond (41,0 % contre 33,7 %).

**Ce que mesure le diagnostic `ew11`.** Les onze ETF à poids égal font mieux que la stratégie sur les deux fenêtres (Sharpe à taux nul 0,65 contre 0,40 sur w1, 1,15 contre 0,93 sur w2), sans écart significatif après Holm. Choisir les secteurs les plus survendus n'apporte rien de mesurable par rapport à les détenir tous.

**Ce que le correctif change.** Sur w1, le Sharpe passe de 0,069 à 0,162 et le CAGR de 3,8 % à 5,6 %. Le drawdown reste au même niveau (41,0 % contre 41,7 %). Les huit lignes résiduelles occupaient chacune une place pendant 20 séances avec presque rien d'investi, soit environ 3 % des places-séances de la fenêtre (8 × 20 sur 3 × 1761). La faible exposition que le registre qualifiait de « near-cash » vient donc surtout du signal : aux dates d'ordre, la stratégie ne détient le plus souvent que deux lignes sur trois (médiane au rejeu), avec ou sans correctif. Le verdict ne change pas. Pas de re-réglage des paramètres : un ajustement rétrospectif serait du surapprentissage (EPIC #9768).

> **Historique des mesures (traçabilité)** : (1) run du 2026-04-28 sur code pré-#1630 (2014-2025, 2768 j.) : v1 Sharpe 0,288 / DD 42,4 %, v2 0,214, **v3 0,278 / DD 14,7 %** ; (2) run du 2026-08-07 même code stale : v1 0,176 / DD 41,7 % ; (3) run du 2026-08-14, premier sur le code aligné 2018-2025 (#1630) : v1 0,067 / DD 41,7 % ; (4) **mesure du 2026-10-29 ci-dessus** (#23257) : code d'origine 0,069, code corrigé 0,162 sur la même fenêtre, plus la fenêtre hors échantillon et les références détenues. Les chiffres d'avant août 2026 cités dans d'anciens catalogues (0,278 / 14,7 %) sont ceux du **v3** sur 2014-2025. Ils ne se comparent pas aux autres sans l'étiquette de variante et de période.

## Lecture (variante v1)

- **Piège de la valeur en tendance baissière.** Le RSI reste en survente tant que la baisse se poursuit, et le signal « acheter la survente » accumule des perdants dans les marchés baissiers (T4 2018, COVID 2020, 2022). Sans filtre de régime, la v1 reste pleinement exposée, d'où un drawdown de 41 % sur 2018-2024, plus profond que celui de SPY détenu.
- **Concentration sur les trois plus survendus.** Les trois ETF les plus survendus sont souvent ceux qui chutent ensemble (XLE revient dans cinq des huit ré-entrées du tableau ci-dessus).
- **Pas d'edge mesurable.** Ni contre SPY détenu, ni contre le 60/40, ni contre les onze secteurs à poids égal.

Les variantes v2 (+ filtre SMA200) et v3 (+ stop-loss 8 %) sont conçues pour répondre à ces faiblesses. Les tableaux et le verdict ci-dessus ne portent que sur v1 : ils ne prouvent pas la performance de v2/v3. Le code distingue les sorties sur stop des sorties par durée ; une ligne stoppée est soldée sans ré-entrée le même jour en mode corrigé.

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Mean reversion RSI(14) avec 3 variantes (v1 RSI pur, v2 +régime SMA200, v3 +stop-loss 8 %) sur 11 ETF sectoriels GICS ; re-entrée du même jour corrigée par #23257, modes de référence |

## Références

- [Documentation QuantConnect](https://www.quantconnect.com/docs/)
- EPIC de consolidation QC / Trading : #1621
- Discipliné par l'EPIC #9768 (dérive des métriques de backtest à travers les révisions)
- Mesure contre références détenues et correction de l'exécution : #23257 (même défaut sur `projects/MeanReversion` : #23199)
