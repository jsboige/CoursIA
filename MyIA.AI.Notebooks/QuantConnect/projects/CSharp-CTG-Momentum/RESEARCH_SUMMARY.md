# CTG-Momentum Robustness Research (2015-2025)

**Date**: 2026-02-17
**Mise à jour** : 2026-10-25, backtest C# sur QC Cloud avec une fenêtre figée (#22541)
**Mise à jour** : 2026-10-26, script proxy `research_robustness_simple.py` aligné sur les indicateurs de `Main.cs` et ré-exécuté sur la fenêtre figée (#21836)
**Projet QC**: CSharp-CTG-Momentum (ID: 19225388)
**Objectif**: Valider la stratégie sur une période étendue maximale (2015-2025) avant déploiement

---

## Contexte

### Stratégie actuelle
- **Période**: 2015-01-01 → 2025-12-31 (bornes figées dans `Main.cs`, paramètres QC `start-date` et `end-date`, #22541)
- **Univers**: OEF ETF (S&P 100 constituants)
- **Logic**: Momentum ranking (AnnualizedExponentialSlope 90j)
- **Filtres**:
  - SPY > SMA(200) pour acheter (regime filter) ; les ventes ne dépendent pas du régime
  - Action > EMA(150)
  - Gap < 15 % sur 90j (plus forte variation absolue d'une clôture à la suivante)
  - Pente annualisée × R² > 10 (échelle en pourcentage)
- **Sizing**: 1.0% risk ATR-based
- **Bug corrigé**: SMA(10) → SMA(200) (indicateur de régime `SMA("SPY", 200)` de `Main.cs`)

### Méthodologie de recherche

- **Univers proxy**: 30 large caps multisectoriels (Tech, Finance, Healthcare, Payments, Consumer, Energy, Entertainment, Software)
- **Source données**: yfinance (alternative à QuantBook pour research offline), chargées dès 2014-01-01 pour préchauffer les indicateurs
- **Fenêtre**: données 2015-01-02 → 2025-12-31 ; série hebdomadaire du proxy 2015-01-08 → 2025-12-18 (10,94 ans)
- **Rebalancing**: Hebdomadaire (jeudis, à l'ouverture, sur les indicateurs de la clôture de la veille), 557 jeudis

---

## Résultats Clés

### Proxy Python et backtest C#, fenêtre figée 2015-2025

| Mesure | Fenêtre | Sharpe | CAGR | MaxDD | Note |
|--------|---------|--------|------|-------|------|
| Proxy Python (script `research_robustness_simple.py`) | données 2015-01-02 → 2025-12-31, série 2015-01-08 → 2025-12-18 | 0,727 | 13,46 % | 25,94 % | indicateurs des classes C#, 30 grandes capitalisations, sans frais |
| SPY sur la même série hebdomadaire | idem | 0,876 | 13,46 % | 28,64 % | référence calculée par le script |
| Proxy Python (carnet `research_robustness.ipynb`) | données 2015-01-02 → 2025-12-31, série 2015-01-08 → 2025-12-18 | 1,106 | 25,33 % | 29,93 % | 30 grandes capitalisations, sans frais |
| Backtest C# QC Cloud, univers OEF | 2015-01-01 → 2025-12-31 | **0,438** | **14,0 %** | **42,4 %** | S&P 100, frais IB, 888 ordres |

Le Sharpe du script et celui du carnet sont calculés sur des rendements hebdomadaires sans taux sans risque ; celui de QC en retranche un.

**Lecture du script** : sur la fenêtre figée, le proxy fait le même rendement total que SPY (298,16 % contre 298,13 %), avec une pire baisse plus faible (25,94 % contre 28,64 %) et un Sharpe plus bas (0,727 contre 0,876). Le critère Sharpe >= 0,4 est atteint, mais le proxy ne fait pas mieux que détenir SPY sur la même fenêtre.

**Écart entre le script et le carnet** : les deux partent des mêmes 30 titres et de la même fenêtre, mais le carnet s'écarte de `Main.cs` sur plusieurs points que le script suit désormais :

| Point | Carnet | Script et `Main.cs` |
|-------|--------|---------------------|
| Momentum | rendement 90 jours annualisé, seuil 0 | régression du log-prix sur 90 séances, pente annualisée × R², seuil 10 |
| Moyenne de tendance | SMA(150) | EMA(150) |
| Gap | ouverture contre clôture de la veille | clôture contre clôture précédente |
| Classement | filtre puis top 20 | top 20 par pente, puis filtre |
| Moment de l'ordre | signal et exécution à la clôture du même jeudi | indicateurs de la veille, ordre à l'ouverture du jeudi (`Main.cs` : 1 minute après l'ouverture) |
| Liste filtrée vide | les positions sont gardées | toute ligne absente de la liste est vendue (`Main.cs`, boucle de vente) |
| Régime pendant l'échauffement | SMA(200) non calculée comptée Risk-OFF (2015-01-02 → 2015-10-21) | SMA(200) préchauffée sur 2014, aucun jour sans SMA dans la fenêtre |

L'effet de chacun de ces points sur l'écart de Sharpe (1,106 contre 0,727) n'a pas été mesuré séparément.

**Écart avec le backtest C#** : aucun des deux proxys ne retrouve le backtest C#. Le chiffre « 2021-Now : 0,507 » comparé ici auparavant venait d'un backtest à fenêtre glissante qui n'était pas identifié ; il est retiré. Trois différences de construction restent entre le script et `Main.cs`, sans avoir été mesurées séparément :

- la liste fixe de 30 titres du proxy a été choisie en 2026 et contient dès 2015 des titres devenus de grandes capitalisations depuis (biais de sélection probable), quand le backtest C# lit l'univers OEF ;
- le proxy ne reproduit pas le réajustement bimensuel des tailles de position de `Main.cs` ;
- le proxy ne compte aucun frais ni glissement.

Le proxy tient en moyenne 1,9 position (au plus 3) : avec la règle de taille de `Main.cs` (1 % du capital divisé par l'ATR), une ligne pèse une large part du capital. Le nombre de lignes du backtest C# n'est pas relevé ici.

Les frais IB du backtest C# pèsent environ 2,5 % du capital initial sur onze ans : ils n'expliquent pas l'écart à eux seuls. Identifiants des backtests et sous-périodes : section « Retest QC500 » du README.

**Mesures du carnet `research_robustness.ipynb`** : ré-exécuté sur la fenêtre figée (données yfinance du 2015-01-02 au 2025-12-31 ; la série de rendements du proxy court du 2015-01-08 au 2025-12-18, bornes effectives imprimées par le carnet), il donne : CAGR 25,33 %, Sharpe 1,106, drawdown max 29,93 %, 1,9 position en moyenne ; 12 semestres positifs sur 18 (2017-2025), Sharpe moyen par semestre 0,86. Les tableaux des sections suivantes viennent du script (`research_results.txt`), pas du carnet.

---

## Analyse du SMA(200) Regime Filter

### Temps passé en Risk-ON vs Risk-OFF

Mesuré par le script à la clôture, SMA(200) préchauffée sur 2014 (aucun jour de la fenêtre sans SMA) :

- **Risk-ON (SPY > SMA200)**: 2275 jours (82,2 %)
- **Risk-OFF (SPY < SMA200)**: 491 jours (17,8 %)
- **Transitions**: 60 sur 11 ans (2015 : 9, 2016 : 3, 2017 : 0, 2018 : 9, 2019 : 5, 2020 : 6, 2021 : 0, 2022 : 15, 2023 : 9, 2024 : 0, 2025 : 4)

### Périodes Risk-OFF d'au moins 10 séances

| Période | Durée | Variation SPY (premier → dernier jour) | Contexte |
|---------|-------|----------------------------------------|----------|
| 2015-08-20 → 2015-10-21 | 44 séances | -0,5 % | Baisse d'août 2015 |
| 2015-12-31 → 2016-03-10 | 48 séances | -2,1 % | China fears, oil crash |
| 2018-10-23 → 2018-11-05 | 10 séances | -0,1 % | Correction Q4 2018 |
| 2018-11-12 → 2019-02-01 | 52 séances | -0,3 % | Fin correction 2018 |
| **2020-02-27 → 2020-05-22** | **59 séances** | **-0,1 %** | **COVID Crash** |
| 2022-02-11 → 2022-03-17 | 22 séances | +0,1 % | Début bear 2022 |
| **2022-04-11 → 2022-11-29** | **160 séances** | **-9,4 %** | **Inflation Bear Market** |
| 2022-12-05 → 2023-01-10 | 24 séances | -1,8 % | Fin bear 2022 |
| 2025-03-10 → 2025-05-09 | 42 séances | +1,0 % | Turbulence récente |

La période 2015-01-02 → 2015-10-21 que listait l'ancienne version (203 jours) venait de l'échauffement de la SMA(200) : faute de valeur, les premiers mois étaient comptés Risk-OFF. Avec l'échauffement sur 2014, seule la baisse d'août 2015 reste.

**Lecture** : le filtre passe en Risk-OFF pendant la chute de 2020 et pendant la baisse de 2022. Dans `Main.cs`, il ne fait que bloquer les achats : les ventes viennent de la liste filtrée, quel que soit le régime. L'effet sur le résultat se lit dans les semestres correspondants, section suivante.

---

## Stabilité par semestre (22 semestres, backtest unique)

Le backtest unique est découpé en semestres ; aucun paramètre n'est ré-estimé d'un semestre à l'autre : c'est une mesure de stabilité dans le temps, pas une validation walk-forward.

| Semestre | Stratégie | SPY | Écart | Sharpe |
|----------|-----------|-----|-------|--------|
| 2015-01 → 2015-07 | +4,05 % | +3,83 % | +0,22 | 0,647 |
| 2015-07 → 2016-01 | +12,67 % | -1,77 % | +14,44 | 1,515 |
| 2016-01 → 2016-07 | -20,66 % | +3,82 % | -24,48 | -2,150 |
| 2016-07 → 2017-01 | +8,25 % | +8,27 % | -0,02 | 0,971 |
| 2017-01 → 2017-07 | +14,74 % | +8,57 % | +6,17 | 1,360 |
| 2017-07 → 2018-01 | +15,07 % | +12,11 % | +2,96 | 1,338 |
| 2018-01 → 2018-07 | +25,59 % | +1,99 % | +23,60 | 1,994 |
| 2018-07 → 2019-01 | -9,43 % | -7,47 % | -1,96 | -0,741 |
| 2019-01 → 2019-07 | +15,42 % | +18,60 % | -3,18 | 2,697 |
| 2019-07 → 2020-01 | +15,69 % | +11,84 % | +3,84 | 2,417 |
| **2020-01 → 2020-07** | **-10,19 %** | **-3,85 %** | **-6,34** | -0,441 |
| 2020-07 → 2021-01 | +16,56 % | +22,65 % | -6,09 | 1,243 |
| 2021-01 → 2021-07 | +15,22 % | +14,45 % | +0,77 | 1,645 |
| 2021-07 → 2022-01 | +18,87 % | +12,76 % | +6,11 | 1,726 |
| **2022-01 → 2022-07** | **-15,82 %** | **-20,18 %** | **+4,37** | -1,087 |
| 2022-07 → 2023-01 | -1,37 % | +2,53 % | -3,89 | -0,498 |
| 2023-01 → 2023-07 | +39,82 % | +15,12 % | +24,70 | 3,623 |
| 2023-07 → 2024-01 | +3,58 % | +9,63 % | -6,05 | 0,420 |
| 2024-01 → 2024-07 | +7,19 % | +15,34 % | -8,15 | 0,945 |
| 2024-07 → 2025-01 | +3,17 % | +10,77 % | -7,60 | 0,450 |
| 2025-01 → 2025-07 | -7,65 % | +2,36 % | -10,01 | -1,053 |
| 2025-07 → 2026-01 | +12,00 % | +10,86 % | +1,13 | 1,430 |

L'écart est en points de pourcentage ; le semestre 2025-07 → 2026-01 s'arrête au dernier jeudi de la fenêtre (2025-12-18).

### Synthèse par semestre

- **Semestres positifs**: 16 / 22
- **Semestres au-dessus de SPY**: 11 / 22
- **Écart moyen à SPY**: +0,48 point
- **Pire semestre**: 2016-01 → 2016-07 (-20,66 %, SPY +3,82 %)
- **Meilleur semestre**: 2023-01 → 2023-07 (+39,82 %)

**Lecture** : la stratégie fait mieux que SPY sur la moitié des semestres. Les écarts sont larges dans les deux sens (de -24,48 à +24,70 points), et leur moyenne est proche de zéro.

---

## Réponses aux Questions de Recherche

### 1. Protection SMA(200) durant corrections?

**Résultat partagé**, mesuré par le script :
- COVID 2020 (2020-01 → 2020-07) : stratégie -10,19 % contre SPY -3,85 %, donc en dessous de SPY ; pire baisse dans le semestre 25,94 % contre 28,64 % pour SPY. Cette baisse est aussi la pire de toute la fenêtre.
- Baisse 2022 (2022-01 → 2022-07) : stratégie -15,82 % contre SPY -20,18 %, au-dessus de SPY ; pire baisse dans le semestre 15,75 % contre 21,40 %.
- Correction 2018 (2018-07 → 2019-01) : stratégie -9,43 % contre SPY -7,47 %.

### 2. Stabilité momentum en régimes variés?

**Instable d'un semestre à l'autre** : 16 semestres positifs sur 22, 11 au-dessus de SPY, écart moyen +0,48 point. Le pire semestre (2016-01 → 2016-07, -20,66 %) tombe pendant une hausse de SPY ; le meilleur (2023-01 → 2023-07, +39,82 %) pendant la reprise de 2023.

### 3. Utilité du filtre gap 15%?

**Non mesurée** : sur 11 140 titres classés dans le top 20 au fil des 557 jeudis, le filtre gap en écarte 363, après la pente (4123) et l'EMA(150) (307). Son effet sur le résultat demanderait un second backtest sans le filtre, que le script ne fait pas.

### 4. Stabilité du backtest C# d'une sous-période à l'autre?

| Backtest C# QC Cloud, univers OEF | 2015-2019 | 2020-2025 | 2015-2025 | Proxy 2015-2025 (carnet) |
|-----------------------------------|-----------|-----------|-----------|--------------------------|
| Sharpe | 0,476 | 0,445 | 0,438 | 1,106 |
| CAGR | 12,9 % | 15,8 % | 14,0 % | 25,33 % |
| MaxDD | 33,9 % | 42,4 % | 42,4 % | 29,93 % |

Chaque sous-période repart du capital initial, avec des indicateurs préchauffés sur 200 jours avant la date de début (`SetWarmUp(200)`).

**Lecture** : le Sharpe du backtest C# est stable d'une sous-période à l'autre (0,476 puis 0,445). C'est son niveau qui s'écarte du proxy, pas sa stabilité. Le drawdown de 42,4 % tombe dans la seconde sous-période.

---

## Conclusions et Recommandations

### 1. Bugfix SMA(10)→SMA(200)

`Main.cs` utilise `SMA("SPY", 200)`. Sur le proxy, ce filtre est en Risk-ON 82,2 % du temps, avec 60 transitions en onze ans. Le script ne mesure pas la version SMA(10) : la comparaison des deux filtres reste à faire.

### 2. Extension de période

**Fait : fenêtre 2015-01-01 → 2025-12-31** (#22541)

**Raisons**:
1. Couvre plusieurs régimes de marché (hausse 2015-2017, corrections 2018 et 2020, baisse 2022, reprise 2023-2025)
2. Sharpe du backtest C# stable sur les deux sous-périodes (0,476 puis 0,445)

### 3. Paramètres actuels

Les paramètres de `Main.cs` (SMA 200, pente sur 90 séances, gap 15 %, risque 1 %) n'ont pas été optimisés par ce travail, et leur sensibilité n'est pas mesurée par le script. Le carnet mesure seulement l'effet de la période de la SMA sur le temps passé en Risk-ON et le nombre de transitions.

### 4. Prochaines étapes

1. ~~Modifier `Main.cs`~~ : fait, fenêtre figée 2015-01-01 → 2025-12-31, bornes en paramètres QC (#22541)
2. ~~Compiler et backtester sur QC Cloud~~ : fait, identifiants dans le README
3. **Critères mesurés** sur le backtest C# univers OEF, fenêtre figée :
   - Sharpe >= 0.4 : **atteint** (0,438) ; la fourchette attendue 0,8-1,2 n'est **pas** atteinte
   - Max DD < 35 % : **non atteint** (42,4 %)
   - CAGR >= 15 % : **non atteint** (14,0 %)
4. **Validation non acquise** (deux critères sur trois manqués) : la condition « si validation OK » de l'étape suivante n'est pas remplie
5. Piste : mesurer séparément l'effet de la liste de 30 titres et de la concentration du proxy, pour savoir laquelle porte l'écart de Sharpe avec le backtest C#
6. Piste : aligner le carnet sur les points du tableau « Écart entre le script et le carnet », ou mesurer l'effet de chacun

---

## Limites de cette Recherche

### Univers proxy contre univers OEF

- **Proxy**: 30 large caps multisectoriels, choisis aujourd'hui
- **OEF**: S&P 100 constituants (~100 stocks), composition de chaque date
- **Impact**: biais de survie probable sur le proxy ; ses chiffres absolus ne valent pas pour la stratégie C#

### Simplifications du script

1. **Indicateurs**: ceux des classes C# du projet (pente exponentielle × R², EMA(150), gap clôture à clôture, ATR de Wilder), recalculés sur les données yfinance
2. **Frais**: Non inclus dans backtest Python
3. **Slippage**: Non modélisé
4. **Tailles**: pas de réajustement bimensuel des tailles de position
5. **Rebalancing**: Jeudis à l'ouverture, indicateurs de la clôture de la veille (le code C# passe ses ordres 1 minute après l'ouverture du jeudi)

**Conclusion**: Le backtest QC Cloud sur la fenêtre figée (#22541) donne un Sharpe de 0,438 et une pire baisse de 42,4 %. Le script proxy, plus fidèle aux indicateurs C# que le carnet, donne un Sharpe de 0,727 sans frais, en dessous de celui de SPY sur la même fenêtre (0,876) : ni le proxy ni le backtest C# ne montrent un avantage de la stratégie sur la détention de SPY.

---

## Fichiers Générés

- `research_robustness_simple.py`: Script Python standalone (yfinance), indicateurs des classes C#, fenêtre figée 2015-2025
- `research_results.txt`: Output complet du backtest
- `RESEARCH_SUMMARY.md`: Ce document
- `research_robustness.ipynb`: Notebook Jupyter exécuté (yfinance, données 2015-01-02 → 2025-12-31, série du proxy 2015-01-08 → 2025-12-18)

---

**Auteur**: Claude Code Agent (qc-research-notebook)
**Date**: 2026-02-17
**Projet**: partner-course-quant-trading/examples/CSharp-CTG-Momentum
