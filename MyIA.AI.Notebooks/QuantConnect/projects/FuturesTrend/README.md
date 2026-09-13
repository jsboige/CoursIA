# FuturesTrend (Multi-Asset Trend Following v3.1)

Stratégie de **suivi de tendance multi-actifs** sur 6 ETF diversifiés (SPY, GLD, EFA, VNQ, DBC, XLE), basée sur un breakout Donchian filtré par tendance. Malgré son nom historique, l'algorithme courant (`main.py`, classe `FuturesTrendFollowing`) trade des **ETF actions/matières premières** — non des contrats futures.

## Résumé

| Paramètre | Valeur |
|-----------|--------|
| **Instrument** | 6 ETF (SPY, GLD, EFA, VNQ, DBC, XLE) |
| **Univers** | Actions US, or, intl, immobilier, matières, énergie |
| **Signal** | Breakout Donchian (20j) + filtre tendance SMA50 |
| **Entry** | Clôture > Max(High, 20 jours) ET prix > SMA50 |
| **Exit** | Clôture < Min(Low, 10 jours) |
| **Position Sizing** | 33 % de poids fixe par position |
| **Max positions** | 3 (concentrées sur les meilleures dynamiques) |
| **Benchmark** | SPY |

## Métriques de backtest (2015-2024)

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | 0.07 |
| CAGR | 4.170% |
| Max Drawdown | 15.500% |
| Net Profit | 60.618% |
| Total Orders | 463 |
| Probabilistic Sharpe Ratio | 0.007% |

> **Provenance** : backtest QC Cloud `b869c19d1320401e3c3a84ae7037abc4` (2026-08-05),
> projet 28657834, IBKR margin, 2913 jours tradeables (2015-2024), $100k initial.
> Re-exécuter via QC Cloud ou `lean backtest` pour recalculer.
>
> **Lecture honnête** : un Sharpe de 0,07 avec PSR 0,007 % est un **edge statistiquement
> nul** — la stratégie ne bat pas de façon fiable le buy-and-hold de SPY. La docstring du
> `main.py` épingle v3.1 = Sharpe 0,301 / CAGR 8,0 %, mesurés sur une fenêtre plus étroite
> (antérieure à l'extension 2015-2024) ; sur la période complète, l'edge de trend-following
> s'érode (0,301 → 0,07). C'est un contre-exemple pédagogique : une logique de suivi de
> tendance séduisante en sample ne conserve pas son edge hors-échantillon. Les valeurs
> `~0.5-0.8` auparavant inscrites en prose ici étaient **surévaluées** (de ~5-10x).

## Fichiers

- `main.py` - Stratégie `FuturesTrendFollowing` v3.1 (breakout Donchian + filtre SMA50)
- `research.ipynb` - Analyse des tendances, optimisation des paramètres
- `quantbook.ipynb` - Notebook de recherche QuantConnect

## Logique

### Entry
- **Long** : sur les ETF en **tendance haussière** (prix > SMA50) dont la clôture casse le **Max(High, 20 jours)** (breakout Donchian).
- Les candidats sont triés par momentum (prix / entry_high) ; seuls les **3 meilleurs** entrent (concentration sur les tendances les plus fortes).

### Exit
- **Long exit** : clôture < **Min(Low, 10 jours)** (canal Donchian de sortie).

### Position Sizing
- **Poids fixe de 33 %** par position (`set_holdings(symbol, 0.33)`), jusqu'à **3 positions** simultanées (99 % max investis). Pas de sizing par risque/ATR (testé en v4.0, régressif — coupait les gagnants trop tôt).

## Configuration

```python
self.entry_period = 20      # Canal Donchian d'entrée (high breakout)
self.exit_period = 10       # Canal Donchian de sortie (low breakdown)
self.trend_sma_period = 50  # Filtre de tendance long-terme
self.weight = 0.33          # Poids fixe par position
self.max_positions = 3      # Concentration maximale
```

## Risques

- **Whipsaws** : faux signaux en marchés range-bound (le breakout Donchian génère de nombreuses petites pertes en consolidation).
- **Low Win Rate** : beaucoup de petites pertes, peu de grosses tendances gagnantes (profil asymétrique du trend-following).
- **Drawdown** : 15,5 % observés sur 2015-2024 (le filtre SMA50 les atténue sans les éliminer).
- **Regime dependency** : l'edge s'érode hors des régimes de tendance forte (cf. écart 0,301 → 0,07 entre fenêtre étroite et période complète).

## Améliorations possibles

- Filtre de volatilité (ATR) pour réduire les whipsaws.
- Trailing stop (testé en v4.0 = régressif, à reprendre différemment).
- Pyramiding (ajouter sur confirmation de tendance).
- Dynamisation de l'univers (rotation sectorielle).

## Variante Carver #13 (portage substantiel — issue #15549)

Le fichier `main_carver13.py` (classe `CarverThirteen`) est un **portage local** de la
stratégie n° 13 de Robert Carver (*Advanced Futures Trading Strategies*, Harriman House
2023, ISBN 9780857199683), telle que recréée dans l'article QuantConnect
*Futures Trend Following and Carry in Different Risk Regimes* (#15989, Derek Melchin,
2026-01-02). Cette variante coexiste avec `main.py` v3.1 sans le modifier — v3.1
reste la **baseline ETF** à laquelle Carver #13 sera comparé.

**QC Cloud n'exécute que `main.py`** — comportement documenté de la plateforme
(documentation QuantConnect, section *Project Structure*,
<https://www.quantconnect.com/docs/v2>), et **constaté firsthand** ce cycle : le
projet dédié 36488678, dont `main.py` porte le code Carver, a produit un run sur la
fenêtre Carver (2763 séances, 2016-2026) tandis que `breadth_multiplier.py`, présent
dans le même projet, n'en était pas le point d'entrée. Un portage posé à côté sous un
autre nom n'est donc **jamais** exécuté. Mesurer la jambe Carver #13 impose un
**projet QC séparé** portant le portage en `main.py` — ce qui a été fait
(`FuturesTrend-Carver13`, 36488678) précisément pour ne pas écraser le point d'entrée
de la baseline, c'est-à-dire l'un des deux bras de la comparaison.

**Précision sur une observation antérieure de ce dossier** : l'énumération « 17
backtests, aucun Carver » dans le projet 28657834 n'est **pas** une preuve de cette
règle — vérifié ce cycle, `main_carver13.py` n'a **jamais été uploadé** dans ce projet
(fichiers présents : `main.py`, `research.ipynb`, `quantbook.ipynb`), donc l'absence
de run Carver y est triviale et ne dit rien des points d'entrée. La règle repose sur
la doc plateforme et le constat positif ci-dessus, pas sur cette énumération. Voir
« Résultat mesuré de la comparaison » ci-dessous.

| Composant | v3.1 (ETF, baseline) | Carver #13 (c.1109) |
|-----------|----------------------|---------------------|
| Univers | 6 ETF (SPY/GLD/EFA/VNQ/DBC/XLE) | 19 futures continus (ES/NQ/YM/ZN/ZB/ZF/6E/6B/6J/CL/NG/RB/GC/SI/HG/ZC/ZW/ZS/SB) |
| Signal entrée | Donchian 20j + filtre SMA50 | 6 horizons EWMAC (Carver pairs 8/32, 16/64, 32/128, 64/256, 16/48, 32/96) avec scalaire per-horizon `sqrt(slow/32)` (c.1063 increment) |
| Carry factor | absent | **désactivé** (voir note ci-dessous ; c.1107 + c.1109) |
| Multiplicateur régime | absent | vol-régime borné [0.5, 2] |
| FDM (Forecast Diversification Multiplier) | absent | **requalifié honnêtement** en *breadth multiplier* sign-invariant (effective breadth of absolute magnitudes / INVERSE concentration), clip [1, 2] (c.1109 REPAIR-3 + c.1111 REPAIR-5 + c.1113 REPAIR-7, voir note) |
| Cap forecasts | n/a | +/-20 par forecast |
| Position sizing | fixe 33% par position (max 3) | vol-scaled, sign-normalisé, retarget du **delta** (pas d'aller-retour fabriqué, c.1109) |
| Fenêtre de backtest | 2015-2024 | 2016-2026 (acceptance #15549) |
| **Backtest mesuré (2026-09-13)** | **Sharpe 0,07 / CAGR 4,170 % / MaxDD 15,500 % / PSR 0,007 % / 463 ordres / 2913 séances** | **0 ordre — Sharpe/CAGR/MaxDD/PSR n/a (indéfinis : aucune série de rendements) / $0,00 / 2763 séances** |

### Résultat mesuré de la comparaison (2026-09-13, acceptance #15549)

Les deux bras ont été mesurés dans QC Cloud. La baseline est relue **firsthand**
(backtest `b869c19d1320401e3c3a84ae7037abc4`, projet 28657834) et non reprise de la
prose. La jambe Carver #13 a été **exécutée pour la première fois** : projet QC dédié
`FuturesTrend-Carver13` (36488678, créé pour ne pas écraser le point d'entrée de la
baseline), compile `BuildSuccess` 0 erreur, backtest
`b7b7217ee540757f3d78167ab9eeea2e`.

**Provenance exacte du bras baseline, champ par champ** (payload `read_backtest`
relecture du 2026-09-13 ; run « FuturesTrend v3.1 real metrics 2015-2024 », créé
2026-08-05) : `sharpeRatio: "0.07"`, `compoundingAnnualReturn: "4.170%"`,
`drawdown: "15.500%"`, `totalNetProfit: "60.618%"`,
`probabilisticSharpeRatio: "0.007%"`, `netProfitAbsolute: "$61,146.46"`,
`tradeableDates: 2913`, `totalOrders: 463`. Fenêtre du code (`main.py`) :
2015-01-01 → 2024-12-31, capital initial $100 000.

**Non-réconciliation arithmétique de ce payload, portée sans masquage** :
$61 146,46 / $100 000 = **+61,146 %**, alors que le même run rapporte
`totalNetProfit: "60.618%"` ; et 1,0417^10 = 1,504 → **+50,4 %** sur la fenêtre de
10,0 ans, incompatible avec +60,618 %. La base du champ pourcent de QC n'est pas
documentée dans le payload. Les valeurs de ce README sont une **transcription exacte
du payload, champ par champ** — pas des valeurs recalculées — afin que tout lecteur
puisse refaire l'arithmétique et trancher lui-même.

| Métrique | Baseline ETF v3.1 (2015-2024) | Carver #13 (2016-2026) |
|---|---|---|
| Sharpe | 0,07 | **n/a** |
| CAGR | 4,170 % | **n/a** |
| Max drawdown | 15,500 % | **n/a** |
| PSR | 0,007 % | **n/a** |
| Net profit | +60,618 % ($61 146,46) | **$0,00** |
| Ordres | 463 | **0** |
| Séances négociables | 2913 | 2763 |

**Sur les `n/a` de la colonne Carver** : pour un run à 0 ordre, Sharpe / CAGR / MaxDD /
PSR sont **indéfinis** — il n'existe aucune série de rendements, et le « 0 » affiché
par le payload QC est une valeur par défaut, pas une mesure. Les zéros réellement
mesurés sont : **0 ordre**, **$0,00** de profit, **2763 séances** négociables, compile
0 erreur. Écrire « Sharpe 0 » dans les mêmes cases numériques que la baseline
inviterait précisément la lecture « Carver sous-performe » que le verdict interdit.

**Verdict : `INCONCLUSIVE` — et le motif n'est pas une faiblesse d'edge.** La jambe
Carver #13 n'émet **aucun ordre** sur 2763 séances : elle ne perd pas contre la
baseline, elle ne trade pas du tout. Un bras à 0 ordre ne peut ni battre ni perdre.
C'est une **non-fonctionnalité**, pas une mesure d'edge : la conclusion scientifique
`BEATS` / `NO BEATS` est **indécidable en l'état**, et l'accepter comme « Carver sous-
performe » serait exactement l'erreur que l'acceptance interdit.

**Ce résultat reproduit une observation antérieure** (préflight adjoint po-2025 :
« 0 orders + Sharpe 0 / 2762 dates ») — il la corrobore désormais par une exécution
indépendante et datée, avec le backtestId à l'appui.

**Caveat de fenêtre, non effacé** : la baseline est mesurée sur 2015-2024 et la jambe
Carver sur 2016-2026 (dates fixées en dur dans chaque `initialize()`). Les deux
colonnes ne sont donc pas alignées à la séance près ; l'écart est porté ici plutôt
que suppose neutre. Il est **secondaire** devant le fait mesuré (0 ordre), qui rend
la comparaison sans objet.

**Ce qui reste ouvert** : la cause du 0 ordre. Un instrument d'instrumentation
existe déjà dans le code (`_rebalance_early_returns`, REPAIR-9 c.1117 : `warming_up`,
`bulk_empty`, `no_raw_forecasts`, `abs_sum_zero`, `completed_no_order`,
`completed_with_orders`) et est journalisé en fin d'algorithme — mais le wrapper
`qc-mcp-lite` ne rend **pas** les runtime logs (`self.log`), donc la branche réellement
empruntée n'est pas lisible par ce canal. Diagnostic suivant : rejouer avec
`self.error(...)` sur le compteur (surfacé dans le champ `error`), ou lire l'onglet
Logs de l'UI QC.

**Correction d'une affirmation fausse de ce dépôt.** Le `config.json` et cette section
présentaient le portage comme reconnu par QC Cloud « sans modifier la baseline » :
c'est **faux** — QC n'exécute que `main.py` (doc plateforme + constat firsthand sur
36488678, détail en tête de section). Mesurer la jambe Carver impose soit un
projet dédié (ce qui a été fait), soit d'écraser `main.py` — donc de détruire le point
d'entrée de la baseline, c'est-à-dire l'un des deux bras de la comparaison. Le
précédent inversé était faux avec la même force d'affirmation et sans source nommée ;
cette correction cite les siennes.

### Note Tell c.1069 strict — Carry désactivé sur cette implémentation (c.1107)

Le carry proxy front-only initialement livré (c.1106) réduisait à la pente
`EWMA(8,32)` sur la même série de closes — formule bit-identique au signal
`EWMAC(8,32)` déjà inclus dans la moyenne des 6 horizons EWMAC. Le blend 60/40
trend+carry était donc un forecast 100% trend avec un coefficient 0.4 sur un
signal dupliqué. Pour éviter de livrer une stratégie qui se présente à tort
comme un blend trend+carry, l'implémentation c.1107 fait **trend-only** :
`_carry_forecast(front, deferred)` reste défini comme stub utilisable mais
n'est plus appelé depuis `_rebalance` ; le forecast est `trend_component` pur
(moyenne des 6 EWMAC, capée à +/-20).

Le carry **proprement dit** (rapport front/deferred via l'API `Future` chain)
est documenté comme follow-up de l'acceptance #15549 : il demande la
disponibilité de la chain API (présent en QC Cloud, pas en local sans
credentials). La méthode `_carry_forecast(front_close, deferred_close)`
reste l'interface prévue — l'appelant futur (lane QC équipée) n'a qu'à passer
les deux closes réelles.

### Note Tell c.1069 strict — FDM requalifié en breadth multiplier (c.1109 REPAIR-3 + c.1111 REPAIR-5)

Le préflight adjoint po-2025 (`msg-20260911T043805-i7tl0g` pour c.1109,
puis `msg-20260911T053342-rwwap4`) a détecté deux défauts sémantiques
successifs sur la formule livrée c.1107 (`sum(|f|)/sqrt(sum(f^2))`
clip `[1, 2]`) :

**c.1109 REPAIR-3 — formule n'est PAS une pénalité de concentration.**
La formule instantanée ne peut pas pénaliser la concentration sans
estimateur de corrélation exogène : le ratio monte (≥1) quand les
signaux s'alignent, et monte aussi quand ils sont indépendants — c'est
l'inverse de l'intention Carver. `_fdm` est renommé `_breadth_multiplier`.

**c.1111 REPAIR-5 — formule est sign-invariant.** L'adjoint a observé
que `abs(float(f))` efface les signes, donc `[10,10]` et `[10,-10]`
rendent **le même** `breadth = sqrt(2)`. La métrique mesure donc
strictement la **largeur effective des magnitudes absolues** (effective
breadth of absolute magnitudes), pas l'alignement directionnel, ni le
book unidirectionnel, ni une pénalité Carver-true. La prose antérieure
qui disait « bonus quand le book est unidirectionnel / aligned »
(REPAIR-3 c.1109) ou « sign-invariant magnitude concentration »
(REPAIR-5 c.1111) avait tort sur ce point : `|f|` retire le signe à
l'entrée, le multiplier est par construction sign-invariant. Le signe
des forecasts est préservé séparément, en aval, par le ratio
`forecast / abs_sum` dans `_rebalance`.

**c.1113 REPAIR-7 — formule mesure une largeur effective, pas une
concentration** (correction sémantique par adjoint po-2025 habilité
n°3 Tell c.15069 strict). Le ratio `sum(|f|)/sqrt(sum(f^2))` range de
**1.0** (une magnitude domine, le reste à 0 — concentration MAXIMUM)
à **sqrt(N)** (toutes les magnitudes égales — concentration ZÉRO) :
c'est l'**inverse** d'une mesure de concentration. Appeler cela «
magnitude concentration » dans les itérations précédentes inversait
la sémantique. La formule mesure une **largeur effective des magnitudes
absolues** (effective breadth of absolute magnitudes, INVERSE
concentration).

**REPAIR-5 c.1111** (Tell c.1069 strict honnêteté référentielle, par
adjoint po-2025 habilité n°3 urne `delivered` Tell c.15069 strict) :
- Docstring `_breadth_multiplier` reformulée « sign-invariant effective
  breadth of absolute magnitudes » ; retrait des claims « one-directional
  / aligned » et « magnitude concentration » ; précision que seul le
  multiplier est sign-invariant, le poids final préserve le signe.
- Clip `[1, 2]` décrit comme « soft cap on gross leverage » (lorsqu'une
  magnitude domine, leverage capé à 1x ; lorsque les magnitudes sont
  étalées, leverage amplifié jusqu'à 2x).
- `config.json` corrigé : « Carver FDM with corrected clip [1,2] » →
  « breadth multiplier clip [1, 2] — sign-invariant effective breadth of
  absolute magnitudes / INVERSE concentration, NOT Carver FDM,
  REPAIR-3 c.1109 + REPAIR-5 c.1111 + REPAIR-7 c.1113 ».
- Module docstring mis à jour (NOT a Carver FDM, NOT a directional-
  alignment proxy, NOT a concentration measure).

**REPAIR-6 c.1111 (worker)** : cohérence README ↔ source REPAIR-5 —
le présent paragraphe remplace la note « REPAIR-3 c.1109 seule » qui
disait encore « bonus quand le book est unidirectionnel », et la section
« Statut courant » est étendue avec REPAIR-5 c.1111.

**REPAIR-7 c.1113 (worker)** : cohérence sémantique « effective breadth /
inverse concentration » + test CPU exécutable
`tests/test_breadth_multiplier.py` protégeant le caractère sign-invariant
(4 cas : `[10,10] == [10,-10]`, `[10,0]` clipé à 1, 4 magnitudes égales
clipées à 2, exécution locale sans QC Cloud). Le caractère
sign-invariant n'est plus seulement documenté, il est **protégé par
un test**. Préflight adjoint habilité n°3
`msg-20260911T063424-qnc0q9`.

**Règle d'or** : `_breadth_multiplier` répond à « quelle est la largeur
effective des magnitudes absolues ? » (= inverse concentration), **pas**
à « les magnitudes sont-elles concentrées ? », ni à « les forecasts
sont-ils alignés ? » ni à « le book est-il unidirectionnel ? ». Pour
ces dernières questions, il faut un estimateur signé exogène (moyenne
signée, dispersion signée, corrélation rolling) qui n'est pas dans
cette formule. Le Carver FDM au sens propre (estimateur
signed-correlation rolling) reste une dette de fond (#15549 acceptance
follow-up).

### Note Tell c.1069 strict — Retarget delta direct, pas d'aller-retour fabriqué (c.1109 REPAIR-3)

Le préflight adjoint a aussi détecté que `_rebalance` liquidait toutes
les positions investies avant `set_holdings`, ce qui **fabrique** un
aller-retour (1 liquidate + 1 set_holdings = double commission) même
quand la cible est proche de la position actuelle.

**REPAIR-3 c.1109** :
- Liquidation uniquement sur **changement de signe** (long → short ou
  inverse) ou **cible ~ 0**.
- `set_holdings(sym, target_weight)` est idempotent côté broker
  (ajustement à la cible absolue, pas de commission synthétique sur la
  jambe existante quand le signe est conservé).
- Les coûts backtestés deviennent comparables à un rebalancement réel.

### Statut courant (c.1111, lane `myia-po-2027:CoursIA-2` ; mis à jour 2026-09-13, lane `myia-po-2026:CoursIA`)

- Le code **compile statiquement** (`ast.parse` PASS, 7 fonctions / 1 classe / 465

  lignes, EOL LF, 0 secret literal).
- **Backtest exécuté le 2026-09-13** (supersède l'état « Aucun backtest exécuté » de

  la lane po-2027, dont le verdict `RECOVERABLE-MACHINE` — credentials QC absents,
  vérifié firsthand `env | grep -iE "QC_|QUANTCONNECT"` = 0 hit — est désormais
  **résolu** : la jambe QC Cloud a été portée par la lane `myia-po-2026:CoursIA`,
  **sans transmission de secret**, sur un projet QC dédié). Résultat : compile
  `BuildSuccess` 0 erreur, backtest `b7b7217ee540757f3d78167ab9eeea2e` `Completed`,
  2763 séances négociables, **0 ordre**. Détail et comparaison au bras baseline :
  section « Résultat mesuré de la comparaison » ci-dessus.
- **Verdict rendu** : `INCONCLUSIVE` — **non pas** parce que Carver #13 perdrait

  contre la baseline, mais parce que la jambe n'émet **aucun ordre** (0 ordre /
  2763 séances) : un bras qui ne trade pas ne peut ni battre ni perdre. La
  comparaison scientifique reste **indécidable** tant que la cause du 0 ordre n'est
  pas dissipée. Le Sharpe 0,944 vs 0,749 rapporté par l'article #15989 sur 2020-2023
  n'a **pas** été présumé : il n'entre pas dans ce verdict (fenêtre favorable
  non-représentative, et la jambe mesurée ici est muette de toute façon).
- **REPAIR c.1107** : deux défauts détectés par le préflight adjoint po-2025

  (`msg-20260911T040615-4c08xy`) avant lancement des runs QC Cloud — (a) carry
  proxy identique à EWMAC(8,32), (b) FDM clip à l'inverse de la docstring.
- **c.1063 increment** : scalaire per-horizon `sqrt(slow/32)`, warmup 2x cohérent,

  history bulk 1 call. Détails dans le commit `e41a4eb8d632`.
- **REPAIR-3 c.1109** : FDM requalifié en breadth multiplier (Tell c.1069 strict

  honnêteté référentielle) + retarget delta direct (pas d'aller-retour fabriqué).
  Préflight adjoint po-2025 `msg-20260911T043805-i7tl0g` ; jambe QC po-2026
  suspendue jusqu'au nouveau head exact.
- **REPAIR-5 c.1111** : docstring `_breadth_multiplier` sign-invariant magnitude

  concentration (Tell c.1069 strict honnêteté référentielle — l'`abs()` efface les
  signes, `[10,10] == [10,-10]`) + `config.json` Carver FDM stale → breadth
  multiplier sign-invariant. Préflight adjoint po-2025
  `msg-20260911T053342-rwwap4` ; adjoint habilité n°3 urne `delivered`
  Tell c.15069 strict a pushé le commit `5c316080f10f`. QC demeurait suspendu
  jusqu'à cette dissipation par le worker (REPAIR-6 c.1111 = cohérence prose
  README ↔ source).
- **REPAIR-6 c.1111 (worker)** : cohérence README ↔ source REPAIR-5 — section

  « Note Tell c.1069 strict — FDM requalifié » étendue avec le défaut sign-invariant
  (la prose c.1109 disait « bonus quand le book est unidirectionnel », faux) +
  statut courant étendu avec REPAIR-5. Amend borné scope unique
  `FuturesTrend/README.md`. Push `--force-with-lease=refs/heads/feature/15549-carver13-futures:5c316080f10ffcf0dd011a4da1a7ce77dad20277`.
- **REPAIR-7 c.1113 (worker)** : correction sémantique « effective breadth /

  inverse concentration » (Tell c.1069 strict honnêteté référentielle, par
  préflight adjoint po-2025 habilité n°3 urne `delivered` Tell c.15069 strict,
  `msg-20260911T063424-qnc0q9`) — la formule `sum(|f|)/sqrt(sum(f^2))` mesure
  une largeur effective (1 = concentré, sqrt(N) = étalé), pas une concentration.
  Source `main_carver13.py` docstring `_breadth_multiplier` refondue + module
  docstring ligne 27-29 ; `config.json` libellé cohérent ; README.md sections
  « Note Tell c.1069 strict » et « Statut courant » étendues. Ajout d'un test
  CPU exécutable `tests/test_breadth_multiplier.py` (4 cas : sign-invariant,
  `[10,0]` clipé à 1, 4 magnitudes égales clipées à 2, exécution locale sans
  QC Cloud) — le caractère sign-invariant n'est plus seulement documenté, il est
  **protégé par un test**. Préflight adjoint habilité n°3 : QC demeure suspendu
  jusqu'au nouveau head.

## Références

- Curtis Faith (2007), *Way of the Turtle* — règles de trend-following Donchian.
- Moskowitz, Ooi & Pedersen (2012), *Time Series Momentum* — trend-following multi-actifs.
- Carver, Robert (2023), *Advanced Futures Trading Strategies: 30 Fully Tested
  Strategies for Multiple Trading Styles and Time Frames*, Harriman House,
  ISBN 9780857199683 — source primaire de la stratégie n° 13 (EWMAC + carry +
  vol-régime + FDM).
- QuantConnect research article #15989 (Derek Melchin, 2026-01-02) — recréation
  pédagogique de la stratégie n° 13 sur QC Cloud.
- Analyse détaillée : `research.ipynb`.
