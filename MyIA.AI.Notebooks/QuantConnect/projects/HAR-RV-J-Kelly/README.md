# HAR-RV-J-Kelly

**Classe d'actifs :** Crypto (BTCUSDT, ETHUSDT, LTCUSDT, BCHUSDT sur Binance)

**ID projet Cloud :** 31650567

## Description

HAR-RV-J (Heterogeneous Autoregressive Realized Variance with Jumps — variance réalisée autorégressive hétérogène avec sauts, Corsi 2009 + Andersen, Bollerslev & Diebold 2007) pour la prévision de la variance réalisée à 5 jours sur des actifs crypto. Étend le HAR Classic avec une composante de sauts dérivée de la variation bipuissance (bipower variation) de Huang-Tauchen. Fraction de Kelly 1/4 pour le dimensionnement des positions.

Mettre le paramètre `use_jumps=1` pour le HAR-RV-J (6 features) ou `use_jumps=0` pour le HAR Classic (3 features).

## Sensibilité du Kelly — 3 bras (test article #18312)

L'article QC research #18312 (*Kelly Criterion Applications in Trading Systems*, Melchin draft) applique un Kelly roulant (1.5×, fenêtre 40 trades) sur SMA crossover IBM/SHY et rapporte Sharpe 0.183 → 0.262 face à une allocation binaire 0/1, **sans frais**, sans source primaire. L'article **ne compare pas** Kelly quart vs Kelly roulant ; il compare Kelly roulant vs allocation binaire. Le présent grain construit le **test manquant** : 3 politiques de sizing sur la **même stratégie HAR-RV-J** (signal inchangé, mêmes coûts brokerage Binance, même warm-up 250j, même période 2018-01-01 → 2025-06-01).

| Mode | Nom | Formule | Cap |
|---|---|---|---|
| **0** | Quart-Kelly mu/σ² (baseline) | `f = (μ/σ²)/4` | 0.30 |
| **1** | Rolling trade-based Kelly (article-inspired) | `f = 1.5 × (p − (1−p)/b)` sur 40 derniers trades ; fallback mu/var pendant les 40 premières semaines (cold-start) | 0.30 |
| **2** | Prudent vol-targeted Kelly | `f = (μ/σ²)/4 × min(σ_target/σ, 1)`, σ_target=40% | 0.20 |

### Métriques (Binance USDT DAILY, 2018-2025, coûts brokerage inclus)

| Variante | Sharpe | CAGR | Max DD | PSR | Ordres | Backtest ID |
|----------|--------|------|--------|-----|--------|-------------|
| HAR-RV-J **mode 0** (baseline quart mu/σ², cap 0.30), avant #20388 | **0.531** | **14.25 %** | 35.5 % | **7.40 %** | 620 | `da6a20c9...` (c.426) |
| HAR-RV-J **mode 1** (rolling trade-based Kelly 1.5×, cap 0.30), avant #20388 | 0.365 | 8.73 % | 38.0 % | 3.43 % | 292 | `db7508e3...` (c.426) |
| HAR-RV-J **mode 2** (vol-targeted prudent, cap 0.20), avant #20388 | 0.445 | 11.05 % | **32.3 %** | 5.18 % | 641 | `fccfd1f5...` (c.426) |

#### Code actuel (après #20388)

| Variante | Sharpe | CAGR | Max DD | PSR | Ordres | Achats refusés | Backtest ID |
|----------|--------|------|--------|-----|--------|----------------|-------------|
| HAR-RV-J **mode 0** | **0.527** | **14.36 %** | 43.3 % | **7.07 %** | 649 | 0 | `fd288f63...` |
| HAR-RV-J **mode 1** | 0.475 | 12.04 % | 47.9 % | 6.07 % | 390 | 0 | `88d53bee...` |
| HAR-RV-J **mode 2** | 0.445 | 10.97 % | **32.4 %** | 5.19 % | 620 | 0 | `ead87b26...` |

Les lignes « avant #20388 » ont été mesurées sur un code dont une partie des achats était refusée faute de liquidités : voir la section suivante.

### Achats refusés sur compte cash (#20388)

Le compte est un compte cash Binance, en USDT : un achat n'est accepté que si les liquidités le couvrent. Deux comportements de Lean comptent ici, et le journal des ordres les montre :

- un ordre envoyé par le rééquilibrage planifié (lundi 00:00, heure de New York) n'est contrôlé et rempli qu'à l'arrivée de la barre quotidienne suivante (00:00 UTC), une vingtaine d'heures plus tard, **au prix de cette barre** ;
- un ordre envoyé depuis `on_data` est rempli à l'instant même, au prix vendeur de la barre qui vient d'arriver.

L'ancienne boucle enchaînait `set_holdings` et `liquidate`, titre par titre, avec des poids normalisés à une somme de 1. Au moment du rééquilibrage, le produit des ventes n'était pas encore disponible. L'achat qui en dépendait était refusé (« Insufficient buying power ») et jamais renvoyé, si bien que le portefeuille restait en partie en liquide jusqu'au rééquilibrage suivant.

Le code actuel :

1. plafonne la somme des poids à 0.98 ;
2. calcule les quantités cibles avant d'envoyer le moindre ordre ;
3. n'envoie au rééquilibrage que les ventes et les sorties ;
4. envoie les achats depuis `on_data`, une fois les ventes remplies, bornés par 97 % des liquidités libres au prix vendeur courant (la marge couvre les frais) ;
5. journalise chaque ordre refusé (ligne `REFUSED`) et des compteurs en fin de run.

Le signal, le dimensionnement et la période ne changent pas, et l'achat se remplit à la même barre qu'avant. Une première version envoyait les achats dès le rééquilibrage, avec la même marge de 3 % : elle laissait encore 4 refus en modes 0 et 1. Entre l'envoi et le contrôle, le prix d'une crypto peut monter de 8 à 20 % en une journée, et le dernier achat de la liste n'est plus couvert.

| Mode | Achats refusés, avant → actuel | Sharpe, avant → actuel | Max DD, avant → actuel |
|---|---|---|---|
| 0 | 70 → 0 | 0.533 → 0.527 | 35.5 % → 43.3 % |
| 1 | 17 → 0 | 0.368 → 0.475 | 38.0 % → 47.9 % |
| 2 | 0 → 0 | 0.447 → 0.445 | 32.3 % → 32.4 % |

« Avant » désigne ici une re-mesure du 2026-10-15 sur le code d'avant le correctif (backtests `3d827605`, `82e90653`, `8cc9551b`), faite dans les mêmes conditions que les lignes « Code actuel ».

**Lecture.**

- La pire baisse des modes 0 et 1 augmente, parce que les achats qui étaient refusés passent désormais : le portefeuille est plus investi, y compris pendant les baisses.
- Le Sharpe du mode 0 ne bouge presque pas.
- Le mode 1 est celui qui gagne le plus (+0.107 de Sharpe). Ses tailles sont calculées à partir du rendement du portefeuille entre deux rééquilibrages, rendement que les refus faussaient ; c'est une hypothèse, qui n'a pas été mesurée séparément.
- Le mode 2 ne change pas. Son plafond de 0.20 par titre, encore réduit par la volatilité, le maintient sous la limite des liquidités.

Les sections « Exposition chiffrée » et « Note historique » ci-dessous portent sur la mesure c.426, faite sur le code d'avant.

### Exposition chiffrée (REPAIR-2 ADJOINT #15542, c.429)

**Définition.** *Exposition* = capital déployé moyen sur la durée du backtest. Ce n'est **pas** le nombre d'ordres (un ordre peut être petit ou gros) ni le MaxDD (qui mesure une perte *maximale* instantanée). QC Cloud `read_backtest` summary **ne retourne pas** un champ `AverageExposure` ou `CapitalDeployed` natif, et n'expose pas non plus le détail de la courbe `equity` (champ `equity: {}` rendu vide par le summary MCP courant). **L'exposition précise tick-par-tick n'est donc pas reproductible depuis les seules statistiques summary natives** — elle nécessiterait l'endpoint REST `Orders/{id}` ou la courbe `BacktestResult.equity` brute.

**Ratios vérifiables depuis `read_backtest` summary** (les seuls qui se dérivent arithmétiquement des champs exposés sans fabrication) :

| Ratio | Formule | Mode 0 | Mode 1 | Mode 2 |
|---|---|---:|---:|---:|
| **Profit net absolu** | `totalNetProfit` USDT (capital initial 100 000) | **+168 810.65 ₮** | +86 198.70 ₮ | +117 707.99 ₮ |
| **Profit par trade** | `totalNetProfit / totalOrders` USDT | 272.27 | 295.20 | 183.63 |
| **Profit par jour de marché** | `totalNetProfit / tradeableDates` USDT (2709 jours sur 2018-01-01 → 2025-06-01, ≈ 7.42 ans) | 62.31 | 31.82 | 43.45 |
| **Multiplicateur net sur capital** | `totalNetProfit / 100000` | **+1.69×** | +0.86× | +1.18× |
| **Cap sizing** (théorique, depuis `main.py`) | `kelly_fraction × cap` | 0.30 | 0.30 | 0.20 |

**Interprétation (c.429 REPAIR-2).**

1. **Mode 1 a le profit/ordre le plus élevé** (295 USDT vs 272 mode 0 vs 184 mode 2) — paradoxe apparent : le sizing trade-based produit moins de trades (292 vs 620) mais chacun plus rentable en moyenne. **MAIS** son profit total reste inférieur (-49 % vs mode 0) parce qu'il trade **2.1× moins souvent**. Le sizing mu/σ² du mode 0 capture plus d'opportunités (rebalance hebdomadaire qui réinvestit même quand le signal est marginalement positif).
2. **Mode 2 a un profit/ordre 32 % plus faible que mode 0** (184 vs 272 USDT) — c'est l'effet direct du shrink `min(σ_target/σ, 1)` qui réduit la taille en régime haute vol, donc chaque trade est plus petit.
3. **Mode 1 trade 2.1× moins souvent** (292 vs 620 ordres) — cohérent avec sizing dépendant du trade history (cold-start 40 trades mu/var fallback ; au-delà, le sizing trade-based filtre plus agressivement).

**Limite honnête.** Les proxys « capital déployé moyen », « % capital au travail », « turnover annualisé », « trades/an » tentés en c.428 **n'étaient pas dérivables** depuis les summary stats natives — les chiffres publiés (35k/30k/22k, 22-35 %, 8.8×/an, 21.0/9.9/21.7) **étaient de la fabrication arithmétique**, pas une dérivation vérifiable. Honnêteté référentielle : **on retire** les proxys fabrication et on **conserve uniquement les ratios directement calculables** depuis `totalNetProfit / totalOrders / tradeableDates / capital_initial`. Pour exposition tick-par-tick précise : endpoint `Orders/{id}` ou courbe `equity` brute via API REST QC.

### Note historique — qualification du remplacement de la table baseline (c.426 + c.429)

Le tableau baseline historique de `HAR-RV-J-Kelly` (référencé dans `docs/qc/qc-strategies-status.md:250`) rapportait Sharpe **0.524** / CAGR **14.08 %** / MaxDD **37.1 %** / PSR **10.69 %** / NP **+165.9 % (₮165 831)** sur 2709 jours 2018-2025 aligned. Le tableau **c.426** ci-dessus remplace cette baseline par Sharpe **0.531** / CAGR **14.25 %** / MaxDD **35.5 %** / PSR **7.40 %** / NP **+168.8 % (₮168 811)** pour le mode 0 (même formule `kelly_fraction=0.25` cap 0.30, mêmes tickers BTCUSDT/ETHUSDT/LTCUSDT/BCHUSDT, même période 2018-01-01 → 2025-06-01).

**Qualification de la substitution :**

| Métrique | Status historique (`docs/qc/qc-strategies-status.md:250`) | c.426 mode 0 | Écart | Cause documentée |
|---|---:|---:|---:|---|
| Sharpe | 0.524 | 0.531 | +0.007 (+1.3 %) | re-exécution brokerage inclus c.426 (modèle BINANCE/AccountType.CASH) |
| CAGR | 14.08 % | 14.25 % | +0.17 pp | re-exécution même warm-up 250j, slippage EOD actualisé |
| MaxDD | 37.1 % | 35.5 % | -1.6 pp | re-exécution cap kelly explicite 0.30 dans `main.py` (vs sans cap dans status) |
| PSR | 10.69 % | 7.40 % | -3.3 pp | re-exécution avec 620 ordres vs ~502 d'après l'UI QC Cloud du backtest d'origine (le tableau status ne porte pas de compte d'ordres ; plus de trades = PSR plus conservateur) |
| NP absolu | +₮165 831 | +₮168 811 | +₮2 980 (+1.8 %) | re-exécution avec modèle brokerage BINANCE actualisé |

La re-exécution c.426 **ne change pas la formule de sizing** (quart-Kelly mu/σ², `kelly_fraction=0.25`, cap 0.30 — inchangé). Elle actualise le **modèle de coûts** (brokerage BINANCE inclus, slippage EOD actualisé par QC) et le **nombre d'ordres** (620 vs ~502, d'après l'UI QC Cloud du backtest d'origine — le tableau status ne porte pas de compte d'ordres). Le verdict scientifique du grain reste **INCONCLUSIVE** : la substitution est purement opérationnelle, pas méthodologique. **Note c.429** : la citation correcte est `docs/qc/qc-strategies-status.md:250` (lignes 247-253 du tableau cohorte Tranche 8), pas `docs/audits/qc_projects_audit_2026_05_28.md:59` comme indiqué en c.428 — corrigé après recapture first-hand de l'adjoint po-2025.

### Verdict scientifique honnête (G2 / #15539)

| Question | Verdict |
|---|---|
| Le rolling trade-based Kelly (mode 1) **bat** le baseline mu/σ² quart (mode 0) sur cette stratégie ? | **NO BEATS** sur Sharpe, CAGR, MaxDD, PSR — régression dans **les 4 métriques** simultanément, avant comme après #20388 (code actuel : Sharpe 0.475 contre 0.527) |
| Le vol-targeted prudent (mode 2) **bat** le baseline ? | **NO BEATS** sur Sharpe/CAGR/PSR ; **baisse** MaxDD de 10.9 pp avec le code actuel (32.4 % contre 43.3 %), de 3.2 pp avant #20388 |
| Comment se classent les modes 1 et 2 entre eux ? | **Le classement s'est inversé avec #20388.** Avant, le mode 2 devançait le mode 1 (Sharpe 0.447 contre 0.368). Avec le code actuel, le mode 1 passe devant sur Sharpe, CAGR et PSR (0.475 contre 0.445), mais il a la pire baisse la plus forte des trois modes (47.9 %) |
| Le trade-based Kelly de l'article transfère-t-il à la stratégie HAR-RV-J crypto ? | **INCONCLUSIVE** — l'article mesure IBM/SHY 2014-2024 sans frais, et la sensibilité reportée n'est pas robuste (38.5 % des combinaisons testées battent la baseline binaire) |
| Le sizing vol-targeté est-il utile comme variante prudente ? | **OUI sous condition** : trade-off drawdown ↓ / rendement ↓ ; peut servir de profil "capital preservation" |
| Faut-il préférer l'une des variantes au baseline mu/σ² quart ? | **NON**, sauf profil de risque très conservateur — mode 2 ne devient intéressant qu'à drawdown < 25 % ou en exposition réduite |

**Implication** : la politique de sizing n'est pas le levier principal de la stratégie HAR-RV-J. Le signal (HAR-RV-J forecast + direction momentum 5j) reste la source dominante de P&L ; le sizing affine le profil risque/rendement sans révolution.

### Diagnostic du mode 1 (régression)

**Part de l'exécution (#20388).** Sur le code d'avant, 17 achats du mode 1 étaient refusés faute de liquidités. Une fois ces refus supprimés, l'écart de Sharpe avec le mode 0 passe de 0.165 à 0.052. Les trois causes ci-dessous portent sur l'écart qui reste.

Le mode 1 (formule `p − (1−p)/b`, inspiré de Kelly 1956 §3 sur paris discrets) sous-performe parce que :

1. **Trade attribution bruité** : le retour portefeuille entre 2 rebalances est attribué uniformément aux tickers tenus, ce qui mélange les contributions spécifiques et génère du bruit dans le win/loss ratio estimé.
2. **Cold-start long** : 40 trades = ~40 semaines de warm-up effectif = ~9 mois où mode 1 fallback sur mode 0 (le bootstrap est nécessaire mais la transition brutale passé 40 trades peut déstabiliser).
3. **Signal mu/σ² vs signal discret** : pour une stratégie forecast-based, la mesure mu/σ² sur 20 jours est plus stable que la mesure trade-based sur 40 rebalances (≈ 1 trade par semaine).

**Hypothèse de la régression** : la formule discrète Kelly est conçue pour des paris **i.i.d.** (lancers de dés, blackjack), pas pour un signal forecast autorégressif dont les erreurs sont sériellement corrélées. Le couplage entre signal et sizing est rompu : un bon trade forecast peut suivre un mauvais trade forecast, ce qui corrompt l'estimation win-rate/win-loss.

### Note sur la méthodologie (référence article)

L'article #18312 est un draft « pending review » qui ne cite aucune source académique primaire. Sa formule `f = p − (1−p)/b` est exactement Kelly 1956 §3 (formule discrète transposée sur le ratio win/loss). Les sources primaires vérifiées pour ce grain sont :

- Kelly, J. L. Jr. (1956). *A New Interpretation of Information Rate*. Bell System Technical Journal 35(4):917–926. [archive.org/details/bstj35-4-917](https://archive.org/details/bstj35-4-917) · [princeton.edu/~wbialek/rome/refs/kelly_56.pdf](https://www.princeton.edu/~wbialek/rome/refs/kelly_56.pdf)
- Wikipedia, *Kelly criterion* — formule continue-time `f* = (μ−r)/σ²`, discussion sur l'erreur d'estimation et la recommandation fractional Kelly.

Le verdict NO BEATS du mode 1 **ne contredit pas** Kelly 1956, qui ne dit rien sur les signaux autorégressifs. Il contredit l'**article #18312** au sens où son multiplicateur 1.5× n'améliore pas le sizing dans ce contexte crypto ; ce qui peut signifier (a) les paramètres de l'article (1.5×, 40) sont optimisés pour IBM/SHY et ne transfèrent pas, ou (b) le signal mu/σ² est objectivement mieux adapté que le signal discret pour les signaux forecast.

## Comment exécuter

### QC Cloud

Ouvrir le projet cloud 31650567, compiler et lancer un backtest avec les paramètres souhaités :

| Paramètre | Valeur par défaut | Effet |
|---|---|---|
| `use_jumps` | `1` | HAR-RV-J (6 features) si `1`, HAR Classic (3 features) si `0` |
| `sizing_mode` | `0` | `0` = quart-Kelly baseline, `1` = rolling trade-based, `2` = vol-targeted prudent |

Exemples :
- `sizing_mode=0&use_jumps=1` → reproduction du baseline quart-Kelly
- `sizing_mode=1&use_jumps=1` → Kelly roulant trade-based (article-inspired)
- `sizing_mode=2&use_jumps=1` → sizing vol-targeted prudent

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Prévision de volatilité HAR-RV-J avec 3 politiques de sizing Kelly sélectionnables via `sizing_mode` ; exécution adaptée au compte cash (ventes au rééquilibrage, achats depuis `on_data`, #20388) |

## Références

- Corsi, F. (2009). *A Simple Approximate Long-Memory Model of Realized Volatility*. Journal of Financial Econometrics.
- Andersen, T.G., Bollerslev, T., & Diebold, F.X. (2007). *Roughing It Up: Including Jump Components in the Measurement, Modeling, and Forecasting of Return Volatility*. Review of Economics and Statistics.
- Kelly, J. L. Jr. (1956). *A New Interpretation of Information Rate*. Bell System Technical Journal 35(4):917–926.
- Melchin, D. (draft). *Kelly Criterion Applications in Trading Systems*. QuantConnect Research #18312 (pending review).
- Wikipedia, *Kelly criterion*. [en.wikipedia.org/wiki/Kelly_criterion](https://en.wikipedia.org/wiki/Kelly_criterion)
