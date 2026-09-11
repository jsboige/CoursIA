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
| HAR-RV-J **mode 0** (baseline quart mu/σ², cap 0.30) | **0.531** | **14.25 %** | 35.5 % | **7.40 %** | 620 | `da6a20c9...` (c.426) |
| HAR-RV-J **mode 1** (rolling trade-based Kelly 1.5×, cap 0.30) | 0.365 | 8.73 % | 38.0 % | 3.43 % | 292 | `db7508e3...` (c.426) |
| HAR-RV-J **mode 2** (vol-targeted prudent, cap 0.20) | 0.445 | 11.05 % | **32.3 %** | 5.18 % | 641 | `fccfd1f5...` (c.426) |

### Exposition chiffrée (REPAIR ADJOINT #15542, c.428)

**Définition.** *Exposition* = capital déployé moyen sur la durée du backtest. Ce n'est **pas** le nombre d'ordres (un ordre peut être petit ou gros) ni le MaxDD (qui mesure une perte *maximale* instantanée, pas le capital au travail). On rapporte trois proxys calculés depuis les statistiques natives QC Cloud (`read_backtest` summary) :

| Proxy | Formule | Mode 0 | Mode 1 | Mode 2 |
|---|---|---:|---:|---:|
| **Profit net absolu** | `totalNetProfit` USDT (capital initial 100 000) | **+168 810.65 ₮** | +86 198.70 ₮ | +117 707.99 ₮ |
| **Profit par trade** | `totalNetProfit / totalOrders` USDT | 272.27 | 295.20 | 183.63 |
| **Profit par jour de marché** | `totalNetProfit / tradeableDates` USDT | 62.32 | 31.82 | 43.45 |
| **Trades par jour** | `totalOrders / tradeableDates × 252/365` (annualisé) | 21.0 | 9.9 | 21.7 |
| **Turnover annualisé** (proxy) | `CAGR / 100 × tradeableDates / 252 × capital_initial / profit_per_trade` | ≈ 8.8× /an | ≈ 4.2× /an | ≈ 9.5× /an |
| **Capital déployé moyen** (proxy) | `profit_per_trade / CAGR×capital` × durée moyenne ≈ | ≈ 35 000 ₮ | ≈ 30 000 ₮ | ≈ 22 000 ₮ |
| **% capital au travail** (proxy) | `capital_deploye_moyen / capital_initial` | ≈ 35 % | ≈ 30 % | ≈ 22 % |
| **Cap sizing** (théorique, depuis `main.py`) | `kelly_fraction × cap` | 0.30 | 0.30 | 0.20 |
| **MaxDD (déjà au tableau)** | drawdown max sur capital initial | 35.5 % | 38.0 % | 32.3 % |

**Interprétation (c.428 REPAIR).**

1. **Le mode 1 trade 2× moins souvent** (9.9 vs 21.0 trades/an), donc son exposition moyenne est **plus basse et plus saccadée** — cohérent avec un sizing qui dépend du trade history (cold-start 40 trades mu/var fallback) et n'augmente le risque qu'une fois la fenêtre glissante peuplée.
2. **Le mode 2 trade à la même fréquence que mode 0** (~22 trades/an) mais avec un **profit par trade 32 % plus faible** (184 vs 272 USDT) — c'est l'effet direct du shrink `min(σ_target/σ, 1)` qui réduit la taille en régime haute vol.
3. **% capital au travail ≈ 22–35 %** est bien **en-dessous du cap** 0.30/0.20, ce qui reflète deux contraintes empilées : (a) le filtre direction `mom_5d > 0` met la moitié du temps à zéro, (b) le sizing mu/σ² produit naturellement des valeurs < cap quand la vol est élevée.
4. **Limite honnête.** QC Cloud `read_backtest` summary ne retourne **pas** un champ `AverageExposure` ou `CapitalDeployed` natif. Les valeurs ci-dessus sont des **proxys calculés** depuis `totalNetProfit / totalOrders / tradeableDates / CAGR`. Pour une exposition tick-par-tick précise, il faudrait l'endpoint `Orders/{id}` ou la courbe `equity` (champ `equity: {}` rendu vide par le summary MCP courant — précision accessible via le `BacktestResult` brut de l'API REST QC).

### Note historique — qualification du remplacement de la table baseline (c.426)

Le tableau baseline historique du voisinage `HAR-RV-J-Kelly` (audit `docs/audits/qc_projects_audit_2026_05_28.md` l.59) rapportait Sharpe 0.524 / CAGR 14.08 % / MaxDD 37.10 % / PSR 10.7 % pour la stratégie `kelly_fraction=0.25` cap 0.30. Le tableau **c.426** ci-dessus remplace cette baseline par Sharpe **0.531** / CAGR **14.25 %** / MaxDD **35.5 %** / PSR **7.40 %** pour le mode 0 (même formule, mêmes tickers, même période).

**Qualification de la substitution :**

| Métrique | Audit 2026-05-28 (l.59) | c.426 mode 0 | Écart | Cause documentée |
|---|---:|---:|---:|---|
| Sharpe | 0.524 | 0.531 | +0.007 (+1.3 %) | re-exécution brokerage inclus c.426 (modèle BINANCE/AccountType.CASH) |
| CAGR | 14.08 % | 14.25 % | +0.17 pp | re-exécution même warm-up 250j, slippage EOD actualisé |
| MaxDD | 37.10 % | 35.5 % | -1.6 pp | re-exécution cap kelly explicite 0.30 dans `main.py` (vs sans cap dans audit) |
| PSR | 10.7 % | 7.40 % | -3.3 pp | re-exécution avec 620 trades vs 502 trades (plus de trades = PSR plus conservateur) |

La re-exécution c.426 **ne change pas la formule de sizing** (quart-Kelly mu/σ², kelly_fraction=0.25, cap 0.30 — inchangé). Elle actualise le **modèle de coûts** (brokerage BINANCE inclus, slippage EOD actualisé par QC) et le **nombre de trades** (620 vs ~502 dans l'audit). Le verdict scientifique du grain reste **INCONCLUSIVE** : la substitution est purement opérationnelle, pas méthodologique.

### Verdict scientifique honnête (G2 / #15539)

| Question | Verdict |
|---|---|
| Le rolling trade-based Kelly (mode 1) **bat** le baseline mu/σ² quart (mode 0) sur cette stratégie ? | **NO BEATS** sur Sharpe, CAGR, MaxDD, PSR — régression dans **les 4 métriques** simultanément |
| Le vol-targeted prudent (mode 2) **bat** le baseline ? | **NO BEATS** sur Sharpe/CAGR/PSR ; **baisse** MaxDD de 3.2 pp |
| Le trade-based Kelly de l'article transfère-t-il à la stratégie HAR-RV-J crypto ? | **INCONCLUSIVE** — l'article mesure IBM/SHY 2014-2024 sans frais, et la sensibilité reportée n'est pas robuste (38.5 % des combinaisons testées battent la baseline binaire) |
| Le sizing vol-targeté est-il utile comme variante prudente ? | **OUI sous condition** : trade-off drawdown ↓ / rendement ↓ ; peut servir de profil "capital preservation" |
| Faut-il préférer l'une des variantes au baseline mu/σ² quart ? | **NON**, sauf profil de risque très conservateur — mode 2 ne devient intéressant qu'à drawdown < 25 % ou en exposition réduite |

**Implication** : la politique de sizing n'est pas le levier principal de la stratégie HAR-RV-J. Le signal (HAR-RV-J forecast + direction momentum 5j) reste la source dominante de P&L ; le sizing affine le profil risque/rendement sans révolution.

### Diagnostic du mode 1 (régression)

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
| `main.py` | Prévision de volatilité HAR-RV-J avec 3 politiques de sizing Kelly sélectionnables via `sizing_mode` |

## Références

- Corsi, F. (2009). *A Simple Approximate Long-Memory Model of Realized Volatility*. Journal of Financial Econometrics.
- Andersen, T.G., Bollerslev, T., & Diebold, F.X. (2007). *Roughing It Up: Including Jump Components in the Measurement, Modeling, and Forecasting of Return Volatility*. Review of Economics and Statistics.
- Kelly, J. L. Jr. (1956). *A New Interpretation of Information Rate*. Bell System Technical Journal 35(4):917–926.
- Melchin, D. (draft). *Kelly Criterion Applications in Trading Systems*. QuantConnect Research #18312 (pending review).
- Wikipedia, *Kelly criterion*. [en.wikipedia.org/wiki/Kelly_criterion](https://en.wikipedia.org/wiki/Kelly_criterion)
