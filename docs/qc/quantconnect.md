# QuantConnect (QC) - Configuration et règles

Document de reference pour la coordination QC (MCP, orgs, patterns, anti-patterns). Pour les details pédagogiques et le mapping livre Jared, voir la **navigation des docs QC** ci-dessous.

## Navigation des docs QC du dépôt

Le repo contient déjà plusieurs documents canoniques. **Ne pas dupliquer ici** ce qui est en source-of-truth ailleurs :

| Document | Role | Source canonique de |
|----------|------|---------------------|
| [MyIA.AI.Notebooks/QuantConnect/README.md](../../MyIA.AI.Notebooks/QuantConnect/README.md) | Entrée série pédagogique | Catalog des 27+ notebooks Python, structure series |
| [MyIA.AI.Notebooks/QuantConnect/GETTING-STARTED.md](../../MyIA.AI.Notebooks/QuantConnect/GETTING-STARTED.md) | Setup utilisateur | Première prise en main QC + LEAN |
| [MyIA.AI.Notebooks/QuantConnect/BOOK_MAPPING.md](../../MyIA.AI.Notebooks/QuantConnect/BOOK_MAPPING.md) | Mapping livre Jared | 63 exemples / 71 deliverables HandsOnAITradingBook -> nos notebooks/projects |
| [MyIA.AI.Notebooks/QuantConnect/docs/HANDSON_AI_TRADING_MAPPING.md](../../MyIA.AI.Notebooks/QuantConnect/docs/HANDSON_AI_TRADING_MAPPING.md) | Mapping détaillé Ch06 | 22 strategies ML du livre |
| [MyIA.AI.Notebooks/QuantConnect/docs/HANDSON_DATA_REQUIREMENTS.md](../../MyIA.AI.Notebooks/QuantConnect/docs/HANDSON_DATA_REQUIREMENTS.md) | Besoins datasets livre | Datasets requis par exemple |
| [MyIA.AI.Notebooks/QuantConnect/docs/PAPER_TRADING_ARCHITECTURE.md](../../MyIA.AI.Notebooks/QuantConnect/docs/PAPER_TRADING_ARCHITECTURE.md) | Pédagogie paper trading | Architecture paper -> live, brokers IBKR/Binance |
| [MyIA.AI.Notebooks/QuantConnect/docs/PAPER_TO_LIVE_TRANSITION.md](../../MyIA.AI.Notebooks/QuantConnect/docs/PAPER_TO_LIVE_TRANSITION.md) | Procédure transition | Checklist paper -> live |
| [MyIA.AI.Notebooks/QuantConnect/docs/PROCEDURE_DEPLOIEMENT.md](../../MyIA.AI.Notebooks/QuantConnect/docs/PROCEDURE_DEPLOIEMENT.md) | Procédure déploiement | Workflow déploiement strategies |
| [MyIA.AI.Notebooks/QuantConnect/docs/qc_strategies_catalog.md](../../MyIA.AI.Notebooks/QuantConnect/docs/qc_strategies_catalog.md) | Catalog strategies live | 96 ALIVE projects, Sharpe top 15, IDs QC Cloud (régénéré depuis API) |
| [MyIA.AI.Notebooks/QuantConnect/docs/audits/](../../MyIA.AI.Notebooks/QuantConnect/docs/audits/) | Audits historiques | AUDIT_QC_CLOUD, AUDIT_QC_ORG_2026-04, AUDIT_RAPPORT_2026-03-22, VALIDATION-REPORT |
| [MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/REGISTRY.md](../../MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/REGISTRY.md) | Registry training | 70+ checkpoints, stages -1/0/1/2, Anti-Bias |
| [docs/archive/ml-trading-state.md](../archive/ml-trading-state.md) | Leçons ML trading | Pattern central vol vs direction, 7 disciplines, anti-FAANG |
| [MyIA.AI.Notebooks/QuantConnect/docs/QC_CLOUD_ASSISTANTS_WORKFLOW.md](../../MyIA.AI.Notebooks/QuantConnect/docs/QC_CLOUD_ASSISTANTS_WORKFLOW.md) | Assistants QC Cloud | 8 assistants, protocole coûts QCC, matrice delegation |

**Règle de coherence** : pour les performances par stratégie (Sharpe, CAGR) -> `qc_strategies_catalog.md`. Pour les patterns réutilisables -> ce fichier. Pour les leçons ML trans-iteration -> `docs/archive/ml-trading-state.md`. Pour le mapping livre -> `BOOK_MAPPING.md` (racine, pas doublon `docs/`).

## Backtests obligatoires

Toute modification d'une stratégie QC (main.py, paramètres, périodes) **DOIT** être validée par un backtest :

1. `create_compile` pour vérifier la compilation
2. `create_backtest` pour lancer le backtest
3. `read_backtest` pour récupérer les métriques (Sharpe, CAGR, MaxDD)
4. Reporter les résultats dans le message de commit ET sur RooSync

**Changer une date ou un paramètre sans backtest = travail invalide.**

## QC Cloud API - Accès via MCP Docker (OBLIGATOIRE)

**Méthode d'accès** : Utiliser le MCP Docker `quantconnect/mcp-server` configure dans `.mcp.json` a la racine du projet.

- **NE PAS** utiliser de scripts Python avec l'API REST directe (provoque du rate-limiting et des erreurs d'auth)
- Le MCP gère l'authentification et le rate-limiting automatiquement
- Fichier de config : `.mcp.json` (déjà dans `.gitignore`, JAMAIS committer)

### Configuration `.mcp.json`

```json
{
  "mcpServers": {
    "qc-mcp": {
      "command": "docker",
      "args": ["run", "-i", "--rm",
        "-e", "QUANTCONNECT_USER_ID",
        "-e", "QUANTCONNECT_API_TOKEN",
        "-e", "QUANTCONNECT_ORGANIZATION_ID",
        "-e", "AGENT_NAME",
        "quantconnect/mcp-server"],
      "env": {
        "QUANTCONNECT_USER_ID": "<voir dashboard RooSync>",
        "QUANTCONNECT_API_TOKEN": "<voir dashboard RooSync>",
        "QUANTCONNECT_ORGANIZATION_ID": "<voir dashboard RooSync>",
        "AGENT_NAME": "claude-code"
      }
    }
  }
}
```

### Alternative légère : `qc-mcp-lite` (~5k tokens vs ~40k)

Le MCP Docker officiel charge un schema d'outils volumineux (~40k tokens). Pour les workflows de backtest standard, le dépôt fournit un wrapper Python léger **`scripts/qc-mcp-lite/server.py`** (~10 outils, schema <5k tokens) qui re-expose l'API QC v2 sans conteneur Docker.

Outils exposes : `create_compile`, `read_compile`, `create_backtest`, `read_backtest` (Sharpe/CAGR/MaxDD), `list_backtests`, `list_projects`, `read_project`, `read_file`, `create_file`, `update_file_contents`. Auth = pattern QC v2 (`SHA256(token:timestamp)` + header `Basic userId:hash`). Rate limiting 10 appels/min applique in-process (même limite fleet-wide).

Config `.mcp.json` (remplace l'entrée Docker `qc-mcp` ; secrets dans `.env` gitignore, **JAMAIS inline**) :

```json
{
  "mcpServers": {
    "qc-mcp-lite": {
      "command": "python",
      "args": ["scripts/qc-mcp-lite/server.py"],
      "env": {
        "QC_API_USER_ID": "<voir dashboard RooSync>",
        "QC_API_ACCESS_TOKEN": "<voir dashboard RooSync>"
      }
    }
  }
}
```

Verification rapide : `python -c "from server import list_projects; print(list_projects())"` depuis `scripts/qc-mcp-lite/`. Procédure complete (setup `.env`, retour au MCP Docker complet) : [`scripts/qc-mcp-lite/README.md`](../../scripts/qc-mcp-lite/README.md).

### Rate limiting strict

MAX 10 appels/minute entre TOUS les agents. Avant de lancer un backtest, poster sur le dashboard. Un seul agent a la fois sur l'API QC.

### Pour retrouver les tokens

- Dashboard workspace CoursIA : section status
- Messages RooSync : tag `quantconnect` ou `TOKEN`
- En cas de token invalide : demander au coordinateur (ai-01) via RooSync

### Troubleshooting hash mismatch (incident 2026-04-05)

`~/.claude.json` (config globale Claude Code) contient parfois une section `mcpServers` par workspace qui **surcharge** `.mcp.json` local. Un ancien token cache la peut causer `Hash doesn't match` malgré le bon token dans `.mcp.json` projet.

Vérifier dans cet ordre :

1. `~/.claude.json` section du workspace (config globale qui peut surcharger)
2. `.mcp.json` racine projet (config projet standard)
3. Token valide sur QC (tester via API directe Python)

**Fix recurrent** : supprimer l'entrée `mcpServers.qc-mcp` de `~/.claude.json` pour que `.mcp.json` soit la seule source de vérité.

## Organisations QC

QC est multi-tenant via les "organizations". Le cluster CoursIA utilise plusieurs orgs en parallèle selon le contexte :

| Org | Tier | Usage | Backtest API |
|-----|------|-------|--------------|
| Research tier dedicated (default user) | Research (payant) | Deploiements de reference, Binance crypto data subscription, projets de développement | Inclus |
| Partner school | Free/sponsored | Cours partenaire, masterclass Quant League | NON inclus |
| ECE | Free | Matériel pédagogique ECE | NON inclus |

**Règle d'or** : pour `create_backtest` programmatique via API, il faut **une org avec backtest API incluse** (research tier). Les orgs gratuites/éducatives (partenaire, ECE) n'ont PAS l'API backtest — erreur récurrente : tenter `create_backtest` sur une org partenaire échoue silencieusement ou avec rate-limit. Vérifier l'org cible avant de dispatcher.

### Switcher d'org

L'orga par défaut du MCP est définie par `QUANTCONNECT_ORGANIZATION_ID` dans `.mcp.json`. Deux options pour changer ponctuellement :

1. Éditer `.mcp.json` env var et rebuild le MCP Docker container
2. Spécifier `organizationId` explicitement par appel quand le tool MCP l'accepte

Note : `read_account` retourne TOUJOURS l'orga par défaut du USER_ID (la research tier quand non force par env var).

### Énumération des orgs

Il n'existe pas d'endpoint `list_organizations`. La seule façon : `mcp__qc-mcp__list_projects` retourne les projets de toutes les orgs dont l'user est membre+ — agréger les `organizationId` distincts.

## Structure QC dans le dépôt

```
MyIA.AI.Notebooks/QuantConnect/
  Python/           # 27+ notebooks progressifs (QC-Py-01 a QC-Py-Cloud-XX)
  projects/          # ~50 strategies avec main.py + research.ipynb
  shared/            # Librairie utilitaire (backtestlib, indicators, plotting)
  partner-course-quant-trading/  # Cours partenaire : exercices, templates, lean-workspace
  docs/              # Documentation technique (pas de coordination)
```

## QC Cloud Assistants — méthode privilégiée Quantbook execution

QuantConnect expose 8 assistants intégrés (Conductor, Ideas, Research, Research Validation, Backtest, Paper Testing, Live Monitoring, Mia) accessibles via :

```
https://www.quantconnect.com/organization/<org_id>/assistants
```

**Le Research Assistant résout le problème "Quantbook execution Windows local impossible"** : il execute les cells du notebook sur QC Cloud, itère automatiquement (edit, execute, fix, re-execute) jusqu'au succès, et les tokens consommes sont ceux de QC (pas Anthropic).

### Workflow Research Assistant (via Playwright)

1. Naviguer `https://www.quantconnect.com/organization/<org_id>/assistants`
2. Cliquer "New Task" sur **Research Assistant**
3. Créer tâche avec prompt + `project_id` QC Cloud cible
4. Deployer : l'agent execute les cells du notebook
5. Lire les résultats dans **Tasks > Deployments > Completed**

### Limites et précautions

- **Validation cluster obligatoire post-deployment** : même si Research Assistant claim "Sharpe 3.50", refaire en local par walk-forward 5-fold + multi-seed >=4 + transaction costs avant tout claim BEATS. Cf [.claude/rules/pr-review-discipline.md](../../.claude/rules/pr-review-discipline.md) section C.
- **Coût QC tokens** : ne pas lancer 50 deployments en parallèle sans vérifier le burn rate
- **Éviter chevauchement agents** sur même deployment (tokens dupliqués) : coordination via dashboard avant lancement
- **Notebook output download** : Playwright snapshot ou API download artifact (workflow exact a documenter par usage)

### Cas d'usage privilégiés

- Re-execution Quantbooks audit (cf section validation H.7 de CLAUDE.md)
- Validation algos QC Cloud avant import dans projects/
- Debugging multi-aller-retour des strategies en iteration

## Architecture composites (AlphaModel + MultiStrategyPCM)

Pattern standardise pour combiner plusieurs strategies dans un même algo QC :

### Structure de fichiers (3 fichiers obligatoires)

- `main.py` : `QCAlgorithm` avec `set_alpha(CompositeAlphaModel(...))` + `set_portfolio_construction(MultiStrategyPCM(...))`
- `alpha_models.py` : une classe par alpha, chaque avec `self.name` et `source_model=self.name`
- `portfolio_construction.py` : `MultiStrategyPCM` avec `determine_target_percent` (PAS `create_targets`)

### MultiStrategyPCM — design

- Groupe les insights par `source_model`
- Alloue une slice de capital par stratégie via dict `alpha_allocations`
- Supporte branches weight-hint ET equal-weight
- Utilise `set_rebalancing_func` pour le rebalance timing

### AlphaModel — règles

- DOIT avoir `self.name = "StrategyName"` dans `__init__`
- DOIT passer `source_model=self.name` a tous les `Insight.price()`
- DOIT filtrer par liste explicite de tickers (PAS `algorithm.securities.values()`)
- DOIT enregistrer les indicateurs dans `on_securities_changed` uniquement pour les tickers connus
- NE JAMAIS ajouter SPY comme equity benchmark dans l'univers (cause un leak si on itère `securities`)

### Composites realises — leçons (consolidation, pas snapshot)

| Composite | Allocation optimum | Sharpe | Leçon |
|-----------|--------------------|--------|-------|
| TrendWeather (TrendStocks + AllWeather) | T75 / AW25 | **1.15+** | Sweep monotone : plus de TrendStocks = meilleur Sharpe. ROC63 momentum weighting = gain majeur (0.79 -> 1.13) |
| FamaFrenchAllWeather | FF20 / AW80 | ~0.59 | Sweep monotone vers AllWeather : FamaFrench n'ajoute pas de diversification |
| MomentumRegime (SectorMomentum + RegimeSwitching) | ABANDONNE | max 0.24 | Problème "double-defense" : les deux alphas défensifs sur les mêmes périodes |
| EMATrend (EMA-Cross + TrendStocks) | en cours | a venir | Overlap 5 tech stocks entre strategies (intentionnel) |

**Règle générale** : si le sweep d'allocation montre un comportement monotone (90/10 ou 10/90 gagne), le second alpha n'apporte pas de diversification — vérifier qu'il occupe un quadrant de marche distinct du premier. Confirmation par la "décennie 2015+" : risk-off via TLT détruit la valeur, equity défensifs (XLP/IEF) > bonds long.

## Patterns universels (consolidation 30+ iterations strategies)

### Patterns confirmés (a ré-utiliser)

1. **Risk-adjusted momentum** (return/vol) > raw momentum
2. **Skip-month** (Jegadeesh 1990) : exclure le dernier mois — single-asset only
3. **TLT risk-off détruit la valeur** sur la décennie 2015+ : XLP/IEF > TLT
4. **Stop-loss -8% a -12%** : réduit MaxDD sans tronquer les reversions
5. **ATR sizing contre-productif** pour Donchian trend following
6. **Profit target 50%** pour options (TastyTrade) + VIX band 15-35
7. **Drift rebalancing 3%** > SMA overlay pour portfolios statiques
8. **Vol window 60d > 20d** pour covariance min-var
9. **Monthly + regime-change rebal > daily** : réduit trades 80%
10. **Trail breakeven 3% > 4%** pour BTC daily
11. **SMA50 >> SMA100 pour crypto** : SMA100 filtre les bonnes entrées bull
12. **SL 6% minimum sur BTC daily** : 5% trop serré
13. **OLS hedge ratio ne sauve pas pairs trading** : le problème est les paires elles-mêmes
14. **Fix structural bugs >> academic improvements** : leverage/risk mgmt > signal refinement
15. **Diversifier instruments > relaxer seuils** : ajouter SPY+QQQ+IWM > baisser RSI threshold
16. **Composite via Algorithm Framework** = clean separation (AlphaModel + PCM + source_model)
17. **Biweekly rebalance est l'optimum** pour ML (weekly = trop de turnover, monthly = trop lent)
18. **Anti-overfitting** (max_depth 5, min_samples 10) critique pour tree models
19. **MLPClassifier/MLPRegressor** de sklearn marche bien sur QC Cloud
20. **Selective liquidation** réduit le turnover vs full portfolio wipe

### Anti-patterns critiques

- **SPY Parking** : investir en SPY quand inactif = beta loading déguisé, le Sharpe monte mais l'alpha est nul
- **Backtests courts = overfitting** : Trend-Following Sharpe 2.157 (3 mois) -> 0.06 (7 ans)
- **ChatGPT/academic suggestions** : 3/4 dégradent sur QC cloud. Ne garder que les fixes structurels
- **yfinance != QC cloud** : 6/12 research suggestions dégradent en pratique
- **Crypto strategies pre-2018 unreliable** : 2017 bubble distortion
- **MaximumDrawdownPercentPortfolio** = JAMAIS sur multi-stock (liquidation simultanée)
- **1 param a la fois** : changer tout ensemble -> regression non-diagnostiquable
- **Raw momentum + min-var** : ne pas combiner (double penalisation)
- **Fake ML implementations** (hardcoded weights) : pires que real sklearn models
- **SMA100 filter trop restrictif pour mean reversion**
- **USD trend filter degrade FX momentum**

## Leçons techniques QC

- `read_file` AVANT `update_file_contents` : collaboration lock (expire vite)
- Options : `Resolution.MINUTE` sinon chain vide
- 1 seul backtest a la fois sur le node QC
- `algo.rsi(symbol, 14, Resolution.Hour)` ne marche pas dans `OnSecuritiesChanged` -> utiliser `register_indicator`
- `class X(QCAlgorithm, Mixin)` interdit (Python/CLR multiple inheritance)
- Binance CASH : `set_account_currency("USDT")` + `set_cash(10000)`
- Binance fees : preleve en BTC -> utiliser `portfolio[sym].quantity` pas `order qty`
- QC API auth : `SHA256(token:timestamp)` as hash, header `Timestamp`, Basic auth
- Chart API : data seulement pour backtests récents (~quelques heures)

## Historique training & checkpoints (preservation)

Toute l'historique des trainings ML/QC est préservée dans le dépôt et accessible a tous les agents, **PAS dans des memos chronologiques** :

| Source | Contenu |
|--------|---------|
| `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/REGISTRY.md` | Registry 70+ checkpoints, BEATS/FAIL/MIXED par symbole, stages -1/0/1/2, Anti-Bias audit |
| `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/CURRICULUM.md` | Plan global ML curriculum |
| `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/docs/M1..M17 + Stage2 + Stage7 + RECAP_KEEPERS_V2` | 35 fichiers de notes méthodologiques par iteration |
| `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/docs/Curriculum_V2_Meta_Analysis.md` | Meta-analyse curriculum V2 |
| `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/results/*/checkpoint.jsonl` + `train.log` | 27 runs avec état par combo et logs unbuffered (local, gitignored) |
| QC Cloud (MCP `list_projects` + `list_backtests` + `read_backtest`) | Sharpe/CAGR/MaxDD live de chaque iteration |
| [docs/archive/ml-trading-state.md](../archive/ml-trading-state.md) | Leçons consolidées (vol vs direction, parcimonie, transaction costs, recommandations datasets) |

**Règle** : pas de duplication. Si tu veux ajouter une note sur une iteration training, vise `ML-Training-Pipeline/docs/M<N>_*.md` ou QC Cloud notes, pas un memo coordinateur. Pour une leçon trans-iteration : `docs/archive/ml-trading-state.md`.

## Livre de reference

*Hands-On AI Trading* de Jared Broad — https://www.hands-on-ai-trading.com/

- Repo exemples : https://github.com/QuantConnect/HandsOnAITradingBook
- 22 exemples : Ch06 (19 strategies ML), Ch07 (1 RL hedging options), Ch08 (2 portfolio)
- Issues associées : #107 (mapping), #143 (implementation ML)

Le livre couvre les patterns ML actuels (RF, XGBoost, LSTM, CNN temporel, Chronos foundation models, RL hedging) avec exemples QC Cloud directement importables. Cf `MyIA.AI.Notebooks/QuantConnect/projects/` pour les imports realises.

## Reference QC partnership

QuantConnect (Jared Broad, CEO) sponsorise l'usage éducatif via le code promo `education2025` (annule 100% du coût des seats Trading Firm). Architecture éducative recommandée :

- Org sponsorisée = espace commun (algos d'exemple, evaluation collective, masterclass), avec coupon
- Comptes perso FREE pour les étudiants = suffisants pour term projects sur leur poste
- Coût minimum par org éducative avec coupon : 14$/mois (1 noeud B2-8 backtest)

**Mécanique du coupon** : cart vide non accepte pour checkout, minimum 1 noeud compute requis. Rate limit API : 15 min de cooldown si on clique trop vite sur +/-. Le coupon couvre les seats Trading Firm (unlimited members), pas le compute.

**Hands-On AI Trading book** : recommandation officielle de Jared pour le cursus (cf section "Livre de reference").
