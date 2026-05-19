# QuantConnect (QC) - Configuration et regles

Document de reference pour la coordination QC (MCP, orgs, patterns, anti-patterns). Pour les details pedagogiques et le mapping livre Jared, voir la **navigation des docs QC** ci-dessous.

## Navigation des docs QC du depot

Le repo contient deja plusieurs documents canoniques. **Ne pas dupliquer ici** ce qui est en source-of-truth ailleurs :

| Document | Role | Source canonique de |
|----------|------|---------------------|
| [MyIA.AI.Notebooks/QuantConnect/README.md](../MyIA.AI.Notebooks/QuantConnect/README.md) | Entree serie pedagogique | Catalog des 27+ notebooks Python, structure series |
| [MyIA.AI.Notebooks/QuantConnect/GETTING-STARTED.md](../MyIA.AI.Notebooks/QuantConnect/GETTING-STARTED.md) | Setup utilisateur | Premiere prise en main QC + LEAN |
| [MyIA.AI.Notebooks/QuantConnect/BOOK_MAPPING.md](../MyIA.AI.Notebooks/QuantConnect/BOOK_MAPPING.md) | Mapping livre Jared | 63 exemples / 71 deliverables HandsOnAITradingBook -> nos notebooks/projects |
| [MyIA.AI.Notebooks/QuantConnect/docs/HANDSON_AI_TRADING_MAPPING.md](../MyIA.AI.Notebooks/QuantConnect/docs/HANDSON_AI_TRADING_MAPPING.md) | Mapping detaille Ch06 | 22 strategies ML du livre |
| [MyIA.AI.Notebooks/QuantConnect/docs/HANDSON_DATA_REQUIREMENTS.md](../MyIA.AI.Notebooks/QuantConnect/docs/HANDSON_DATA_REQUIREMENTS.md) | Besoins datasets livre | Datasets requis par exemple |
| [MyIA.AI.Notebooks/QuantConnect/docs/PAPER_TRADING_ARCHITECTURE.md](../MyIA.AI.Notebooks/QuantConnect/docs/PAPER_TRADING_ARCHITECTURE.md) | Pedagogie paper trading | Architecture paper -> live, brokers IBKR/Binance |
| [MyIA.AI.Notebooks/QuantConnect/docs/PAPER_TO_LIVE_TRANSITION.md](../MyIA.AI.Notebooks/QuantConnect/docs/PAPER_TO_LIVE_TRANSITION.md) | Procedure transition | Checklist paper -> live |
| [MyIA.AI.Notebooks/QuantConnect/docs/PROCEDURE_DEPLOIEMENT.md](../MyIA.AI.Notebooks/QuantConnect/docs/PROCEDURE_DEPLOIEMENT.md) | Procedure deploiement | Workflow deploiement strategies |
| [MyIA.AI.Notebooks/QuantConnect/docs/qc_strategies_catalog.md](../MyIA.AI.Notebooks/QuantConnect/docs/qc_strategies_catalog.md) | Catalog strategies live | 96 ALIVE projects, Sharpe top 15, IDs QC Cloud (regenere depuis API) |
| [MyIA.AI.Notebooks/QuantConnect/docs/audits/](../MyIA.AI.Notebooks/QuantConnect/docs/audits/) | Audits historiques | AUDIT_QC_CLOUD, AUDIT_QC_ORG_2026-04, AUDIT_RAPPORT_2026-03-22, VALIDATION-REPORT |
| [MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/REGISTRY.md](../MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/REGISTRY.md) | Registry training | 70+ checkpoints, stages -1/0/1/2, Anti-Bias |
| [docs/ml-trading-state.md](ml-trading-state.md) | Lecons ML trading | Pattern central vol vs direction, 7 disciplines, anti-FAANG |

**Regle de coherence** : pour les performances par strategie (Sharpe, CAGR) -> `qc_strategies_catalog.md`. Pour les patterns reutilisables -> ce fichier. Pour les lecons ML trans-iteration -> `ml-trading-state.md`. Pour le mapping livre -> `BOOK_MAPPING.md` (racine, pas doublon `docs/`).

## Backtests obligatoires

Toute modification d'une strategie QC (main.py, parametres, periodes) **DOIT** etre validee par un backtest :

1. `create_compile` pour verifier la compilation
2. `create_backtest` pour lancer le backtest
3. `read_backtest` pour recuperer les metriques (Sharpe, CAGR, MaxDD)
4. Reporter les resultats dans le message de commit ET sur RooSync

**Changer une date ou un parametre sans backtest = travail invalide.**

## QC Cloud API - Acces via MCP Docker (OBLIGATOIRE)

**Methode d'acces** : Utiliser le MCP Docker `quantconnect/mcp-server` configure dans `.mcp.json` a la racine du projet.

- **NE PAS** utiliser de scripts Python avec l'API REST directe (provoque du rate-limiting et des erreurs d'auth)
- Le MCP gere l'authentification et le rate-limiting automatiquement
- Fichier de config : `.mcp.json` (deja dans `.gitignore`, JAMAIS committer)

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

### Rate limiting strict

MAX 10 appels/minute entre TOUS les agents. Avant de lancer un backtest, poster sur le dashboard. Un seul agent a la fois sur l'API QC.

### Pour retrouver les tokens

- Dashboard workspace CoursIA : section status
- Messages RooSync : tag `quantconnect` ou `TOKEN`
- En cas de token invalide : demander au coordinateur (ai-01) via RooSync

### Troubleshooting hash mismatch (incident 2026-04-05)

`~/.claude.json` (config globale Claude Code) contient parfois une section `mcpServers` par workspace qui **surcharge** `.mcp.json` local. Un ancien token cache la peut causer `Hash doesn't match` malgre le bon token dans `.mcp.json` projet.

Verifier dans cet ordre :

1. `~/.claude.json` section du workspace (config globale qui peut surcharger)
2. `.mcp.json` racine projet (config projet standard)
3. Token valide sur QC (tester via API directe Python)

**Fix recurrent** : supprimer l'entree `mcpServers.qc-mcp` de `~/.claude.json` pour que `.mcp.json` soit la seule source de verite.

## Organisations QC

QC est multi-tenant via les "organizations". Le cluster CoursIA utilise plusieurs orgs en parallele selon le contexte :

| Org | Tier | Usage | Backtest API |
|-----|------|-------|--------------|
| Research tier dedicated (default user) | Research (payant) | Deploiements de reference, Binance crypto data subscription, projets de developpement | Inclus |
| ESGF | Free/sponsored | Cours ESGF, masterclass Quant League | NON inclus |
| ECE | Free | Materiel pedagogique ECE | NON inclus |

**Regle d'or** : pour `create_backtest` programmatique via API, il faut **une org avec backtest API incluse** (research tier). Les orgs gratuites/educatives (ESGF, ECE) n'ont PAS l'API backtest — erreur recurrente : tenter `create_backtest` sur ESGF echoue silencieusement ou avec rate-limit. Verifier l'org cible avant de dispatcher.

### Switcher d'org

L'orga par defaut du MCP est definie par `QUANTCONNECT_ORGANIZATION_ID` dans `.mcp.json`. Deux options pour changer ponctuellement :

1. Editer `.mcp.json` env var et rebuild le MCP Docker container
2. Specifier `organizationId` explicitement par appel quand le tool MCP l'accepte

Note : `read_account` retourne TOUJOURS l'orga par defaut du USER_ID (la research tier quand non force par env var).

### Enumeration des orgs

Il n'existe pas d'endpoint `list_organizations`. La seule facon : `mcp__qc-mcp__list_projects` retourne les projets de toutes les orgs dont l'user est membre+ — agreger les `organizationId` distincts.

## Structure QC dans le depot

```
MyIA.AI.Notebooks/QuantConnect/
  Python/           # 27+ notebooks progressifs (QC-Py-01 a QC-Py-Cloud-XX)
  projects/          # ~50 strategies avec main.py + research.ipynb
  shared/            # Librairie utilitaire (backtestlib, indicators, plotting)
  ESGF-2026/         # Cours ESGF : exercices, templates, lean-workspace
  docs/              # Documentation technique (pas de coordination)
```

## QC Cloud Assistants — methode privilegiee Quantbook execution

QuantConnect expose 8 assistants integres (Conductor, Ideas, Research, Research Validation, Backtest, Paper Testing, Live Monitoring, Mia) accessibles via :

```
https://www.quantconnect.com/organization/<org_id>/assistants
```

**Le Research Assistant resout le probleme "Quantbook execution Windows local impossible"** : il execute les cells du notebook sur QC Cloud, itere automatiquement (edit, execute, fix, re-execute) jusqu'au succes, et les tokens consommes sont ceux de QC (pas Anthropic).

### Workflow Research Assistant (via Playwright)

1. Naviguer `https://www.quantconnect.com/organization/<org_id>/assistants`
2. Cliquer "New Task" sur **Research Assistant**
3. Creer tache avec prompt + `project_id` QC Cloud cible
4. Deployer : l'agent execute les cells du notebook
5. Lire les resultats dans **Tasks > Deployments > Completed**

### Limites et precautions

- **Validation cluster obligatoire post-deployment** : meme si Research Assistant claim "Sharpe 3.50", refaire en local par walk-forward 5-fold + multi-seed >=4 + transaction costs avant tout claim BEATS. Cf [.claude/rules/pr-review-discipline.md](../.claude/rules/pr-review-discipline.md) section C.
- **Cout QC tokens** : ne pas lancer 50 deployments en parallele sans verifier le burn rate
- **Eviter chevauchement agents** sur meme deployment (tokens dupliques) : coordination via dashboard avant lancement
- **Notebook output download** : Playwright snapshot ou API download artifact (workflow exact a documenter par usage)

### Cas d'usage privilegies

- Re-execution Quantbooks audit (cf section validation H.7 de CLAUDE.md)
- Validation algos QC Cloud avant import dans projects/
- Debugging multi-aller-retour des strategies en iteration

## Architecture composites (AlphaModel + MultiStrategyPCM)

Pattern standardise pour combiner plusieurs strategies dans un meme algo QC :

### Structure de fichiers (3 fichiers obligatoires)

- `main.py` : `QCAlgorithm` avec `set_alpha(CompositeAlphaModel(...))` + `set_portfolio_construction(MultiStrategyPCM(...))`
- `alpha_models.py` : une classe par alpha, chaque avec `self.name` et `source_model=self.name`
- `portfolio_construction.py` : `MultiStrategyPCM` avec `determine_target_percent` (PAS `create_targets`)

### MultiStrategyPCM — design

- Groupe les insights par `source_model`
- Alloue une slice de capital par strategie via dict `alpha_allocations`
- Supporte branches weight-hint ET equal-weight
- Utilise `set_rebalancing_func` pour le rebalance timing

### AlphaModel — regles

- DOIT avoir `self.name = "StrategyName"` dans `__init__`
- DOIT passer `source_model=self.name` a tous les `Insight.price()`
- DOIT filtrer par liste explicite de tickers (PAS `algorithm.securities.values()`)
- DOIT enregistrer les indicateurs dans `on_securities_changed` uniquement pour les tickers connus
- NE JAMAIS ajouter SPY comme equity benchmark dans l'univers (cause un leak si on itere `securities`)

### Composites realises — lecons (consolidation, pas snapshot)

| Composite | Allocation optimum | Sharpe | Lecon |
|-----------|--------------------|--------|-------|
| TrendWeather (TrendStocks + AllWeather) | T75 / AW25 | **1.15+** | Sweep monotone : plus de TrendStocks = meilleur Sharpe. ROC63 momentum weighting = gain majeur (0.79 -> 1.13) |
| FamaFrenchAllWeather | FF20 / AW80 | ~0.59 | Sweep monotone vers AllWeather : FamaFrench n'ajoute pas de diversification |
| MomentumRegime (SectorMomentum + RegimeSwitching) | ABANDONNE | max 0.24 | Probleme "double-defense" : les deux alphas defensifs sur les memes periodes |
| EMATrend (EMA-Cross + TrendStocks) | en cours | a venir | Overlap 5 tech stocks entre strategies (intentionnel) |

**Regle generale** : si le sweep d'allocation montre un comportement monotone (90/10 ou 10/90 gagne), le second alpha n'apporte pas de diversification — verifier qu'il occupe un quadrant de marche distinct du premier. Confirmation par la "decennie 2015+" : risk-off via TLT detruit la valeur, equity defensifs (XLP/IEF) > bonds long.

## Patterns universels (consolidation 30+ iterations strategies)

### Patterns confirmes (a ré-utiliser)

1. **Risk-adjusted momentum** (return/vol) > raw momentum
2. **Skip-month** (Jegadeesh 1990) : exclure le dernier mois — single-asset only
3. **TLT risk-off detruit la valeur** sur la decennie 2015+ : XLP/IEF > TLT
4. **Stop-loss -8% a -12%** : reduit MaxDD sans tronquer les reversions
5. **ATR sizing contre-productif** pour Donchian trend following
6. **Profit target 50%** pour options (TastyTrade) + VIX band 15-35
7. **Drift rebalancing 3%** > SMA overlay pour portfolios statiques
8. **Vol window 60d > 20d** pour covariance min-var
9. **Monthly + regime-change rebal > daily** : reduit trades 80%
10. **Trail breakeven 3% > 4%** pour BTC daily
11. **SMA50 >> SMA100 pour crypto** : SMA100 filtre les bonnes entrees bull
12. **SL 6% minimum sur BTC daily** : 5% trop serre
13. **OLS hedge ratio ne sauve pas pairs trading** : le probleme est les paires elles-memes
14. **Fix structural bugs >> academic improvements** : leverage/risk mgmt > signal refinement
15. **Diversifier instruments > relaxer seuils** : ajouter SPY+QQQ+IWM > baisser RSI threshold
16. **Composite via Algorithm Framework** = clean separation (AlphaModel + PCM + source_model)
17. **Biweekly rebalance est l'optimum** pour ML (weekly = trop de turnover, monthly = trop lent)
18. **Anti-overfitting** (max_depth 5, min_samples 10) critique pour tree models
19. **MLPClassifier/MLPRegressor** de sklearn marche bien sur QC Cloud
20. **Selective liquidation** reduit le turnover vs full portfolio wipe

### Anti-patterns critiques

- **SPY Parking** : investir en SPY quand inactif = beta loading deguise, le Sharpe monte mais l'alpha est nul
- **Backtests courts = overfitting** : Trend-Following Sharpe 2.157 (3 mois) -> 0.06 (7 ans)
- **ChatGPT/academic suggestions** : 3/4 degradent sur QC cloud. Ne garder que les fixes structurels
- **yfinance != QC cloud** : 6/12 research suggestions degradent en pratique
- **Crypto strategies pre-2018 unreliable** : 2017 bubble distortion
- **MaximumDrawdownPercentPortfolio** = JAMAIS sur multi-stock (liquidation simultanee)
- **1 param a la fois** : changer tout ensemble -> regression non-diagnostiquable
- **Raw momentum + min-var** : ne pas combiner (double penalisation)
- **Fake ML implementations** (hardcoded weights) : pires que real sklearn models
- **SMA100 filter trop restrictif pour mean reversion**
- **USD trend filter degrade FX momentum**

## Lecons techniques QC

- `read_file` AVANT `update_file_contents` : collaboration lock (expire vite)
- Options : `Resolution.MINUTE` sinon chain vide
- 1 seul backtest a la fois sur le node QC
- `algo.rsi(symbol, 14, Resolution.Hour)` ne marche pas dans `OnSecuritiesChanged` -> utiliser `register_indicator`
- `class X(QCAlgorithm, Mixin)` interdit (Python/CLR multiple inheritance)
- Binance CASH : `set_account_currency("USDT")` + `set_cash(10000)`
- Binance fees : preleve en BTC -> utiliser `portfolio[sym].quantity` pas `order qty`
- QC API auth : `SHA256(token:timestamp)` as hash, header `Timestamp`, Basic auth
- Chart API : data seulement pour backtests recents (~quelques heures)

## Historique training & checkpoints (preservation)

Toute l'historique des trainings ML/QC est preservee dans le depot et accessible a tous les agents, **PAS dans des memos chronologiques** :

| Source | Contenu |
|--------|---------|
| `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/REGISTRY.md` | Registry 70+ checkpoints, BEATS/FAIL/MIXED par symbole, stages -1/0/1/2, Anti-Bias audit |
| `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/CURRICULUM.md` | Plan global ML curriculum |
| `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/docs/M1..M17 + Stage2 + Stage7 + RECAP_KEEPERS_V2` | 35 fichiers de notes methodologiques par iteration |
| `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/docs/Curriculum_V2_Meta_Analysis.md` | Meta-analyse curriculum V2 |
| `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/results/*/checkpoint.jsonl` + `train.log` | 27 runs avec etat par combo et logs unbuffered (local, gitignored) |
| QC Cloud (MCP `list_projects` + `list_backtests` + `read_backtest`) | Sharpe/CAGR/MaxDD live de chaque iteration |
| [docs/ml-trading-state.md](ml-trading-state.md) | Lecons consolidees (vol vs direction, parcimonie, transaction costs, recommandations datasets) |

**Regle** : pas de duplication. Si tu veux ajouter une note sur une iteration training, vise `ML-Training-Pipeline/docs/M<N>_*.md` ou QC Cloud notes, pas un memo coordinateur. Pour une lecon trans-iteration : `docs/ml-trading-state.md`.

## Livre de reference

*Hands-On AI Trading* de Jared Broad — https://www.hands-on-ai-trading.com/

- Repo exemples : https://github.com/QuantConnect/HandsOnAITradingBook
- 22 exemples : Ch06 (19 strategies ML), Ch07 (1 RL hedging options), Ch08 (2 portfolio)
- Issues associees : #107 (mapping), #143 (implementation ML)

Le livre couvre les patterns ML actuels (RF, XGBoost, LSTM, CNN temporel, Chronos foundation models, RL hedging) avec exemples QC Cloud directement importables. Cf `MyIA.AI.Notebooks/QuantConnect/projects/` pour les imports realises.

## Reference QC partnership

QuantConnect (Jared Broad, CEO) sponsorise l'usage educatif via le code promo `education2025` (annule 100% du cout des seats Trading Firm). Architecture educative recommandee :

- Org sponsorisee = espace commun (algos d'exemple, evaluation collective, masterclass), avec coupon
- Comptes perso FREE pour les etudiants = suffisants pour term projects sur leur poste
- Cout minimum par org educative avec coupon : 14$/mois (1 noeud B2-8 backtest)

**Mecanique du coupon** : cart vide non accepte pour checkout, minimum 1 noeud compute requis. Rate limit API : 15 min de cooldown si on clique trop vite sur +/-. Le coupon couvre les seats Trading Firm (unlimited members), pas le compute.

**Hands-On AI Trading book** : recommandation officielle de Jared pour le cursus (cf section "Livre de reference").
