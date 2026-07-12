# Backtests comparatifs QuantConnect — cohorte `1630-*-aligned`

> Epic [#1621](../MyIA.AI.Notebooks/QuantConnect/) (Consolidation QC/Trading) · cohorte de stratégies `1630-*` alignées pour l'évaluation comparative.
>
> Ce document consolide les métriques de backtest des stratégies de la cohorte `1630-*-aligned` (et baselines associées) exécutées via **QC Cloud** (MCP `qc-mcp-lite`), afin d'établir une référence comparative reproductible. Les backtests sont lancés depuis la lane po-2026 (creds `QC_API_*` locales).

## Méthodologie

- **Exécution** : QuantConnect Cloud (API REST via `scripts/qc-mcp-lite/server.py`). Aucune exécution locale fictive (règle [sota-not-workaround.md](../.claude/rules/sota-not-workaround.md) : un quantbook s'exécute **via QC Cloud**).
- **Garde anti-exception silencieuse** (leçon c.331) : chaque backtest est validé sur le payload brut — `totalOrders > 0` requis. Un backtest « Completed » avec 0 ordres indique une exception silencieuse dans `rebalance()` (scheduled-event qui ne stoppe pas le run) et est **rejeté**, pas consigné comme métrique valide.
- **Période** : backtests multi-années sur univers SPY/ETF (dates exactes par stratégie dans QC Cloud).
- **Coûts de transaction** : inclus par défaut par le moteur QC (fill slippage + fees).

## Métriques comparatives

| Stratégie | Projet QC | Cycle | Total Orders | Sharpe | CAGR | Max Drawdown | Net Profit | Statut |
|-----------|-----------|-------|--------------|--------|------|--------------|------------|--------|
| `1630-DualMomentum-aligned` | 33286487 | c.332 | 318 | 0.350 | 8.413 % | 14.900 % | 76.088 % ($59 745) | OK |
| `1630-RiskParity-aligned` | 33286158 | c.332 | 309 | 0.361 | 8.303 % | 18.400 % | 74.841 % ($60 837) | OK |
| `baseline-clone-TrendFollowing-repo-1630` | 33078355 | c.336 | 453 | 0.360 | 7.290 % | 15.000 % | 102.225 % ($83 495) | OK |
| `1630-baseline-AdaptiveConformalRisk` | 33278416 | c.338 | 1079 | 0.449 | 11.522 % | 22.500 % | 139.392 % ($126 394) | OK |
| `1630-baseline-PCAStatArbitrage` | 33281920 | c.339 | 2312 | 0.204 | 6.716 % | 31.800 % | 57.664 % ($715 857 †) | OK |
| `1630-robustness-c2-regime` | 33280244 | c.340 | 5715 | 0.574 | 11.947 % | 18.600 % | 120.480 % ($105 403) | OK |

> Les métriques sont consignées après exécution du backtest (résultat brut vérifié `totalOrders > 0`, garde anti-exception silencieuse c.331).
>
> **† Capital initial différent** : PCAStatArbitrage tourne avec un capital initial ~$1.24 M contre ~$78–91 k pour les autres stratégies (défaut QC). Le `netProfitAbsolute` ($715 857) n'est donc **pas comparable** inter-stratégies — seul le pourcentage `totalNetProfit` (57.664 %) l'est.

## Lecture comparative (6 stratégies)

Les six stratégies validées affichent quatre profils distincts :

- **Trois stratégies tactiques (DualMomentum, RiskParity, TrendFollowing) : Sharpe ~0.35–0.36** — rentabilité ajustée du risque modeste, dans la plage attendue pour une allocation tactique ETF multi-actifs (référence : Sharpe SPY long-terme ~0.4–0.5). Étonnamment, ces trois stratégies convergent vers la même valeur de Sharpe malgré des logiques de signaux différentes.
- **robustness-c2-regime prend la tête : Sharpe 0.574, PSR 7.365 %, drawdown 18.6 %, Net +120 %** — le **meilleur profil risque/rendement de la cohorte**, surpassant AdaptiveConformalRisk sur les trois axes ajustés : Sharpe supérieur (0.574 vs 0.449), PSR ~3× supérieur (7.4 % vs 2.5 %), **et drawdown plus contenu** (18.6 % vs 22.5 %). C'est le seul cas de la cohorte où une rentabilité élevée (CAGR 11.9 %) s'accompagne d'un risque **inférieur** aux stratégies agressives — la signature d'un design *regime-aware* (filtrage des régimes défavorables) qui réussit sur cette période. Le nombre d'ordres (5715, le plus élevé) confirme un rebalancement actif haute-fréquence.
- **AdaptiveConformalRisk (2ᵉ) : Sharpe 0.449, PSR 2.5 %, drawdown 22.5 %, Net +139 %** — toujours au-dessus de la bande benchmark, mais désormais devancée. Conserve le **rendement absolu le plus élevé** (139 %) au prix d'un drawdown profond.
- **PCAStatArbitrage sous-performe nettement : Sharpe 0.204, CAGR 6.7 %, drawdown 31.8 %** — le **plus faible rendement ajusté du risque de la cohorte** et le **drawdown le plus profond**, malgré un nombre d'ordres élevé (2312). Leçon pédagogique honnête : la sophistication conceptuelle (PCA statistical arbitrage, signaux mean-reversion à haute fréquence) **ne se traduit pas en alpha** sur cette période — la complexité du modèle n'est pas un gage de performance.
- **Drawdown** : PCAStatArbitrage (31.8 %) > AdaptiveConformalRisk (22.5 %) > robustness-c2-regime (18.6 %) ≈ RiskParity (18.4 %) > DualMomentum/TrendFollowing (14.9–15.0 %). Notable : robustness-c2-regime combine **Sharpe le plus élevé** avec un drawdown **modéré** — le meilleur couple risque/rendement.
- **Net Profit (pourcentage, comparable)** : AdaptiveConformalRisk (139 %) > robustness-c2-regime (120 %) > TrendFollowing (102 %) > DualMomentum (76 %) > RiskParity (75 %) > **PCAStatArbitrage (58 %)**. Le `netProfitAbsolute` n'est **pas** comparable inter-stratégies pour PCA (cf † capital initial).
- **Aucune exception silencieuse** : 309–5715 ordres confirment un rebalancement actif (vs le piège 0-trade de c.331, désormais détecté par le garde).

**Verdict honnête (G.2)** : NO BEATS manifesto reste l'interprétation prudente pour les 3 stratégies tactiques (Sharpe ~0.36 = plage benchmark) et **s'impose d'autant plus pour PCAStatArbitrage** (Sharpe 0.204 = **sous le benchmark**, drawdown maximal). **robustness-c2-regime est désormais le candidat alpha principal** (Sharpe 0.574 + PSR 7.4 % + drawdown contenu 18.6 %), devançant AdaptiveConformalRisk (0.449 + 2.5 %). Ces deux candidats nécessitent toutefois, avant d'être affirmés, une validation **multi-seed / walk-forward** (cf [pr-review-discipline.md](../.claude/rules/pr-review-discipline.md) §C) pour exclure que l'écart ne soit un artefact du régime de la période — c'est précisément le test que *robustness-c2-regime* est censé passer, ce qui rend une validation walk-forward multi-régimes d'autant plus décisive pour confirmer ou infirmer sa première place.

## Cohorte complète — suite

Les 6 stratégies `1630-*-aligned` de la cohorte sont désormais backtestées et consignées (cycle c.340). La **suite logique** est la validation walk-forward multi-régimes des deux candidats alpha (`robustness-c2-regime`, `AdaptiveConformalRisk`) — cf verdict honnête ci-dessus — pour confirmer ou infirmer leur première place hors de la période in-sample (cf [pr-review-discipline.md](../.claude/rules/pr-review-discipline.md) §C).

## Voir aussi

- [docs/qc/quantconnect.md](qc/quantconnect.md) — structure QC, MCP, livre de référence
- [`.claude/rules/sota-not-workaround.md`](../.claude/rules/sota-not-workaround.md) — quantbooks via QC Cloud
- Mémoire po-2026 `qc-mcp-lite-backtest-setup.md` — setup wrapper Python
