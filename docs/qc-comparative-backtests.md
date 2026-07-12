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

> Les métriques sont consignées après exécution du backtest (résultat brut vérifié `totalOrders > 0`, garde anti-exception silencieuse c.331).
>
> **† Capital initial différent** : PCAStatArbitrage tourne avec un capital initial ~$1.24 M contre ~$78–91 k pour les autres stratégies (défaut QC). Le `netProfitAbsolute` ($715 857) n'est donc **pas comparable** inter-stratégies — seul le pourcentage `totalNetProfit` (57.664 %) l'est.

## Lecture comparative (5 stratégies)

Les cinq stratégies validées affichent trois profils distincts :

- **Trois stratégies tactiques (DualMomentum, RiskParity, TrendFollowing) : Sharpe ~0.35–0.36** — rentabilité ajustée du risque modeste, dans la plage attendue pour une allocation tactique ETF multi-actifs (référence : Sharpe SPY long-terme ~0.4–0.5). Étonnamment, ces trois stratégies convergent vers la même valeur de Sharpe malgré des logiques de signaux différentes.
- **AdaptiveConformalRisk se détache : Sharpe 0.449, CAGR 11.5 %, Net +139 %** — le seul membre de la cohorte dont le Sharpe **dépasse nettement la bande de référence ~0.36**. Le Probabilistic Sharpe Ratio (2.509 %) est aussi nettement supérieur aux autres (<1 %). Ce surcroît de rentabilité s'accompagne d'un drawdown plus profond (22.5 % vs 14.9–18.4 %) — un profil risque/rendement plus agressif, caractéristique d'une stratégie à risque adaptatif (conformal risk control).
- **PCAStatArbitrage sous-performe nettement : Sharpe 0.204, CAGR 6.7 %, drawdown 31.8 %** — le **plus faible rendement ajusté du risque de la cohorte** et le **drawdown le plus profond**, malgré le nombre d'ordres le plus élevé (2312, ~2× ACR, ~7× les tactiques). Leçon pédagogique honnête : la sophistication conceptuelle (PCA statistical arbitrage, signaux mean-reversion à haute fréquence) **ne se traduit pas en alpha** sur cette période — la complexité du modèle n'est pas un gage de performance. Le PSR (0.497 %) est dans la moyenne basse.
- **Drawdown** : PCAStatArbitrage (31.8 %) > AdaptiveConformalRisk (22.5 %) > RiskParity (18.4 %) > DualMomentum/TrendFollowing (14.9–15.0 %). Les deux stratégies « à risque adaptatif / quantitatif » (PCA, ACR) maximisent l'un le rendement (ACR), l'autre le drawdown (PCA) — sans WalkForward on ne peut départager skill de chance.
- **Net Profit (pourcentage, comparable)** : AdaptiveConformalRisk (139 %) > TrendFollowing (102 %) > DualMomentum (76 %) > RiskParity (75 %) > **PCAStatArbitrage (58 %)**. Le `netProfitAbsolute` n'est **pas** comparable inter-stratégies (cf † capital initial).
- **Aucune exception silencieuse** : 309–2312 ordres confirment un rebalancement actif (vs le piège 0-trade de c.331, désormais détecté par le garde).

**Verdict honnête (G.2)** : NO BEATS manifesto reste l'interprétation prudente pour les 3 stratégies tactiques (Sharpe ~0.36 = plage benchmark) et **s'impose d'autant plus pour PCAStatArbitrage** (Sharpe 0.204 = **sous le benchmark**, drawdown maximal). **AdaptiveConformalRisk reste le seul candidat alpha prometteur** (Sharpe 0.449 + PSR 2.5 % vs ~0.36 + <1 % pour le reste) mais ce verdict nécessite, avant d'être affirmé, une validation multi-seed / walk-forward (cf [pr-review-discipline.md](../.claude/rules/pr-review-discipline.md) §C) pour exclure que l'écart ne soit un artefact du régime de la période. La cohorte sert de **baseline de référence** pour la dernière stratégie restante (robustness-c2-regime).

## Stratégies en file (cycles suivants)

Backtests restants à lancer sur la cohorte, pour étendre la comparative :

- `1630-robustness-c2-regime` (33280244)

## Voir aussi

- [docs/qc/quantconnect.md](qc/quantconnect.md) — structure QC, MCP, livre de référence
- [`.claude/rules/sota-not-workaround.md`](../.claude/rules/sota-not-workaround.md) — quantbooks via QC Cloud
- Mémoire po-2026 `qc-mcp-lite-backtest-setup.md` — setup wrapper Python
