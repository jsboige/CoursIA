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

> Les métriques sont consignées après exécution du backtest c.336 (résultat brut vérifié `totalOrders > 0`).

## Lecture comparative (3 stratégies)

Les trois stratégies validées (DualMomentum, RiskParity, TrendFollowing) affichent un profil **modéré et cohérent** :

- **Sharpe ~0.35–0.36** — rentabilité ajustée du risque modeste mais positive, sur la plage attendue pour une allocation tactique ETF multi-actifs (référence : Sharpe SPY long-terme ~0.4–0.5). Étonnamment, les trois stratégies convergent vers la même valeur de Sharpe malgré des logiques de signaux très différentes.
- **CAGR** : DualMomentum et RiskParity ~8.3–8.4 %, TrendFollowing 7.3 % (légèrement inférieur).
- **Drawdown 14.9–15.0 % (DualMomentum, TrendFollowing) vs 18.4 % (RiskParity)** — RiskParity paie sa diversification constante par un drawdown plus profond ; les stratégies momentum/trend contrôlent mieux le risque extrême via leurs stops.
- **Net Profit : TrendFollowing (102.2 %, $83 495) > DualMomentum (76.1 %) > RiskParity (74.8 %)** — TrendFollowing, sur la période la plus longue (2516 jours tradeables vs 1761), surpasse en absolu tout en restant dans la même bande de Sharpe.
- **Aucune exception silencieuse** : 309–453 ordres confirment un rebalancement actif (vs le piège 0-trade de c.331, désormais détecté par le garde).

**Verdict honnête (G.2)** : NO BEATS manifesto sur les trois stratégies — performances dans la plage du benchmark (Sharpe ~0.36, pas d'alpha manifeste au-delà du buy-and-hold SPY ajusté du risque). La cohorte sert de **baseline de référence** pour comparer les stratégies suivantes (AdaptiveConformalRisk, PCAStatArbitrage) et détecter un éventuel alpha.

## Stratégies en file (cycles suivants)

Backtests restants à lancer sur la cohorte, pour étendre la comparative :

- `1630-baseline-AdaptiveConformalRisk` (33278416)
- `1630-baseline-PCAStatArbitrage` (33281920)
- `1630-robustness-c2-regime` (33280244)

## Voir aussi

- [docs/qc/quantconnect.md](qc/quantconnect.md) — structure QC, MCP, livre de référence
- [`.claude/rules/sota-not-workaround.md`](../.claude/rules/sota-not-workaround.md) — quantbooks via QC Cloud
- Mémoire po-2026 `qc-mcp-lite-backtest-setup.md` — setup wrapper Python
