# LeveragedETFMomentum-QC

**Classe d'actifs :** Actions US (ETFs à effet de levier)
**ID projet Cloud :** QC Project ID: 29687520 (cloné 2026-04-04, **non redéployé en QC Cloud**)

> 🇬🇧 **English version** : voir [`README.en.md`](README.en.md) (golden set préservé, original avant bascule FR).

## Description

Clone de la **QC Strategy Library #60** (*Leveraged ETF Momentum Allocator* par **Grant Forman**). Stratégie de momentum sur ETFs à effet de levier avec rotation agressive entre SPY/QQQ/TQQQ/UVXY/TECL/SPXL/SQQQ/TECS/BSV selon conditions RSI + SMA régime (bull > 200 SMA, bear/volatility branches).

## Mesures vérifiées (multi-source)

> **Note honnête (#1621, drainage #9434)** : le dossier LeveragedETFMomentum-QC souffrait d'une **misattribution library-claim** : le README présentait « Sharpe 1.80, CAGR 101.03%, MaxDD 47.50% » comme « Backtest Metrics » alors que ces chiffres sont la **revendication de la QC Strategy Library #60** (cf. `main.py:6` : `# OOS 1Y Sharpe 1.80, 5Y CAGR 101.03%, 5Y Drawdown 47.50%, 54% Win Rate`) — **PAS une sortie de backtest local**. Le dossier **ne contient pas de `research.ipynb`** contrairement à d'autres clones (#9530 DualMomentum, #9537 EMA-Cross-Crypto, #9542 DynamicVIXSpyRegime-QC) — la reproduction locale n'a **pas eu lieu**. Les tableaux ci-dessous citent la **library claim avec sa traçabilité explicite** + un **drapeau SUSPECT overfit haussier** (lev. ETFs + rotation agressive sur fenêtre 2015-2024 incluant 85% bull market).

| Source | Sharpe | CAGR | MaxDD | Période | Univers |
|--------|--------|------|-------|---------|---------|
| **QC Strategy Library #60** (revendication originale, `main.py:6`) | **1.80** | **101.03%** | **47.50%** | **OOS 1Y** (5Y CAGR — fenêtre non précisée) | 9 ETFs à effet de levier (SPY/QQQ/TQQQ/UVXY/TECL/SPXL/SQQQ/TECS/BSV) |
| `main.py` docstring (`main.py:6-8`) | n/a | n/a | n/a | `SetStartDate(2015, 1, 1)`, `set_end_date(2024, 12, 31)` | idem |
| Repro locale | **NON REPRODUITE** | n/a | n/a | n/a | n/a |

**Lecture honnête — SUSPECT OVERFIT HAUSSIER (c.1277-L4 ★★)** : un CAGR de **101.03 %** sur 5 ans avec un Sharpe de 1.80 sur des **ETFs à effet de levier** (TQQQ = 3× QQQ, TECL = 3× Technology, SPXL = 3× S&P500) **rotant aggressivement** entre Bull (TQQQ) et Bear (UVXY/TECS/SQQQ) est **structurellement aligned sur un bull market**. La fenêtre 2015-2024 inclut :
- 6 années de bull market quasi-continue (2015-2019, 2020-2021, 2023-2024) où le levier triple TQQQ a multiplié les gains
- Seulement 2 bear quarters notables (Q4 2018, Q1 2020) et le drawdown 2022 (peu profond pour le QQQ/TQQQ)
- **Un vrai bear sustained (genre 2008-2009 ou 2022 inflation bear)** pourrait produire un MaxDD **largement supérieur à 47.50%** car le levier triple amplifie les baisses

Cf. **c.1277-L4 ★★** (AllWeather) : un Sharpe > 2× la base sur SMA crossover = SUSPECT overfit structurel sur univers uptrend. Ici la même mécanique s'applique : la **stratégie est rentable sur le backtest mais vulnérable à un vrai bear sustained** (lev. ETF decay + bear whipsaw).

**Vérification de la library claim** : la QC Strategy Library #60 (Grant Forman, `https://www.quantconnect.com/strategies/60`) est une stratégie publique à visée **pédagogique** sur la mécanique de **rotation sectorielle conditionnelle** — **PAS un signal de déploiement live**. Le `QC Project ID 29687520` (cloné 2026-04-04) **n'a jamais été déployé en QC Cloud** (README legacy confirmait « Copy files to a new QC Cloud project to run »).

**Reproductibilité** : la library claim est **reproductible localement** via Lean CLI (`lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/LeveragedETFMomentum-QC"`) — les 9 tickers sont des ETFs liquides courant 2015-2024. **Cette PR n'exécute pas la repro locale** (hors scope, future action séparée) ; la note « Metrics from original library, not locally reproduced » du README legacy reste vraie.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/LeveragedETFMomentum-QC"`
**QC Cloud :** QC Project ID `29687520` cloné 2026-04-04, **non redéployé en Cloud**. Copier `main.py` dans un nouveau projet QC Cloud pour exécuter. Note : la repro locale Docker Lean devrait reproduire la library claim (avec dividendes/frais) — variations attendues ~10-20% sur MaxDD, ~5-15% sur CAGR (frais Interactive Brokers + dividendes).

## Fichiers

- `main.py` - Stratégie (clone QC Strategy Library #60, conditional sector rotation sur 9 ETFs à effet de levier)

## Références

- QuantConnect Strategy Library #60 — *Leveraged ETF Momentum Allocator* par Grant Forman : `https://www.quantconnect.com/strategies/60`
- `main.py:6-8` docstring : source library + URL + QC Project ID 29687520 + auteur Grant Forman
- c.1277-L4 ★★ (AllWeather) — SUSPECT overfit sur SMA crossover > 2× base ; même mécanique applicable ici pour lev. ETFs en bull-only backtest
- c.1281-L1 ★★ (DynamicVIXSpyRegime-QC) — pattern library claim misattribution
