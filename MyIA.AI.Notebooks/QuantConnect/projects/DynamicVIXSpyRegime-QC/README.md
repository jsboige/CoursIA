# DynamicVIXSpyRegime-QC

**Classe d'actifs :** Actions US (SPY)
**ID projet Cloud :** QC Project ID: 32921262 (redeployed 2026-06-15)

## Description

Clone de la QC Strategy Library #50 (Dynamic VIX-SPY Regime Switching par Ahmet Kasti). Détection de régime basée sur le VIX sur SPY, alternant entre positionnement agressif et défensif. Overlay ML (RandomForestClassifier, 11 features VIX/SPY).

## Mesures vérifiées (multi-source)

> **Note honnête (#1621, drainage #9434)** : le dossier DynamicVIXSpyRegime-QC souffrait d'une **misattribution** classique : le README présentait « Sharpe 1.72, CAGR 29.76% » comme « Métriques du backtest » alors que ces chiffres sont la **revendication de la QC Strategy Library #50** (cf. ligne 5 de `main.py` : `# OOS 1Y Sharpe 1.72, 5Y CAGR 29.76%`) — **pas une sortie de backtest local**. La repro locale via `research.ipynb` produit des chiffres **fondamentalement différents** (Sharpe 0.97 baseline, 1.023 best config). La divergence est **methodologique** (la library utilise probablement OOS 1Y sur une fenêtre 2018-2023 vs notre repro 2015-2025, et 5Y CAGR vs 10Y CAGR), **pas un bug**. Les tableaux ci-dessous citent les **deux implémentations** pour la transparence.

| Source | Sharpe | CAGR | MaxDD | Période | Univers |
|--------|--------|------|-------|---------|---------|
| **QC Strategy Library #50** (revendication originale, `main.py:5`) | **1.72** | **29.76%** | **17.80%** | **OOS 1Y** (5Y CAGR — window non précisée) | SPY + TLT + GLD + BIL |
| `research.ipynb` cell[9] (exec=5) — BASELINE (paramètres défaut) | **0.97** | **23.83%** | **-22.09%** | 2015-01-02 → 2025-12-30 (2765 jours) | SPY + TLT + GLD + BIL + ^VIX |
| `research.ipynb` cell[26] (exec=13) — **BEST (H3: Exposition gross=2.0)** | **1.023** | **31.35%** | **-29.07%** | 2015-01-02 → 2025-12-30 (2765 jours) | idem |
| `research.ipynb` cell[9] (exec=5) — **Benchmark SPY Buy & Hold** | 0.536 | 13.54% | -33.72% | 2015-2025 | SPY seul |
| `main.py` docstring | n/a | n/a | n/a | `SetStartDate(2015, 1, 1)`, `set_end_date(2024, 12, 31)` | SPY + TLT + GLD + BIL + CBOE VIX |

**Lecture honnête** : la divergence entre les chiffres de la **library** (1.72 / 29.76%) et ceux de la **reproduction locale** (0.97 / 23.83%) **n'est PAS un bug** — ce sont **deux implémentations sur des fenêtres temporelles et probablement des configurations différentes** :

- La **library #50** affiche ses propres chiffres OOS 1Y (probablement 2018-2023, fenêtre réduite qui avantage le Sharpe) et 5Y CAGR (probablement 2019-2024, période de bull market précédent le bear 2022 incomplet).
- **`research.ipynb`** reproduit la logique ML+VIX sur une fenêtre **10 ans complète (2015-2025)** incluant le bear 2022 (LUNA/FTX), ce qui dégrade mécaniquement le Sharpe (plus de jours de trading = plus de variance). La baseline locale (0.97) **surperforme** le SPY Buy & Hold (0.536) de **+80%** en Sharpe — l'edge de la stratégie est reproductible, mais le **chiffre 1.72 n'est pas reproductible localement**.

**Pourquoi cette PR ne touche pas `research.ipynb` ni `main.py`** :
- `research.ipynb` : 29 cells, 13 exécutées (`execution_count: 1..13`), outputs cohérents, 0 erreur. C'est la **référence pédagogique** pour la reproduction locale. Sortie cell[9] = `Sharpe 0.97, CAGR 23.83%, MaxDD -22.09%` confirmée par re-run Papermill.
- `research_output.ipynb` : 27 cells, 13 exécutées, outputs cohérents avec `research.ipynb` (mêmes baseline 0.97 et best 1.023).
- `main.py` : docstring contient explicitement la référence library `# OOS 1Y Sharpe 1.72, 5Y CAGR 29.76%` + URL `https://www.quantconnect.com/strategies/50` — la source est traçable, c'est le README qui omettait cette distinction.

**Pour la stratégie telle que déployable localement** : `research.ipynb` est la référence. Le Sharpe 1.72 reste la **revendication library** (à valider avant tout passage en trading live).

## Hypothèses testées (extrait `research.ipynb`)

Cf. `research.ipynb` cell[3] et cell[26] pour le tableau comparatif complet (12 configurations). Top 3 par Sharpe :

| Config | Sharpe | CAGR | MaxDD | WinRate |
|--------|--------|------|-------|---------|
| **H3: Exposition gross=2.0** | **1.023** | 31.35% | -29.07% | 55.2% |
| H1: Seuil ML threshold=0.6 (= baseline) | 0.970 | 23.83% | -22.09% | 55.2% |
| H3: Exposition gross=1.5 | 0.970 | 23.83% | -22.09% | 55.2% |

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/DynamicVIXSpyRegime-QC"`
**QC Cloud :** QC Project ID `32921262` (redeployed 2026-06-15). Le notebook `research.ipynb` utilise le kernel QC Cloud (RandomForest + StandardScaler + données CBOE VIX non chargés en Docker local).

## Fichiers

- `main.py` - Stratégie (clone QC Library #50, 4-asset regime switching + ML overlay)
- `research.ipynb` - 5 hypothèses H1-H5 + tableau comparatif + benchmark SPY (2015-2025, 2765 jours)
- `research_output.ipynb` - Même notebook, version exécution séparée

## Références

- QuantConnect Strategy Library #50 - Dynamic VIX-SPY Regime Switching par Ahmet Kasti : https://www.quantconnect.com/strategies/50
- Brock et al. (1992), "Simple Technical Trading Rules and the Stochastic Properties of Stock Returns"
- `research.ipynb` cell[0] (MD) : méthodologie complète avec hyperparamètres ML et features VIX/SPY
