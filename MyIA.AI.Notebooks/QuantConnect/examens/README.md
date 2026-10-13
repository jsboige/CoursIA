# Examens — Trading Algorithmique (5BD ALT1)

Sujets de rattrapage 2024 et 2025 du cours « Introduction au Trading Algorithmique », avec leurs corrigés. Publication autorisée par le mainteneur (28/09/2026) : ces sujets ne seront plus réutilisés en examen. Importés du gisement Drive (`G:\Mon Drive\MyIA\IA\Rattrapages\Trading\`) sous forme de sources LaTeX — les PDF compilés, les `.docx` et les fichiers de build (`aux/log/fls/fdb_latexmk`) restent sur le Drive.

| Sujet | Énoncé | Corrigé |
|---|---|---|
| Rattrapage 2024 | [rattrapage-2024.tex](rattrapage-2024.tex) | [rattrapage-2024-corrige.tex](rattrapage-2024-corrige.tex) — bonnes réponses préfixées `(CORRECT)` |
| Rattrapage 2025 | [rattrapage-2025.tex](rattrapage-2025.tex) | [rattrapage-2025-corrige.tex](rattrapage-2025-corrige.tex) — bonnes réponses surlignées `\hl{...}` |

## Rattachement aux notebooks de la série

| Notion traitée dans les sujets | Notebook d'accueil |
|---|---|
| Ordres au marché / à cours limité, exécution, slippage | [`Python/QC-Py-09-Order-Types.ipynb`](../Python/QC-Py-09-Order-Types.ipynb) |
| Sélection d'univers, filtrage d'actifs | [`Python/QC-Py-05-Universe-Selection.ipynb`](../Python/QC-Py-05-Universe-Selection.ipynb) |
| Risque, diversification, pondération, rebalancement | [`Python/QC-Py-10-Risk-Portfolio-Management.ipynb`](../Python/QC-Py-10-Risk-Portfolio-Management.ipynb) |
| Backtest : métriques de performance (Sharpe, alpha, drawdown) | [`Python/QC-Py-12-Backtesting-Analysis.ipynb`](../Python/QC-Py-12-Backtesting-Analysis.ipynb) |
| Biais de survie, validité du backtest, surapprentissage du test | [`Python/QC-Py-12b-Backtest-Validity.ipynb`](../Python/QC-Py-12b-Backtest-Validity.ipynb) |
| Stratégies multi-actifs, paires, arbitrage | [`Python/QC-Py-08-Multi-Asset-Strategies.ipynb`](../Python/QC-Py-08-Multi-Asset-Strategies.ipynb) |
| Indicateurs techniques, scalping, HFT | [`Python/QC-Py-11-Technical-Indicators.ipynb`](../Python/QC-Py-11-Technical-Indicators.ipynb) |
| API Lean (`SetStartDate`, `OnData`, warm-up) — section pratique | [`Python/QC-Py-02-Platform-Fundamentals.ipynb`](../Python/QC-Py-02-Platform-Fundamentals.ipynb) et [`GETTING-STARTED.md`](../GETTING-STARTED.md) |
| Analyse technique (prix/volume) en théorie générale | couverte par les indicateurs ci-dessus ; pas de notebook dédié « analyse technique » — signalé, sans place inventée |

## Notes d'import (28/09/2026)

- Le sujet 2025 source portait le titre erroné « Corrigé du QCM de Rattrapage 2025 » (copie dé-surlignée du corrigé) : titre corrigé en « QCM de Rattrapage 2025 » à l'import, et BOM UTF-8 supprimé. Le corps est inchangé.
- Le sujet 2025 conserve la ligne d'instructions « La bonne réponse est surlignée en vert » héritée du corrigé — sans effet sur l'énoncé (aucune réponse n'y figure) ; signalé plutôt que réécrit.
- La banque de QCM transverse (chapitres IA, issue #18223) vit dans `cross-series/qcm/` — ces sujets Trading sont distincts (questions ouvertes + QCM Lean) et restent dans leur série d'accueil.
