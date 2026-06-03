# Classification des Notebooks QuantConnect (QC-Py-01 a 04)

**Date**: 2026-05-04
**Auteur**: Hermes Agent (automated analysis)
**Scope**: Determiner quels notebooks sont executables localement vs necessitent QuantConnect Cloud

---

## Methodologie

Chaque cellule de code a ete classee selon 3 categories :
- **LOCAL** : utilise uniquement Python stdlib, pandas, numpy, matplotlib, sklearn
- **QC CLOUD** : importe ou utilise QuantBook, QCAlgorithm, AlgorithmImports, ou toute API QuantConnect
- **AMBIGU** : dependencies incertaines

Indicateurs QC Cloud detectes : `QuantBook`, `qb.`, `QCAlgorithm`, `AlgorithmImports`, `QuantConnect`, `AddEquity`, `AddCrypto`, `AddForex`, `History(`, `SetStartDate`, `SetCash`, `LEAN`, `dotnet`, `conda install`

---

## Resultats par Notebook

### QC-Py-01-Setup.ipynb

| Metrique | Valeur |
|----------|--------|
| Cellules code totales | 7 |
| LOCAL | 3 |
| QC CLOUD | 4 |
| AMBIGU | 0 |
| **Verdict** | **NECESSITE QC CLOUD** |

**Details des cellules**:
- `[0]` QC CLOUD - Import `from AlgorithmImports import *` + `QuantConnect`
- `[1]` QC CLOUD - Explication de l'architecture LEAN
- `[2]` QC CLOUD - Verification installation `quantconnect`
- `[3]` QC CLOUD - Installation packages via LEAN
- `[4]` LOCAL - Commande shell commentee (`lean project-create`)
- `[5]` LOCAL - Commande shell commentee (`lean data download`)
- `[6]` LOCAL - Commande shell commentee (`lean backtest`)

**Note**: Les 3 cellules LOCAL sont des commandes shell entourees de commentaires (`#`). Elles ne produisent aucun output si executees en Python.

---

### QC-Py-02-Platform-Fundamentals.ipynb

| Metrique | Valeur |
|----------|--------|
| Cellules code totales | 5 |
| LOCAL | 0 |
| QC CLOUD | 5 |
| AMBIGU | 0 |
| **Verdict** | **NECESSITE QC CLOUD (100%)** |

**Details des cellules**:
- `[0]` QC CLOUD - Import `AlgorithmImports` + classe `FirstAlgorithm(QCAlgorithm)`
- `[1]` QC CLOUD - Override `Initialize()` avec `SetStartDate`, `SetCash`, `AddEquity`
- `[2]` QC CLOUD - Override `OnData()` avec logique de trading
- `[3]` QC CLOUD - Backtest manuel avec `SetStartDate`, `AddEquity`, `History`
- `[4]` QC CLOUD - Classe complete `MovingAverageCrossAlgorithm(QCAlgorithm)`

**Note**: 100% du code depend de l'ecosysteme QC (QCAlgorithm, Lean engine).

---

### QC-Py-03-Data-Management.ipynb

| Metrique | Valeur |
|----------|--------|
| Cellules code totales | 10 |
| LOCAL | 0 |
| QC CLOUD | 10 |
| AMBIGU | 0 |
| **Verdict** | **NECESSITE QC CLOUD (100%)** |

**Details des cellules**:
- `[0]` QC CLOUD - Import + `AddEquity("SPY")` dans `Initialize()`
- `[1]` QC CLOUD - Acces aux donnees via `self.Securities`
- `[2]` QC CLOUD - Filtres univers + `AddEquity` conditionnel
- `[3]` QC CLOUD - Consolidateurs de donnees (`Consolidate`)
- `[4]` QC CLOUD - Indicateurs techniques QC (`SMA`, `EMA`)
- `[5]` QC CLOUD - Slices et subscription managers
- `[6]` QC CLOUD - `History()` avec resolutions multiples
- `[7]` QC CLOUD - Resolution et fill forwarding
- `[8]` QC CLOUD - Donnees custom / universe selection
- `[9]` QC CLOUD - Resolutions dans `OnData()`

**Note**: 100% du code depend de QCAlgorithm et de l'engine LEAN.

---

### QC-Py-04-Research-Workflow.ipynb

| Metrique | Valeur |
|----------|--------|
| Cellules code totales | 25 |
| LOCAL | 19 |
| QC CLOUD | 5 |
| AMBIGU | 1 |
| **Verdict** | **NECESSITE QC CLOUD (chaines de dependance)** |

**Details des cellules QC CLOUD (bloquantes)**:
- `[0]` QC CLOUD - `from QuantConnect import *` + `QuantConnect.Research`
- `[1]` QC CLOUD - `qb = QuantBook()`
- `[2]` QC CLOUD - `qb.AddEquity("SPY")`, `qb.AddEquity("AAPL")`
- `[3]` QC CLOUD - `qb.History(...)` - **produit la variable `history` utilisee par TOUTES les cellules suivantes**
- `[19]` QC CLOUD - Classe `ResearchStrategy(QCAlgorithm)` pour backtest

**Chaines de dependance**:
Les 19 cellules LOCAL et 1 AMBIGU dependent de la variable `history` produite par la cellule [3] (`qb.History()`). Sans QuantBook, aucune de ces cellules ne peut s'executer car elles manipulent des DataFrames QC.

**Note**: Ce notebook est le meilleur candidat pour une execution locale *si* on remplace les cellules QC Cloud par un stub qui genere un DataFrame pandas equivalent (telechargement via yfinance par exemple).

---

## Synthese

| Notebook | Total Cells | QC Cloud | Local | Verdict | Executable localement? |
|----------|-------------|----------|-------|---------|----------------------|
| QC-Py-01-Setup | 7 | 4 (57%) | 3 (43%) | MIXTE | **NON** (cells LOCAL = commentaires) |
| QC-Py-02-Platform-Fundamentals | 5 | 5 (100%) | 0 (0%) | 100% QC | **NON** |
| QC-Py-03-Data-Management | 10 | 10 (100%) | 0 (0%) | 100% QC | **NON** |
| QC-Py-04-Research-Workflow | 25 | 5 (20%) | 19 (80%) | MIXTE | **NON** (dependances QC) |

### Conclusion

**Aucun des 4 notebooks n'est executable localement.** Tous necessitent QuantConnect Cloud (QuantBook / Lean engine).

- **QC-Py-02** et **QC-Py-03** sont 100% codes QC (QCAlgorithm, LEAN).
- **QC-Py-01** a 3 cellules "local" mais ce sont des commandes shell commentees.
- **QC-Py-04** est le seul avec une logique d'analyse potentiellement locale (pandas/matplotlib/sklearn), mais toutes les cellules dependent de donnees fetched via `qb.History()`.

### Recommandations

1. **Execution QC Cloud** : Utiliser le MCP `qc-mcp` ou Playwright pour injecter les outputs reels depuis QuantConnect Cloud.
2. **QC-Py-04 stub** : Creer une version locale avec `yfinance` comme substitut de `qb.History()` pour permettre l'execution des 19 cellules d'analyse hors QC.
3. **CI** : Mettre en place une validation syntaxique des notebooks QC via `nbformat` (verifie la structure JSON valide) en attendant l'integration QC Cloud.
