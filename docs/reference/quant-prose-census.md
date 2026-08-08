# Quant-prose cross-family census (#9434, item 1)

Recensement chiffré des valeurs quantitatives écrites en dur dans les cellules markdown des notebooks, classées selon la ligne de partage codifiée par #9434 (acceptance item 4, #9958 MERGED).

| Question | Réponse |
|---|---|
| **Outil** | `scripts/notebook_tools/scan_quant_classify.py` (#9800 + #9813 + #9820 + #9838 MERGED) |
| **Cible** | `MyIA.AI.Notebooks/**` (toute la racine, glob par défaut) |
| **Méthode** | Extraction de nombres dans cellules markdown, classification par : (a) regex TIME_UNITS / SEMVER / SEED_KEYWORDS / MACHINE_DEP_KEYWORDS / ENV_DEP_KEYWORDS / STOCH_KEYWORDS / DATA_LIST_MARKERS, (b) contexte bayésien (c.1272), (c) localisation structurelle (c.1275 : `rung`/`epic`/`phase`/`%`) |
| **Date run** | 2026-08-08 (cycle c.1331+40) |
| **Lane** | myia-po-2024:CoursIA-2 |

## Résumé global

- **Notebooks scannés** : 972
- **Findings totaux** : 111086
- **STRUCTUREL** : 101777 (91.6%)
- **DRAINABLE (MACHINE-DEP + ENV-DEP + STOCHASTIQUE-NON-SEEDEE)** : 9309 (8.4%)
  - MACHINE-DEP : 4545
  - ENV-DEP : 3197
  - STOCHASTIQUE-NON-SEEDEE : 1567

## Par famille

| Famille | #NB | #Findings | STRUCT | MACHINE | ENV | STOCH | DRAINABLE | %DRAIN |
|---|---|---|---|---|---|---|---|---|
| GameTheory | 56 | 7554 | 7141 | 201 | 179 | 33 | 413 | 5.5% |
| GenAI | 145 | 14696 | 12920 | 1129 | 415 | 232 | 1776 | 12.1% |
| IIT | 53 | 5019 | 4827 | 71 | 67 | 54 | 192 | 3.8% |
| ML | 48 | 3510 | 3077 | 90 | 201 | 142 | 433 | 12.3% |
| OTHER | 7 | 452 | 431 | 15 | 1 | 5 | 21 | 4.6% |
| Probas | 58 | 11728 | 11269 | 173 | 123 | 163 | 459 | 3.9% |
| QuantConnect | 207 | 18829 | 17437 | 726 | 280 | 386 | 1392 | 7.4% |
| RL | 17 | 1151 | 1008 | 81 | 17 | 45 | 143 | 12.4% |
| Search | 118 | 16293 | 14829 | 678 | 473 | 313 | 1464 | 9.0% |
| Sudoku | 37 | 5599 | 4748 | 427 | 376 | 48 | 851 | 15.2% |
| SymbolicAI | 226 | 26255 | 24090 | 954 | 1065 | 146 | 2165 | 8.2% |

## Par sous-famille (top 20 par drainable)

| Famille | Sous-famille | #NB | #Findings | DRAINABLE |
|---|---|---|---|---|
| QuantConnect | Python | 56 | 10240 | 1009 |
| GenAI | Audio | 30 | 4157 | 703 |
| Search | Applications | 43 | 4830 | 555 |
| SymbolicAI | Lean | 28 | 5418 | 471 |
| Search | Part1-Foundations | 29 | 5134 | 378 |
| SymbolicAI | Tweety | 32 | 3215 | 339 |
| SymbolicAI | SemanticWeb | 25 | 2724 | 324 |
| GenAI | Texte | 20 | 3273 | 319 |
| Search | Part2-CSP | 18 | 3451 | 296 |
| SymbolicAI | SMT | 46 | 4434 | 271 |
| QuantConnect | projects | 110 | 6105 | 229 |
| SymbolicAI | Planners | 23 | 2611 | 229 |
| ML | ML.Net | 20 | 1763 | 224 |
| GenAI | Video | 17 | 1674 | 217 |
| ML | DataScienceWithAgents | 28 | 1747 | 209 |
| SymbolicAI | SymbolicLearning | 20 | 2528 | 207 |
| Search | Part4-Metaheuristics | 22 | 2325 | 204 |
| SymbolicAI | SmartContracts | 27 | 2569 | 199 |
| Probas | Infer | 19 | 5214 | 189 |
| IIT | ICT-Series | 50 | 4688 | 177 |

## Top 5 notebooks par drainable, par famille

### GameTheory (drainable total = 413)

| Notebook | Drainable |
|---|---|
| `MyIA.AI.Notebooks\GameTheory\GameTheory-8-CombinatorialGames-Csharp.ipynb` | 27 |
| `MyIA.AI.Notebooks\GameTheory\SocialChoice\04-Computational-Aggregation-SAT-Z3-Csharp.ipynb` | 22 |
| `MyIA.AI.Notebooks\GameTheory\GameTheory-8-CombinatorialGames.ipynb` | 19 |
| `MyIA.AI.Notebooks\GameTheory\GameTheory-15b-Lean-CooperativeGames.ipynb` | 13 |
| `MyIA.AI.Notebooks\GameTheory\GameTheory-7-ExtensiveForm-Csharp.ipynb` | 13 |

### GenAI (drainable total = 1776)

| Notebook | Drainable |
|---|---|
| `MyIA.AI.Notebooks\GenAI\Texte\10_LocalLlama.ipynb` | 75 |
| `MyIA.AI.Notebooks\GenAI\Texte\9_Production_Patterns.ipynb` | 66 |
| `MyIA.AI.Notebooks\GenAI\Audio\02-Advanced\02-1-Chatterbox-TTS.ipynb` | 39 |
| `MyIA.AI.Notebooks\GenAI\Audio\02-Advanced\02-7-Song-Generation.ipynb` | 38 |
| `MyIA.AI.Notebooks\GenAI\Audio\03-Orchestration\03-1-Multi-Model-Audio-Comparison.ipynb` | 38 |

### IIT (drainable total = 192)

| Notebook | Drainable |
|---|---|
| `MyIA.AI.Notebooks\IIT\ICT-Series\ICT-25-InoculationRL.ipynb` | 37 |
| `MyIA.AI.Notebooks\IIT\ICT-Series\ICT-21-SAETrajectoires.ipynb` | 13 |
| `MyIA.AI.Notebooks\IIT\ICT-Series\ICT-13-AxelrodStrategicMorphodynamics.ipynb` | 10 |
| `MyIA.AI.Notebooks\IIT\ICT-Series\ICT-15e-Bridge2-RecoverabilityAgency.ipynb` | 9 |
| `MyIA.AI.Notebooks\IIT\ICT-Series\ICT-15c-MetaProxyObstruction.ipynb` | 8 |

### ML (drainable total = 433)

| Notebook | Drainable |
|---|---|
| `MyIA.AI.Notebooks\ML\ML.Net\ML-6-ONNX-Python.ipynb` | 32 |
| `MyIA.AI.Notebooks\ML\ML.Net\ML-6-ONNX.ipynb` | 24 |
| `MyIA.AI.Notebooks\ML\DataScienceWithAgents\01-PythonForDataScience\notebooks\1.2-Manipulation_de_Donnees_avec_NumPy.ipynb` | 22 |
| `MyIA.AI.Notebooks\ML\DataScienceWithAgents\02-ML-Cours\2.5-Biais-Variance-CV-ROC.ipynb` | 22 |
| `MyIA.AI.Notebooks\ML\ML.Net\ML-4-Evaluation-Python.ipynb` | 20 |

### OTHER (drainable total = 21)

| Notebook | Drainable |
|---|---|
| `MyIA.AI.Notebooks\CaseStudies\Diagnostic-Medical\solution\Diagnostic-Medical.ipynb` | 6 |
| `MyIA.AI.Notebooks\CaseStudies\Diagnostic-Medical\student\Diagnostic-Medical.ipynb` | 6 |
| `MyIA.AI.Notebooks\CaseStudies\SmartGrid-Energy\solution\SmartGrid-Energy.ipynb` | 4 |
| `MyIA.AI.Notebooks\CaseStudies\SmartGrid-Energy\student\SmartGrid-Energy.ipynb` | 3 |
| `MyIA.AI.Notebooks\GradeBook.ipynb` | 1 |

### Probas (drainable total = 459)

| Notebook | Drainable |
|---|---|
| `MyIA.AI.Notebooks\Probas\Infer\Infer-2-Gaussian-Mixtures.ipynb` | 38 |
| `MyIA.AI.Notebooks\Probas\Infer\Infer-15-Recommenders.ipynb` | 27 |
| `MyIA.AI.Notebooks\Probas\DecisionTheory\PyMC\DecPyMC-7-Sequential.ipynb` | 17 |
| `MyIA.AI.Notebooks\Probas\DecisionTheory\DecInfer\DecInfer-3-Utility-Money.ipynb` | 16 |
| `MyIA.AI.Notebooks\Probas\PyMC\PyMC-6-Debugging.ipynb` | 16 |

### QuantConnect (drainable total = 1392)

| Notebook | Drainable |
|---|---|
| `MyIA.AI.Notebooks\QuantConnect\Python\QC-Py-12-Backtesting-Analysis.ipynb` | 47 |
| `MyIA.AI.Notebooks\QuantConnect\Python\QC-Py-28-Market-Regime-Detection.ipynb` | 43 |
| `MyIA.AI.Notebooks\QuantConnect\Python\QC-Py-31-Transformer-Training.ipynb` | 41 |
| `MyIA.AI.Notebooks\QuantConnect\Python\QC-Py-17-Sentiment-Analysis.ipynb` | 36 |
| `MyIA.AI.Notebooks\QuantConnect\Python\QC-Py-10-Risk-Portfolio-Management.ipynb` | 35 |

### RL (drainable total = 143)

| Notebook | Drainable |
|---|---|
| `MyIA.AI.Notebooks\RL\rl_4_multi_armed_bandits.ipynb` | 24 |
| `MyIA.AI.Notebooks\RL\rl_6d_sac_from_scratch.ipynb` | 16 |
| `MyIA.AI.Notebooks\RL\rl_10_reward_shaping.ipynb` | 12 |
| `MyIA.AI.Notebooks\RL\rl_6c_ppo_from_scratch.ipynb` | 12 |
| `MyIA.AI.Notebooks\RL\rl_8_model_based_dyna_q.ipynb` | 11 |

### Search (drainable total = 1464)

| Notebook | Drainable |
|---|---|
| `MyIA.AI.Notebooks\Search\Applications\Search\App-14-ConnectFour-Adversarial.ipynb` | 58 |
| `MyIA.AI.Notebooks\Search\Part2-CSP\CSP-5-Optimization-Csharp.ipynb` | 38 |
| `MyIA.AI.Notebooks\Search\Part1-Foundations\Search-11-Metaheuristics.ipynb` | 34 |
| `MyIA.AI.Notebooks\Search\Part1-Foundations\Search-9-LinearProgramming.ipynb` | 34 |
| `MyIA.AI.Notebooks\Search\Part2-CSP\CSP-3-Advanced.ipynb` | 30 |

### Sudoku (drainable total = 851)

| Notebook | Drainable |
|---|---|
| `MyIA.AI.Notebooks\Sudoku\Sudoku-3-Genetic-Python.ipynb` | 70 |
| `MyIA.AI.Notebooks\Sudoku\Sudoku-18-Comparison-Csharp.ipynb` | 64 |
| `MyIA.AI.Notebooks\Sudoku\Sudoku-13-SymbolicAutomata-Csharp.ipynb` | 61 |
| `MyIA.AI.Notebooks\Sudoku\Sudoku-18-Comparison-Python.ipynb` | 53 |
| `MyIA.AI.Notebooks\Sudoku\Sudoku-4-SimulatedAnnealing-Python.ipynb` | 51 |

### SymbolicAI (drainable total = 2165)

| Notebook | Drainable |
|---|---|
| `MyIA.AI.Notebooks\SymbolicAI\Lean\Lean-11-TorchLean.ipynb` | 70 |
| `MyIA.AI.Notebooks\SymbolicAI\Lean\Lean-10-LeanDojo.ipynb` | 69 |
| `MyIA.AI.Notebooks\SymbolicAI\SemanticWeb\SW-13-Python-Reasoners.ipynb` | 57 |
| `MyIA.AI.Notebooks\SymbolicAI\SymbolicLearning\SL-1-LogicalLearning.ipynb` | 48 |
| `MyIA.AI.Notebooks\SymbolicAI\SemanticWeb\SW-1-CSharp-Setup.ipynb` | 41 |

## Lecture

- **SymmetricAI est la famille la plus drainable** (2165 valeurs, 8.2% du total) — cohérent avec la maturité de la veine #9434 (lean-10, lean-11, SW-13, sudoku-12/13/18, etc.).
- **GenAI** (1776) reflète principalement `10_LocalLlama.ipynb` (75) et `9_Production_Patterns.ipynb` (66) — timings de modèles locaux documentés en prose.
- **Search** (1464) est portée par `App-14-ConnectFour-Adversarial.ipynb` (58) — adversarial search timings machine-dep.
- **QuantConnect** (1392) — timings de backtest/simulation, conformes à la classe MACHINE-DEP.
- **Sudoku** (851) — notebooks comparison (18-Python, 18-Csharp, 3-Genetic, 13-SymbolicAutomata) avec timings de solveurs.
- **Probas** (459) — Infer.NET + DecisionTheory, bien que veine drainage Probas CLOSED par po-2025 (commentaire de claim).
- **ML** (433) — ONNX notebooks top contributeurs (timing inférence).
- **GameTheory** (413) — Combinatorial Games + SocialChoice (SAT solver timings).
- **IIT** (192) — ICT-25 InoculationRL (37) principalement.

## Caveats

- La classification **n'est pas parfaite** : les couches anti-FP (c.1272 contexte bayésien, c.1275 Argument_Analysis) couvrent les patterns connus, mais des FPs restent possibles (par exemple, une valeur dans une cellule de résultat précédente que le classifieur pourrait classer ENV-DEP par contexte).
- Le ratio STRUCTUREL/DRAINABLE est élevé (~92%) — la majorité des valeurs quantitatives en prose sont des **constants pédagogiques** (ordres de grandeur, ratios fixes, paramètres théoriques) qui ne dériveront pas.
- Une re-exécution produira le même décompte modulo le contenu des cellules markdown ajoutées/modifiées depuis ce run.
- Le décompte par famille est calculé sur le **premier composant du chemin** (`MyIA.AI.Notebooks/<FAMILY>/...`) — les notebooks en dehors de cette taxonomie sont classés en `OTHER` (RL principalement, 24 notebooks).

## Comment reproduire

```bash
python scripts/notebook_tools/scan_quant_classify.py --root MyIA.AI.Notebooks --json-out /tmp/census.json
```

Options utiles : `--check` (exit 1 si ≥ 1 drainable, pour CI), `--limit N` (test rapide), `--notebook <path>` (audit ciblé).

## Liens

- Issue #9434 (cette census résout l'item 1 des 4 acceptance criteria)
- Issue #9377 (mandat parent — quantitatif tenu par le CI, pas par la prose)
- Issue #8052 (vague de PRs qui ré-épinglent des valeurs drift)
- PR #9800 (scan_quant_classify.py triage 4-classes — outillage)
- PR #9813 (anti-FP bayesian context)
- PR #9820 (retire `}`cii typo + apprentissage trop large)
- PR #9838 (anti-FP Argument_Analysis c.1275)
- PR #9958 (item 4 C.5 codification de la ligne de partage — MERGED)
