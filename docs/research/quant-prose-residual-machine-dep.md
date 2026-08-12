# Inventaire residuel machine-dep timings (issue #10158)
**Date** : scan `check_machine_dep_timing.py --all` sur **1008** notebooks.
**Detector summary** : {"wallclock": 220, "distribution_param": 58, "domain_quantity": 30, "ambiguous": 0, "total": 308}

## Classification par categorie
| Categorie | Count | Signification |
|---|---|---|
| RUNTIME_MEASURED | 42 | Valeur runtime drainable -- a remplacer par ordre de grandeur ou borne superieure. |
| RUNTIME_HINT | 27 | Timeout/delay/rate-limit -- defensable mais a contextualiser par un commentaire. |
| CONFIG_PARAMETRIC | 118 | Duree de sample/taille d'evenement -- frozen, ne pas toucher. |
| AMBIGUOUS | 121 | Contexte insuffisant -- revue manuelle requise. |

## Top 15 familles par drainage potentiel
| Famille | Drainable | Frozen | Total |
|---|---|---|---|
| `GenAI/Audio` | 24 | 38 | 62 |
| `Sudoku/Sudoku-13-SymbolicAutomata-Csharp.ipynb` | 23 | 5 | 28 |
| `Probas/Infer` | 20 | 26 | 46 |
| `Search/Applications` | 13 | 5 | 18 |
| `QuantConnect/Python` | 12 | 1 | 13 |
| `Sudoku/Sudoku-3-Genetic-Python.ipynb` | 9 | 4 | 13 |
| `SymbolicAI/Lean` | 7 | 2 | 9 |
| `SymbolicAI/Planners` | 6 | 3 | 9 |
| `Search/Part2-CSP` | 5 | 4 | 9 |
| `Sudoku/Sudoku-18-Comparison-Csharp.ipynb` | 5 | 0 | 5 |
| `Sudoku/Sudoku-18-Comparison-Python.ipynb` | 5 | 0 | 5 |
| `GenAI/Image` | 4 | 0 | 4 |
| `GenAI/Plateformes-Conversationnelles` | 4 | 0 | 4 |
| `GenAI/Texte` | 4 | 1 | 5 |
| `GenAI/Video` | 4 | 4 | 8 |

## Top 20 notebooks par drainage reel (RUNTIME_MEASURED)
| Notebook | Runtime | Hint | Ambiguous | Frozen |
|---|---|---|---|---|
| `Sudoku-13-SymbolicAutomata-Csharp.ipynb` | 0 | 5 | 18 | 5 |
| `Infer-2-Gaussian-Mixtures.ipynb` | 0 | 0 | 19 | 26 |
| `Sudoku-3-Genetic-Python.ipynb` | 3 | 0 | 6 | 4 |
| `04-1-Educational-Audio-Content.ipynb` | 7 | 0 | 0 | 1 |
| `04-6-Audiobook-Pipeline.ipynb` | 6 | 0 | 0 | 2 |
| `Sudoku-18-Comparison-Csharp.ipynb` | 2 | 0 | 3 | 0 |
| `Sudoku-18-Comparison-Python.ipynb` | 1 | 2 | 2 | 0 |
| `Infer-101.ipynb` | 0 | 0 | 4 | 10 |
| `QC-Py-26-LLM-Trading-Signals.ipynb` | 0 | 0 | 4 | 0 |
| `Sudoku-10-ORTools-Csharp.ipynb` | 0 | 0 | 4 | 0 |
| `App-2b-GraphColoring-CSharp.ipynb` | 0 | 0 | 3 | 0 |
| `Sudoku-18b-Statistical-Comparison-Python.ipynb` | 0 | 0 | 3 | 0 |
| `Lean-7b-Examples.ipynb` | 3 | 0 | 0 | 0 |
| `Planners-8-Temporal.ipynb` | 0 | 0 | 3 | 0 |
| `00-3-API-Endpoints-Configuration.ipynb` | 0 | 2 | 0 | 0 |
| `03-1-Multi-Model-Audio-Comparison.ipynb` | 0 | 0 | 2 | 1 |
| `04-3-Music-Composition-Workflow.ipynb` | 1 | 1 | 0 | 4 |
| `04-7-TTS-Voice-Benchmark.ipynb` | 2 | 0 | 0 | 0 |
| `03-3-Performance-Optimization.ipynb` | 0 | 0 | 2 | 0 |
| `03-Chat-Streaming-QA-OWUI.ipynb` | 0 | 2 | 0 | 0 |

## Synthese executoire
- **Drainable total** : 190 findings (RUNTIME_MEASURED + RUNTIME_HINT + AMBIGUOUS)
- **Frozen (a ne pas toucher)** : 118 findings (CONFIG_PARAMETRIC)
- **Ratio drainage** : 61.7%

Prochaine tranche : prendre la famille avec le plus de RUNTIME_MEASURED strict (cf. table ci-dessus) et drainer manuellement, puis re-lancer ce script.

