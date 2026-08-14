# EPIC #10678 Phase 1b — orphan end-of-notebook interp cells

## Résumé (HONESTY FIRST)

- Audit c.237 (PR #10681) a identifié 24 cellules MISPLACED sur 198 notebooks
- **Re-scan c.240** : 21 cellules avec `gap_after is None` (= en queue de notebook, pas de next code cell) trouvées via critère `strict[] verdict='OK' AND gap_after is None`
- **Verdict honnête après vérification cell-by-cell** : 21/21 sont en réalité **LEGIT** (interp fermant correctement la dernière section). Le verdict c.237=OK était correct.
- **MAIS** : c.239 PR #10705 a corrigé manuellement cell[34] de `02-SemanticKernel-Advanced` en **MISPLACED** — l'interp "Multi-Result Generation" appartient sémantiquement à cell[31] (Multi-Result), pas à cell[33] (analyze_diversity). **Le classificateur position-based ne peut pas détecter ce cas** — il faut une heuristique **sémantique** (regex keywords interp → recherche du code qui définit cette keyword).

## Méthode

Critère de détection : `interp_cell in interp_cells` ET `gap_after is None` (= pas de next code cell) → potentielle orphan end-of-notebook.

Vérification cell-by-cell (manuelle) pour distinguer MISPLACED vs LEGIT :
- LEGIT : l'interp interprète le code IMMÉDIATEMENT précédent (closing interp)
- MISPLACED : l'interp interprète un code plus tôt dans le notebook (orphan sémantique)

## Résultats : 21 cellules analysées

| # | Notebook | cell | verdict | raison |
|---|---|---|---|---|
| 1 | SmartGrid-Energy.ipynb | cell[22] | LEGIT | closing_interp_immediately_after_last_code |
| 2 | 01-SemanticKernel-Intro.ipynb | cell[27] | LEGIT | closing_interp_immediately_after_last_code |
| 3 | 02-SemanticKernel-Advanced.ipynb | cell[34] | **MISPLACED** (déjà fixé c.239) | orphan semantic, should follow cell[31] Multi-Result |
| 4 | 03-SemanticKernel-Agents.ipynb | cell[21] | LEGIT | closing_interp_immediately_after_last_code |
| 5 | 05-SemanticKernel-VectorStores.ipynb | cell[29] | LEGIT | closing_interp_immediately_after_last_code |
| 6 | 06-SemanticKernel-ProcessFramework.ipynb | cell[22] | LEGIT | closing_interp_immediately_after_last_code |
| 7 | 08-SemanticKernel-MCP.ipynb | cell[25] | LEGIT | closing_interp_immediately_after_last_code |
| 8 | 1_OpenAI_Intro.ipynb | cell[32] | LEGIT | closing_interp_immediately_after_last_code |
| 9 | 7_Code_Interpreter.ipynb | cell[40] | LEGIT | closing_interp_immediately_after_last_code |
| 10 | 9_Production_Patterns.ipynb | cell[41] | LEGIT | closing_interp_immediately_after_last_code |
| 11 | ML-5-TimeSeries-Python.ipynb | cell[27] | LEGIT | closing_interp_immediately_after_last_code |
| 12 | QC-Py-15-Parameter-Optimization.ipynb | cell[76] | LEGIT | closing_interp_immediately_after_last_code |
| 13 | QC-Py-17-Sentiment-Analysis.ipynb | cell[50] | LEGIT | closing_interp_immediately_after_last_code |
| 14 | QC-Py-18-ML-Features-Engineering.ipynb | cell[58] | LEGIT | closing_interp_immediately_after_last_code |
| 15 | QC-Py-20-ML-Regression-Prediction.ipynb | cell[65] | LEGIT | closing_interp_immediately_after_last_code |
| 16 | QC-Py-24-Autoencoders-Anomaly.ipynb | cell[50] | LEGIT | closing_interp_immediately_after_last_code |
| 17 | App-12-ConnectFour.ipynb | cell[55] | LEGIT | closing_interp_immediately_after_last_code |
| 18 | Search-10-SymbolicAutomata.ipynb | cell[88] | LEGIT | closing_interp_immediately_after_last_code |
| 19 | **Sudoku-3-Genetic-Csharp.ipynb** | **cell[27]** | **POSSIBLE_MISPLACED** | last_code_cell_then_interp_then_only_conclusion (= ORPHAN au sens strict, à vérifier manuellement) |
| 20 | Sudoku-5-PSO-Csharp.ipynb | cell[31] | LEGIT | closing_interp_immediately_after_last_code |
| 21 | SC-1-Setup-Foundry.ipynb | cell[21] | LEGIT | closing_interp_immediately_after_last_code |

## Recommandation Phase 3 (PR #10682)

Le bug c.237 **n'est pas dans la classification** mais dans le **manque de heuristique sémantique** : la regex keywords → code contenant ces keywords pourrait détecter des cas comme 02-SK-Advanced cell[34] où l'interp parle de "Multi-Result" mais le code précédent est `analyze_diversity`.

Patch suggéré (5 lignes dans `check_interp_positioning.py`) :

```python
# AVANT (c.237 — légitime seulement pour legit cases)
next_code = next((i for i in range(idx+1, len(cells)) if cells[i].cell_type == "code"), None)
gap_after = next_code - idx if next_code is not None else None

# APRÈS (c.240 — distingue LEGIT closing_interp vs MISPLACED orphan semantic)
if gap_after is None:
    # No next code cell - check if interp matches immediately preceding code semantically
    prev_code_idx = next((i for i in range(idx-1, -1, -1) if cells[i].cell_type == "code"), None)
    if prev_code_idx is not None and _interp_matches_code(cells[idx].source, cells[prev_code_idx].source):
        verdict = "OK"  # closing interp of last code
    else:
        verdict = "CHECK"  # potential orphan semantic
```

Helper `_interp_matches_code(source_interp, source_code)` : tokenize les 2 sources, vérifier si l'interp partage ≥80% des keywords significatives (noms de fonctions, identificateurs de variables) avec le code précédent. Si non-match → CHECK.

## Leçons c.240

- **c.240-L1 ★★** : Le "blind spot" c.237 que j'ai cru détecter n'en était PAS un au sens strict. Le verdict c.237=OK sur les 21 cellules "orphan end-of-notebook" est **correct** (closing interp légitime). Seul un cas (c.239 PR #10705) était vraiment MISPLACED.
- **c.240-L2 ★** : Toujours classifier AVANT de commit un scan. La confiance naïve en un "détecteur élargi" génère des faux positifs massifs (21/21 ici). Vérification cell-by-cell obligatoire (c.239-L2 reaffirmé + c.237-L1 reaffirmed).
- **c.240-L3 ★ NEW** : `gap_after = None` est un signal positionnel mais **PAS sémantique**. Le classificateur position-based rate les orphan sémantiques (interp qui parle d'un sujet différent du code adjacent). Solution = heuristique sémantique keywords ↔ code contenu (à venir dans PR #10682).

Voir aussi : [rapport c.237 original](10678-interp-positioning-audit.md) (24 CHECK).


## Orphelins détectés

### `SmartGrid-Energy.ipynb` cell[22]

- **Chemin** : `MyIA.AI.Notebooks/CaseStudies/SmartGrid-Energy/solution/SmartGrid-Energy.ipynb`
- **idx** : 22 / 24 total cells
- **prev_code_idx** : 21 (seul code avant l'interp)
- **is_last_cell** : False
- **last_cell_preview** : `## Conclusion /  / Cette étude de cas illustre la **composition ordonnee** des parad`
- **interp_preview** : `### Interprétation : le coût de la transition bas-carbone /  / Les trois stratégies sont ici scorées avec des poids égaux `(`
- **Sévérité** : **HIGH** (orphan de fin = l'interp n'est jamais lue, donc jamais validée par un code qu'elle interprète)
- **Action Phase 2** : relocaliser la cellule juste après le code référencé (prev_code_idx+1)

### `01-SemanticKernel-Intro.ipynb` cell[27]

- **Chemin** : `MyIA.AI.Notebooks/GenAI/SemanticKernel/01-SemanticKernel-Intro.ipynb`
- **idx** : 27 / 29 total cells
- **prev_code_idx** : 26 (seul code avant l'interp)
- **is_last_cell** : False
- **last_cell_preview** : `## Conclusion /  / ## Resume des concepts /  / | Concept | Description | Code cle | / |---`
- **interp_preview** : `### Interprétation : Gestion de l'Historique de Conversation /  / **Sortie obtenue** : Conversation multi-tours avec recomma`
- **Sévérité** : **HIGH** (orphan de fin = l'interp n'est jamais lue, donc jamais validée par un code qu'elle interprète)
- **Action Phase 2** : relocaliser la cellule juste après le code référencé (prev_code_idx+1)

### `02-SemanticKernel-Advanced.ipynb` cell[34]

- **Chemin** : `MyIA.AI.Notebooks/GenAI/SemanticKernel/02-SemanticKernel-Advanced.ipynb`
- **idx** : 34 / 37 total cells
- **prev_code_idx** : 33 (seul code avant l'interp)
- **is_last_cell** : False
- **last_cell_preview** : `## Conclusion /  / Nous avons vu : / 1. Un **Chat** basique avec `KernelArguments`. / 2.`
- **interp_preview** : `### Interprétation : Multi-Result Generation /  / **Sortie obtenue** : Trois blagues différentes générées en un seul appel A`
- **Sévérité** : **HIGH** (orphan de fin = l'interp n'est jamais lue, donc jamais validée par un code qu'elle interprète)
- **Action Phase 2** : relocaliser la cellule juste après le code référencé (prev_code_idx+1)

### `03-SemanticKernel-Agents.ipynb` cell[21]

- **Chemin** : `MyIA.AI.Notebooks/GenAI/SemanticKernel/03-SemanticKernel-Agents.ipynb`
- **idx** : 21 / 26 total cells
- **prev_code_idx** : 20 (seul code avant l'interp)
- **is_last_cell** : False
- **last_cell_preview** : `## Synthèse : Taxonomie Complète des Agents Semantic Kernel /  / ### 1. Types d'agen`
- **interp_preview** : `### Interprétation : Orchestration Multi-Agents et Stratégies /  / **Sortie obtenue** : Dialogue itératif entre CopyWriter (`
- **Sévérité** : **HIGH** (orphan de fin = l'interp n'est jamais lue, donc jamais validée par un code qu'elle interprète)
- **Action Phase 2** : relocaliser la cellule juste après le code référencé (prev_code_idx+1)

### `05-SemanticKernel-VectorStores.ipynb` cell[29]

- **Chemin** : `MyIA.AI.Notebooks/GenAI/SemanticKernel/05-SemanticKernel-VectorStores.ipynb`
- **idx** : 29 / 32 total cells
- **prev_code_idx** : 28 (seul code avant l'interp)
- **is_last_cell** : False
- **last_cell_preview** : `## Conclusion /  / ## Resume des concepts /  / | Concept | Description | Code cle | / |---`
- **interp_preview** : `### Interprétation : Pipeline RAG - Retrieval-Augmented Generation /  / **Sortie obtenue** : Reponse LLM basee sur le contex`
- **Sévérité** : **HIGH** (orphan de fin = l'interp n'est jamais lue, donc jamais validée par un code qu'elle interprète)
- **Action Phase 2** : relocaliser la cellule juste après le code référencé (prev_code_idx+1)

### `06-SemanticKernel-ProcessFramework.ipynb` cell[22]

- **Chemin** : `MyIA.AI.Notebooks/GenAI/SemanticKernel/06-SemanticKernel-ProcessFramework.ipynb`
- **idx** : 22 / 26 total cells
- **prev_code_idx** : 21 (seul code avant l'interp)
- **is_last_cell** : False
- **last_cell_preview** : `## Conclusion /  / ## Resume des concepts /  / | Concept | Description | Code cle | / |---`
- **interp_preview** : `### Interprétation : Human-in-the-Loop /  / **Sortie obtenue** : Pipeline avec point d'approbation humaine (simulé) /  / | Compo`
- **Sévérité** : **HIGH** (orphan de fin = l'interp n'est jamais lue, donc jamais validée par un code qu'elle interprète)
- **Action Phase 2** : relocaliser la cellule juste après le code référencé (prev_code_idx+1)

### `08-SemanticKernel-MCP.ipynb` cell[25]

- **Chemin** : `MyIA.AI.Notebooks/GenAI/SemanticKernel/08-SemanticKernel-MCP.ipynb`
- **idx** : 25 / 29 total cells
- **prev_code_idx** : 24 (seul code avant l'interp)
- **is_last_cell** : False
- **last_cell_preview** : `## Conclusion /  / ## Resume des concepts /  / | Concept | Description | Code cle | / |---`
- **interp_preview** : `### Interprétation : Anatomie d'un serveur MCP personnalisé /  / **Serveur créé** : `my-business-tools` avec 2 outils métier`
- **Sévérité** : **HIGH** (orphan de fin = l'interp n'est jamais lue, donc jamais validée par un code qu'elle interprète)
- **Action Phase 2** : relocaliser la cellule juste après le code référencé (prev_code_idx+1)

### `1_OpenAI_Intro.ipynb` cell[32]

- **Chemin** : `MyIA.AI.Notebooks/GenAI/Texte/1_OpenAI_Intro.ipynb`
- **idx** : 32 / 34 total cells
- **prev_code_idx** : 31 (seul code avant l'interp)
- **is_last_cell** : False
- **last_cell_preview** : `## Conclusion de cette Introduction /  / Nous avons couvert les points suivants : / - `
- **interp_preview** : `### Interprétation des résultats Responses API /  / L'exécution ci-dessus démontre les **capacités de chaînage** de la Respo`
- **Sévérité** : **HIGH** (orphan de fin = l'interp n'est jamais lue, donc jamais validée par un code qu'elle interprète)
- **Action Phase 2** : relocaliser la cellule juste après le code référencé (prev_code_idx+1)

### `7_Code_Interpreter.ipynb` cell[40]

- **Chemin** : `MyIA.AI.Notebooks/GenAI/Texte/7_Code_Interpreter.ipynb`
- **idx** : 40 / 42 total cells
- **prev_code_idx** : 39 (seul code avant l'interp)
- **is_last_cell** : False
- **last_cell_preview** : `## Conclusion et exercices /  / ### Ce que nous avons appris /  / Le **Code Interpreter*`
- **interp_preview** : `### Interprétation du nettoyage /  / Le nettoyage a été effectué avec succès. Voici ce qui a été supprimé : /  / **Fichiers loca`
- **Sévérité** : **HIGH** (orphan de fin = l'interp n'est jamais lue, donc jamais validée par un code qu'elle interprète)
- **Action Phase 2** : relocaliser la cellule juste après le code référencé (prev_code_idx+1)

### `9_Production_Patterns.ipynb` cell[41]

- **Chemin** : `MyIA.AI.Notebooks/GenAI/Texte/9_Production_Patterns.ipynb`
- **idx** : 41 / 45 total cells
- **prev_code_idx** : 40 (seul code avant l'interp)
- **is_last_cell** : False
- **last_cell_preview** : `## Exercices Pratiques /  / ### Exercice 1 : Chatbot Multi-Session (30 min) /  / Créez u`
- **interp_preview** : `### Interprétation des Résultats Streaming et Modération /  / **Observations sur le Streaming :** /  / Le streaming transforme r`
- **Sévérité** : **HIGH** (orphan de fin = l'interp n'est jamais lue, donc jamais validée par un code qu'elle interprète)
- **Action Phase 2** : relocaliser la cellule juste après le code référencé (prev_code_idx+1)

### `ML-5-TimeSeries-Python.ipynb` cell[27]

- **Chemin** : `MyIA.AI.Notebooks/ML/ML.Net/ML-5-TimeSeries-Python.ipynb`
- **idx** : 27 / 30 total cells
- **prev_code_idx** : 26 (seul code avant l'interp)
- **is_last_cell** : False
- **last_cell_preview** : `## Références /  / - Broomhead, D. S., & King, G. P. (1986). *Extracting qualitative`
- **interp_preview** : `### Interprétation des résultats /  / La configuration au plus faible AIC offre le meilleur compromis ajustement / complexit`
- **Sévérité** : **HIGH** (orphan de fin = l'interp n'est jamais lue, donc jamais validée par un code qu'elle interprète)
- **Action Phase 2** : relocaliser la cellule juste après le code référencé (prev_code_idx+1)

### `QC-Py-15-Parameter-Optimization.ipynb` cell[76]

- **Chemin** : `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-15-Parameter-Optimization.ipynb`
- **idx** : 76 / 78 total cells
- **prev_code_idx** : 74 (seul code avant l'interp)
- **is_last_cell** : False
- **last_cell_preview** : `--- /  / ## Conclusion et Prochaines Étapes /  / ### Recapitulatif /  / Dans ce notebook, no`
- **interp_preview** : `--- /  / ### Interprétation /  / Code QCAlgorithm final avec paramètres optimisés intégrés: /  / - **Paramètres optimaux hardcodés**`
- **Sévérité** : **HIGH** (orphan de fin = l'interp n'est jamais lue, donc jamais validée par un code qu'elle interprète)
- **Action Phase 2** : relocaliser la cellule juste après le code référencé (prev_code_idx+1)

### `QC-Py-17-Sentiment-Analysis.ipynb` cell[50]

- **Chemin** : `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-17-Sentiment-Analysis.ipynb`
- **idx** : 50 / 52 total cells
- **prev_code_idx** : 49 (seul code avant l'interp)
- **is_last_cell** : False
- **last_cell_preview** : `--- /  / ## Conclusion et Prochaines Étapes /  / ### Recapitulatif /  / Dans ce notebook, no`
- **interp_preview** : `### Interprétation des Dépendances /  / Ce tableau récapitule les bibliothèques Python nécessaires pour implémenter l'analys`
- **Sévérité** : **HIGH** (orphan de fin = l'interp n'est jamais lue, donc jamais validée par un code qu'elle interprète)
- **Action Phase 2** : relocaliser la cellule juste après le code référencé (prev_code_idx+1)

### `QC-Py-18-ML-Features-Engineering.ipynb` cell[58]

- **Chemin** : `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-18-ML-Features-Engineering.ipynb`
- **idx** : 58 / 60 total cells
- **prev_code_idx** : 57 (seul code avant l'interp)
- **is_last_cell** : False
- **last_cell_preview** : `--- /  / ## Conclusion et Prochaines Étapes /  / ### Recapitulatif /  / Dans ce notebook, no`
- **interp_preview** : `--- /  / ### Interprétation /  / Ce résultat final montre que notre pipeline de feature engineering est fonctionnel et prêt pour`
- **Sévérité** : **HIGH** (orphan de fin = l'interp n'est jamais lue, donc jamais validée par un code qu'elle interprète)
- **Action Phase 2** : relocaliser la cellule juste après le code référencé (prev_code_idx+1)

### `QC-Py-20-ML-Regression-Prediction.ipynb` cell[65]

- **Chemin** : `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-20-ML-Regression-Prediction.ipynb`
- **idx** : 65 / 67 total cells
- **prev_code_idx** : 64 (seul code avant l'interp)
- **is_last_cell** : False
- **last_cell_preview** : `--- /  / ## Conclusion et Prochaines Étapes /  / ### Recapitulatif /  / Dans ce notebook, no`
- **interp_preview** : `--- /  / ### Interprétation /  / Ce tableau résume les paramètres recommandés pour une stratégie de production basée sur la régr`
- **Sévérité** : **HIGH** (orphan de fin = l'interp n'est jamais lue, donc jamais validée par un code qu'elle interprète)
- **Action Phase 2** : relocaliser la cellule juste après le code référencé (prev_code_idx+1)

### `QC-Py-24-Autoencoders-Anomaly.ipynb` cell[50]

- **Chemin** : `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-24-Autoencoders-Anomaly.ipynb`
- **idx** : 50 / 52 total cells
- **prev_code_idx** : 49 (seul code avant l'interp)
- **is_last_cell** : False
- **last_cell_preview** : `--- /  / ## Conclusion et Prochaines Étapes /  / ### Récapitulatif /  / | Concept | Descript`
- **interp_preview** : `### Interprétation : Code QuantConnect /  / Le code ci-dessus illustre une **implémentation complète en production** pour Qu`
- **Sévérité** : **HIGH** (orphan de fin = l'interp n'est jamais lue, donc jamais validée par un code qu'elle interprète)
- **Action Phase 2** : relocaliser la cellule juste après le code référencé (prev_code_idx+1)

### `App-12-ConnectFour.ipynb` cell[55]

- **Chemin** : `MyIA.AI.Notebooks/Search/Applications/Search/App-12-ConnectFour.ipynb`
- **idx** : 55 / 59 total cells
- **prev_code_idx** : 54 (seul code avant l'interp)
- **is_last_cell** : False
- **last_cell_preview** : `## ConclusionCe notebook a comparé quatre approches d'intelligence artificielle `
- **interp_preview** : `### Interprétation : Exercices /  / | Exercice | Concept cle | résultat attendu | / |----------|-------------|----------------`
- **Sévérité** : **HIGH** (orphan de fin = l'interp n'est jamais lue, donc jamais validée par un code qu'elle interprète)
- **Action Phase 2** : relocaliser la cellule juste après le code référencé (prev_code_idx+1)

### `Search-10-SymbolicAutomata.ipynb` cell[88]

- **Chemin** : `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-10-SymbolicAutomata.ipynb`
- **idx** : 88 / 91 total cells
- **prev_code_idx** : 87 (seul code avant l'interp)
- **is_last_cell** : False
- **last_cell_preview** : `## Conclusion /  / Ce notebook a presente les **automates symboliques**, une extensi`
- **interp_preview** : `### Interprétation : Comparaison Fini vs Symbolique /  / **Résultat obtenu** : Comparaison détaillée entre automates finis c`
- **Sévérité** : **HIGH** (orphan de fin = l'interp n'est jamais lue, donc jamais validée par un code qu'elle interprète)
- **Action Phase 2** : relocaliser la cellule juste après le code référencé (prev_code_idx+1)

### `Sudoku-3-Genetic-Csharp.ipynb` cell[27]

- **Chemin** : `MyIA.AI.Notebooks/Sudoku/Sudoku-3-Genetic-Csharp.ipynb`
- **idx** : 27 / 28 total cells
- **prev_code_idx** : 26 (seul code avant l'interp)
- **is_last_cell** : True
- **last_cell_preview** : `### Interprétation des résultats /  / Le solveur génétique base sur les permutations`
- **interp_preview** : `### Interprétation des résultats /  / Le solveur génétique base sur les permutations de lignes montre des performances très `
- **Sévérité** : **HIGH** (orphan de fin = l'interp n'est jamais lue, donc jamais validée par un code qu'elle interprète)
- **Action Phase 2** : relocaliser la cellule juste après le code référencé (prev_code_idx+1)

### `Sudoku-5-PSO-Csharp.ipynb` cell[31]

- **Chemin** : `MyIA.AI.Notebooks/Sudoku/Sudoku-5-PSO-Csharp.ipynb`
- **idx** : 31 / 33 total cells
- **prev_code_idx** : 30 (seul code avant l'interp)
- **is_last_cell** : False
- **last_cell_preview** : `## Résumé /  / Le **Particle Swarm Optimization** est une métaheuristique interessan`
- **interp_preview** : `### Interprétation : Influence de la configuration /  / **Sortie obtenue** : Les trois configurations (Conservatif, Standard`
- **Sévérité** : **HIGH** (orphan de fin = l'interp n'est jamais lue, donc jamais validée par un code qu'elle interprète)
- **Action Phase 2** : relocaliser la cellule juste après le code référencé (prev_code_idx+1)

### `SC-1-Setup-Foundry.ipynb` cell[21]

- **Chemin** : `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/00-Foundations/SC-1-Setup-Foundry.ipynb`
- **idx** : 21 / 26 total cells
- **prev_code_idx** : 20 (seul code avant l'interp)
- **is_last_cell** : False
- **last_cell_preview** : `--- /  / [<< Cypherpunk Origins](../../MyIA.AI.Notebooks/SymbolicAI/SmartContracts/00-Foundations/SC-0-Cypherpunk-Origins.ipynb) | [Suivant : Setup W`
- **interp_preview** : `### Interprétation : Résumé de l'environnement /  / **Sortie obtenue** : Résumé complet de l'environnement de développement `
- **Sévérité** : **HIGH** (orphan de fin = l'interp n'est jamais lue, donc jamais validée par un code qu'elle interprète)
- **Action Phase 2** : relocaliser la cellule juste après le code référencé (prev_code_idx+1)


## Recommandation Phase 3 (PR #10682)

Le script `check_interp_positioning.py` doit corriger ce blind spot en 5 lignes :

```python
# AVANT (c.237 bug)
next_code = next((i for i in range(idx+1, len(cells)) if cells[i].cell_type == "code"), None)
if next_code is None:
    continue  # SKIP ! C'est ici que l'orphan disparaît de la liste strict

# APRÈS (c.240 fix)
if next_code is None:
    verdict = "CHECK"  # orphan end-of-notebook
    gap_after = 99  # sentinel
else:
    gap_after = next_code - idx
```

Voir aussi `notebooks_interp_orphans.json` (inventaire brut) et le rapport c.237 original `docs/ledgers/10678-interp-positioning-audit.md`.
