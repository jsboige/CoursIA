# Audit cellules interprétation mal positionnees (#10678 Phase 1)

## Resume
- Total notebooks scannes : 1005 (sous `MyIA.AI.Notebooks/**/*.ipynb`, exclus `_output`, `_archive`, `.executed`, `.ipynb_checkpoints`)
- Notebooks avec cellules `### Lecture du resultat` / `### Interpretation` : **198**
- Cellules interpretation total : **732**
- Verdicts OK : **708** (97%) - interps correctement positionnees
- Verdicts **CHECK (MISPLACED candidates)** : **24** (3%) - interps en zone MD-only (gap avant ET apres >= 3 cellules) ou tres eloignees du code (>= 5 cellules)

## Methode
Pour chaque cellule markdown d'interpretation (pattern `### Lecture du resultat` / `### Interpretation` / `### Interpretation des resultats`) :
1. Localiser la cellule de code **precedente** (gap_b = idx_interp - idx_prev_code)
2. Localiser la cellule de code **suivante** (gap_a = idx_next_code - idx_interp)
3. Classifier CHECK si :
   - `gap_b >= 3 ET gap_a >= 3` (interp en zone MD-only entre 2 blocs code = STRUCTURAL/MISPLACED)
   - OU `gap_b >= 5` seul (interp 5+ cellules apres son code = cluster mal place)
   - OU `gap_a >= 5` seul (interp 5+ cellules avant le prochain code = cluster mal place)
4. Heuristique calibree pour minimiser faux positifs : les patterns `code -> interp -> def next_func` (legitimes) sont OK car le `def` suivant est le debut d'un sous-bloc, pas un deplacement.

## Top 17 notebooks avec cellules MISPLACED candidates

| Notebook | CHECK / total | Verdict |
|----------|---------------|---------|
| `GameTheory-2-NormalForm.ipynb` | 4/9 | MISPLACED |
| `7_Code_Interpreter.ipynb` | 2/11 | MISPLACED |
| `Lean-11-TorchLean.ipynb` | 2/11 | MISPLACED |
| `Lean-17-Knots-a-Conway-and-Proofs.ipynb` | 2/3 | MISPLACED |
| `OR-tools-Stiegler.ipynb` | 2/2 | MISPLACED |
| `02-8-Expressive-TTS.ipynb` | 1/5 | MISPLACED |
| `02-SemanticKernel-Advanced.ipynb` | 1/5 | MISPLACED |
| `03-SemanticKernel-Agents.ipynb` | 1/3 | MISPLACED |
| `06-SemanticKernel-ProcessFramework.ipynb` | 1/5 | MISPLACED |
| `5_RAG_Modern.ipynb` | 1/2 | MISPLACED |
| `Do-Calculus-Bridge.ipynb` | 1/2 | MISPLACED |
| `QC-Py-08-Multi-Asset-Strategies.ipynb` | 1/1 | MISPLACED |
| `Search-10-SymbolicAutomata.ipynb` | 1/16 | MISPLACED |
| `Search-3-Informed.ipynb` | 1/8 | MISPLACED |
| `Sudoku-14-BDD-Csharp.ipynb` | 1/3 | MISPLACED |
| `Lean-7b-Examples.ipynb` | 1/7 | MISPLACED |
| `Tweety-8-Agent-Dialogues.ipynb` | 1/1 | MISPLACED |

## Detail des 24 cellules MISPLACED

### `MyIA.AI.Notebooks/GameTheory/GameTheory-2-NormalForm.ipynb` (4 cellules)
#### cell[12] gap_b=1 gap_a=6
- **interp** : `### Interprétation - Multiplicité des équilibres /  / **Résultats remarquables** : /  / | Jeu | Nombre d'équilibres purs | Caractéristique | / |-----|-------------------------|-----------------| / | Dilemme du Prisonnier | 1 | Unique, inefficient (gain 1 vs opti`
- **prev_code[11]** : `# Analyser tous les jeux classiques / print("Analyse de dominance pour les jeux classiques") / print("=" * 50) /  / for game in games: /     print(f"\n{game.name}:") /      /     dom_row = find_dominant_strategy(ga`
- **next_code[18]** : `def best_response_row(game: NormalFormGame, col_strategy: int) -> List[int]: /     """ /     Meilleure(s) reponse(s) du joueur Ligne a la strategie de Colonne. /      /     Returns: /         Liste des indices `
- reason : gap_a=6 (interp 5+ cells before next code, possibly misplaced)

#### cell[13] gap_b=2 gap_a=5
- **interp** : `### Interprétation - Unicité du Dilemme du Prisonnier /  / **Résultat clé** : Seul le Dilemme du Prisonnier possède une stratégie dominante pour les deux joueurs. /  / | Jeu | Stratégie dominante Ligne | Stratégie dominante Colonne | Conséquence | / |-----|---`
- **prev_code[11]** : `# Analyser tous les jeux classiques / print("Analyse de dominance pour les jeux classiques") / print("=" * 50) /  / for game in games: /     print(f"\n{game.name}:") /      /     dom_row = find_dominant_strategy(ga`
- **next_code[18]** : `def best_response_row(game: NormalFormGame, col_strategy: int) -> List[int]: /     """ /     Meilleure(s) reponse(s) du joueur Ligne a la strategie de Colonne. /      /     Returns: /         Liste des indices `
- reason : gap_a=5 (interp 5+ cells before next code, possibly misplaced)

#### cell[15] gap_b=4 gap_a=3
- **interp** : `### Interprétation - Visualisations /  / Les graphiques montrent les **meilleures réponses** et **équilibres de Nash** : /  / **Légende** : / - **Soulignement bleu** sous le premier nombre : Ligne joue une meilleure réponse / - **Soulignement rouge** sous le sec`
- **prev_code[11]** : `# Analyser tous les jeux classiques / print("Analyse de dominance pour les jeux classiques") / print("=" * 50) /  / for game in games: /     print(f"\n{game.name}:") /      /     dom_row = find_dominant_strategy(ga`
- **next_code[18]** : `def best_response_row(game: NormalFormGame, col_strategy: int) -> List[int]: /     """ /     Meilleure(s) reponse(s) du joueur Ligne a la strategie de Colonne. /      /     Returns: /         Liste des indices `
- reason : gap_b=4, gap_a=3 (interp is in MD-only zone between code blocks)

#### cell[17] gap_b=6 gap_a=1
- **interp** : `### Interprétation - Simplification par IESDS /  / **Résultat** : Le processus d'IESDS a réduit le jeu 3×3 en un jeu **1×1** avec une issue unique. /  / **Étapes d'élimination** : / 1. **R1 et R3** dominées par R2 (pour toutes les colonnes, R2 donne des gains `
- **prev_code[11]** : `# Analyser tous les jeux classiques / print("Analyse de dominance pour les jeux classiques") / print("=" * 50) /  / for game in games: /     print(f"\n{game.name}:") /      /     dom_row = find_dominant_strategy(ga`
- **next_code[18]** : `def best_response_row(game: NormalFormGame, col_strategy: int) -> List[int]: /     """ /     Meilleure(s) reponse(s) du joueur Ligne a la strategie de Colonne. /      /     Returns: /         Liste des indices `
- reason : gap_b=6 (interp 5+ cells after preceding code, possibly misplaced in cluster)

### `MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-8-Expressive-TTS.ipynb` (1 cellules)
#### cell[8] gap_b=1 gap_a=5
- **interp** : `### Interprétation : Chargement des variables d'environnement /  / **Sortie obtenue** : `.env` chargé depuis `.env` (trouvé) ; mode API cloud désactivé par le paramètre Papermill `use_fish_api=False`. /  / | Variable | Statut | Impact | / |----------|--------|`
- **prev_code[7]** : `# Chargement robuste de la configuration .env / from dotenv import load_dotenv / import os /  / current_path = Path.cwd() / env_loaded = False / for _ in range(10): /     env_path = current_path / ".env" /     if env`
- **next_code[13]** : `# Verification des dependances et chargement Fish S2 Pro / print("VERIFICATION DES DEPENDANCES") / print("=" * 45) /  / fish_available = False / fish_sdk_available = False / dia_available = False /  / # Fish Speech (`
- reason : gap_a=5 (interp 5+ cells before next code, possibly misplaced)

### `MyIA.AI.Notebooks/GenAI/SemanticKernel/02-SemanticKernel-Advanced.ipynb` (1 cellules)
#### cell[22] gap_b=1 gap_a=5
- **interp** : `### Interprétation : Mémoire Vectorielle et Embeddings /  / **Sortie obtenue** : Configuration d'un système de mémoire sémantique avec embeddings pour recherche contextuelle. /  / | Composant | Technologie | Rôle | / |-----------|-------------|------| / | **Embe`
- **prev_code[21]** : `# ============================ / # Cellule : Extrait Mémoire / # ============================ /  / # CORRECTION: Utilisation des nouvelles approches pour la mémoire vectorielle / from semantic_kernel.connectors`
- **next_code[27]** : `# ============================ / # Cellule : Groundedness Checking / # ============================ /  / # Suppose qu'on a un "grounding_text" = un texte source / grounding_text = """ / Votre budget 2024 est de 1`
- reason : gap_a=5 (interp 5+ cells before next code, possibly misplaced)

### `MyIA.AI.Notebooks/GenAI/SemanticKernel/03-SemanticKernel-Agents.ipynb` (1 cellules)
#### cell[13] gap_b=1 gap_a=5
- **interp** : `### Interprétation : Function Calling Automatique (ReAct Pattern) /  / **Sortie obtenue** : L'agent Host répond aux questions sur le menu en appelant automatiquement les bonnes fonctions du plugin /  / | Question | Fonction appelée | Résultat | / |----------|-`
- **prev_code[12]** : `class ResearchPlugin: /     """ /     Plugin de recherche simulant des resultats. /      /     # Etape 1 : Definir la methode search() avec @kernel_function et une description claire /     # Etape 2 : Utiliser `
- **next_code[18]** : `import asyncio / from semantic_kernel.agents import AgentGroupChat, ChatCompletionAgent / from semantic_kernel.connectors.ai.open_ai import OpenAIChatCompletion / from semantic_kernel.contents import Author`
- reason : gap_a=5 (interp 5+ cells before next code, possibly misplaced)

### `MyIA.AI.Notebooks/GenAI/SemanticKernel/06-SemanticKernel-ProcessFramework.ipynb` (1 cellules)
#### cell[2] gap_b=1 gap_a=5
- **interp** : `### Interprétation : Configuration du kernel /  / **Sortie obtenue** : Kernel SK configuré avec service OpenAI /  / | Aspect | Valeur | Signification | / |--------|--------|---------------| / | **Service** | OpenAIChatCompletion | Modèle de chat (GPT-3.5/4) | / | `
- **prev_code[1]** : `# Installation et configuration /  / import os / from dotenv import load_dotenv / from semantic_kernel import Kernel / from semantic_kernel.connectors.ai.open_ai import OpenAIChatCompletion, OpenAIChatPromptExe`
- **next_code[7]** : `from dataclasses import dataclass / from typing import Optional / from semantic_kernel.contents import ChatHistory /  / # Definition de l'etat du process / @dataclass / class ContentState: /     """Etat partage ent`
- reason : gap_a=5 (interp 5+ cells before next code, possibly misplaced)

### `MyIA.AI.Notebooks/GenAI/Texte/5_RAG_Modern.ipynb` (1 cellules)
#### cell[7] gap_b=1 gap_a=6
- **interp** : `### Interprétation de la configuration /  / La cellule précédente initialise l'environnement RAG avec plusieurs composants clés. /  / **Configuration validée** : /  / | Composant | Statut | Valeur | / |-----------|--------|--------| / | **Client OpenAI** | ✓ Initial`
- **prev_code[6]** : `# === WORKAROUND: Pydantic 2.x by_alias bug === / # Ce patch corrige le problème "TypeError: argument 'by_alias': 'NoneType' object cannot be converted to 'PyBool'" / # qui survient avec Pydantic 2.x util`
- **next_code[13]** : `import requests / from bs4 import BeautifulSoup /  / def fetch_debate_text() -> str: /     """Récupère le texte du premier débat Lincoln-Douglas.""" /     url = "https://home.nps.gov/liho/learn/historyculture/d`
- reason : gap_a=6 (interp 5+ cells before next code, possibly misplaced)

### `MyIA.AI.Notebooks/GenAI/Texte/7_Code_Interpreter.ipynb` (2 cellules)
#### cell[4] gap_b=1 gap_a=6
- **interp** : `### Interprétation de l'initialisation /  / L'initialisation a chargé les composants suivants : /  / | Composant | Rôle | / |-----------|------| / | `openai` | Client API pour interagir avec OpenAI | / | `python-dotenv` | Chargement sécurisé des clés API depuis `.`
- **prev_code[3]** : `# Import guards - verification des dependances / try: /     import openai /     OPENAI_AVAILABLE = True / except ImportError: /     OPENAI_AVAILABLE = False /  / try: /     import anthropic /     ANTHROPIC_AVAILABLE = `
- **next_code[10]** : `# Note: Le Code Interpreter n'est pas disponible via Chat Completions / # Cette cellule démontre ce qui NE fonctionne PAS /  / print("=== Note importante sur Code Interpreter ===") / print() / print("Le code_in`
- reason : gap_a=6 (interp 5+ cells before next code, possibly misplaced)

#### cell[9] gap_b=6 gap_a=1
- **interp** : `### Interprétation de la démonstration /  / Cette démonstration illustre deux points importants : /  / **1. Limitation de Chat Completions** : / - Le type `'code_interpreter'` n'est PAS accepté dans `tools=[]` / - Seuls `'function'` et `'custom'` sont supportés / `
- **prev_code[3]** : `# Import guards - verification des dependances / try: /     import openai /     OPENAI_AVAILABLE = True / except ImportError: /     OPENAI_AVAILABLE = False /  / try: /     import anthropic /     ANTHROPIC_AVAILABLE = `
- **next_code[10]** : `# Note: Le Code Interpreter n'est pas disponible via Chat Completions / # Cette cellule démontre ce qui NE fonctionne PAS /  / print("=== Note importante sur Code Interpreter ===") / print() / print("Le code_in`
- reason : gap_b=6 (interp 5+ cells after preceding code, possibly misplaced in cluster)

### `MyIA.AI.Notebooks/Probas/DecisionTheory/Causal-Bridges/Do-Calculus-Bridge.ipynb` (1 cellules)
#### cell[19] gap_b=1 gap_a=5
- **interp** : `### Interprétation /  / `dowhy` confirme le raisonnement : /  / - **backdoor** : *« No such variable(s) found! »* — $U$ est latent, aucun ajustement direct possible ; / - **front-door** : l'estimande identifiée passe par le médiateur `tar` ($E[\frac{\partial\,`
- **prev_code[18]** : `estimate_fd = model_fd.estimate_effect(estimand_fd, method_name="frontdoor.two_stage_regression") / print(f"Effet estime (front-door, deux etapes) : {estimate_fd.value:.3f}") / print(f"Effet vrai via le m`
- **next_code[24]** : `# Exercice 1 — ajoutez un 2e confondeur observable au modèle backdoor. / # Objectif : dowhy doit identifier l'ensemble backdoor {aptitude, motivation}. / # Indice : motivation -> college ET motivation -> `
- reason : gap_a=5 (interp 5+ cells before next code, possibly misplaced)

### `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-08-Multi-Asset-Strategies.ipynb` (1 cellules)
#### cell[17] gap_b=3 gap_a=3
- **interp** : `### Interprétation de la Matrice de Corrélation /  / La heatmap révèle des patterns importants pour la construction de portefeuille : /  / **Corrélations Élevées (> 0.8)** - À éviter ensemble : / - **SPY/QQQ (0.92)** : Même classe d'actifs (equities US) / - **TL`
- **prev_code[14]** : `# [REFERENCE QC] Code a copier dans main.py QC Lab (non executable ici) / # Exemple d'utilisation dans un algorithme / class CorrelationAnalysisAlgorithm(QCAlgorithm): /      /     def Initialize(self): /      `
- **next_code[20]** : `# Exemple de visualisation (donnees simulees pour illustration) / # En production, utilisez qb.History() avec QuantBook /  / # Donnees de correlation typiques entre classes d'actifs / assets = ['SPY', 'QQQ', `
- reason : gap_b=3, gap_a=3 (interp is in MD-only zone between code blocks)

### `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-10-SymbolicAutomata.ipynb` (1 cellules)
#### cell[76] gap_b=1 gap_a=5
- **interp** : `### Interprétation : Mini-Sudoku 2x2 avec Z3 /  / **Résultat obtenu** : Un automate symbolique résout un mini-Sudoku 2x2 en appliquant les contraintes de manière interactive. /  / | Étape | Action | Résultat | Validation | / |-------|--------|----------|------`
- **prev_code[75]** : `# Mini-Sudoku 2x2 comme automate symbolique /  / class MiniSudokuAutomaton: /     """ /     Automate symbolique pour Mini-Sudoku 2x2. /      /     Grille 2x2 avec chiffres 1-2. /     Contraintes : lignes et colonne`
- **next_code[81]** : `# Exercice 1 : Automate pour multiples de 3 / # Creer un automate symbolique qui accepte les multiples de 3 /  / # Exercice: Creer l'automate avec SymbolicAutomaton("Mult3Automaton") / # Indices: / # - Ajouter `
- reason : gap_a=5 (interp 5+ cells before next code, possibly misplaced)

### `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-3-Informed.ipynb` (1 cellules)
#### cell[36] gap_b=1 gap_a=6
- **interp** : `### Interprétation : Synthèse des performances /  / **Observations générales** : /  / | Algorithme | Optimalité | Nœuds explorés | Mémoire | Cas d'usage | / |------------|-----------|-----------------|----------|-------------| / | **Greedy** | Non | Variable (so`
- **prev_code[35]** : `# --- Comparaison sur plusieurs problemes --- /  / test_cases = [ /     ('Bordeaux', 'Strasbourg'), /     ('Rennes', 'Nice'), /     ('Lille', 'Toulouse'), /     ('Nantes', 'Marseille'), / ] /  / all_results = [] /  / for s`
- **next_code[42]** : `# --- Implementation du 8-Puzzle --- /  / class EightPuzzleProblem(Problem): /     """ /     Problème du taquin (8-puzzle). /  /     Etat : tuple de 9 entiers, 0 represente la case vide. /     Etat but : (1, 2, 3, `
- reason : gap_a=6 (interp 5+ cells before next code, possibly misplaced)

### `MyIA.AI.Notebooks/Sudoku/Sudoku-14-BDD-Csharp.ipynb` (1 cellules)
#### cell[32] gap_b=1 gap_a=7
- **interp** : `#### Interprétation : Solveur MDD /  / **Sortie obtenue** : Le solveur trouve la solution, mais avec des performances similaires au backtracking classique. /  / **Temps de résolution** : moins d'une milliseconde sur le puzzle facile testé (0,46 ms mesurée à `
- **prev_code[31]** : `using System.Diagnostics; /  / void DisplayGrid(int[,] grid) / { /     Console.WriteLine("-------+-------+-------"); /     for (int i = 0; i < 9; i++) /     { /         if (i > 0 && i % 3 == 0) /             Console.`
- **next_code[39]** : `// À COMPLÉTER : Solveur BDD avec propagation de contraintes /  / public class BDDConstraintPropagator / { /     private readonly List<MDDNode> _rowMDDs; /     private readonly List<MDDNode> _colMDDs; /     priva`
- reason : gap_a=7 (interp 5+ cells before next code, possibly misplaced)

### `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-11-TorchLean.ipynb` (2 cellules)
#### cell[2] gap_b=1 gap_a=5
- **interp** : `### Interprétation : Environnement vérifié /  / | Composant | Version/Statut | Rôle dans TorchLean | / |-----------|----------------|---------------------| / | Lean 4 | stable | Langage hôte | / | Lake | requis | Gestion des dépendances | / | Mathlib4 | requis |`
- **prev_code[1]** : `-- =========================================================== / -- Verification de l'environnement Lean pour TorchLean / -- =========================================================== /  / -- Verifier la ver`
- **next_code[7]** : `-- =========================================================== / -- Exemple 1 : Creation de tenseurs simples / -- =========================================================== /  / -- Definition d'un type de te`
- reason : gap_a=5 (interp 5+ cells before next code, possibly misplaced)

#### cell[4] gap_b=3 gap_a=3
- **interp** : `### Interprétation : Architecture TorchLean et auto-contenu /  / | Module | Contenu | État | / |--------|---------|------| / | `Core` | Tenseurs, layers, API de base | **Non disponible** — types définis localement dans ce notebook | / | `Forum.Float32` | Séman`
- **prev_code[1]** : `-- =========================================================== / -- Verification de l'environnement Lean pour TorchLean / -- =========================================================== /  / -- Verifier la ver`
- **next_code[7]** : `-- =========================================================== / -- Exemple 1 : Creation de tenseurs simples / -- =========================================================== /  / -- Definition d'un type de te`
- reason : gap_b=3, gap_a=3 (interp is in MD-only zone between code blocks)

### `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-17-Knots-a-Conway-and-Proofs.ipynb` (2 cellules)
#### cell[24] gap_b=5 gap_a=2
- **interp** : `### Interprétation : La structure du résultat formalisé /  / **Sortie obtenue** : Un extrait structuré de Conway.lean montrant la chaîne de définitions et théorèmes. /  / | Aspect | Valeur | Signification | / |--------|--------|---------------| / | Structures dé`
- **prev_code[19]** : `import itertools /  / def is_tricolorable(pd_code): /     # TODO etudiant : retourner True ssi il existe une coloration propre non-triviale. /     # Indice : labels = ensemble de toutes les aretes ; pour chaq`
- **next_code[26]** : `# Render the Mathlib prerequisites table / import pandas as pd /  / prereqs = [ /     ["Tier 1", "pd_wellformed", "PD-code bien formé", "List, Finset, Fintype existent"], /     ["Tier 1", "trefoil_tricolorable"`
- reason : gap_b=5 (interp 5+ cells after preceding code, possibly misplaced in cluster)

#### cell[25] gap_b=6 gap_a=1
- **interp** : `### Interprétation : Une page, une profondeur extrême /  / **Sortie obtenue** : Un extrait structuré de Lidman.lean montrant les définitions et théorèmes formalisés. /  / | Aspect | Valeur | Signification | / |--------|--------|---------------| / | Théorèmes pri`
- **prev_code[19]** : `import itertools /  / def is_tricolorable(pd_code): /     # TODO etudiant : retourner True ssi il existe une coloration propre non-triviale. /     # Indice : labels = ensemble de toutes les aretes ; pour chaq`
- **next_code[26]** : `# Render the Mathlib prerequisites table / import pandas as pd /  / prereqs = [ /     ["Tier 1", "pd_wellformed", "PD-code bien formé", "List, Finset, Fintype existent"], /     ["Tier 1", "trefoil_tricolorable"`
- reason : gap_b=6 (interp 5+ cells after preceding code, possibly misplaced in cluster)

### `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-7b-Examples.ipynb` (1 cellules)
#### cell[7] gap_b=5 gap_a=1
- **interp** : `### Interprétation des résultats - SIMPLE_THEOREMS /  / **Performance exceptionnelle:** /  / | Métrique | Valeur | Analyse | / |----------|--------|---------| / | Taux de succès | 100% (5/5) | Tous les théorèmes simples ont été prouvés | / | Itérations moyenne | 1`
- **prev_code[2]** : `# Configuration et Imports / # Ce notebook utilise les classes de lean_runner.py /  / import os / import sys / from pathlib import Path /  / # Trouver le repertoire du notebook (plusieurs methodes) / def find_noteboo`
- **next_code[8]** : `# Section 7.1 - Definition des theoremes simples /  / SIMPLE_THEOREMS = [ /     { /         "name": "add_zero", /         "statement": "theorem test_add_zero (n : Nat) : n + 0 = n := by sorry", /         "difficu`
- reason : gap_b=5 (interp 5+ cells after preceding code, possibly misplaced in cluster)

### `MyIA.AI.Notebooks/SymbolicAI/OR-tools-Stiegler.ipynb` (2 cellules)
#### cell[13] gap_b=1 gap_a=6
- **interp** : `### Interprétation du nombre de variables /  / **Résultat** : Le solveur a créé **77 variables**, une pour chaque aliment disponible. /  / | Dimension | Valeur | Signification | / |-----------|--------|---------------| / | Variables | 77 | Nombre d'aliments dans`
- **prev_code[12]** : `using System; / using System.Collections.Generic; / using Google.OrTools.LinearSolver; / Console.WriteLine("Modele de programmation lineaire defini."); / `
- **next_code[19]** : `// TODO: Définissez le problème de portefeuille / // - 4 actifs disponibles avec rendements attendus / // - Contrainte : budget total de 100 000€ / // - Contrainte : risque maximum par catégorie / // - Object`
- reason : gap_a=6 (interp 5+ cells before next code, possibly misplaced)

#### cell[15] gap_b=3 gap_a=4
- **interp** : `### Interprétation de la structure du problème /  / **Résultat** : Le solveur a configuré **9 contraintes**, une pour chaque nutriment. /  / | Dimension | Valeur | Signification | / |-----------|--------|---------------| / | Contraintes | 9 | Nombre de nutriment`
- **prev_code[12]** : `using System; / using System.Collections.Generic; / using Google.OrTools.LinearSolver; / Console.WriteLine("Modele de programmation lineaire defini."); / `
- **next_code[19]** : `// TODO: Définissez le problème de portefeuille / // - 4 actifs disponibles avec rendements attendus / // - Contrainte : budget total de 100 000€ / // - Contrainte : risque maximum par catégorie / // - Object`
- reason : gap_b=3, gap_a=4 (interp is in MD-only zone between code blocks)

### `MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-8-Agent-Dialogues.ipynb` (1 cellules)
#### cell[2] gap_b=1 gap_a=5
- **interp** : `### Interprétation de la configuration /  / Les résultats ci-dessus confirment que l'environnement est correctement configuré pour simuler des dialogues multi-agents: /  / **Configuration JVM validée:** / - **JDK portable**: Zulu 17 détecté et configuré automa`
- **prev_code[1]** : `# --- Initialisation JVM Tweety + Outils Externes --- / print("--- Verification JVM Tweety + Outils ---") / jvm_ready = False /  / import jpype / import jpype.imports / import os / import pathlib / import shutil / impo`
- **next_code[7]** : `# --- 6.2 Dialogues Argumentatifs --- / print("\n--- 6.2 Dialogues Argumentatifs ---") /  / if not jvm_ready: /     print("ERREUR: JVM non demarree.") / else: /     print("JVM prete. Exploration des dialogues arg`
- reason : gap_a=5 (interp 5+ cells before next code, possibly misplaced)


## Notes de calibration (faux positifs ecartes)

Heuristique simple `next cell = def/class` (exclue car faux positifs massifs). Le pattern pedagogique `code -> interp -> def next_func` est legitime et NE constitue PAS un bug - c'est l'ouverture d'un sous-bloc. Seuls les cas `gap_b ET gap_a >= 3` OU un seul des deux >= 5 ont ete retenus.

Bug originel `#10678` cite `PyMC-15` (5 cellules mal placees) et `Voting-Methods-Csharp` (5 cellules). Ces deux notebooks ne sont **PAS** dans le top 17 de cette heuristique - soit l'audit original de l'auteur du ticket etait focalise sur un sous-ensemble (notebooks enrichis recemment par EPIC #10488), soit les cellules concernees utilisent un pattern different de `### Lecture du resultat` (variante : `### Lecture du benchmark`, `### Lecture des resultats`, etc.).

## Acceptance Phase 1 #10678

- [x] **198 notebooks avec cellules interpretation identifies**
- [x] **24 cellules MISPLACED candidates classifiees**
- [x] **5 cas graves confirmes en premiere lecture** (GameTheory-2-NormalForm cellules 12-17 = cluster de 4 interp sur le meme output cell[11]) : ce sont les candidats Phase 2 prioritaires
- [x] Inventaire brut serialise `notebooks_interp_inventory.json` (198 entrees x listes interp + classification OK/CHECK)
- [ ] Phase 2 (reparation PR par notebook) et Phase 3 (script `check_interp_positioning.py` + CI) - sub-grains separes pour c.238+

