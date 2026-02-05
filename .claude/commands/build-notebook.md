# Build Notebook Command

Construit ou améliore des notebooks Jupyter de manière itérative.

## Usage

```
/build-notebook <action> <notebook_path> [options]
```

## Arguments

- `action`: Type d'action
  - `new`: Créer un nouveau notebook
  - `improve`: Améliorer un notebook existant
  - `fix`: Corriger les erreurs d'exécution

- `notebook_path`: Chemin du notebook
  - Pour `new`: Chemin où créer le notebook
  - Pour `improve`/`fix`: Notebook existant à modifier

- Options:
  - `--topic=<topic>`: Sujet du notebook (requis pour new)
  - `--domain=<domain>`: Domaine (ML, Probas, GenAI, GameTheory, etc.)
  - `--level=<level>`: Niveau (intro, intermediate, advanced)
  - `--quality=<score>`: Score qualité cible (0-100, défaut: 90)
  - `--max-iter=<n>`: Nombre max d'itérations (défaut: 5)
  - `--focus=<areas>`: Zones à améliorer (execution, pedagogy, content, structure)

## Instructions pour Claude

### 1. Charger l'agent notebook-iterative-builder

L'agent complet est dans `.claude/agents/notebook-iterative-builder.md`.

### 2. Workflow selon l'action

#### Action: new

```
1. Design      → notebook-designer crée la structure
2. Execute     → notebook-executor vérifie le code
3. Validate    → notebook-validator évalue la qualité
4. Enrich      → notebook-enricher ajoute du contenu
5. Fix         → notebook-cell-iterator corrige les erreurs
6. Re-validate → Vérifier le score cible
7. Iterate     → Répéter jusqu'à quality_target
```

#### Action: improve

```
1. Analyze     → Analyser la structure existante
2. Validate    → Identifier les points faibles
3. Enrich      → Ajouter du contenu pédagogique
4. Execute     → Vérifier que tout fonctionne
5. Re-validate → Mesurer l'amélioration
6. Iterate     → Répéter jusqu'à quality_target
```

#### Action: fix

```
1. Execute     → Identifier les erreurs d'exécution
2. Fix         → Corriger via notebook-cell-iterator
3. Validate    → Vérifier que les erreurs sont corrigées
4. Iterate     → Répéter jusqu'à 0 erreur
```

### 3. Agents utilisés

| Agent | Fichier | Rôle |
|-------|---------|------|
| notebook-designer | `.claude/agents/notebook-designer.md` | Créer structure initiale |
| notebook-executor | `.claude/agents/notebook-executor.md` | Exécuter le notebook |
| notebook-validator | `.claude/agents/notebook-validator.md` | Valider tous aspects |
| notebook-enricher | `.claude/agents/notebook-enricher.md` | Ajouter contenu pédagogique |
| notebook-cell-iterator | `.claude/agents/notebook-cell-iterator.md` | Corriger cellules |
| notebook-cleaner | `.claude/agents/notebook-cleaner.md` | Nettoyer structure |

### 4. Critères de qualité

Score global = moyenne pondérée :

| Catégorie | Poids | Critères |
|-----------|-------|----------|
| Structure | 15% | JSON valide, metadata, cellules |
| Syntaxe | 15% | Code valide, markdown, LaTeX |
| Exécution | 30% | Pas d'erreurs, pas de timeout |
| Pédagogie | 25% | Progression, ratio code/markdown, explications |
| Contenu | 15% | Visualisations, formules, conclusion |

### 5. Pour notebooks GenAI

Utiliser les scripts dans `scripts/genai-stack/` :

```bash
# Valider la stack avant construction
python scripts/genai-stack/validate_stack.py

# Vérifier les services requis
python scripts/genai-stack/check_vram.py

# Valider les notebooks
python scripts/genai-stack/validate_notebooks.py <path>
```

### 6. Rapport d'itération

```markdown
# Build Report: {notebook_name}

Mode: {new|improve|fix}
Final Status: SUCCESS | PARTIAL | FAILED

## Iteration History

| Iter | Structure | Syntax | Execution | Pedagogy | Content | Overall |
|------|-----------|--------|-----------|----------|---------|---------|
| 1    | 85%       | 90%    | 70%       | 60%      | 65%     | 72%     |
| 2    | 90%       | 95%    | 85%       | 75%      | 70%     | 82%     |
| 3    | 95%       | 100%   | 95%       | 85%      | 80%     | 90%     |

Final score: 90% ✅ (target: 90%)

## Actions Applied

- Iteration 1: Fixed 2 errors, added 3 markdown cells
- Iteration 2: Optimized cell 30, added interpretations
- Iteration 3: Improved introduction
```

## Exemples

```
/build-notebook new MyIA.AI.Notebooks/ML/SVM-Intro.ipynb --topic="Support Vector Machines" --domain=ML --level=intermediate
/build-notebook improve MyIA.AI.Notebooks/Probas/Infer/Infer-2.ipynb --quality=95 --focus=pedagogy,content
/build-notebook fix MyIA.AI.Notebooks/GameTheory/GameTheory-15.ipynb --max-iter=5
```

## Agent associé

Pour des workflows complexes :

```python
Task(
    subagent_type="general-purpose",
    prompt="""
    Tu es un agent notebook-iterative-builder.
    Lis .claude/agents/notebook-iterative-builder.md

    Mode: improve
    Notebook path: MyIA.AI.Notebooks/GenAI/Image/01-Foundation/01-1-DALLE3.ipynb
    Quality target: 90
    Max iterations: 5
    Focus areas: ["execution", "pedagogy"]
    """,
    description="Build notebook"
)
```

## Domaines supportés

| Domaine | Spécificités |
|---------|-------------|
| ML | Métriques, courbes d'apprentissage, matrices de confusion |
| Probas | Distributions, priors/posteriors, formules Bayes |
| GenAI | APIs image, prompts, authentification services |
| GameTheory | Équilibres Nash, Shapley, arbres de jeu |
| SymbolicAI | Logique formelle, preuves, satisfiabilité |
| Sudoku/Search | Contraintes, algorithmes génétiques |
