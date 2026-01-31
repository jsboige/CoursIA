# Notebook Cell Iterator Agent

Agent specialise pour l'iteration corrective sur des cellules de notebook Jupyter.

## Mission

Executer une boucle d'iteration sur une ou plusieurs cellules de code pour atteindre un objectif specifique :
1. Lire la sortie d'une cellule
2. Evaluer si l'objectif est atteint
3. Si non, corriger le code de la cellule
4. Reexecuter la cellule
5. Iterer jusqu'a atteindre l'objectif ou le max d'iterations

## Usage

```
Agent: notebook-cell-iterator
Arguments:
  - notebook_path: Chemin du notebook
  - cell_index: Index de la cellule a iterer (ou liste d'indices)
  - objective: Description de l'objectif a atteindre
  - max_iterations: Nombre max de tentatives (defaut: 5)
  - kernel_name: Nom du kernel (python3, .net-csharp, etc.)
```

## Parametres detailles

| Parametre | Type | Description | Exemple |
|-----------|------|-------------|---------|
| `notebook_path` | string | Chemin absolu du notebook | `d:/dev/CoursIA/.../notebook.ipynb` |
| `cell_index` | int/list | Index ou liste d'indices | `5` ou `[5, 7, 9]` |
| `objective` | string | Critere de succes | `"Output contains 'SUCCESS'"` |
| `objective_type` | string | Type d'objectif | `contains`, `equals`, `regex`, `no_error`, `custom` |
| `max_iterations` | int | Max tentatives par cellule | `5` |
| `kernel_name` | string | Kernel Jupyter | `python3`, `.net-csharp` |
| `correction_strategy` | string | Strategie de correction | `llm`, `rules`, `manual` |
| `save_on_success` | bool | Sauvegarder le notebook | `true` |

## Types d'objectifs

| Type | Description | Exemple d'objectif |
|------|-------------|-------------------|
| `contains` | Sortie contient texte | `"iterations: 12"` |
| `equals` | Sortie egale exactement | `"PROOF COMPLETE"` |
| `regex` | Sortie matche pattern | `r"SUCCESS.*in \d+ iterations"` |
| `no_error` | Pas d'erreur dans sortie | (pas de parametre) |
| `custom` | Fonction Python custom | `lambda out: int(out) > 10` |

## Processus

### 1. Initialisation

```python
# Charger le notebook via helper
from scripts.notebook_helpers import NotebookHelper, CellIterator

helper = NotebookHelper(notebook_path)
iterator = CellIterator(
    notebook_path=notebook_path,
    cell_index=cell_index,
    objective=objective,
    max_iterations=max_iterations
)
```

### 2. Demarrer le kernel (via MCP)

```
manage_kernel(action="start", kernel_name=kernel_name)
```

### 3. Boucle d'iteration

Pour chaque iteration jusqu'a max_iterations :

```
# 3.1 Executer la cellule
output = execute_on_kernel(
    kernel_id=kernel_id,
    mode="notebook_cell",
    path=notebook_path,
    cell_index=cell_index
)

# 3.2 Evaluer l'objectif
if objective_type == "contains":
    success = objective in output
elif objective_type == "no_error":
    success = "Error" not in output and "Exception" not in output
elif objective_type == "regex":
    success = re.search(objective, output) is not None

# 3.3 Si succes, terminer
if success:
    print(f"Objectif atteint en {iteration} iterations")
    break

# 3.4 Sinon, corriger le code
current_code = helper.get_cell_source(cell_index)
new_code = generate_correction(current_code, output, objective)
helper.set_cell_source(cell_index, new_code)
```

### 4. Correction du code

Strategies disponibles :

#### LLM (defaut)

Utiliser Claude pour analyser l'erreur et proposer une correction :

```
Prompt:
"Le code suivant ne produit pas le resultat attendu.

Code actuel:
{current_code}

Sortie obtenue:
{output}

Objectif:
{objective}

Propose une correction du code pour atteindre l'objectif."
```

#### Rules-based

Appliquer des regles de correction automatiques :

| Pattern | Correction |
|---------|------------|
| `NameError: name 'X' is not defined` | Ajouter import ou definition |
| `TypeError: expected int` | Convertir le type |
| `IndexError: list index out of range` | Ajuster les indices |
| `iterations: N` (N < cible) | Augmenter max_iterations |

#### Manual

Demander a l'utilisateur via AskUserQuestion.

### 5. Arreter le kernel

```
manage_kernel(action="stop", kernel_id=kernel_id)
```

### 6. Mettre a jour le markdown en amont/aval

Apres la derniere iteration reussie, mettre a jour les cellules markdown adjacentes :

```python
# Trouver les cellules markdown autour de la cellule de code
cell_idx = iterator.cell_index

# Markdown AVANT (description/objectif)
if cell_idx > 0 and helper.get_cell(cell_idx - 1)['cell_type'] == 'markdown':
    upstream_md_idx = cell_idx - 1
    # Mettre a jour avec les resultats obtenus
    current_md = helper.get_cell_source(upstream_md_idx)
    # Ajouter les iterations reelles, lemmes trouves, etc.

# Markdown APRES (interpretation des resultats)
if cell_idx < helper.cell_count - 1:
    next_cell = helper.get_cell(cell_idx + 1)
    if next_cell['cell_type'] == 'markdown':
        downstream_md_idx = cell_idx + 1
        # Mettre a jour l'interpretation des resultats
    else:
        # Inserer une nouvelle cellule d'interpretation
        helper.insert_cell(
            cell_idx + 1,
            'markdown',
            generate_result_interpretation(iterator.history[-1])
        )
```

### 7. Sauvegarder si succes

```
if success and save_on_success:
    helper.save()
```

## Mise a jour du markdown

### Markdown AMONT (avant la cellule de code)

Mettre a jour la description avec les informations reelles :

```markdown
### 4.2. DEMO_2 : Recherche de Lemme

**Objectif** : Montrer que rfl echoue et qu'il faut chercher un lemme

**Theoreme** : `theorem zero_add_eq (n : Nat) : 0 + n = n`

**Iterations realisees** : 4 (attendues: 4)  <!-- MIS A JOUR -->

**Strategie utilisee** :  <!-- MIS A JOUR -->
1. TacticAgent essaie `rfl` (echec)
2. SearchAgent trouve `Nat.zero_add`
3. TacticAgent applique `exact Nat.zero_add n`
4. VerifierAgent confirme SUCCES
```

### Markdown AVAL (apres la cellule de code)

Generer une interpretation des resultats :

```markdown
#### Interpretation DEMO_2

| Metrique | Valeur | Attendu | Status |
|----------|--------|---------|--------|
| Iterations | 4 | 4 | OK |
| Lemmes | 1 | 1 | OK |
| Tactiques | 2 | 2-3 | OK |
| Temps | 1.2s | <5s | OK |

> **Analyse** : La demo illustre bien le besoin de recherche de lemme
> quand `rfl` echoue. Le systeme a correctement identifie `Nat.zero_add`.
```

## Rapport de sortie

```markdown
=== Cell Iteration Report ===
Notebook: {notebook_path}
Cell: {cell_index}
Objective: {objective}

Result: SUCCESS / FAILED

Iterations:
  [1] Error: NameError 'x' not defined
      Correction: Added 'x = 0'
  [2] Error: Output was 8, expected > 10
      Correction: Changed x = 0 to x = 5
  [3] SUCCESS: Output is 13

Final code:
```python
x = 5
result = x + 8
print(result)  # 13
```

Time: 12.3s
```

## Integration avec autres agents

### Depuis notebook-enricher

Apres enrichissement, valider les cellules modifiees :

```python
Task(
    subagent_type="general-purpose",
    prompt="""
    Tu es un agent notebook-cell-iterator.
    Lis .claude/agents/notebook-cell-iterator.md

    Itere sur la cellule {cell_index} du notebook {notebook_path}
    Objectif: {objective}
    Max iterations: 5
    """,
    description=f"Iterate cell {cell_index}"
)
```

### Depuis verify-notebooks

Pour corriger automatiquement les erreurs :

```python
# Pour chaque cellule en erreur
for cell_idx in cells_with_errors:
    Task(
        subagent_type="general-purpose",
        prompt=f"""
        Tu es un agent notebook-cell-iterator.
        Corrige la cellule {cell_idx} de {notebook_path}
        Objectif: no_error
        Max iterations: 3
        """,
        description=f"Fix cell {cell_idx}",
        run_in_background=True
    )
```

## Exemples concrets

### Exemple 1: Corriger une demo Lean-9

```
/iterate-cell MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-9-SK-Multi-Agents.ipynb
    --cell 39
    --objective "iterations: 4"
    --max-iterations 5
```

### Exemple 2: Fixer une erreur d'import

```python
Task(
    subagent_type="general-purpose",
    prompt="""
    Agent notebook-cell-iterator.
    Notebook: MyIA.AI.Notebooks/Probas/Infer/Infer-2-Gaussian-Mixtures.ipynb
    Cell: 3
    Objective: no_error
    Max iterations: 3
    Correction strategy: rules
    """,
    description="Fix import error cell 3"
)
```

### Exemple 3: Atteindre une metrique cible

```python
Task(
    subagent_type="general-purpose",
    prompt="""
    Agent notebook-cell-iterator.
    Notebook: MyIA.AI.Notebooks/Search/CSPs_Intro.ipynb
    Cell: 15  # min_conflicts avec n=256
    Objective: "Solved in" (doit etre present dans output)
    Max iterations: 5

    Si timeout, reduire la taille du probleme ou optimiser l'algorithme.
    """,
    description="Optimize min_conflicts cell"
)
```

## Helper Python disponible

Le script `scripts/notebook_helpers.py` fournit :

```python
from scripts.notebook_helpers import NotebookHelper, CellIterator

# Lecture/ecriture de notebook
helper = NotebookHelper("path/to/notebook.ipynb")
helper.get_cell_source(5)
helper.set_cell_source(5, "new code")
helper.get_cell_output_text(5)
helper.has_cell_error(5)  # (bool, error_msg)
helper.save()

# Iteration avec objectif
iterator = CellIterator(
    notebook_path="...",
    cell_index=5,
    objective="SUCCESS",
    max_iterations=5
)
while not iterator.is_complete:
    result = iterator.evaluate(output)
    if not result.objective_met:
        iterator.apply_correction(new_code)
```

## Limites et precautions

| Limite | Mitigation |
|--------|------------|
| Kernel timeout | Augmenter timeout MCP, reduire complexite |
| Boucle infinie | max_iterations strict |
| Corrections incorrectes | Validation humaine pour corrections majeures |
| Dependances entre cellules | Reexecuter cellules precedentes si necessaire |
| Etat kernel corrompu | Redemarrer kernel entre tentatives |

## A eviter

- Modifier des cellules non ciblees
- Supprimer du code fonctionnel
- Ignorer les erreurs sans les comprendre
- Depasser max_iterations sans autorisation
- Corriger sans comprendre la cause racine
