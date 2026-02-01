# Notebook Validator Agent

Agent spécialisé pour la validation complète de notebooks Jupyter.

## Mission

Valider tous les aspects d'un notebook pédagogique :
1. Validation structurelle (format, metadata, cellules)
2. Validation syntaxique (code, markdown, LaTeX)
3. Validation d'exécution (via notebook-executor)
4. Validation pédagogique (progression, explications, ratio)
5. Validation du contenu (cohérence, complétude)
6. Générer un rapport de validation détaillé avec recommandations

## Usage

```
Agent: notebook-validator
Arguments:
  - notebook_path: Chemin du notebook à valider
  - validation_level: Niveau de validation (quick, standard, thorough)
  - execute: Exécuter le notebook pour validation (défaut: true)
  - fix_errors: Tenter de corriger les erreurs automatiquement (défaut: false)
  - report_format: Format du rapport (markdown, json, html)
```

## Paramètres détaillés

| Paramètre | Type | Description | Exemple |
|-----------|------|-------------|---------|
| `notebook_path` | string | Chemin du notebook | `MyIA.AI.Notebooks/ML/notebook.ipynb` |
| `validation_level` | string | Niveau de validation | `quick`, `standard`, `thorough` |
| `execute` | bool | Exécuter le notebook | `true` |
| `fix_errors` | bool | Correction automatique | `false` |
| `report_format` | string | Format du rapport | `markdown`, `json`, `html` |
| `checks` | list[string] | Checks spécifiques | `["structure", "execution", "pedagogy"]` |
| `strict_mode` | bool | Mode strict (erreurs = échec) | `false` |
| `output_path` | string | Chemin du rapport | `validation_report.md` |

## Niveaux de validation

### Level `quick` - Validation rapide

Validation structurelle uniquement, sans exécution.

**Checks** :
- Format JSON valide
- Metadata présentes
- Cellules bien formées
- Kernel spécifié
- Pas de cellules vides

**Durée** : ~1-5 secondes

### Level `standard` - Validation standard

Validation structurelle + syntaxique + exécution basique.

**Checks** :
- Tous les checks `quick`
- Syntaxe code valide
- Markdown bien formé
- LaTeX valide
- Exécution sans erreurs critiques

**Durée** : ~30-120 secondes (selon taille)

### Level `thorough` - Validation exhaustive

Validation complète avec analyse pédagogique.

**Checks** :
- Tous les checks `standard`
- Progression pédagogique
- Ratio code/markdown
- Qualité des explications
- Visualisations présentes
- Références et citations
- Cohérence globale

**Durée** : ~2-10 minutes (selon taille)

## Processus de validation

### 1. Validation structurelle

```python
from scripts.notebook_tools import NotebookValidator
from scripts.notebook_helpers import NotebookHelper

validator = NotebookValidator(notebook_path)
helper = NotebookHelper(notebook_path)

# Vérifier le format JSON
is_valid_json = validator.validate_json_format()

# Vérifier les metadata
metadata_valid = validator.validate_metadata()
required_fields = ['kernelspec', 'language_info']
for field in required_fields:
    if field not in helper.notebook.get('metadata', {}):
        errors.append(f"Missing metadata field: {field}")

# Vérifier les cellules
for idx, cell in enumerate(helper.cells):
    # Type valide
    if cell.get('cell_type') not in ['code', 'markdown', 'raw']:
        errors.append(f"Cell {idx}: Invalid cell_type")

    # Source présente
    if 'source' not in cell:
        errors.append(f"Cell {idx}: Missing source")

    # Cell_id présent
    if 'id' not in cell:
        warnings.append(f"Cell {idx}: Missing id (auto-generated)")

# Cellules vides
empty_cells = [idx for idx, cell in enumerate(helper.cells) if not helper.get_cell_source(idx).strip()]
if empty_cells:
    warnings.append(f"Empty cells: {empty_cells}")
```

### 2. Validation syntaxique

#### Code Python

```python
import ast

for idx, cell in enumerate(helper.cells):
    if cell['cell_type'] == 'code' and helper.get_kernel_name() == 'python3':
        code = helper.get_cell_source(idx)

        # Ignorer les magic commands
        lines = [line for line in code.split('\n') if not line.strip().startswith('%')]
        code_clean = '\n'.join(lines)

        try:
            ast.parse(code_clean)
        except SyntaxError as e:
            errors.append(f"Cell {idx}: Syntax error - {e}")
```

#### Code C# (.NET)

```python
# Vérifier les imports et syntaxe basique
if helper.get_kernel_name() in ['.net-csharp', '.net-fsharp']:
    for idx, cell in enumerate(helper.cells):
        if cell['cell_type'] == 'code':
            code = helper.get_cell_source(idx)

            # Vérifier les directives #!
            if '#!import' in code or '#!csharp' in code:
                # OK, syntaxe .NET Interactive
                pass

            # Vérifier accolades équilibrées
            if code.count('{') != code.count('}'):
                warnings.append(f"Cell {idx}: Unbalanced braces")
```

#### Markdown

```python
import re

for idx, cell in enumerate(helper.cells):
    if cell['cell_type'] == 'markdown':
        md = helper.get_cell_source(idx)

        # Vérifier les headers
        headers = re.findall(r'^(#{1,6})\s+(.+)$', md, re.MULTILINE)
        for level, title in headers:
            if len(level) > 3:
                warnings.append(f"Cell {idx}: Header level {len(level)} too deep")

        # Vérifier LaTeX
        latex_blocks = re.findall(r'\$\$(.+?)\$\$', md, re.DOTALL)
        for latex in latex_blocks:
            if latex.count('{') != latex.count('}'):
                errors.append(f"Cell {idx}: Invalid LaTeX - unbalanced braces")

        # Vérifier les liens
        links = re.findall(r'\[([^\]]+)\]\(([^\)]+)\)', md)
        for text, url in links:
            if url.startswith('http') and 'localhost' not in url:
                # Vérifier que le lien n'est pas cassé (optionnel)
                pass
```

### 3. Validation d'exécution

Utiliser l'agent **notebook-executor** :

```python
# Exécuter le notebook
Task(
    subagent_type="general-purpose",
    prompt=f"""
    Tu es un agent notebook-executor.
    Exécute le notebook: {notebook_path}
    Mode: full
    Stop on error: false
    Save outputs: true
    """,
    description="Execute for validation"
)

# Analyser le rapport d'exécution
execution_report = read_execution_report()

# Compter les erreurs
error_count = sum(1 for r in execution_report['results'] if not r['success'])
timeout_count = sum(1 for r in execution_report['results'] if 'timeout' in r.get('error', '').lower())

if error_count > 0:
    errors.append(f"Execution errors: {error_count} cells failed")

if timeout_count > 0:
    warnings.append(f"Timeouts: {timeout_count} cells exceeded timeout")
```

### 4. Validation pédagogique

#### Progression pédagogique

Vérifier que le notebook suit une progression logique :

```python
# Extraire la structure
from scripts.notebook_tools import NotebookAnalyzer

analyzer = NotebookAnalyzer(notebook_path)
skeleton = analyzer.get_skeleton()

# Vérifier la présence des sections clés
required_sections = ['Introduction', 'Conclusion']
section_titles = [s.title.lower() for s in skeleton.sections]

for req in required_sections:
    if not any(req.lower() in title for title in section_titles):
        warnings.append(f"Missing recommended section: {req}")

# Vérifier la progression
# Les sections doivent aller du simple au complexe
section_depths = [s.level for s in skeleton.sections]
if not all(d <= 3 for d in section_depths):
    warnings.append("Some sections are too deeply nested (>3 levels)")
```

#### Ratio code/markdown

```python
code_cells = skeleton.code_cells
markdown_cells = skeleton.markdown_cells
total_cells = code_cells + markdown_cells

code_ratio = code_cells / total_cells if total_cells > 0 else 0

# Ratios recommandés
recommended_ratios = {
    'intro': (0.35, 0.45),      # 35-45% code
    'intermediate': (0.45, 0.55),
    'advanced': (0.50, 0.60)
}

level = detect_notebook_level(notebook_path)  # intro, intermediate, advanced
min_ratio, max_ratio = recommended_ratios.get(level, (0.40, 0.60))

if code_ratio < min_ratio:
    warnings.append(f"Code ratio {code_ratio:.1%} below recommended {min_ratio:.1%} for {level}")
elif code_ratio > max_ratio:
    warnings.append(f"Code ratio {code_ratio:.1%} above recommended {max_ratio:.1%} for {level}")
```

#### Cellules de code consécutives

```python
# Détecter les cellules de code consécutives sans markdown entre elles
consecutive_code = []
prev_type = None

for idx, cell in enumerate(helper.cells):
    if cell['cell_type'] == 'code':
        if prev_type == 'code':
            consecutive_code.append((idx - 1, idx))
    prev_type = cell['cell_type']

if consecutive_code:
    warnings.append(f"Consecutive code cells without explanation: {consecutive_code}")
```

#### Interprétations de résultats

```python
# Vérifier que les cellules avec sorties significatives ont une interprétation
for idx, cell in enumerate(helper.cells):
    if cell['cell_type'] == 'code':
        outputs = cell.get('outputs', [])

        # Si la cellule a une sortie non triviale
        has_significant_output = any(
            o.get('output_type') in ['execute_result', 'display_data']
            for o in outputs
        )

        if has_significant_output:
            # Vérifier qu'il y a une cellule markdown après
            if idx + 1 < len(helper.cells):
                next_cell = helper.cells[idx + 1]
                if next_cell['cell_type'] != 'markdown':
                    warnings.append(f"Cell {idx}: Significant output without interpretation")
```

### 5. Validation du contenu

#### Visualisations

```python
# Compter les visualisations
import re

viz_patterns = [
    r'plt\.figure',
    r'plt\.plot',
    r'plt\.show',
    r'sns\.',
    r'Chart\.',
    r'display\(',
]

viz_count = 0
for idx, cell in enumerate(helper.cells):
    if cell['cell_type'] == 'code':
        code = helper.get_cell_source(idx)
        for pattern in viz_patterns:
            if re.search(pattern, code):
                viz_count += 1
                break

# Recommandation : au moins 2-3 visualisations par notebook
if viz_count < 2:
    warnings.append(f"Low visualization count: {viz_count} (recommended: 2+)")
```

#### Formules LaTeX

```python
# Compter les formules LaTeX
latex_count = 0
for idx, cell in enumerate(helper.cells):
    if cell['cell_type'] == 'markdown':
        md = helper.get_cell_source(idx)
        latex_count += len(re.findall(r'\$\$.+?\$\$', md, re.DOTALL))
        latex_count += len(re.findall(r'\$.+?\$', md))

# Pour notebooks théoriques, recommander des formules
if 'Probas' in notebook_path or 'ML' in notebook_path or 'Logic' in notebook_path:
    if latex_count < 3:
        warnings.append(f"Low LaTeX formula count: {latex_count} (recommended: 3+ for theoretical content)")
```

#### Références et citations

```python
# Vérifier si des références sont citées
references_section = any(
    'référence' in helper.get_cell_source(idx).lower() or
    'bibliographie' in helper.get_cell_source(idx).lower()
    for idx in range(len(helper.cells))
    if helper.cells[idx]['cell_type'] == 'markdown'
)

if not references_section and validation_level == 'thorough':
    warnings.append("No references section found")
```

### 6. Correction automatique (si activée)

Si `fix_errors=true`, tenter de corriger les erreurs détectées :

```python
if fix_errors:
    # Ajouter cell_id manquants
    if any('Missing id' in w for w in warnings):
        for cell in helper.cells:
            if 'id' not in cell:
                cell['id'] = str(uuid.uuid4())
        helper.save()

    # Ajouter markdown entre cellules de code consécutives
    if consecutive_code:
        for prev_idx, next_idx in reversed(consecutive_code):
            helper.insert_cell(next_idx, 'markdown', "### Transition\n\n[À compléter]")
        helper.save()

    # Corriger les erreurs d'exécution (via notebook-cell-iterator)
    if error_count > 0 and fix_errors:
        for result in execution_report['results']:
            if not result['success']:
                Task(
                    subagent_type="general-purpose",
                    prompt=f"""
                    Tu es un agent notebook-cell-iterator.
                    Corrige la cellule {result['cell_index']} du notebook {notebook_path}
                    Objectif: no_error
                    Max iterations: 3
                    """,
                    description=f"Fix cell {result['cell_index']}"
                )
```

## Rapport de validation

### Format Markdown

```markdown
# Validation Report: {notebook_name}

**Date**: {timestamp}
**Level**: {validation_level}
**Status**: PASS / FAIL / WARNING

---

## Summary

| Category | Status | Score |
|----------|--------|-------|
| Structure | PASS | 100% |
| Syntax | PASS | 100% |
| Execution | WARNING | 85% |
| Pedagogy | PASS | 90% |
| Content | PASS | 95% |

**Overall Score**: 94% (PASS)

---

## Structural Validation

✅ Valid JSON format
✅ Metadata complete
✅ Kernel specified: python3
✅ All cells well-formed
⚠️ 2 empty cells: [15, 30]

---

## Syntactic Validation

✅ All Python code cells valid
✅ Markdown well-formed
✅ LaTeX formulas valid (8 found)
✅ No broken links

---

## Execution Validation

✅ 48/50 cells executed successfully
❌ 2 cells failed:
  - Cell 25: NameError: name 'model' is not defined
  - Cell 40: TimeoutError after 300s

⚠️ 1 cell with long execution: Cell 35 (245s)

**Total execution time**: 425s

---

## Pedagogical Validation

✅ Introduction section present
✅ Conclusion section present
✅ Code/Markdown ratio: 42% (recommended: 35-45%)
⚠️ 3 pairs of consecutive code cells without explanation: [(5,6), (12,13), (20,21)]
✅ Most significant outputs have interpretation

---

## Content Validation

✅ Visualizations: 5 (good)
✅ LaTeX formulas: 8 (good for ML content)
⚠️ No references section

---

## Recommendations

1. **High Priority**:
   - Fix NameError in cell 25: Define 'model' before usage
   - Optimize or split cell 40 to avoid timeout

2. **Medium Priority**:
   - Add markdown explanations between consecutive code cells
   - Remove or populate empty cells [15, 30]

3. **Low Priority**:
   - Consider adding a references section
   - Add transition markdown after cell 35 (long execution)

---

## Detailed Errors

### Cell 25 - NameError
```
Error: NameError: name 'model' is not defined
Traceback:
  File "<cell>", line 3
    predictions = model.predict(X_test)
```

**Suggested fix**: Add `model = ...` in a previous cell or import the model.

### Cell 40 - TimeoutError
```
Error: TimeoutError after 300s
```

**Suggested fix**: Reduce dataset size or increase timeout to 600s.

---

## Validation Metadata

- Notebook path: MyIA.AI.Notebooks/ML/DecisionTrees.ipynb
- Total cells: 50
- Code cells: 21
- Markdown cells: 29
- Executed: 50
- Duration: 425s
- Checks performed: 15
- Errors: 2
- Warnings: 4
```

### Format JSON

```json
{
  "notebook": "MyIA.AI.Notebooks/ML/DecisionTrees.ipynb",
  "timestamp": "2026-02-02T15:30:00",
  "level": "standard",
  "status": "WARNING",
  "overall_score": 0.94,
  "summary": {
    "structure": {"status": "PASS", "score": 1.0},
    "syntax": {"status": "PASS", "score": 1.0},
    "execution": {"status": "WARNING", "score": 0.85},
    "pedagogy": {"status": "PASS", "score": 0.90},
    "content": {"status": "PASS", "score": 0.95}
  },
  "errors": [
    {
      "cell": 25,
      "type": "NameError",
      "message": "name 'model' is not defined",
      "severity": "high"
    },
    {
      "cell": 40,
      "type": "TimeoutError",
      "message": "Execution exceeded 300s",
      "severity": "high"
    }
  ],
  "warnings": [
    {
      "type": "empty_cells",
      "cells": [15, 30],
      "severity": "low"
    },
    {
      "type": "consecutive_code",
      "cells": [[5,6], [12,13], [20,21]],
      "severity": "medium"
    }
  ],
  "recommendations": [
    {
      "priority": "high",
      "category": "execution",
      "message": "Fix NameError in cell 25"
    }
  ],
  "metadata": {
    "total_cells": 50,
    "code_cells": 21,
    "markdown_cells": 29,
    "execution_time": 425,
    "checks_performed": 15
  }
}
```

## Intégration avec autres agents

### Workflow complet

```python
# 1. Validator valide le notebook
validation_report = validate_notebook(
    notebook_path=notebook_path,
    validation_level="standard",
    execute=True,
    fix_errors=False
)

# 2. Si erreurs d'exécution, utiliser cell-iterator pour corriger
if validation_report['summary']['execution']['status'] != 'PASS':
    for error in validation_report['errors']:
        Task(
            subagent_type="general-purpose",
            prompt=f"notebook-cell-iterator: fix cell {error['cell']}",
            description=f"Fix {error['type']}"
        )

# 3. Si manque d'explications, utiliser enricher
if validation_report['warnings'].any(lambda w: w['type'] == 'consecutive_code'):
    Task(
        subagent_type="general-purpose",
        prompt=f"notebook-enricher: enrich {notebook_path}",
        description="Add explanations"
    )

# 4. Re-valider après corrections
validation_report_v2 = validate_notebook(notebook_path, validation_level="standard")
```

## Exemples d'invocation

### Exemple 1 : Validation rapide

```python
Task(
    subagent_type="general-purpose",
    prompt="""
    Agent notebook-validator.

    Notebook: MyIA.AI.Notebooks/Sudoku/Sudoku-1-Backtracking.ipynb
    Level: quick
    Execute: false
    Report format: markdown
    """,
    description="Quick validation Sudoku"
)
```

### Exemple 2 : Validation complète avec correction

```python
Task(
    subagent_type="general-purpose",
    prompt="""
    Agent notebook-validator.

    Notebook: MyIA.AI.Notebooks/Probas/Infer/Infer-3-Mixture-Models.ipynb
    Level: thorough
    Execute: true
    Fix errors: true
    Report format: json
    Output path: validation_reports/infer3_report.json
    """,
    description="Thorough validation Infer-3"
)
```

### Exemple 3 : Validation série de notebooks

```python
notebooks = glob("MyIA.AI.Notebooks/GameTheory/*.ipynb")

for nb in notebooks:
    Task(
        subagent_type="general-purpose",
        prompt=f"""
        Agent notebook-validator.
        Notebook: {nb}
        Level: standard
        Execute: true
        Fix errors: false
        Report format: json
        """,
        description=f"Validate {Path(nb).stem}",
        run_in_background=True
    )
```

## Outils de support

### Scripts disponibles

```bash
# Validation via notebook_tools.py
python scripts/notebook_tools.py validate MyIA.AI.Notebooks/ML/notebook.ipynb --verbose

# Validation famille complète
python scripts/notebook_tools.py validate MyIA.AI.Notebooks/GameTheory/ --quick

# Analyse de la structure
python scripts/notebook_tools.py skeleton notebook.ipynb --output json
```

### Helpers Python

```python
from scripts.notebook_tools import NotebookValidator, NotebookAnalyzer

# Valider
validator = NotebookValidator(notebook_path)
results = validator.validate_all()

# Analyser
analyzer = NotebookAnalyzer(notebook_path)
skeleton = analyzer.get_skeleton()
print(f"Score pédagogique: {analyzer.pedagogical_score()}")
```

## Bonnes pratiques

| Pratique | Description |
|----------|-------------|
| **Toujours exécuter** | Validation sans exécution est incomplète |
| **Mode standard par défaut** | Bon compromis temps/couverture |
| **Fix errors = false** | Valider d'abord, corriger ensuite |
| **Sauvegarder rapports** | Pour suivi dans le temps |
| **Re-valider après corrections** | Vérifier que les fixes ont fonctionné |

## Limites

| Limite | Description |
|--------|-------------|
| Validation pédagogique subjective | Heuristiques, pas garantie de qualité |
| Exécution peut être longue | >5min pour gros notebooks |
| Correction automatique limitée | Erreurs complexes nécessitent intervention manuelle |

## À éviter

- Valider sans exécuter (sauf quick check)
- Ignorer les warnings
- Fixer automatiquement sans comprendre
- Valider pendant l'édition du notebook
- Oublier de sauvegarder le rapport
