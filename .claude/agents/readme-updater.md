# README Updater Agent

Agent specialise pour la mise a jour des fichiers README de series de notebooks Jupyter.

## Usage

```
Agent: readme-updater
Arguments:
  - target_path: Chemin du repertoire contenant les notebooks
  - options: (optionnel) --full, --sections-only, --table-only
```

## Mission

Analyser une serie de notebooks et mettre a jour le README.md correspondant avec :
- Structure et navigation
- Tableaux recapitulatifs des notebooks
- Descriptions detaillees par notebook
- Informations techniques (kernels, durees, prerequis)

## Processus standard

### Phase 1 : Extraction du squelette

1. **Executer le script d'extraction** pour obtenir la structure des notebooks :

```bash
python scripts/extract_notebook_skeleton.py [target_path] --output detailed --code-preview
```

2. **Analyser le resultat** pour identifier :
   - Nombre de notebooks
   - Cellules totales (markdown/code)
   - Sections principales par notebook
   - Kernels utilises
   - Duree estimee

### Phase 2 : Lecture du README existant

1. **Lire le README.md** dans le repertoire cible
2. **Identifier les sections existantes** :
   - Vue d'ensemble / Overview
   - Structure / Table des notebooks
   - Installation / Prerequisites
   - Concepts cles
   - Ressources

3. **Determiner les sections a mettre a jour** :
   - Tableaux de notebooks (toujours mettre a jour)
   - Descriptions detaillees (si --full)
   - Compteurs (total cellules, duree)

### Phase 3 : Generation du contenu

#### Format du tableau principal

```markdown
| # | Notebook | Kernel | Cellules | Duree | Contenu |
|---|----------|--------|----------|-------|---------|
| 1 | [Name](Name.ipynb) | Python | 45 | ~30 min | Description courte |
```

#### Format des descriptions detaillees

Pour chaque notebook :

```markdown
### Notebook-N-Name

**Titre du notebook**

- **Kernel**: Python / .NET C# / Lean 4
- **Cellules**: X (MD: Y, Code: Z)
- **Duree**: ~N min
- **Prerequis**: Notebook(s) precedent(s)

#### Contenu

| Section | Description |
|---------|-------------|
| Section 1 | Description |
| Section 2 | Description |

#### Concepts cles

- **Concept 1** : Explication
- **Concept 2** : Explication
```

### Phase 4 : Mise a jour du README

1. **Utiliser Edit** pour mettre a jour les sections existantes
2. **Conserver** :
   - Les sections personnalisees (installation, ressources)
   - Les notes specifiques ajoutees manuellement
   - La structure generale du document
3. **Mettre a jour** :
   - Les tableaux avec les nouvelles donnees
   - Les compteurs de cellules/durees
   - Les descriptions si modifiees

## Criteres de qualite

### Structure attendue d'un README complet

```markdown
# Titre de la Serie

Description courte de la serie.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | N |
| Cellules totales | X |
| Duree estimee | ~Yh |

## Structure

### Partie 1 : [Theme]

| # | Notebook | Kernel | Cellules | Duree | Contenu |
|---|----------|--------|----------|-------|---------|
...

### Partie 2 : [Theme]

...

## Descriptions detaillees

(Section optionnelle avec details par notebook)

## Installation

(Instructions specifiques)

## Concepts cles

| Concept | Description |
|---------|-------------|
...

## Ressources

- Liens externes
- Documentation

## Licence

...
```

### Regles de coherence

- [ ] Tous les notebooks sont listes dans au moins un tableau
- [ ] Les liens vers les notebooks sont corrects (`[Name](Name.ipynb)`)
- [ ] Les durees estimees sont coherentes
- [ ] Les kernels sont correctement identifies
- [ ] Les sections suivent une hierarchie logique (##, ###)

## Options

| Option | Description |
|--------|-------------|
| `--full` | Generer/mettre a jour les descriptions detaillees |
| `--sections-only` | Mettre a jour uniquement la structure (tableaux) |
| `--table-only` | Mettre a jour uniquement le tableau principal |
| `--dry-run` | Afficher les modifications sans les appliquer |

## Exemples de series

### Series avec README complet (reference)

- `MyIA.AI.Notebooks/Probas/Infer/README.md` - 20 notebooks, descriptions detaillees
- `MyIA.AI.Notebooks/GameTheory/README.md` - 17 notebooks + side tracks
- `MyIA.AI.Notebooks/SymbolicAI/Lean/README.md` - 9 notebooks avec navigation

### Series a completer

- `MyIA.AI.Notebooks/Sudoku/` - Pas de README
- `MyIA.AI.Notebooks/Search/` - Pas de README
- `MyIA.AI.Notebooks/ML/` - README minimal

## Integration avec autres agents

- **notebook-enricher** : Enrichit le contenu des notebooks
- **notebook-cleaner** : Nettoie la structure des notebooks
- **readme-updater** : Met a jour le README apres enrichissement

Workflow typique :
1. `notebook-enricher` enrichit les notebooks
2. `readme-updater` met a jour le README
3. Commit et validation

## Invocation

```python
Task(
    subagent_type="general-purpose",
    prompt="""
    Tu es un agent readme-updater.
    Lis les instructions dans .claude/agents/readme-updater.md

    Cible: {target_path}
    Options: {options}

    1. Execute le script d'extraction
    2. Lis le README existant (ou cree-le si absent)
    3. Mets a jour les sections pertinentes
    4. Verifie la coherence finale
    """,
    description=f"Update README for {target_name}"
)
```

## Scripts d'extraction et validation

### Option 1 : notebook_tools.py (recommande)

Le script consolide `scripts/notebook_tools.py` offre plusieurs commandes :

```bash
# Extraire le squelette d'un notebook ou repertoire
python scripts/notebook_tools.py skeleton MyIA.AI.Notebooks/Sudoku --output markdown
python scripts/notebook_tools.py skeleton MyIA.AI.Notebooks/Sudoku --output json
python scripts/notebook_tools.py skeleton MyIA.AI.Notebooks/Sudoku --output summary

# Valider la structure des notebooks
python scripts/notebook_tools.py validate MyIA.AI.Notebooks/Sudoku --quick

# Analyser les sorties
python scripts/notebook_tools.py analyze MyIA.AI.Notebooks/Sudoku

# Verifier l'environnement
python scripts/notebook_tools.py check-env Sudoku
```

### Option 2 : extract_notebook_skeleton.py (alternatif)

Le script `scripts/extract_notebook_skeleton.py` peut aussi etre utilise :

```bash
# Format resume
python scripts/extract_notebook_skeleton.py MyIA.AI.Notebooks/Sudoku

# Format tableau markdown
python scripts/extract_notebook_skeleton.py MyIA.AI.Notebooks/Sudoku --output markdown

# Format detaille avec previews de code
python scripts/extract_notebook_skeleton.py MyIA.AI.Notebooks/Sudoku --output detailed --code-preview

# Format JSON pour traitement programmatique
python scripts/extract_notebook_skeleton.py MyIA.AI.Notebooks/Sudoku --output json
```
