---
name: readme-updater
description: Update README files for notebook series (notebook presentation, structure tables, navigation links; totals are left to the catalogue regeneration). Use after adding or modifying notebooks in a series.
tools: Read, Glob, Grep, Bash, Write, Edit
model: haiku
memory: user
skills:
  - notebook-helpers
---

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
- Structure et navigation, avec la signaletique des niveaux de lecture
- Parcours principal (numeros nus) et approfondissements (lettres), presentes separement
- Descriptions detaillees par notebook
- Informations techniques (kernels, durees, prerequis)

## Processus standard

### Phase 1 : Extraction du squelette

1. **Executer le script d'extraction** pour obtenir la structure des notebooks :

```bash
python scripts/notebook_tools/extract_notebook_skeleton.py [target_path] --output detailed --code-preview
```

2. **Analyser le resultat** pour identifier :
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
   - **Jamais les totaux** (nombre de notebooks, cellules, comptes par langage) : ils relevent de la regeneration du catalogue (`CATALOG-STATUS`, #9377) ; une ligne de compte fausse se supprime au profit du renvoi au catalogue

### Phase 3 : Generation du contenu

#### Deux dimensions, trois niveaux de lecture (doctrine #5081, forme #3973)

Un README de serie ne presente **jamais** les notebooks comme une sequence unique a lire de bout en bout.

- **Numeros nus** (`01`, `02`, ...) : le **parcours principal**, lisible sans ouvrir une seule lettre.
- **Lettres** (`02b`, `02c`, ...) : des **approfondissements** d'un palier. Le lecteur y va quand il veut creuser ce palier, pas pour avancer dans la serie.
- **Niveau de lecture** : chaque section et chaque ligne porte son public, `Decouverte`, `Licence` ou `Recherche`. La matiere de niveau Recherche (resultats recents, notes techniques, statut de maturite) se place **apres** le parcours principal, jamais au milieu.

#### Format du tableau principal (numeros nus SEULEMENT)

```markdown
| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|----------|--------------------|--------|------------------|
| 02 | [Formes normales](Serie-02-NormalForm.ipynb) | Description courte | Decouverte | [02b](Serie-02b-X.ipynb) · [02c](Serie-02c-Y.ipynb) |
```

- Une ligne par numero nu. Aucune lettre en ligne : les lettres ne sont que des liens courts dans la derniere colonne.
- Deux implementations d'un meme notebook (Python, C#, Lean) partagent la ligne : `[Python](...) · [C#](...)` dans la colonne Notebook.

#### Format des approfondissements

Une sous-section par palier qui porte des lettres, dans l'ordre des numeros :

```markdown
### Autour de 02 — theme du palier

| Lettre | Notebook | Ce qu'il ajoute | Prerequis en plus | Public |
|--------|----------|-----------------|-------------------|--------|
| 02b | [Titre](Serie-02b-X.ipynb) | Ce que la lettre apporte au palier | Notebooks ou notions a connaitre en plus | Licence |
```

#### Descriptions detaillees (optionnelles)

Si le README en porte, elles suivent le meme ordre : numeros nus d'abord, puis les approfondissements par palier. Format par notebook : titre, kernel, prerequis, contenu, concepts cles.

### Phase 4 : Mise a jour du README

1. **Utiliser Edit** pour mettre a jour les sections existantes
2. **Conserver** :
   - Les sections personnalisees (installation, ressources)
   - Les notes specifiques ajoutees manuellement
   - La structure generale du document
3. **Mettre a jour** :
   - Les tableaux avec les nouvelles donnees
   - Les descriptions si modifiees

## Criteres de qualite

### Structure attendue d'un README complet

```markdown
# Titre de la Serie

Paragraphe d'ouverture (niveau Decouverte) : ce que la serie enseigne, a qui, avec quels prerequis d'entree.

## Comment lire ce README

- Vous decouvrez le sujet : lisez le **Parcours principal**, dans l'ordre des numeros.
- Vous voulez creuser un palier : ouvrez sa section dans **Approfondissements**.
- Vous cherchez la recherche en cours : **Sous-series** et **Pour aller plus loin**.

## Parcours principal

(Table des numeros nus, format ci-dessus. Eventuellement decoupee en phases, chaque phase avec une phrase qui dit ce qu'elle construit.)

## Approfondissements

(Une sous-section par palier qui porte des lettres.)

## Sous-series

(Prefixe, notebook pont depuis la serie mere, et sa propre table au meme format.)

## Installation

(Instructions specifiques, par kernel.)

## Pour aller plus loin

(Niveau Recherche : notes techniques, statut de maturite, formalisations, references pointues.)

## Ressources

- Liens externes
- Documentation
```

(Pas de total de notebooks ni de cellules : le decompte vit dans le bloc `CATALOG-STATUS`, regenere automatiquement.)

### Regles de coherence

- [ ] Tous les notebooks sont listes dans au moins un tableau
- [ ] La table du parcours principal ne contient que des numeros nus ; chaque lettre du dossier figure sous « Approfondissements »
- [ ] Chaque section porte son niveau de lecture, et la matiere de niveau Recherche est placee apres le parcours principal
- [ ] Les liens vers les notebooks sont corrects (format: `texte` + `(chemin.ipynb)`)
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

Le script consolide `scripts/notebook_tools/notebook_tools.py` offre plusieurs commandes :

```bash
# Extraire le squelette d'un notebook ou repertoire
python scripts/notebook_tools/notebook_tools.py skeleton MyIA.AI.Notebooks/Sudoku --output markdown
python scripts/notebook_tools/notebook_tools.py skeleton MyIA.AI.Notebooks/Sudoku --output json
python scripts/notebook_tools/notebook_tools.py skeleton MyIA.AI.Notebooks/Sudoku --output summary

# Valider la structure des notebooks
python scripts/notebook_tools/notebook_tools.py validate MyIA.AI.Notebooks/Sudoku --quick

# Analyser les sorties
python scripts/notebook_tools/notebook_tools.py analyze MyIA.AI.Notebooks/Sudoku

# Verifier l'environnement
python scripts/notebook_tools/notebook_tools.py check-env Sudoku
```

### Option 2 : extract_notebook_skeleton.py (alternatif)

Le script `scripts/notebook_tools/extract_notebook_skeleton.py` peut aussi etre utilise :

```bash
# Format resume
python scripts/notebook_tools/extract_notebook_skeleton.py MyIA.AI.Notebooks/Sudoku

# Format tableau markdown
python scripts/notebook_tools/extract_notebook_skeleton.py MyIA.AI.Notebooks/Sudoku --output markdown

# Format detaille avec previews de code
python scripts/notebook_tools/extract_notebook_skeleton.py MyIA.AI.Notebooks/Sudoku --output detailed --code-preview

# Format JSON pour traitement programmatique
python scripts/notebook_tools/extract_notebook_skeleton.py MyIA.AI.Notebooks/Sudoku --output json
```
