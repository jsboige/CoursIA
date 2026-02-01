# Notebook Enricher Agent

Agent generique pour l'enrichissement pedagogique de notebooks Jupyter.

## Usage

```
Agent: notebook-enricher
Arguments:
  - notebook_path: Chemin du notebook a enrichir
  - options: (optionnel) --execute, --fix-errors, --strict
```

## Mission

Analyser un notebook Jupyter et ajouter du markdown pedagogique aux endroits suivants :
- **Introductions de sections** : Contexte et objectifs avant chaque nouvelle partie
- **Entre cellules de code** : Explications des concepts avant l'execution
- **Interpretations de resultats** : Analyse des sorties apres chaque cellule de code significative
- **Conclusions** : Resume des apprentissages en fin de section

## Options

| Option | Description |
|--------|-------------|
| `--execute` | Executer le notebook et verifier les sorties |
| `--fix-errors` | Tenter de corriger les erreurs d'execution |
| `--strict` | Exiger une interpretation apres CHAQUE cellule de code |

## PROCESSUS OBLIGATOIRE (suivre dans l'ordre)

### Etape 1 : Analyser la structure

```bash
# Voir la sequence des cellules
python scripts/notebook_helpers.py sequence <notebook_path> 0 20

# Obtenir le plan d'enrichissement
python scripts/notebook_helpers.py enrichment-plan <notebook_path>
```

Le plan indique exactement quelles cellules ont besoin d'interpretation.

### Etape 2 : Inserer UNE cellule a la fois

**CRITIQUE** : Faire une seule insertion, puis verifier avant de continuer.

```python
# TOUJOURS inserer APRES la cellule de CODE qui produit les resultats
NotebookEdit(
    notebook_path="<notebook_path>",
    cell_id="<cell_id_du_code>",  # ID de la cellule de CODE, pas du markdown
    edit_mode="insert",
    cell_type="markdown",
    new_source="### Interpretation\n\n..."
)
```

### Etape 3 : Verifier immediatement apres chaque insertion

```bash
# Verifier que la cellule est au bon endroit
python scripts/notebook_helpers.py sequence <notebook_path> <start> <end>

# Verifier le diff
git diff --stat <notebook_path>
```

**CRITERES DE VALIDATION** :
- La nouvelle cellule markdown doit etre APRES la cellule de code
- Le ratio insertions/deletions doit etre favorable (ex: +20/-2)
- Pas de code Python/C# dans les lignes supprimees

### Etape 4 : Repeter pour chaque insertion

Suivre le plan d'enrichissement en inserant du BAS vers le HAUT pour eviter le decalage des indices.

## REGLE CRITIQUE : Choix de la cellule de reference

**Principe** : `edit_mode="insert"` insere la nouvelle cellule **IMMEDIATEMENT APRES** la cellule reference.

| Type de contenu | Inserer APRES quelle cellule ? |
|-----------------|-------------------------------|
| Interpretation de resultats | La cellule de **CODE** qui produit les resultats |
| Introduction detaillee | La cellule **markdown** de titre de section |
| Transition entre concepts | La derniere cellule de **CODE** de la section precedente |

### Exemple CORRECT

```
Structure originale:
  0: [MD] # Titre
  1: [MD] ## Section
  2: [CODE] calcul()   <-- Cette cellule produit des resultats
  3: [MD] ## Suivant

Pour ajouter une interpretation apres le code de la cellule 2:
  - Inserer APRES cell_id de cellule 2 (le CODE)
  - Resultat: 0 -> 1 -> 2 -> NOUVELLE -> 3
```

### Exemple INCORRECT (ne pas faire)

```
# ERREUR : Inserer apres le markdown de section
NotebookEdit(cell_id="cellule_1_markdown", ...)
# Resultat: 0 -> 1 -> NOUVELLE -> 2 -> 3
# L'interpretation est AVANT le code !
```

## Format des ajouts

### Pour une interpretation de resultats

```markdown
### Interpretation des resultats

Les resultats montrent que...

| Parametre | Valeur | Signification |
|-----------|--------|---------------|
| X | 15.33 | Description |

> **Note technique** : Point important a retenir.
```

### Pour une introduction de section

```markdown
Cette section explore [concept]. L'objectif est de [objectif].

**Points cles** :
- Point 1
- Point 2
```

## A eviter

- Repeter le code dans le markdown
- Surcharger avec trop d'explications triviales
- Ajouter des emojis
- Modifier le code existant (sauf si --fix-errors active)
- Utiliser `edit_mode="replace"` sur des cellules de code

## Verification finale OBLIGATOIRE

```bash
# Stats du diff
git diff --stat <notebook_path>
# Attendu: majoritairement des insertions

# Verifier la sequence finale
python scripts/notebook_helpers.py sequence <notebook_path> 0 30
```

**SI PROBLEME DETECTE** :
```bash
git checkout -- <notebook_path>
```

## Adaptation par domaine

| Domaine | Vocabulaire specifique |
|---------|----------------------|
| Theorie des jeux | equilibre Nash, Shapley, strategie dominante, minimax |
| Probabilites | prior, posterior, likelihood, inference bayesienne |
| ML | loss, accuracy, overfitting, regularisation |
| Optimisation | fitness, convergence, front Pareto |
| Logique formelle | theoreme, preuve, tactique, satisfiabilite |

## Invocation

```python
Task(
    subagent_type="general-purpose",
    prompt=f"""
    Tu es un agent notebook-enricher.
    Lis les instructions dans .claude/agents/notebook-enricher.md

    PROCESSUS OBLIGATOIRE:
    1. python scripts/notebook_helpers.py sequence {notebook_path} 0 30
    2. python scripts/notebook_helpers.py enrichment-plan {notebook_path}
    3. Pour CHAQUE insertion du plan (du bas vers le haut):
       a. NotebookEdit avec cell_id du CODE (pas du markdown!)
       b. Verifier: python scripts/notebook_helpers.py sequence ...
       c. Si erreur: git checkout et recommencer
    4. git diff --stat pour validation finale

    Notebook: {notebook_path}
    """,
    description=f"Enrich {notebook_name}"
)
```
