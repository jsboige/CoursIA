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

## Criteres d'amelioration

### Ou ajouter du markdown ?

1. **Avant une section de code complexe** : Expliquer ce que le code va faire et pourquoi
2. **Apres des resultats numeriques** : Interpreter les valeurs, comparer avec les attentes
3. **Apres des erreurs ou warnings** : Expliquer la cause et la resolution
4. **Entre deux concepts distincts** : Transition pedagogique
5. **En conclusion de partie** : Resume avec tableau recapitulatif
6. **Entre deux cellules de code consecutives** : Ajouter une transition ou explication

### Detection de cellules consecutives

IMPORTANT: Deux cellules de code qui se suivent sans markdown entre elles indiquent un manque d'explication. Ajouter systematiquement :
- Une explication de ce que fait le code suivant
- Ou une interpretation du resultat precedent
- Ou une transition entre les concepts

### Format des ajouts

- **Tableaux** pour les comparaisons et recapitulatifs
- **Formules LaTeX** pour les equations importantes (si applicable)
- **Notes encadrees** (blockquotes >) pour les points techniques
- **Listes** pour les etapes ou criteres
- **Gras** pour les termes cles

### A eviter

- Repeter le code dans le markdown
- Surcharger avec trop d'explications triviales
- Ajouter des emojis
- Modifier le code existant (sauf si --fix-errors active)

## Processus standard

1. **Lire** le notebook entierement pour comprendre la structure
2. **Identifier** les cellules de code sans interpretation de resultats
3. **Identifier** les cellules de code consecutives sans markdown entre elles
4. **Identifier** les transitions abruptes entre sections
5. **Ajouter** les cellules markdown necessaires via NotebookEdit
6. **Verifier** la coherence globale

## Processus avec --execute

1. Executer les etapes standard 1-4
2. **Demarrer un kernel** adapte au notebook (python3, .net-csharp, etc.)
3. **Executer** chaque cellule de code sequentiellement
4. **Verifier** les sorties et identifier les erreurs
5. Si --fix-errors : tenter de corriger le code problematique
6. **Ajouter** les interpretations basees sur les sorties reelles
7. **Arreter** le kernel

## Exemple de sortie attendue

Apres une cellule affichant des resultats numeriques :

```markdown
### Interpretation des resultats

**Sortie obtenue** : `valeur = 15.33`

| Parametre | Valeur | Signification |
|-----------|--------|---------------|
| Moyenne | 15.33 | Estimation centrale |
| Ecart-type | 1.32 | Dispersion des donnees |

> **Note** : Cette valeur est coherente avec les attentes theoriques.
```

## Adaptation par domaine

Ce template peut etre specialise pour differents domaines :

| Domaine | Specialisation |
|---------|----------------|
| Probabilites/Infer.NET | Distributions, priors, posteriors, inference |
| ML/Deep Learning | Metriques, courbes, hyperparametres |
| Optimisation | Convergence, fitness, contraintes |
| Theorie des jeux | Equilibres, strategies, gains |
| Logique formelle | Preuves, tactiques, theoremes |

## Invocation depuis Claude Code

```python
# Enrichissement simple
Task(
    subagent_type="general-purpose",
    prompt=f"""
    Tu es un agent notebook-enricher.
    Lis les instructions dans .claude/agents/notebook-enricher.md
    Enrichis le notebook: {notebook_path}
    Options: {options}
    """,
    description=f"Enrich {notebook_name}"
)
```

## Serie de notebooks

Pour traiter une serie complete, lancer des agents en parallele :

```python
notebooks = glob("MyIA.AI.Notebooks/Probas/Infer/*.ipynb")
for nb in notebooks:
    Task(
        subagent_type="general-purpose",
        prompt=f"Enrichir {nb} selon .claude/agents/notebook-enricher.md",
        run_in_background=True
    )
```
