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
5. **Ajouter** les cellules markdown necessaires via NotebookEdit (voir section critique ci-dessous)
6. **Verifier** la coherence globale

## CRITIQUE : Utilisation correcte de NotebookEdit

**TOUJOURS utiliser `edit_mode="insert"`** pour ajouter de nouvelles cellules.

**JAMAIS utiliser `edit_mode="replace"`** sur des cellules existantes, sauf pour corriger des erreurs mineures dans du markdown.

### Exemple CORRECT : Insertion d'une cellule explicative

```python
NotebookEdit(
    notebook_path="chemin/notebook.ipynb",
    cell_id="id_cellule_precedente",   # La nouvelle cellule sera inseree APRES celle-ci
    edit_mode="insert",                 # OBLIGATOIRE pour ajouter
    cell_type="markdown",
    new_source="### Explication\n\nCe code fait..."
)
```

### Exemple INCORRECT (A NE PAS FAIRE)

```python
# DANGEREUX - Ecrase la cellule existante !
NotebookEdit(
    notebook_path="chemin/notebook.ipynb",
    cell_id="id_cellule_code",
    edit_mode="replace",  # INTERDIT sauf correction mineure
    new_source="..."
)
```

### Strategie d'insertion

1. **Lire le notebook** avec `read_cells(path, mode="list")` pour obtenir les IDs de cellules
2. **Identifier les points d'insertion** (apres quelle cellule inserer)
3. **Inserer dans l'ordre inverse** (du bas vers le haut) pour eviter le decalage des indices
4. Ou utiliser les **cell_id** plutot que les indices pour des insertions stables

## OBLIGATOIRE : Verification du diff avant completion

**Avant de terminer**, TOUJOURS executer `git diff --stat <notebook_path>` pour verifier :

1. **Ratio insertions/deletions** : Les insertions doivent largement depasser les deletions
   - CORRECT : `+48 insertions(+), 2 deletions(-)`
   - PROBLEME : `+10 insertions(+), 255 deletions(-)` → Ecrasement detecte !

2. **Si deletions > 50** : STOP ! Quelque chose s'est mal passe
   - Executer `git checkout -- <notebook_path>` pour restaurer
   - Recommencer avec `edit_mode="insert"` uniquement

3. **Verifier le contenu du diff** avec `git diff <notebook_path> | head -100`
   - Les lignes `-` ne doivent PAS contenir de code Python/C#
   - Les lignes `-` acceptables : metadata, cell_id, lignes vides

### Exemple de verification

```bash
# Verifier les stats
git diff --stat MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-1-Setup.ipynb
# Attendu: +20 insertions(+), 1 deletion(-)

# Si probleme detecte, restaurer
git checkout -- MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-1-Setup.ipynb
```

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

Ce template s'adapte automatiquement selon le domaine du notebook. Voici les elements specifiques a chaque domaine :

| Domaine | Specialisation |
|---------|----------------|
| Probabilites/Infer.NET | Distributions, priors, posteriors, inference |
| ML/Deep Learning | Metriques, courbes, hyperparametres |
| Optimisation | Convergence, fitness, contraintes |
| Theorie des jeux | Equilibres, strategies, gains, Shapley |
| Logique formelle | Preuves, tactiques, theoremes |

### Guide d'adaptation par domaine

#### Probabilites/Infer.NET

- **Vocabulaire** : prior, posterior, likelihood, evidence, inference, marginalisation
- **Formules** : Utiliser LaTeX pour Bayes ($P(H|E) = \frac{P(E|H)P(H)}{P(E)}$)
- **Tableaux** : Comparer priors vs posteriors, parametres de distributions
- **Interpretations** : Expliquer ce que signifient les distributions inferees

#### Theorie des jeux

- **Vocabulaire** : equilibre de Nash, strategie dominante, Pareto, minimax, Shapley, Core
- **Formules LaTeX** :
  - Valeur de Shapley : $\phi_i(v) = \sum_{S \subseteq N \setminus \{i\}} \frac{|S|!(n-|S|-1)!}{n!}[v(S \cup \{i\}) - v(S)]$
  - Equilibre Nash : $u_i(s^*_i, s^*_{-i}) \geq u_i(s_i, s^*_{-i})$
- **Tableaux** : Matrices de gains, comparaison equilibres, valeurs Shapley par joueur
- **Visualisations** : Arbres de jeu, diagrammes de meilleure reponse
- **Interpretations** : Expliquer pourquoi un profil est/n'est pas un equilibre

#### ML/Deep Learning

- **Vocabulaire** : loss, accuracy, precision, recall, overfitting, regularisation
- **Tableaux** : Metriques par epoch, comparaison modeles, matrices de confusion
- **Graphiques** : Courbes d'apprentissage, ROC, importance des features

#### Optimisation

- **Vocabulaire** : fitness, convergence, contraintes, espace de recherche, front Pareto
- **Tableaux** : Evolution fitness, comparaison algorithmes, parametres optimaux
- **Interpretations** : Expliquer la convergence ou non-convergence

#### Logique formelle (Lean, Z3, Tweety)

- **Vocabulaire** : theoreme, lemme, preuve, tactique, satisfiabilite
- **Formules** : Notation logique formelle, quantificateurs
- **Interpretations** : Expliquer la strategie de preuve, les tactiques utilisees

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

## Outils de support

Utiliser `scripts/notebook_tools.py` pour preparer l'enrichissement :

```bash
# Analyser la structure d'un notebook
python scripts/notebook_tools.py skeleton MyIA.AI.Notebooks/GameTheory/notebook.ipynb --output json

# Verifier l'etat des sorties
python scripts/notebook_tools.py analyze MyIA.AI.Notebooks/GameTheory/

# Valider la structure et le contenu
python scripts/notebook_tools.py validate MyIA.AI.Notebooks/GameTheory --verbose
```

En Python, utiliser le module directement :

```python
from scripts.notebook_tools import NotebookAnalyzer, NotebookValidator

analyzer = NotebookAnalyzer("notebook.ipynb")
skeleton = analyzer.get_skeleton()
print(f"Sections: {[s.title for s in skeleton.sections]}")
print(f"Code/Markdown ratio: {skeleton.code_cells}/{skeleton.markdown_cells}")
```

## Serie de notebooks

Pour traiter une serie complete, lancer des agents en parallele :

```python
notebooks = glob("MyIA.AI.Notebooks/Probas/Infer/*.ipynb")
for nb in notebooks:
    Task(
        subagent_type="general-purpose",
        prompt=f"Enrichir {nb} selon .claude/agents/notebook-enricher.md",
        run_in_background=True,
        model="sonnet"  # Utiliser Sonnet pour les taches d'enrichissement
    )
```

## Agents specialises disponibles

| Agent | Domaine | Fichier |
|-------|---------|---------|
| infer-notebook-enricher | Probabilites/Infer.NET | .claude/agents/infer-notebook-enricher.md |

> **Note** : Pour les autres domaines (GameTheory, ML, etc.), utiliser cet agent generique
> avec les adaptations decrites dans la section "Guide d'adaptation par domaine".
