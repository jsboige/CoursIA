# Argument_Analysis - Plan de Reconstruction

**Issue** : #632
**Date** : 2026-05-01
**Statut** : Investigation terminee, en attente de decision

## Resume executif

La serie Argument_Analysis comprend **6 notebooks sources** formant un pipeline agentic d'analyse rhetorique combineant Semantic Kernel (Python) avec Tweety (Java/JPype) pour le raisonnement formel en logique propositionnelle.

**Verdict** : Les notebooks sont architecturalement complets et ont ete executes avec succes au moins une fois en mode batch (Papermill, statut `COMPLETE_VALIDATED`). La non-fonctionnalite actuelle est **environnementale** (repertoire de travail, JVM, cles API), pas structurelle.

## Notebooks (6 sources)

| # | Notebook | Role | Etat | Difficulte |
|---|----------|------|------|------------|
| 1 | `UI_configuration.ipynb` | Widgets de configuration UI, extraction texte | Fonctionne en standalone | EASY |
| 2 | `Agentic-0-init.ipynb` | Initialisation : pip install, JVM, Semantic Kernel, state | 3 erreurs en cascade | HARD |
| 3 | `Agentic-1-informal_agent.ipynb` | Agent informel : sophismes, analyse rhetorique | OK (definitions seules) | MEDIUM |
| 4 | `Agentic-2-pl_agent.ipynb` | Agent logique propositionnelle : Tweety + LLM | JVM-dependant | HARD |
| 5 | `Agentic-3-orchestration.ipynb` | Orchestration multi-agents, terminaison | NameError (cascading) | MEDIUM |
| 6 | `Executor.ipynb` | Point d'entree, `%run` des autres notebooks | Erreur path relatif | MEDIUM |

## Causes racines (par severite)

### CRITIQUE 1 : Repertoire de travail (Executor + 0-init)

L'Executor utilise `%run ./Argument_Analysis_UI_configuration.ipynb` avec un chemin relatif. Le 0-init utilise `find_dotenv()` pour `.env`. Ces deux mecanismes echouent quand le CWD de Jupyter n'est pas le dossier `Argument_Analysis/`.

**Impact** : Executor echoue immediatement, 0-init ne charge pas la config.

**Fix** :
- Remplacer les chemins relatifs par `os.path.dirname(os.path.abspath(__file__))` equivalent
- Ou utiliser `__file__` via `ipywidgets` / `Path().resolve()` pattern
- Ajouter `os.chdir()` en debut d'Executor

### CRITIQUE 2 : JVM/Tweety non operationnel

Le JDK 17 portable (`jdk-17-portable/`) n'est pas detecte : `"No JVM shared library file (jvm.dll) found."`. Le code de detection cherche `jvm.dll` mais ne le trouve pas.

**Impact** : `PropositionalLogicPlugin` fonctionne en mode degrade (simulation LLM uniquement, pas de raisonnement formel reel).

**Fix** :
- Verifier le chemin `jdk-17-portable/bin/server/jvm.dll` existe
- Ajouter un fallback `JAVA_HOME` explicite dans le code
- Tester sur la machine cible (Windows, JDK portable)

### ELEVEE 3 : Cle API placeholder

Le fichier `.env` contient `sk-proj-1234567890` (cle factice). Sans cle OpenAI reelle, les agents LLM ne fonctionnent pas.

**Impact** : Aucun agent ne peut generer de reponse.

**Fix** :
- Documenter le besoin dans un `.env.example` avec les cles requises
- Ajouter une validation au demarrage avec message clair
- Supporter OpenRouter comme alternative ( deja configure dans le repo global)

### MOYENNE 4 : Bug callback `query_string` vs `query`

`PropositionalLogicPlugin.execute_and_log_pl_query()` appelle `self._log_callback(query_string=..., raw_result=...)` mais `StateManagerPlugin.log_query_result()` attend `(belief_set_id, query, raw_result)`. Le keyword `query_string` cause un `TypeError`.

**Impact** : Chaque log de requete PL echoue.

**Fix** : Remplacer `query_string=` par `query=` dans `Agentic-2-pl_agent.ipynb`.

### MOYENNE 5 : Erreurs de parsing Tweety

Le LLM genere des "belief sets" en langage naturel au lieu de syntaxe propositionnelle stricte (BNF Tweety). Le parser Java rejette avec `ParserException: Unknown object ID`.

**Impact** : Perturbation des requetes formelles.

**Fix** :
- Ameliorer les prompts pour contraindre le format de sortie
- Ajouter un retry avec feedback d'erreur au LLM
- Ou pre-valider le format avant envoi au parser Java

### FAIBLE 6 : Metadonnees kernel incoherentes

3 notebooks utilisent `kernel: base / python3` (3.13.7), 3 utilisent `kernel: Python 3 / python3` (3.13.2/3.13.3). Pas de consequence fonctionnelle mais complique le debugging.

**Fix** : Harmoniser les metadonnees kernel.

## Infrastructure presente

| Element | Emplacement | Taille | Statut |
|---------|-------------|--------|--------|
| JDK 17 portable | `jdk-17-portable/` | ~300MB | Present mais non detecte |
| Tweety JARs (33) | `libs/*.jar` | ~450MB | Present |
| EProver + SPASS | `ext_tools/` | ~50MB | Present (Cygwin) |
| SAT native libs | `libs/native/*.dll` | ~5MB | Present |
| Fallacy taxonomy | `data/argumentum_fallacies_taxonomy.csv` | 2.2MB | Present |
| OWL ontology | `ontologies/argumentum_fallacies.owl` | 4.7MB | Present |
| Batch outputs | `output/` (3 .ipynb) | -- | Preuve d'execution reussie |

## Strategies de reconstruction

### Option A : Fix minimal (2-3h)

Corriger les 4 bugs code (chemins, callback, prompts PL, kernel metadata). Les notebooks deviennent executables si l'environnement est correctement configure (JDK, .env, CWD).

**Avantages** : Rapide, preserve l'architecture existante.
**Risques** : Reste dependant de JPype/JVM, experience utilisateur fragile.

### Option B : Refactoring modularise (1-2 jours)

En plus du fix minimal :
- Extraire les classes Python dans des modules `.py` distincts
- Remplacer `%run` par des imports Python propres
- Ajouter un `setup.py` / `pyproject.toml` pour les dependances
- Creer un script de verification d'environnement
- Ajouter un `.env.example` avec instructions

**Avantages** : Maintenable, testable, experience utilisateur robuste.
**Risques** : Effort plus important, peut casser le flux existant.

### Option C : Migration partielle Tweety (3-5 jours)

En plus de l'Option B :
- Remplacer JPype/Tweety par `python-tweety` (bindings Python natifs) si disponible
- Ou utiliser le package `tweety-python` sur PyPI
- Eliminer la dependance JVM entiere

**Avantages** : Supprime la dependance Java (~800MB d'infrastructure).
**Risques** : `python-tweety` peut ne pas avoir la parite fonctionnelle. Effort significatif.

## Recommandation

**Option B** (refactoring modularise). L'architecture agentic est saine et a deja fonctionne. Le probleme principal est l'experience developpeur : chemins fragiles, JVM difficile a configurer, pas de validation d'environnement. Un refactoring modulaire resout ces problemes tout en preservant la logique metier.

Etapes prioritaire :
1. Fix bug callback `query_string` (5 min)
2. Fix chemins relatifs -> absolus dans Executor (30 min)
3. Creer `.env.example` avec documentation (15 min)
4. Ajouter script `check_environment.py` (30 min)
5. Extraire classes dans modules `.py` (2h)
6. Harmoniser metadonnees kernel (15 min)
7. Re-executer et valider (1h)

## Dependances pour execution

```
# Python (pip)
semantic-kernel>=1.0
jpype1>=1.4
openai>=1.0
python-dotenv
pandas
requests
ipywidgets
jupyter-ui-poll
cryptography
pydantic
nest-asyncio

# Systeme
JDK 17+ (portable ou installe)
~1.3 GB espace disque (JDK + JARs + ext_tools)
```
