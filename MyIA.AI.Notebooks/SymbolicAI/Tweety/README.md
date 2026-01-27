# TweetyProject - Serie de Notebooks Jupyter

Serie complete de 10 notebooks pour explorer [TweetyProject](https://tweetyproject.org/), une bibliotheque Java pour l'intelligence artificielle symbolique.

## Presentation

TweetyProject est une collection de bibliotheques Java couvrant :
- **Logiques formelles** : Propositionnelle, Premier ordre, Modale, Description, QBF
- **Argumentation computationnelle** : Dung, ASPIC+, DeLP, ABA, ADF
- **Revision de croyances** : AGM, Mesures d'incoherence, MUS/MCS
- **Agents et dialogues** : Multi-agents, Protocoles argumentatifs
- **Preferences et vote** : Ordres de preference, Agregation

Les notebooks utilisent **JPype** pour integrer Java dans Python, permettant un apprentissage interactif.

## Structure de la Serie

| # | Notebook | Theme | Duree |
|---|----------|-------|-------|
| **Fondations** |
| 1 | [Tweety-1-Setup](Tweety-1-Setup.ipynb) | Configuration JVM, JARs, outils externes | 20 min |
| 2 | [Tweety-2-Basic-Logics](Tweety-2-Basic-Logics.ipynb) | Logique Propositionnelle et FOL | 45 min |
| 3 | [Tweety-3-Advanced-Logics](Tweety-3-Advanced-Logics.ipynb) | DL, Modale, QBF, Conditionnelle | 40 min |
| **Revision de Croyances** |
| 4 | [Tweety-4-Belief-Revision](Tweety-4-Belief-Revision.ipynb) | CrMas, MUS, MaxSAT, Mesures d'incoherence | 50 min |
| **Argumentation** |
| 5 | [Tweety-5-Abstract-Argumentation](Tweety-5-Abstract-Argumentation.ipynb) | Dung AF, Semantiques, CF2, Generation | 55 min |
| 6 | [Tweety-6-Structured-Argumentation](Tweety-6-Structured-Argumentation.ipynb) | ASPIC+, DeLP, ABA, ASP | 60 min |
| 7a | [Tweety-7a-Extended-Frameworks](Tweety-7a-Extended-Frameworks.ipynb) | ADF, Bipolar, WAF, SAF, SetAF, Extended | 50 min |
| 7b | [Tweety-7b-Ranking-Probabilistic](Tweety-7b-Ranking-Probabilistic.ipynb) | Ranking Semantics, Probabiliste | 40 min |
| **Applications** |
| 8 | [Tweety-8-Agent-Dialogues](Tweety-8-Agent-Dialogues.ipynb) | Agents, Dialogues argumentatifs, Loteries | 35 min |
| 9 | [Tweety-9-Preferences](Tweety-9-Preferences.ipynb) | Preferences, Theorie du vote | 30 min |

**Duree totale estimee** : ~7 heures

## Prerequis

### Logiciels requis

- **Python 3.10+** avec pip
- **JDK 17+** (telecharge automatiquement si absent)

### Packages Python

```bash
pip install jpype1 requests tqdm clingo z3-solver python-sat
```

### Installation rapide

1. Cloner le repository
2. Ouvrir `Tweety-1-Setup.ipynb`
3. Executer toutes les cellules (telechargement automatique des JARs et JDK)

## Architecture

```
Tweety/
├── Tweety-1-Setup.ipynb          # Configuration
├── Tweety-2-Basic-Logics.ipynb   # PL + FOL
├── Tweety-3-Advanced-Logics.ipynb # DL, ML, QBF, CL
├── Tweety-4-Belief-Revision.ipynb # Revision de croyances
├── Tweety-5-Abstract-Argumentation.ipynb
├── Tweety-6-Structured-Argumentation.ipynb
├── Tweety-7a-Extended-Frameworks.ipynb
├── Tweety-7b-Ranking-Probabilistic.ipynb
├── Tweety-8-Agent-Dialogues.ipynb
├── Tweety-9-Preferences.ipynb
├── libs/                          # JARs Tweety (35 modules)
├── resources/                     # Fichiers d'exemples (.txt, .aba, .aspic)
├── ext_tools/                     # Outils externes (Clingo, SPASS, EProver)
├── jdk-17-portable/              # JDK Zulu (telecharge auto)
├── scripts/
│   ├── verify_all_tweety.py      # Script de validation
│   └── validate_syntax.py        # Validation syntaxe Python
└── README.md                      # Ce fichier
```

## Outils Externes

| Outil | Usage | Installation |
|-------|-------|--------------|
| **Clingo** | ASP (Answer Set Programming) | Auto-telecharge |
| **SPASS** | Logique Modale | Manuel (Windows) |
| **EProver** | FOL haute performance | Inclus |
| **Z3** | SMT solver, MARCO | `pip install z3-solver` |
| **PySAT** | SAT/MaxSAT moderne | `pip install python-sat` |

## Limitations Connues (Tweety 1.28/1.29)

| Limitation | Impact | Contournement |
|------------|--------|---------------|
| **CrMas/InformationObject** | Section revision multi-agents echoue | API refactorisee, classe supprimee |
| **SimpleMlReasoner** | Bloque indefiniment | Utiliser SPASS externe |
| **AF Learning** | ClassCastException | Bug interne, section desactivee |
| **ADF natif SAT** | Raisonnement ADF incomplet | Necessite solveur SAT natif (non JPype) |
| **FOL avec egalite** | Heap space sur grandes requetes | Utiliser EProver externe |

## Modules TweetyProject Couverts

### Logiques (Notebooks 2-3)

| Module | Description | Notebook |
|--------|-------------|----------|
| `logics.pl` | Logique Propositionnelle | 2 |
| `logics.fol` | Logique du Premier Ordre | 2 |
| `logics.dl` | Logique de Description | 3 |
| `logics.ml` | Logique Modale | 3 |
| `logics.qbf` | Quantified Boolean Formulas | 3 |
| `logics.cl` | Logique Conditionnelle | 3 |

### Revision de Croyances (Notebook 4)

| Module | Description |
|--------|-------------|
| `beliefdynamics` | Operateurs de revision AGM |
| `logics.pl.analysis` | Mesures d'incoherence |
| `logics.pl.sat` | MUS, MaxSAT |

### Argumentation (Notebooks 5-7)

| Module | Description | Notebook |
|--------|-------------|----------|
| `arg.dung` | Frameworks de Dung | 5 |
| `arg.aspic` | ASPIC+ | 6 |
| `arg.delp` | Defeasible Logic Programming | 6 |
| `arg.aba` | Assumption-Based Argumentation | 6 |
| `lp.asp` | Answer Set Programming | 6 |
| `arg.adf` | Abstract Dialectical Frameworks | 7a |
| `arg.bipolar` | Frameworks Bipolaires | 7a |
| `arg.weighted` | Frameworks Ponderes | 7a |
| `arg.social` | Argumentation Sociale | 7a |
| `arg.setaf` | Attaques Collectives | 7a |
| `arg.extended` | Attaques Recursives | 7a |
| `arg.rankings` | Semantiques de Classement | 7b |
| `arg.prob` | Argumentation Probabiliste | 7b |

### Agents et Preferences (Notebooks 8-9)

| Module | Description | Notebook |
|--------|-------------|----------|
| `agents` | Framework agents de base | 8 |
| `agents.dialogues` | Dialogues argumentatifs | 8 |
| `agents.dialogues.oppmodels` | Jeux grounded (ArguingAgent) | 8 |
| `agents.dialogues.lotteries` | Loteries argumentatives | 8 |
| `preferences` | Ordres de preference, agregation | 9 |

## Validation des Notebooks

### Script de verification

```bash
cd MyIA.AI.Notebooks/SymbolicAI/Tweety/scripts

# Verification structurelle rapide
python verify_all_tweety.py --quick

# Verification environnement
python verify_all_tweety.py --check-env

# Analyse des sorties existantes
python verify_all_tweety.py --analyze-outputs --verbose

# Execution complete (lent)
python verify_all_tweety.py --execute --verbose

# Notebook specifique
python verify_all_tweety.py --notebook Tweety-2 --analyze-outputs
```

### Options disponibles

| Option | Description |
|--------|-------------|
| `--quick` | Validation structure uniquement |
| `--check-env` | Verifier JDK, JARs, outils |
| `--analyze-outputs` | Analyser sorties existantes |
| `--execute` | Execution Papermill complete |
| `--cell-by-cell` | Execution cellule par cellule |
| `--execute-missing` | Executer cellules sans output |
| `--clean-errors` | Nettoyer sorties en erreur |
| `--verbose` | Sortie detaillee |
| `--json` | Format JSON (CI/CD) |

## Versions TweetyProject

| Version | Date | Nouveautes |
|---------|------|------------|
| **1.28** | Jan 2025 | arg.caf, k-admissibility, API refactoring |
| **1.29** | Jul 2025 | arg.eaf (Epistemic AF), graph rendering |

La version est configurable dans `Tweety-1-Setup.ipynb` (variable `TWEETY_VERSION`).

## Ressources

- **TweetyProject** : https://tweetyproject.org/
- **Documentation API** : https://tweetyproject.org/api/
- **GitHub** : https://github.com/TweetyProjectTeam/TweetyProject
- **JPype** : https://jpype.readthedocs.io/

## Licence

Les notebooks sont distribues sous licence MIT.
TweetyProject est sous licence LGPL 3.0.
