# SymbolicAI - Notebooks TweetyProject

Collection de notebooks Jupyter pour l'apprentissage de l'IA symbolique avec la bibliotheque Java [TweetyProject](https://tweetyproject.org/).

## Serie Tweety - 10 Notebooks Complets

**Statut**: Serie complete validee (100%)

Explorez les logiques symboliques et l'argumentation computationnelle avec cette serie progressive:

### Partie 1 : Fondations

| # | Notebook | Theme | Duree |
|---|----------|-------|-------|
| 1 | [Tweety-1-Setup](Tweety/Tweety-1-Setup.ipynb) | Configuration JVM, JARs, outils externes | 20 min |
| 2 | [Tweety-2-Basic-Logics](Tweety/Tweety-2-Basic-Logics.ipynb) | Logique Propositionnelle (PL) et FOL | 45 min |
| 3 | [Tweety-3-Advanced-Logics](Tweety/Tweety-3-Advanced-Logics.ipynb) | DL, Modale, QBF, Conditionnelle | 40 min |

### Partie 2 : Revision de Croyances

| # | Notebook | Theme | Duree |
|---|----------|-------|-------|
| 4 | [Tweety-4-Belief-Revision](Tweety/Tweety-4-Belief-Revision.ipynb) | CrMas, MUS, MaxSAT, Mesures d'incoherence | 50 min |

### Partie 3 : Argumentation

| # | Notebook | Theme | Duree |
|---|----------|-------|-------|
| 5 | [Tweety-5-Abstract-Argumentation](Tweety/Tweety-5-Abstract-Argumentation.ipynb) | Dung AF, Semantiques, CF2, Generation | 55 min |
| 6 | [Tweety-6-Structured-Argumentation](Tweety/Tweety-6-Structured-Argumentation.ipynb) | ASPIC+, DeLP, ABA, ASP | 60 min |
| 7a | [Tweety-7a-Extended-Frameworks](Tweety/Tweety-7a-Extended-Frameworks.ipynb) | ADF, Bipolar, WAF, SAF, SetAF, Extended | 50 min |
| 7b | [Tweety-7b-Ranking-Probabilistic](Tweety/Tweety-7b-Ranking-Probabilistic.ipynb) | Ranking Semantics, Probabiliste | 40 min |

### Partie 4 : Applications

| # | Notebook | Theme | Duree |
|---|----------|-------|-------|
| 8 | [Tweety-8-Agent-Dialogues](Tweety/Tweety-8-Agent-Dialogues.ipynb) | Agents, Dialogues argumentatifs, Loteries | 35 min |
| 9 | [Tweety-9-Preferences](Tweety/Tweety-9-Preferences.ipynb) | Preferences, Theorie du vote | 30 min |

**Duree totale estimee** : ~7 heures

---

## Contenu Detaille

### 1. Setup - Configuration Environnement
- Installation automatique Python + JPype + Tweety
- Telechargement JDK portable (Zulu 17)
- Telechargement JARs TweetyProject v1.28/1.29
- Configuration outils externes (Clingo, SPASS)
- Demarrage et test JVM

**IMPORTANT**: A executer en premier, obligatoire pour tous les autres notebooks.

### 2. Basic Logics - Logiques Fondamentales
- **Logique Propositionnelle (PL)**: Syntaxe, parsing, mondes possibles
- **Solveurs SAT**: Comparaison CaDiCaL, Glucose, MiniSat avec pySAT
- **Logique du Premier Ordre (FOL)**: Signatures, sorts, predicats

### 3. Advanced Logics - Logiques Avancees
- **Logique de Description (DL)**: ABox, TBox, concepts, roles
- **Logique Modale (ML)**: Operateurs modaux, semantiques Kripke
- **QBF**: Formules booleennes quantifiees
- **Logique Conditionnelle (CL)**

### 4. Belief Revision - Revision de Croyances
- Revision de croyances multi-agents (CrMas)
- Mesures d'incoherence (distance, contension, fuzzy)
- Enumeration MUS (Minimal Unsatisfiable Subsets)
- MaxSAT avec Open-WBO

### 5. Abstract Argumentation - Argumentation de Dung
- Cadres d'argumentation de Dung
- Semantiques: Grounded, Preferred, Stable, Complete, CF2
- Generation et apprentissage de cadres
- Raisonneurs alternatifs

### 6. Structured Argumentation - Argumentation Structuree
- **ASPIC+**: Construction PL/FOL, conversion vers Dung
- **DeLP**: Defeasible Logic Programming
- **ABA**: Assumption-Based Argumentation
- **Argumentation Deductive**
- **ASP**: Answer Set Programming avec Clingo

### 7a. Extended Frameworks - Frameworks Etendus
- **ADF**: Abstract Dialectical Frameworks
- **Bipolar**: Frameworks bipolaires (support + attaque)
- **WAF**: Frameworks ponderes
- **SAF**: Argumentation sociale
- **SetAF**: Attaques collectives
- **EAF/REAF**: Attaques recursives

### 7b. Ranking & Probabilistic - Classement et Probabilites
- Semantiques de classement (Categorizer, h-Categorizer, Burden)
- Argumentation probabiliste
- Comparaison solveurs natifs et Java

### 8. Agent Dialogues - Agents et Dialogues
- Framework agents de base
- Jeux grounded (ArguingAgent)
- Dialogues argumentatifs
- Loteries argumentatives

### 9. Preferences - Preferences et Vote
- Ordres de preference
- Theorie du vote
- Agregation de preferences

---

## Structure du Repertoire

```
SymbolicAI/
├── Tweety/                                # Serie principale
│   ├── Tweety-1-Setup.ipynb
│   ├── Tweety-2-Basic-Logics.ipynb
│   ├── Tweety-3-Advanced-Logics.ipynb
│   ├── Tweety-4-Belief-Revision.ipynb
│   ├── Tweety-5-Abstract-Argumentation.ipynb
│   ├── Tweety-6-Structured-Argumentation.ipynb
│   ├── Tweety-7a-Extended-Frameworks.ipynb
│   ├── Tweety-7b-Ranking-Probabilistic.ipynb
│   ├── Tweety-8-Agent-Dialogues.ipynb
│   ├── Tweety-9-Preferences.ipynb
│   ├── libs/                              # JARs TweetyProject (35 modules)
│   ├── resources/                         # Fichiers d'exemples
│   ├── ext_tools/                         # Outils externes (Clingo, SPASS)
│   ├── jdk-17-portable/                   # JDK Zulu (telecharge auto)
│   ├── scripts/                           # Scripts de validation
│   └── README.md
│
├── Argument_Analysis/                     # Analyse argumentative avec LLM
├── Lean/                                  # Proof Assistant Lean 4
└── README.md                              # Ce fichier
```

---

## Demarrage Rapide

### Installation (Premiere Fois)

1. **Cloner le depot** (si pas deja fait):
```bash
git clone https://github.com/jsboige/CoursIA.git
cd CoursIA/MyIA.AI.Notebooks/SymbolicAI/Tweety
```

2. **Lancer Jupyter**:
```bash
jupyter notebook
```

3. **Executer Tweety-1-Setup.ipynb** en entier
   - Installe automatiquement: packages Python, JDK, JARs Tweety, outils
   - Duree: ~5-10 minutes selon connexion internet

4. **Explorer les notebooks 2-9** dans l'ordre ou a la carte

### Utilisation Quotidienne

Si l'environnement est deja configure:
1. Lancer Jupyter
2. Ouvrir directement le notebook souhaite
3. L'initialisation JVM se fait automatiquement

---

## Verification et Tests

### Script de verification

```bash
cd Tweety/scripts/

# Verification structurelle rapide
python verify_all_tweety.py --quick

# Verification environnement
python verify_all_tweety.py --check-env

# Analyse des sorties existantes
python verify_all_tweety.py --analyze-outputs --verbose

# Execution complete
python verify_all_tweety.py --execute --verbose
```

---

## Outils Externes

| Outil | Usage | Installation |
|-------|-------|--------------|
| **Clingo** | ASP (Answer Set Programming) | Auto-telecharge |
| **SPASS** | Logique Modale | Manuel (Windows) |
| **EProver** | FOL haute performance | Inclus |
| **Z3** | SMT solver, MARCO | `pip install z3-solver` |
| **PySAT** | SAT/MaxSAT moderne | `pip install python-sat` |

---

## Dependances

### Automatiquement Installees

- **Python packages**: jpype1, requests, tqdm, clingo, python-sat, z3-solver
- **JDK**: Zulu 17 portable (auto-telecharge)
- **TweetyProject**: v1.28/1.29 (35 JARs)
- **Clingo**: v5.4.0 (Windows/Linux auto-install)

### Installation manuelle

```bash
pip install jpype1 requests tqdm clingo z3-solver python-sat
```

---

## Limitations Connues (Tweety 1.28/1.29)

| Limitation | Impact | Contournement |
|------------|--------|---------------|
| **CrMas/InformationObject** | Section revision multi-agents | API refactorisee dans 1.28+ |
| **SimpleMlReasoner** | Bloque indefiniment | Utiliser SPASS externe |
| **ADF natif SAT** | Raisonnement ADF incomplet | Necessite solveur SAT natif |
| **SPASS Windows** | Requiert droits admin | Erreur 740 sans elevation |

---

## Ressources

- **TweetyProject**: https://tweetyproject.org/
- **Documentation API**: https://tweetyproject.org/api/
- **GitHub**: https://github.com/TweetyProjectTeam/TweetyProject
- **JPype**: https://jpype.readthedocs.io/

---

## Licence

Les notebooks sont distribues sous licence MIT.
TweetyProject est sous licence LGPL 3.0.

---

**Derniere mise a jour**: 2026-01-31
**Auteur**: Jean-Sebastien Bevilacqua (jsboige@gmail.com)
