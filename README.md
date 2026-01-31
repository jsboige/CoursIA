# CoursIA

Bienvenue dans le depot **CoursIA**, plateforme educative complete pour l'apprentissage de l'intelligence artificielle en C# et Python.

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

## Table des matieres

- [Introduction](#introduction)
- [Cartographie complete](#cartographie-complete)
- [Series de notebooks](#series-de-notebooks)
- [Mise en route](#mise-en-route)
- [Outils Claude Code](#outils-claude-code)
- [Infrastructure](#infrastructure)
- [Contribution](#contribution)

## Introduction

Ce depot contient **100+ notebooks Jupyter** interactifs couvrant :
- **IA Symbolique** : Logiques formelles, argumentation, verification formelle
- **Probabilites** : Inference bayesienne, modeles graphiques (Infer.NET)
- **Theorie des jeux** : Nash, jeux evolutionnaires, cooperatifs
- **Machine Learning** : ML.NET, algorithmes genetiques
- **IA Generative** : OpenAI, LLMs, generation d'images

Les notebooks sont en **C# (.NET Interactive)** et **Python**, avec une documentation pedagogique complete.

## Cartographie complete

### Structure du depot

```
CoursIA/
├── MyIA.AI.Notebooks/           # 100+ notebooks interactifs
│   ├── GenAI/                   # IA Generative (18 notebooks)
│   ├── ML/                      # Machine Learning (5 notebooks)
│   ├── Sudoku/                  # Resolution Sudoku (11 notebooks)
│   ├── Search/                  # Recherche et optimisation (5 notebooks)
│   ├── SymbolicAI/              # IA Symbolique (31 notebooks)
│   │   ├── Tweety/              # TweetyProject - 10 notebooks
│   │   ├── Lean/                # Lean 4 - 10 notebooks
│   │   ├── Argument_Analysis/   # Analyse argumentative - 6 notebooks
│   │   └── Planners/            # Planification (Fast-Downward)
│   ├── Probas/                  # Probabilites
│   │   └── Infer/               # Infer.NET - 20 notebooks
│   ├── GameTheory/              # Theorie des jeux (26 notebooks)
│   ├── IIT/                     # Integrated Information Theory
│   ├── EPF/                     # Devoirs etudiants
│   └── Config/                  # Configuration API
│
├── .claude/                     # Configuration Claude Code
│   ├── agents/                  # 4 agents specialises
│   └── commands/                # 3 skills (commandes slash)
│
├── scripts/                     # Scripts utilitaires
│   ├── verify_notebooks.py      # Verification notebooks
│   ├── extract_notebook_skeleton.py  # Extraction structure
│   └── genai-stack/             # Validation GenAI
│
├── GradeBookApp/                # Systeme de notation etudiants
├── docker-configurations/       # Infrastructure Docker (ComfyUI, Qwen)
├── docs/                        # Documentation projets
└── MyIA.AI.Shared/              # Bibliotheque C# partagee
```

### Statistiques globales

| Categorie | Notebooks | Cellules | Duree estimee |
|-----------|-----------|----------|---------------|
| **SymbolicAI** | 31 | ~920 | ~20h30 |
| **GameTheory** | 26 | ~800 | ~18h30 |
| **Infer.NET** | 20 | ~400 | ~8h |
| **GenAI** | 18 | ~300 | ~6h |
| **Sudoku** | 11 | ~170 | ~2h |
| **Search** | 5 | ~95 | ~1h10 |
| **ML** | 5 | ~80 | ~1h30 |
| **Total** | **~120** | **~2800** | **~60h** |

## Series de notebooks

### SymbolicAI - IA Symbolique

**31 notebooks** couvrant les logiques formelles, l'argumentation computationnelle et la verification formelle.

| Serie | Notebooks | Contenu | README |
|-------|-----------|---------|--------|
| **Tweety** | 10 | TweetyProject, logiques PL/FOL/DL, argumentation Dung, ASPIC+ | [README](MyIA.AI.Notebooks/SymbolicAI/Tweety/README.md) |
| **Lean** | 10 | Lean 4, types dependants, tactiques, Mathlib, LLM integration | [README](MyIA.AI.Notebooks/SymbolicAI/Lean/README.md) |
| **Argument_Analysis** | 6 | Analyse argumentative multi-agents avec Semantic Kernel | - |
| **Autres** | 5 | Z3, OR-Tools, RDF.NET, Fast-Downward | - |

[README SymbolicAI](MyIA.AI.Notebooks/SymbolicAI/README.md)

### GameTheory - Theorie des Jeux

**26 notebooks** (17 principaux + 9 side tracks) combinant Python et Lean 4.

| Partie | Notebooks | Contenu |
|--------|-----------|---------|
| **Fondations** | 1-6 | Forme normale, Nash, minimax, jeux evolutionnaires |
| **Jeux dynamiques** | 7-12 | Forme extensive, backward induction, jeux bayesiens |
| **Avances** | 13-17 | CFR, jeux differentiels, cooperatifs, mechanism design, MARL |
| **Side tracks** | b/c | Lean 4 (formalisations), Python (approfondissements) |

[README GameTheory](MyIA.AI.Notebooks/GameTheory/README.md)

### Probas/Infer - Programmation Probabiliste

**20 notebooks** sur Infer.NET couvrant l'inference bayesienne et la theorie de la decision.

| Groupe | Notebooks | Contenu |
|--------|-----------|---------|
| **Fondamentaux** | 1-3 | Setup, Gaussiennes, Factor Graphs |
| **Modeles classiques** | 4-6 | Reseaux bayesiens, IRT/DINA, TrueSkill |
| **Classification** | 7-8 | Probit/BPM, selection de modeles |
| **Avances** | 9-12 | LDA, crowdsourcing, HMM, recommandation |
| **Reference** | 13 | Debugging, bonnes pratiques |
| **Decision** | 14-20 | Theorie de la decision, utilite, VOI, POMDP |

[README Infer](MyIA.AI.Notebooks/Probas/Infer/README.md)

### Sudoku - Resolution par Contraintes

**11 notebooks** (7 C#, 4 Python) illustrant differentes approches algorithmiques.

| Approche | Notebooks | Technologies |
|----------|-----------|--------------|
| **Backtracking** | 1, Python | MRV, recherche exhaustive |
| **Genetique** | 2, Python | GeneticSharp, PyGAD |
| **Contraintes** | 3, Python | OR-Tools CP/SAT/MIP |
| **SMT** | 4, Python | Z3, bitvectors |
| **Couverture exacte** | 5, Python | Dancing Links (DLX) |
| **Probabiliste** | 6 | Infer.NET |

[README Sudoku](MyIA.AI.Notebooks/Sudoku/README.md)

### Search - Recherche et Optimisation

**5 notebooks** sur les algorithmes de recherche et les metaheuristiques.

| Notebook | Kernel | Contenu |
|----------|--------|---------|
| CSPs_Intro | Python | Programmation par contraintes, AC-3, N-Queens |
| Exploration | Python | BFS, DFS, A*, Hill Climbing, Simulated Annealing |
| GeneticSharp-EdgeDetection | C# | Detection de bords avec GeneticSharp |
| Portfolio_Optimization | C# | Optimisation de portefeuille |
| PyGad-EdgeDetection | Python | Detection de bords avec PyGAD |

[README Search](MyIA.AI.Notebooks/Search/README.md)

### GenAI - IA Generative

**18 notebooks** organises en 4 niveaux progressifs.

| Niveau | Contenu |
|--------|---------|
| **00-Environment** | Setup, Docker, API configuration |
| **01-Foundation** | DALL-E 3, GPT-5, operations de base |
| **02-Advanced** | Qwen Image Edit, FLUX, Stable Diffusion 3.5 |
| **03-Orchestration** | Comparaison multi-modeles, workflows |
| **04-Applications** | Contenu educatif, integration production |

[README GenAI](MyIA.AI.Notebooks/GenAI/README.md)

### ML - Machine Learning

**5 notebooks** sur ML.NET et AutoML.

- ML-1 a ML-4 : Introduction, Features, Entrainement, Evaluation
- TP-prevision-ventes : Projet pratique

## Mise en route

### Prerequis

- **Python 3.10+** avec pip
- **.NET 9.0 SDK** (pour notebooks C#)
- **Visual Studio Code** avec extensions Python, Jupyter, .NET
- **Cles API** : OpenAI, Anthropic (optionnel)

### Installation rapide

```bash
# 1. Cloner le depot
git clone https://github.com/jsboige/CoursIA.git
cd CoursIA

# 2. Environnement Python
python -m venv venv
venv\Scripts\activate  # Windows
pip install jupyter openai anthropic

# 3. Kernel Python
python -m ipykernel install --user --name=coursia --display-name "Python (CoursIA)"

# 4. Packages .NET
dotnet restore MyIA.CoursIA.sln

# 5. Configuration API
cp MyIA.AI.Notebooks/Config/settings.json.openai-example MyIA.AI.Notebooks/Config/settings.json
# Editer et ajouter les cles API
```

### Parcours d'apprentissage suggere

1. **ML** - Introduction au Machine Learning avec ML.NET
2. **Sudoku** - Algorithmes de resolution (backtracking, contraintes)
3. **Search** - Recherche et optimisation
4. **SymbolicAI/Tweety** - Logiques formelles et argumentation
5. **Probas/Infer** - Inference bayesienne
6. **GameTheory** - Theorie des jeux
7. **SymbolicAI/Lean** - Verification formelle
8. **GenAI** - IA generative

## Outils Claude Code

### Skills (Commandes slash)

| Commande | Description |
|----------|-------------|
| `/verify-notebooks [target]` | Verifier et tester les notebooks |
| `/enrich-notebooks [target]` | Enrichir avec du contenu pedagogique |
| `/cleanup-notebooks [target]` | Nettoyer et reorganiser le markdown |

**Exemples** :
```bash
/verify-notebooks Sudoku --quick
/enrich-notebooks Infer --consecutive
/cleanup-notebooks Tweety --dry-run
```

### Agents specialises

| Agent | Fichier | Mission |
|-------|---------|---------|
| `notebook-enricher` | `.claude/agents/notebook-enricher.md` | Enrichissement pedagogique |
| `infer-notebook-enricher` | `.claude/agents/infer-notebook-enricher.md` | Specialisation Infer.NET |
| `notebook-cleaner` | `.claude/agents/notebook-cleaner.md` | Nettoyage markdown |
| `readme-updater` | `.claude/agents/readme-updater.md` | Mise a jour README |

### Scripts utilitaires

```bash
# Verification des notebooks
python scripts/verify_notebooks.py Sudoku --quick

# Extraction structure pour README
python scripts/extract_notebook_skeleton.py MyIA.AI.Notebooks/Sudoku --output markdown

# Validation stack GenAI
python scripts/genai-stack/validate_stack.py
```

## Infrastructure

### Docker - ComfyUI + Qwen

Infrastructure GPU pour la generation d'images :

```bash
cd docker-configurations/services/comfyui-qwen
cp .env.example .env
docker-compose up -d
```

Acces : http://localhost:8188 (authentification Bearer token)

### GradeBookApp

Systeme de notation par evaluations collegiales :

```bash
python GradeBookApp/gradebook.py
```

## Contribution

1. Fork le depot
2. Creer une branche (`git checkout -b feature/nouvelle-fonctionnalite`)
3. Commit (`git commit -m 'Add: nouvelle fonctionnalite'`)
4. Push (`git push origin feature/nouvelle-fonctionnalite`)
5. Ouvrir une Pull Request

### Conventions

- **Pas d'emojis** dans le code et les fichiers generes
- **PEP 8** pour Python, conventions standard pour C#
- **Branches** : `type/nom-court` (ex: `feature/notebook-transformers`)
- **Commits** : `Type: description` (ex: `Add: notebook sur les Transformers`)

## Licence

Ce projet est sous licence MIT - voir [LICENSE](LICENSE).

---

Repository: https://github.com/jsboige/CoursIA
