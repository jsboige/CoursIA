# Guide de Navigation CoursIA — Carte du Visiteur

**Public cible** : etudiant (L3-M2), ingenieur, chercheur, ou visiteur curieux decouvrant le depot pour la premiere fois.

**Objet** : Ce guide vous aide a choisir votre parcours parmi 511 notebooks repartis sur 11 domaines. Plutot qu'une longue liste, il propose des **traversees thematiques** qui relient les series entre elles.

---

## Comment lire ce depot

Chaque dossier `MyIA.AI.Notebooks/<Domaine>/` contient :

- **Un README** avec la table des notebooks, les prerequis, la duree estimee et les liens vers les autres series.
- **Des notebooks Jupyter** (`.ipynb`) executables de bout en bout, rediges en francais, avec des exemples resolus et des exercices a completer.
- **Un marqueur `CATALOG-STATUS`** en tete du README qui donne le nombre de notebooks et leur maturite (`PRODUCTION`, `BETA`, `ALPHA`).

Les notebooks utilisent principalement **Python 3.10+** (PyTorch, OR-Tools, PyMC, OpenSpiel) et accessoirement **C# / .NET 9.0** (Infer.NET, ML.NET, GeneticSharp). Les notebooks Lean 4 s'executent via un kernel WSL dedie.

---

## Les 4 parcours

### Parcours A : Fondements algorithmiques (~50h)

**Pour qui** : etudiants en informatique (L3-M2), candidats a des entretiens techniques, ou toute personne voulant comprendre les algorithmes classiques de l'IA.

**Fil conducteur** : comment explorer un espace de solutions, comment raisonner sur l'incertitude, comment formaliser et prouver.

```text
Search (46 nb)           GameTheory (25 nb)       SymbolicAI (104 nb)
  Search-1 StateSpace      GT-1 Setup                Lean-1 Setup
  Search-2 Uninformed      GT-2 Jeux Matriciels      Lean-2 Tactics
  Search-3 Informed/A*     GT-3 Jeux Extensifs       Tweety-1 Propositional
  Search-6 Adversarial     GT-4 Jeux Repetes         Planners-1 Introduction
  Search-7 MCTS            GT-6 Nash/Equilibres      Planners-4 Fast-Downward
  CSP-1 Fundamentals       GT-10 SPE                 Lean-7 LLM Integration
  CSP-2 Consistency        GT-13 CFR                 Lean-11 Arrow
  CSP-4 Scheduling                                   Lean-13 Grothendieck
```

**Entree recommandee** : [Search-1-StateSpace](../MyIA.AI.Notebooks/Search/Part1-Foundations/Search-1-StateSpace.ipynb) formalise les espaces d'etats, le concept fondateur commun a toute la serie.

**Points de passage** :
1. **Search Part 1** (11 nb, ~12h) : BFS, DFS, A*, recherche locale, algorithmes genetiques, Minimax, MCTS. Le coeur algorithmique.
2. **Search Part 2 — CSP** (9 nb, ~9h) : changement de paradigme — au lieu d'explorer, on reduit les domaines par propagation. AC-3,ordonnancement,optimisation.
3. **GameTheory** (25 nb) : la recherche adversariale (Minimax, MCTS) rencontrela theorie des jeux (Nash, equilibres bayesiens, CFR).
4. **SymbolicAI — Lean** (16 nb) : les memes concepts de preuve et de recherche, formalises en theoreme. Arrow, Conway, Kochen-Specker portes en Lean 4.

**Ponts inter-series** :
- Search-6 (Adversarial) → GT-6 (Nash) : Minimax est un cas particulier de l'equilibre de Nash dans les jeux a somme nulle.
- CSP-6 (Hybridation) → Planners-10 (LLM Planning) : les LLMs comme heuristiques pour la resolution CSP.
- Search-8 (Dancing Links) → Sudoku-5 (DLX) : application directe de l'algorithme X.

---

### Parcours B : IA Generative pratique (~40h)

**Pour qui** : createurs de contenu, developpeurs voulant integrer des modeles generatifs, etudiants en ML applique.

**Fil conducteur** : generer du contenu (images, audio, texte, video) avec des modeles locaux et cloud, puis orchestrer des pipelines complexes.

```text
GenAI (120 nb)
  00-Environment/Setup
  Image/  (SDXL, Flux, Qwen-VL, ComfyUI)
  Audio/  (Whisper STT, Kokoro TTS, FishAudio S2-Pro, MusicGen)
  Texte/  (LLMs, RAG, Reasoning, Structured Outputs)
  Video/  (Generation, animation)
  SemanticKernel/  (Orchestration .NET)
  FineTuning/  (LoRA, adapters)
  Vibe-Coding/  (Claude Code + Roo-Code)
```

**Entree recommandee** : [GenAI/00-Environment/](../MyIA.AI.Notebooks/GenAI/00-Environment/) configure l'infrastructure Docker (ComfyUI, Qwen, vLLM). Les notebooks Image et Audio fonctionnent ensuite sans GPU cloud.

**Points de passage** :
1. **Image** (~20 nb) : generation SDXL/Flux, editing, inpainting avec ComfyUI sur GPU locale.
2. **Audio** (~25 nb) : STT (Whisper), TTS (Kokoro, FishAudio S2-Pro), cloning vocal, pipeline audiobook complet.
3. **Texte** (~15 nb) : LLMs, RAG, code interpreteur, structured outputs, quantization.
4. **Orchestration** (~15 nb) : Semantic Kernel (C#), agentic workflows, multi-model chaining.
5. **Fine-Tuning** (~10 nb) : LoRA, adapters, entra&#94;nement sur donnees custom.

**Ponts inter-series** :
- GenAI/Texte + Search/CSP-6 (LLM+CSP) : les LLMs comme solveurs d'optimisation.
- GenAI/Video + ML (pipeline training) : les modeles de generation video comme cas d'usage ML.
- Vibe-Coding + SymbolicAI/Lean-7 (LLM Integration) : comment les LLMs interagissent avec les outils formels.

---

### Parcours C : Trading algorithmique et ML financier (~60h)

**Pour qui** : etudiants en finance quantitative, data scientists, ingeenieurs interesses par le ML applique.

**Fil conducteur** : construire, backtester et deployer des strategies de trading algorithmique avec un pipeline ML complet.

```text
QuantConnect (101 nb)        Search/ML (metaheuristiques)
  Python/QC-Py-01 a 10        App-10 Portfolio
  projects/ (49 strategies)    App-13 TSP
  ML-Training-Pipeline/        Search-9 LP
```

**Entree recommandee** : [QC-Py-01](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-01-Introduction-Backtesting.ipynb) introduit le backtesting sur la plateforme QuantConnect.

**Points de passage** :
1. **Cours QC Python** (10 nb) : fondements du backtesting, indicateurs, gestion de portefeuille.
2. **Strategies** (49 projets) : GARCH, Kelly, ensemble, momentum, mean-reversion — chacune backtestee.
3. **ML Training Pipeline** : entrainement thermal-safe sur GPU, walk-forward validation, multi-seed.
4. **Optimisation** : les metaheuristiques de Search (SA, GA, PSO) optimisent les hyperparametres.

**Ponts inter-series** :
- QuantConnect + Search (metaheuristiques) : optimisation de portefeuille par algorithmes genetiques.
- QuantConnect + Probas (PyMC) : modelisation bayesienne de la volatilite.
- QuantConnect + RL (PPO, SAC) : agents RL pour le trading.

---

### Parcours D : Preuve formelle et IA symbolique (~40h)

**Pour qui** : mathematiciens, logiciens, etudiants en informatique theorique, personnes interessees par la verification formelle.

**Fil conducteur** : prouver des theoremes classiques (Arrow, Conway, Kochen-Specker) en Lean 4, utiliser des solveurs (Z3, OR-Tools), et explorer les logiques non-classiques.

```text
SymbolicAI (104 nb)
  Lean/  (16 notebooks, theoremes portes)
  Tweety/  (logiques, argumentation)
  Planners/  (PDDL, Fast-Downward, OR-Tools)
  SmartContracts/  (Solidity, verification formelle)
  SemanticWeb/  (RDF, SPARQL, OWL)
  SymbolicLearning/  (ILP, NeuroSymbolic)
```

**Entree recommandee** : [Lean-1-Setup](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-1-Setup.ipynb) configure l'environnement Lean 4 (kernel WSL). Puis [Tweety-1](../MyIA.AI.Notebooks/SymbolicAI/Tweety/01-Propositional-Logic/) pour les fondamentaux logiques.

**Points de passage** :
1. **Lean 4** (16 nb) : de la tactique basique aux theoremes portes (Arrow, Sen, Shapley pour les choix social ; Conway, Kochen-Specker, Free Will pour les mathematiques).
2. **Tweety** (13 nb) : logique propositionnelle, premier ordre, modale, argumentation, Markov Logic Networks.
3. **Planners** (13 nb) : PDDL, Fast-Downward, planification temporelle et hierarchique, LLM+Planning.
4. **SmartContracts** (18 nb) : Solidity, verification formelle, DeFi, oracle manipulation.

**Ponts inter-series** :
- Lean/GameTheory : les theoremes d'Arrow et Shapley sont portes en Lean 4 (Lean-11 a Lean-16).
- Planners/Search : PDDL etend les CSP vers la planification d'actions.
- SmartContracts/Search : la verification de smart contracts utilise les solveurs SMT (Z3).

---

## Carte rapide des series

```text
                    Fondements algorithmiques
                   /          |              \
          Search (46)   GameTheory (25)   SymbolicAI (104)
           |    \           |                   |
           |   CSP (9)     Minimax/MCTS      Lean 4 (16)
           |     |          |                   |
           v     v          v                   v
        Sudoku (32)    RL (7)            Planners (13)
           |
        .NET C#
           |
        Probas (43) --- Infer.NET + PyMC
           |
        ML (27) --- ML.NET + Python

    GenAI (120) --- Images/Audio/Video/Texte/FineTuning
           |
    QuantConnect (101) --- Trading + ML Pipeline
```

## Table de correspondance par technologie

| Technologie | Series concernees |
|-------------|-------------------|
| **Python** | Toutes les series (langage principal) |
| **C# / .NET 9** | Sudoku, Probas/Infer, ML, SmartContracts, GenAI/SemanticKernel |
| **Lean 4** | SymbolicAI/Lean (kernel WSL dedie) |
| **OR-Tools CP-SAT** | Search/CSP, Planners |
| **PyTorch** | GenAI/FineTuning, RL, ML |
| **PyMC** | Probas/PyMC |
| **Infer.NET** | Probas/Infer |
| **OpenSpiel** | GameTheory |
| **Semantic Kernel** | GenAI/SemanticKernel, SymbolicAI/Lean-7 |
| **Solidity** | SmartContracts |
| **Z3** | Search-10 (automates symboliques), SymbolicAI |
| **Stable-Baselines3** | RL |
| **QuantConnect LEAN** | QuantConnect |
| **ComfyUI / Docker** | GenAI (GPU requise) |

## Par duree estimee

| Duree | Parcours | Nb notebooks |
|-------|----------|-------------|
| 10-15h | Decouverte Search + Sudoku | ~20 |
| 20-30h | GenAI Image + Audio | ~30 |
| 30-40h | Trading QC debutant | ~20 |
| 40-50h | Fondements complets | ~80 |
| 60-80h | Parcours A ou C complet | ~100 |
| 120h+ | Expert multi-domaines | 200+ |

---

## Liens rapides

| Serie | README | Nombre | Maturite dominante |
|-------|--------|--------|--------------------|
| [GenAI](../MyIA.AI.Notebooks/GenAI/README.md) | Images, Audio, Video, Texte, LLMs | 120 | PRODUCTION |
| [QuantConnect](../MyIA.AI.Notebooks/QuantConnect/README.md) | Trading algorithmique, backtests | 101 | PRODUCTION |
| [SymbolicAI](../MyIA.AI.Notebooks/SymbolicAI/README.md) | Lean 4, Tweety, Planners, SmartContracts | 104 | PRODUCTION |
| [Search](../MyIA.AI.Notebooks/Search/README.md) | Algorithmes de recherche, CSP | 46 | PRODUCTION |
| [Probas](../MyIA.AI.Notebooks/Probas/README.md) | Infer.NET + PyMC | 43 | PRODUCTION |
| [Sudoku](../MyIA.AI.Notebooks/Sudoku/README.md) | Resolution de contraintes .NET | 32 | PRODUCTION |
| [GameTheory](../MyIA.AI.Notebooks/GameTheory/README.md) | Theorie des jeux, choix social | 25 | PRODUCTION |
| [ML](../MyIA.AI.Notebooks/ML/README.md) | ML.NET + Python | 27 | PRODUCTION |
| [RL](../MyIA.AI.Notebooks/RL/README.md) | Reinforcement Learning | 7 | PRODUCTION |
| [CaseStudies](../MyIA.AI.Notebooks/CaseStudies/README.md) | Etudes de cas | 4 | BETA |
| [IIT](../MyIA.AI.Notebooks/IIT/README.md) | Integrated Information Theory | 2 | ALPHA |

---

**Navigation** : [CLAUDE.md](../CLAUDE.md) | [docs/README.md](README.md) | [Index notebooks](../MyIA.AI.Notebooks/README.md)
