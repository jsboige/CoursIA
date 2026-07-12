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

**Entree recommandee** : [Search-1-StateSpace](../MyIA.AI.Notebooks/Search/Part1-Foundations/Search-1-StateSpace.ipynb) formalise les espaces d'etats, le concept fondateur commun a toute la serie.

**Etapes cles** : Search (BFS, DFS, A*, MCTS) → CSP (propagation, ordonnancement) → GameTheory (Minimax, Nash, CFR) → Lean (preuves formelles). Les series Lean et SymbolicAI sont partagees avec le **Parcours D** ; ici on les lit comme l'aboutissement de la recherche algorithmique (la preuve comme exploration exhaustive dans l'espace des tactiques).

**Ponts inter-series** : Search-6 (Adversarial) → GT-6 (Nash) : Minimax est un cas particulier de l'equilibre de Nash. CSP-6 (Hybridation) → Planners-10 (LLM Planning) : les LLMs comme heuristiques pour la resolution CSP.

---

### Parcours B : IA Generative pratique (~40h)

**Pour qui** : createurs de contenu, developpeurs voulant integrer des modeles generatifs, etudiants en ML applique.

**Fil conducteur** : generer du contenu (images, audio, texte, video) avec des modeles locaux et cloud, puis orchestrer des pipelines complexes.

**Entree recommandee** : [GenAI/00-GenAI-Environment/](../MyIA.AI.Notebooks/GenAI/00-GenAI-Environment/) configure l'infrastructure Docker (ComfyUI, Qwen, vLLM).

**Etapes cles** : Image (SDXL, Flux, ComfyUI) → Audio (Whisper, Kokoro, FishAudio) → Texte (LLMs, RAG, Reasoning) → Orchestration (Semantic Kernel C#) → Fine-Tuning (LoRA).

**Ponts inter-series** : GenAI/Texte + Search/CSP-6 (LLM+CSP) : les LLMs comme solveurs d'optimisation. Vibe-Coding + SymbolicAI/Lean-7 (LLM Integration) : comment les LLMs interagissent avec les outils formels.

---

### Parcours C : Trading algorithmique et ML financier (~60h)

**Pour qui** : etudiants en finance quantitative, data scientists, ingenieurs interesses par le ML applique.

**Fil conducteur** : construire, backtester et deployer des strategies de trading algorithmique avec un pipeline ML complet.

**Entree recommandee** : [QC-Py-01](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-01-Setup.ipynb) introduit le backtesting sur la plateforme QuantConnect.

**Etapes cles** : Cours QC Python (10 nb, backtesting) → Strategies (49 projets, GARCH, Kelly, momentum) → ML Training Pipeline (GPU, walk-forward) → Optimisation (metaheuristiques de Search).

**Ponts inter-series** : QuantConnect + Search (metaheuristiques) : optimisation de portefeuille par algorithmes genetiques. QuantConnect + Probas (PyMC) : modelisation bayesienne de la volatilite. QuantConnect + RL (PPO, SAC) : agents RL pour le trading.

---

### Parcours D : Preuve formelle et IA symbolique (~40h)

**Pour qui** : mathematiciens, logiciens, etudiants en informatique theorique, personnes interessees par la verification formelle.

**Fil conducteur** : prouver des theoremes classiques (Arrow, Conway, Kochen-Specker) en Lean 4, utiliser des solveurs (Z3, OR-Tools), et explorer les logiques non-classiques.

**Entree recommandee** : [Lean-1-Setup](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-1-Setup.ipynb) configure l'environnement Lean 4 (kernel WSL). Puis [Tweety-2](../MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-2-Basic-Logics.ipynb) pour les fondamentaux logiques.

**Etapes cles** : Lean 4 (16 nb, theoremes portes) → Tweety (logiques, argumentation) → Planners (PDDL, Fast-Downward) → SmartContracts (Solidity, verification formelle). Les series Lean et SymbolicAI sont partagees avec le **Parcours A** ; ici on les lit comme le coeur de la verification formelle (la preuve comme garantie, pas comme exploration).

**Ponts inter-series** : GameTheory/social_choice_lean (Arrow/Sen en Lean certifie) ↔ GameTheory/SocialChoice (Python pedagogique) : double traitement. Planners/Search : PDDL etend les CSP vers la planification d'actions.

---

## Ponts conceptuels inter-series

Au-dela des parcours lineaires, le depot tisse des liens profonds entre ses series. La cle de lecture [La mer qui monte](../grothendieckian-lens.md) developpe cette vision d'ensemble ; les ponts ci-dessous en donnent les passages les plus directs.

### La dualite simulation / preuve

Un meme concept est d'abord **illustre numeriquement** (on simule, on calcule, on genere), puis — quand c'est possible — **formalise et verifie mecaniquement** (on prouve). Ce double mouvement est le fil conducteur le plus continu du depot.

| Concept | Versant *simulation* (faire / calculer) | Versant *preuve* (formaliser / verifier) |
|---------|-----------------------------------------|------------------------------------------|
| **Choix social** | [SocialChoice/03-Voting-Methods](../MyIA.AI.Notebooks/GameTheory/SocialChoice/03-Voting-Methods.ipynb) (agreger des votes) | [social_choice_lean](../MyIA.AI.Notebooks/GameTheory/social_choice_lean/) — Arrow/Sen/Voting certifies (0 sorry) |
| **Contraintes** | [CSP-1-Fundamentals](../MyIA.AI.Notebooks/Search/Part2-CSP/CSP-1-Fundamentals.ipynb) (resoudre par propagation) | [SocialChoice/04-SAT-Z3](../MyIA.AI.Notebooks/GameTheory/SocialChoice/04-Computational-Aggregation-SAT-Z3.ipynb) (encoder + verifier via solveur SMT) |
| **Incertitude** | [PyMC-1-Setup](../MyIA.AI.Notebooks/Probas/PyMC/PyMC-1-Setup.ipynb) (echantillonnage MCMC) | [Infer-101](../MyIA.AI.Notebooks/Probas/Infer-101.ipynb) (inference exacte par message-passing) |
| **Smart contracts** | [SC-12-Foundry-Testing](../MyIA.AI.Notebooks/SymbolicAI/SmartContracts/03-Foundry-Testing/SC-12-Foundry-Testing.ipynb), [SC-13-Fuzz-Invariants](../MyIA.AI.Notebooks/SymbolicAI/SmartContracts/03-Foundry-Testing/SC-13-Fuzz-Invariants.ipynb) (tester / fuzzer) | [SC-14-Formal-Verification](../MyIA.AI.Notebooks/SymbolicAI/SmartContracts/03-Foundry-Testing/SC-14-Formal-Verification.ipynb) (verification formelle) |
| **Mathematiques** | [Lean-16b Game of Life](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-16b-Conway-Game-of-Life-Lean.ipynb) (automate cellulaire) | [Lean-15 Grothendieck](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-15-Grothendieck-Tribute.ipynb), [Lean-13 Kochen-Specker](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-13-Kochen-Specker.ipynb), [Lean-16f Free Will](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-16f-Conway-Free-Will-Theorem.ipynb) |

**Comment s'en servir** : pour *ancrer* un concept abstrait, commencez par le versant simulation (intuition, visualisation), puis passez au versant preuve (rigueur, garanties). Les series purement generatives (GenAI, QuantConnect) se situent au bout simulation ; les series Lean sont au bout preuve. Leur point de jonction est la ligne du tableau.

### L'IA comme changement de representation

Plusieurs series du depot pratiquent le meme geste : prendre la sortie incertaine d'un modele et la re-representer dans un cadre verifiable. Ce geste — trouver la representation ou le probleme se dissout — traverse le depot de bout en bout :

- **SymbolicLearning/SL-7** : un LLM reboucle sur une verification logique.
- **Tweety + Argument_Analysis** : le langage naturel traduit en semantiques formelles interrogeables.
- **Planners-10** : une intention en mots naturels confrontee a un solveur qui tranche.
- **SC-11** : un contrat assiste par LLM relu a l'aune de sa verification formelle.
- **Search/CSP** : un meme Sudoku resolu par recherche, par contraintes, ou par SAT — trois representations, trois couts.

Ce mouvement est developpe dans la cle de lecture [La mer qui monte](../grothendieckian-lens.md) : l'IA digne de confiance sera celle qui sait trouver le cadre ou l'affirmation devient controlable.

### Du local au global

Un second fil relie les series : une regle purement locale engendre une structure globale. La regle B3/S23 d'une cellule engendre la Turing-complete. Des strategies individuelles se recollent en un equilibre de Nash ([GameTheory-4](../MyIA.AI.Notebooks/GameTheory/GameTheory-4-NashEquilibrium.ipynb)). Des preferences individuelles se heurtent a l'impossibilite d'Arrow ([social_choice_lean](../MyIA.AI.Notebooks/GameTheory/social_choice_lean/)). Une action PDDL composee avec ses semblables devient un plan. Une transition d'etat de contrat devient une obligation irreversible. Ce geste du recollement — litteral chez Grothendieck (faisceaux, topologies), metaphorique partout ailleurs — est le principe organisateur de la theorie des jeux, de la planification, des smart contracts, et de la theorie du choix social dans le depot.

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

**Navigation** : [CLAUDE.md](../CLAUDE.md) | [docs/README.md](README.md) | [Index notebooks](../MyIA.AI.Notebooks/README.md) | [La mer qui monte](../grothendieckian-lens.md)
