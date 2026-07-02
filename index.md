# 📚 Index des Notebooks CoursIA

Ce document sert de **portail d'entrée éditorial** vers le contenu pédagogique du dépôt CoursIA. Il ne maintient **plus** de liste de liens vers les notebooks individuels (cause racine historique de rot : chemins à la main non resynchronisés après les restructurations de séries).

> **Catalogue à jour** — Pour l'inventaire exhaustif et toujours synchronisé des 637 notebooks (comptes exacts par série, statut READY/DEMO, maturité, owner), consultez **[`COURSE_CATALOG.generated.md`](COURSE_CATALOG.generated.md)**. Ce catalogue est régénéré automatiquement chaque jour par le workflow `catalog-cron.yml` ; il fait foi sur les chiffres et les statuts.

## 🎯 Trois niveaux de lecture

- **Entrée** (le présent fichier, [`index.md`](index.md)) — portail éditorial : thématiques + parcours. Maintenance manuelle, modifications rares.
- **Vue d'ensemble** ([`README.md`](README.md)) — cartographie rapide du dépôt + parcours d'apprentissage par niveau. Maintenance manuelle, vue pédagogique consolidée.
- **Catalogue à jour** ([`COURSE_CATALOG.generated.md`](COURSE_CATALOG.generated.md)) — inventaire exhaustif : 637 notebooks, statuts, maturités, owners. Maintenance **automatique** (workflow `catalog-cron.yml` quotidien).

Les trois niveaux sont complémentaires : l'`index.md` répond à *« quelles thématiques ? »*, le `README.md` à *« par où commencer ? »*, le catalogue à *« quel notebook précis dans quelle série ? »*.

## 🗂️ Thématiques pédagogiques

Chaque série est introduite par son thème central, ses prérequis et un pointeur vers son README détaillé. Aucun lien direct vers un notebook individuel n'est maintenu ici — pour la liste exhaustive, voir le catalogue auto.

### Algorithmes de recherche et résolution de contraintes

- **[Search](MyIA.AI.Notebooks/Search/README.md)** — BFS, A*, métaheuristiques (recuit simulé, algorithmes génétiques), propagation de contraintes. Point d'entrée idéal pour découvrir les paradigmes de recherche sans prérequis IA. *Débutant.*
- **[Sudoku](MyIA.AI.Notebooks/Sudoku/README.md)** — Résolution multi-paradigme d'un même problème NP-complet (33 notebooks C#/Python) : backtracking, métaheuristiques, CP (OR-Tools, Choco), SMT (Z3), inférence probabiliste. Excellent fil rouge pour comparer les approches sur un terrain commun. *Intermédiaire.*

### Apprentissage automatique

- **[ML](MyIA.AI.Notebooks/ML/README.md)** — Machine Learning avec ML.NET et agents ADK : régression, feature engineering, entraînement, évaluation, TP de prévision de ventes. *Intermédiaire.*
- **[RL](MyIA.AI.Notebooks/RL/README.md)** — Reinforcement Learning (PPO, DQN, Stable Baselines3). *Avancé.*

### Intelligence artificielle générative

- **[GenAI](MyIA.AI.Notebooks/GenAI/README.md)** — IA générative multimodale : Image, Audio, Vidéo, Texte, Semantic Kernel, Vibe Coding. La plus grande série du dépôt. *Intermédiaire à avancé selon les sous-séries ; nécessite des clés API (OpenAI, Anthropic) pour les volets LLM.*

### Raisonnement formel et symbolique

- **[SymbolicAI](MyIA.AI.Notebooks/SymbolicAI/README.md)** — Lean 4 (preuves formelles), Tweety (argumentation), Semantic Web (RDF, OWL), Smart Contracts, Planners, Symbolic Learning. *Avancé.*
- **[Probas](MyIA.AI.Notebooks/Probas/README.md)** — Programmation probabiliste (Infer.NET, NumPyro). *Intermédiaire à avancé.*
- **[GameTheory](MyIA.AI.Notebooks/GameTheory/README.md)** — Théorie des jeux, équilibres de Nash, mechanism design, social choice (Arrow, Sen, Voting) avec ports Lean. *Intermédiaire à avancé.*

### Domaines connexes

- **[IIT](MyIA.AI.Notebooks/IIT/README.md)** — Théorie de l'information intégrée (Tononi) avec PyPhi. *Avancé / recherche.*
- **[QuantConnect](MyIA.AI.Notebooks/QuantConnect/README.md)** — Trading algorithmique : notebooks pédagogiques + stratégies backtestées + pipeline ML. *Intermédiaire à avancé.*
- **[CaseStudies](MyIA.AI.Notebooks/CaseStudies/README.md)** — Études de cas interdisciplinaires.
- **[cross-series](MyIA.AI.Notebooks/cross-series/README.md)** — Applications transverses (matching-cv : data science multi-domaines).

## 🚀 Comment choisir son point d'entrée

Pour un plan d'apprentissage guidé par niveau (débutant, intermédiaire, avancé), consultez la section **[Parcours recommandés](README.md#parcours-recommandés)** du `README.md` racine.

Pour un inventaire technique exhaustif (notebook par notebook, statuts d'exécution, owners), consultez **[`COURSE_CATALOG.generated.md`](COURSE_CATALOG.generated.md)**.

## 📖 Documentation projet

Le répertoire **[docs/](docs/README.md)** centralise les règles de travail, l'infrastructure du dépôt, les procédés récurrents (workflow PR, dispatch d'agents, validation notebook) et les guides d'apprentissage. Cette documentation est destinée aux contributeurs internes du cluster et aux coordinateurs IA.

