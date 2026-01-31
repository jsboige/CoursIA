# Theorie des Jeux - Game Theory

Cette serie de notebooks introduit la **Theorie des Jeux**, combinant **Python** (simulations, algorithmes) et **Lean 4** (formalisations, preuves).

## Structure

**17 notebooks principaux** + **9 side tracks** (b = Lean, c = Python approfondissement) = **26 notebooks**

### Partie 1 : Fondations et Jeux statiques (Notebooks 1-6)

| # | Notebook | Kernel | Contenu | Duree |
|---|----------|--------|---------|-------|
| 1 | [GameTheory-1-Setup](GameTheory-1-Setup.ipynb) | Python | Installation Nashpy, OpenSpiel, verification | 20 min |
| 2 | [GameTheory-2-NormalForm](GameTheory-2-NormalForm.ipynb) | Python | Matrices de gains, dominance, best response | 45 min |
| 2b | [GameTheory-2b-Lean-Definitions](GameTheory-2b-Lean-Definitions.ipynb) | Lean 4 | Formalisation Game2x2, strategies, Nash | 45 min |
| 3 | [GameTheory-3-Topology2x2](GameTheory-3-Topology2x2.ipynb) | Python | Classification Robinson-Goforth, table periodique | 55 min |
| 4 | [GameTheory-4-NashEquilibrium](GameTheory-4-NashEquilibrium.ipynb) | Python | Nash pur/mixte, Lemke-Howson, analyse parametrique | 60 min |
| 4b | [GameTheory-4b-Lean-NashExistence](GameTheory-4b-Lean-NashExistence.ipynb) | Lean 4 | Brouwer, Kakutani, preuve existence Nash | 55 min |
| 4c | [GameTheory-4c-NashExistence-Python](GameTheory-4c-NashExistence-Python.ipynb) | Python | Illustrations numeriques point fixe | 35 min |
| 5 | [GameTheory-5-ZeroSum-Minimax](GameTheory-5-ZeroSum-Minimax.ipynb) | Python | Theoreme minimax, LP primal/dual, Von Neumann | 40 min |
| 6 | [GameTheory-6-EvolutionTrust](GameTheory-6-EvolutionTrust.ipynb) | Python | Tournoi Axelrod, tit-for-tat, replicator dynamics | 65 min |

### Partie 2 : Jeux dynamiques et raisonnement strategique (Notebooks 7-12)

| # | Notebook | Kernel | Contenu | Duree |
|---|----------|--------|---------|-------|
| 7 | [GameTheory-7-ExtensiveForm](GameTheory-7-ExtensiveForm.ipynb) | Python | Arbres de jeu, infosets, strategies | 50 min |
| 8 | [GameTheory-8-CombinatorialGames](GameTheory-8-CombinatorialGames.ipynb) | Python | Positions P/N, Nim, Grundy, Sprague-Grundy | 55 min |
| 8b | [GameTheory-8b-Lean-CombinatorialGames](GameTheory-8b-Lean-CombinatorialGames.ipynb) | Lean 4 | PGame mathlib, Nim formel | 50 min |
| 8c | [GameTheory-8c-CombinatorialGames-Python](GameTheory-8c-CombinatorialGames-Python.ipynb) | Python | Approfondissement jeux combinatoires | 40 min |
| 9 | [GameTheory-9-BackwardInduction](GameTheory-9-BackwardInduction.ipynb) | Python | Induction arriere, mille-pattes, escalade | 55 min |
| 10 | [GameTheory-10-ForwardInduction-SPE](GameTheory-10-ForwardInduction-SPE.ipynb) | Python | Induction avant, SPE, menaces credibles | 60 min |
| 11 | [GameTheory-11-BayesianGames](GameTheory-11-BayesianGames.ipynb) | Python | Jeux bayesiens, information incomplete | 55 min |
| 12 | [GameTheory-12-ReputationGames](GameTheory-12-ReputationGames.ipynb) | Python | Jeux de reputation, signaling | 50 min |

### Partie 3 : Algorithmes et applications avancees (Notebooks 13-17)

| # | Notebook | Kernel | Contenu | Duree |
|---|----------|--------|---------|-------|
| 13 | [GameTheory-13-ImperfectInfo-CFR](GameTheory-13-ImperfectInfo-CFR.ipynb) | Python | CFR vanilla, MCCFR, Deep CFR | 70 min |
| 14 | [GameTheory-14-DifferentialGames](GameTheory-14-DifferentialGames.ipynb) | Python | Boucle ouverte/fermee, Stackelberg | 60 min |
| 15 | [GameTheory-15-CooperativeGames](GameTheory-15-CooperativeGames.ipynb) | Python | Shapley, Core, Bondareva-Shapley | 65 min |
| 15b | [GameTheory-15b-Lean-CooperativeGames](GameTheory-15b-Lean-CooperativeGames.ipynb) | Lean 4 | Axiomes Shapley formels, Core | 55 min |
| 15c | [GameTheory-15c-CooperativeGames-Python](GameTheory-15c-CooperativeGames-Python.ipynb) | Python | Exemples avances (Glove Game, politique) | 40 min |
| 16 | [GameTheory-16-MechanismDesign](GameTheory-16-MechanismDesign.ipynb) | Python | Principe de revelation, VCG, matching | 65 min |
| 16b | [GameTheory-16b-Lean-SocialChoice](GameTheory-16b-Lean-SocialChoice.ipynb) | Lean 4 | Arrow, Sen, Electeur Median | 70 min |
| 16c | [GameTheory-16c-SocialChoice-Python](GameTheory-16c-SocialChoice-Python.ipynb) | Python | Condorcet, simulations, modele Downs | 45 min |
| 17 | [GameTheory-17-MultiAgent-RL](GameTheory-17-MultiAgent-RL.ipynb) | Python | NFSP, PSRO, AlphaZero intro | 55 min |

**Duree totale** : ~18h30

## Navigation et Side Tracks

Les **side tracks** approfondissent les concepts du notebook principal :

| Track | Type | Description |
|-------|------|-------------|
| **b** | Lean 4 | Formalisation mathematique, preuves formelles |
| **c** | Python | Approfondissement, exemples avances, visualisations |

**Organisation** :
- Chaque notebook principal inclut des liens vers ses side tracks
- Les side tracks sont optionnels et peuvent etre etudies independamment
- Progression recommandee : notebook principal, puis side track b (formalisation), puis c (applications)

## Statut de maturite

| # | Notebook | Cellules | Exercices | Statut |
|---|----------|----------|-----------|--------|
| 1 | Setup | ~15 | - | **COMPLET** |
| 2 | NormalForm | ~25 | 3 | **COMPLET** |
| 2b | Lean-Definitions | ~25 | 3 | **COMPLET** |
| 3 | Topology2x2 | ~30 | 3 | **COMPLET** |
| 4 | NashEquilibrium | ~35 | 3 | **COMPLET** |
| 4b | Lean-NashExistence | ~20 | 3 | **COMPLET** |
| 4c | NashExistence-Python | ~20 | 2 | **COMPLET** |
| 5 | ZeroSum-Minimax | ~25 | 3 | **COMPLET** |
| 6 | EvolutionTrust | ~40 | 3 | **COMPLET** |
| 7 | ExtensiveForm | ~30 | 3 | **COMPLET** |
| 8 | CombinatorialGames | ~17 | 3 | **NOUVEAU** |
| 8b | Lean-CombinatorialGames | ~25 | 3 | **COMPLET** |
| 8c | CombinatorialGames-Python | ~25 | 3 | **COMPLET** |
| 9 | BackwardInduction | ~35 | 3 | **COMPLET** |
| 10 | ForwardInduction-SPE | ~35 | 3 | **COMPLET** |
| 11 | BayesianGames | ~30 | 3 | **COMPLET** |
| 12 | ReputationGames | ~30 | 3 | **COMPLET** |
| 13 | ImperfectInfo-CFR | ~45 | 3 | **COMPLET** |
| 14 | DifferentialGames | ~35 | 3 | **COMPLET** |
| 15 | CooperativeGames | ~40 | 3 | **COMPLET** |
| 15b | Lean-CooperativeGames | ~30 | 3 | **COMPLET** |
| 15c | CooperativeGames-Python | ~25 | 3 | **COMPLET** |
| 16 | MechanismDesign | ~40 | 3 | **COMPLET** |
| 16b | Lean-SocialChoice | ~30 | 3 | **COMPLET** |
| 16c | SocialChoice-Python | ~25 | 3 | **COMPLET** |
| 17 | MultiAgent-RL | ~35 | 3 | **COMPLET** |

Tous les notebooks incluent :
- Navigation header/footer avec liens
- Plan avec liens ancres
- Tableaux recapitulatifs
- Exercices avec solutions completes

## Prerequisites

- Connaissances de base en logique et mathematiques
- Familiarite avec Python (numpy, matplotlib)
- Pour notebooks Lean (b) : Installation Lean 4 + kernel WSL (voir serie Lean)
- Pour notebooks 13-17 : APIs optionnelles (OpenAI pour AlphaZero)

## Installation

### 1. Environnement Python

```bash
# Creer un environnement conda
conda create -n game-theory python=3.10
conda activate game-theory

# Installer les dependances
pip install -r requirements.txt
```

### 2. Verification

```bash
python -c "import nashpy; import pyspiel; print('OK')"
```

### 3. Configuration API (optionnel)

```bash
cp .env.example .env
# Editer .env et ajouter les cles API si necessaire
```

### 4. Kernel Lean 4 (pour side tracks b)

Voir les instructions dans [Lean-1-Setup](../SymbolicAI/Lean/Lean-1-Setup.ipynb) pour l'installation du kernel Lean 4 WSL.

## Ressources externes

### Theorie des jeux
- [Game Theory (Stanford Encyclopedia)](https://plato.stanford.edu/entries/game-theory/)
- [Evolution of Trust - Nicky Case](https://ncase.me/trust/)
- [Robinson & Goforth - Topology of 2x2 Games](https://www.mdpi.com/2073-4336/6/4/495)

### Jeux combinatoires
- [Winning Ways for Your Mathematical Plays - Conway, Berlekamp, Guy](https://www.akpeters.com/WinningWays/)
- [Lessons in Play - Albert, Nowakowski, Wolfe](https://www.routledge.com/Lessons-in-Play/Albert-Nowakowski-Wolfe/p/book/9781568812779)
- [Sprague-Grundy Theorem (Wikipedia)](https://en.wikipedia.org/wiki/Sprague%E2%80%93Grundy_theorem)

### Bibliotheques Python
- [Nashpy Documentation](https://nashpy.readthedocs.io/)
- [OpenSpiel Documentation](https://openspiel.readthedocs.io/)
- [OpenSpiel Algorithms](https://openspiel.readthedocs.io/en/latest/algorithms.html)

### Formalisations Lean
- [math-xmum/Brouwer](https://github.com/math-xmum/Brouwer) - Nash existence
- [MixedMatched/formalizing-game-theory](https://github.com/MixedMatched/formalizing-game-theory)
- [mathlib4 PGame](https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/PGame/Basic.html)
- [asouther4/lean-social-choice](https://github.com/asouther4/lean-social-choice) - Arrow (Lean 3)

## Structure des fichiers

```
GameTheory/
├── GameTheory-1-Setup.ipynb ... GameTheory-17-MultiAgent-RL.ipynb  # 17 principaux
├── GameTheory-2b-Lean-Definitions.ipynb                            # Side tracks b (Lean)
├── GameTheory-4b-Lean-NashExistence.ipynb
├── GameTheory-8b-Lean-CombinatorialGames.ipynb
├── GameTheory-15b-Lean-CooperativeGames.ipynb
├── GameTheory-16b-Lean-SocialChoice.ipynb
├── GameTheory-4c-NashExistence-Python.ipynb                        # Side tracks c (Python)
├── GameTheory-8c-CombinatorialGames-Python.ipynb
├── GameTheory-15c-CooperativeGames-Python.ipynb
├── GameTheory-16c-SocialChoice-Python.ipynb
├── README.md
├── requirements.txt
├── .env.example
├── game_theory_utils.py           # Utilitaires partages
├── cooperative_games/             # Module jeux cooperatifs
│   ├── __init__.py
│   ├── shapley.py                 # Valeur de Shapley
│   ├── core.py                    # Core, Bondareva-Shapley
│   └── voting.py                  # Jeux de vote
├── trust_simulation/              # Module Evolution of Trust
│   ├── strategies.py              # Tit-for-tat, hawks, doves, etc.
│   ├── tournament.py              # Tournoi Axelrod
│   └── visualization.py           # Animations populations
├── cooperative_games_lean/        # Projet Lake pour Lean cooperatif
├── social_choice_lean/            # Projet Lake pour Lean choix social
├── examples/
│   ├── prisoners_dilemma.py
│   ├── topology_2x2_periodic_table.py
│   ├── nim_game.py
│   ├── kuhn_poker_cfr.py
│   ├── vcg_auction.py
│   └── arrow_simple.lean
└── tests/
    ├── test_nash_computation.py
    ├── test_strategies.py
    ├── test_combinatorial.py
    └── test_lean_definitions.py
```

## Tests

```bash
# Executer tous les tests unitaires
cd MyIA.AI.Notebooks/GameTheory
python -m pytest tests/ -v

# Executer les exemples Python
python examples/prisoners_dilemma.py
python examples/kuhn_poker_cfr.py
python examples/vcg_auction.py
```

## Validation

```bash
# Verifier la structure des notebooks
python scripts/verify_notebooks.py MyIA.AI.Notebooks/GameTheory --quick

# Execution complete (mode batch)
BATCH_MODE=true python scripts/verify_notebooks.py MyIA.AI.Notebooks/GameTheory
```

## Concepts cles

| Concept | Description |
|---------|-------------|
| **Equilibre de Nash** | Profil de strategies ou aucun joueur ne gagne a devier unilateralement |
| **Minimax** | Strategie qui minimise la perte maximale (jeux a somme nulle) |
| **Positions P/N** | Positions perdantes (Previous) et gagnantes (Next) en jeux combinatoires |
| **Sprague-Grundy** | Theoreme unifiant l'analyse des jeux combinatoires impartiaux |
| **CFR** | Counterfactual Regret Minimization - convergence vers Nash |
| **SPE** | Subgame Perfect Equilibrium - Nash credible dans tout sous-jeu |
| **Valeur de Shapley** | Repartition equitable des gains en jeu cooperatif |
| **Core** | Ensemble des allocations stables en jeu cooperatif |
| **Theoreme d'Arrow** | Impossibilite d'agregation parfaite des preferences |

## Licence

Voir la licence du repository principal.
