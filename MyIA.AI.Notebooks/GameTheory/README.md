# Theorie des Jeux - Game Theory

Cette serie de notebooks introduit la **Theorie des Jeux**, combinant **Python** (simulations, algorithmes) et **Lean 4** (formalisations, preuves).

## Structure

### Partie 1 : Fondations et Jeux statiques (Notebooks 1-6)

| # | Notebook | Kernel | Contenu | Duree |
|---|----------|--------|---------|-------|
| 1 | [GameTheory-1-Setup](GameTheory-1-Setup.ipynb) | Python | Installation Nashpy, OpenSpiel, verification | 20 min |
| 2 | [GameTheory-2-NormalForm](GameTheory-2-NormalForm.ipynb) | Python | Matrices de gains, dominance, best response | 45 min |
| 3 | [GameTheory-3-Topology2x2](GameTheory-3-Topology2x2.ipynb) | Python | Classification Robinson-Goforth, table periodique | 55 min |
| 4 | [GameTheory-4-NashEquilibrium](GameTheory-4-NashEquilibrium.ipynb) | Python | Nash pur/mixte, Lemke-Howson, analyse parametrique | 60 min |
| 5 | [GameTheory-5-ZeroSum-Minimax](GameTheory-5-ZeroSum-Minimax.ipynb) | Python | Theoreme minimax, LP primal/dual, Von Neumann | 40 min |
| 6 | [GameTheory-6-EvolutionTrust](GameTheory-6-EvolutionTrust.ipynb) | Python | Tournoi Axelrod, tit-for-tat, replicator dynamics | 65 min |

### Partie 2 : Jeux dynamiques et raisonnement strategique (Notebooks 7-11)

| # | Notebook | Kernel | Contenu | Duree |
|---|----------|--------|---------|-------|
| 7 | [GameTheory-7-ExtensiveForm](GameTheory-7-ExtensiveForm.ipynb) | Python | Arbres de jeu, infosets, strategies | 50 min |
| 8 | [GameTheory-8-BackwardInduction](GameTheory-8-BackwardInduction.ipynb) | Python | Induction arriere, mille-pattes, escalade | 55 min |
| 9 | [GameTheory-9-ForwardInduction-SPE](GameTheory-9-ForwardInduction-SPE.ipynb) | Python | Induction avant, SPE, menaces credibles | 60 min |
| 10 | [GameTheory-10-BayesianGames](GameTheory-10-BayesianGames.ipynb) | Python | Jeux bayesiens, information incomplete | 55 min |
| 11 | [GameTheory-11-ReputationGames](GameTheory-11-ReputationGames.ipynb) | Python | Jeux de reputation, signaling | 50 min |

### Partie 3 : Algorithmes et jeux avances (Notebooks 12-15)

| # | Notebook | Kernel | Contenu | Duree |
|---|----------|--------|---------|-------|
| 12 | [GameTheory-12-ImperfectInfo-CFR](GameTheory-12-ImperfectInfo-CFR.ipynb) | Python | CFR vanilla, MCCFR, Deep CFR | 70 min |
| 13 | [GameTheory-13-DifferentialGames](GameTheory-13-DifferentialGames.ipynb) | Python | Boucle ouverte/fermee, Stackelberg | 60 min |
| 14 | [GameTheory-14-MechanismDesign](GameTheory-14-MechanismDesign.ipynb) | Python | Principe de revelation, VCG, matching | 65 min |
| 15 | [GameTheory-15-MultiAgent-RL](GameTheory-15-MultiAgent-RL.ipynb) | Python | NFSP, PSRO, AlphaZero intro | 55 min |

### Partie 4 : Formalisations Lean 4 (Notebooks 16-19)

| # | Notebook | Kernel | Contenu | Duree |
|---|----------|--------|---------|-------|
| 16 | [GameTheory-16-Lean-Definitions](GameTheory-16-Lean-Definitions.ipynb) | Lean4 | Types Game, Strategy, Nash | 45 min |
| 17 | [GameTheory-17-Lean-NashExistence](GameTheory-17-Lean-NashExistence.ipynb) | Python+Lean | Brouwer, Kakutani, point fixe | 55 min |
| 18 | [GameTheory-18-Lean-CombinatorialGames](GameTheory-18-Lean-CombinatorialGames.ipynb) | Lean4 | PGame mathlib, Nim, Sprague-Grundy | 50 min |
| 19 | [GameTheory-19-Lean-SocialChoice](GameTheory-19-Lean-SocialChoice.ipynb) | Lean4 | Arrow + Sen, impossibilite | 70 min |

**Duree totale** : ~15h30

## Statut de maturite

| # | Notebook | Cellules | Exercices | Solutions | Statut |
|---|----------|----------|-----------|-----------|--------|
| 1 | Setup | ~15 | - | - | **COMPLET** |
| 2 | NormalForm | ~25 | 3 | 3 | **COMPLET** |
| 3 | Topology2x2 | ~30 | 3 | 3 | **COMPLET** |
| 4 | NashEquilibrium | ~35 | 3 | 3 | **COMPLET** |
| 5 | ZeroSum-Minimax | ~25 | 3 | 3 | **COMPLET** |
| 6 | EvolutionTrust | ~40 | 3 | 3 | **COMPLET** |
| 7 | ExtensiveForm | ~30 | 3 | 3 | **COMPLET** |
| 8 | BackwardInduction | ~35 | 3 | 3 | **COMPLET** |
| 9 | ForwardInduction-SPE | ~35 | 3 | 3 | **COMPLET** |
| 10 | BayesianGames | ~30 | 3 | 3 | **COMPLET** |
| 11 | ReputationGames | ~30 | 3 | 3 | **COMPLET** |
| 12 | ImperfectInfo-CFR | ~45 | 3 | 3 | **COMPLET** |
| 13 | DifferentialGames | ~35 | 3 | 3 | **COMPLET** |
| 14 | MechanismDesign | ~40 | 3 | 3 | **COMPLET** |
| 15 | MultiAgent-RL | ~35 | 3 | 3 | **COMPLET** |
| 16 | Lean-Definitions | ~25 | 3 | 3 | **COMPLET** |
| 17 | Lean-NashExistence | ~20 | 3 | 3 | **COMPLET** |
| 18 | Lean-CombinatorialGames | ~25 | 3 | 3 | **COMPLET** |
| 19 | Lean-SocialChoice | ~30 | 3 | 3 | **COMPLET** |

Tous les notebooks incluent :
- Navigation header/footer avec liens
- Plan avec liens ancres
- Tableaux recapitulatifs
- Exercices avec solutions completes

## Prerequisites

- Connaissances de base en logique et mathematiques
- Familiarite avec Python (numpy, matplotlib)
- Pour notebooks 16-19 : Installation Lean 4 (voir serie Lean)
- Pour notebooks 12-15 : APIs optionnelles (OpenAI pour AlphaZero)

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

## Ressources externes

### Theorie des jeux
- [Game Theory (Stanford Encyclopedia)](https://plato.stanford.edu/entries/game-theory/)
- [Evolution of Trust - Nicky Case](https://ncase.me/trust/)
- [Robinson & Goforth - Topology of 2x2 Games](https://www.mdpi.com/2073-4336/6/4/495)

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
├── GameTheory-1-Setup.ipynb ... GameTheory-19-Lean-SocialChoice.ipynb
├── README.md
├── requirements.txt
├── .env.example
├── game_theory_utils.py           # Utilitaires partages
├── trust_simulation/              # Module Evolution of Trust
│   ├── strategies.py              # Tit-for-tat, hawks, doves, etc.
│   ├── tournament.py              # Tournoi Axelrod
│   └── visualization.py           # Animations populations
├── lean_game_defs/                # Fichiers Lean autonomes
│   ├── Basic.lean
│   ├── Nash.lean
│   ├── Combinatorial.lean
│   └── SocialChoice.lean
├── examples/
│   ├── prisoners_dilemma.py
│   ├── topology_2x2_periodic_table.py
│   ├── centipede_game.py
│   ├── kuhn_poker_cfr.py
│   └── arrow_simple.lean
└── tests/
    ├── test_nash_computation.py
    ├── test_strategies.py
    └── test_lean_definitions.py
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
| **CFR** | Counterfactual Regret Minimization - convergence vers Nash |
| **SPE** | Subgame Perfect Equilibrium - Nash credible dans tout sous-jeu |
| **Replicator Dynamics** | Evolution des populations de strategies |
| **Theoreme d'Arrow** | Impossibilite d'agregation parfaite des preferences |

## Licence

Voir la licence du repository principal.
