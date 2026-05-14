# Theorie des Jeux - Game Theory

<!-- CATALOG-STATUS
series: GameTheory
pedagogical_count: 27
breakdown: =27
maturity: BETA=15, ALPHA=7, DRAFT=4, PRODUCTION=1
-->

La théorie des jeux est le langage mathématique de la stratégie. Elle modélise les situations où des agents rationnels prennent des décisions dont le résultat dépend des choix des autres : enchères, négociations commerciales, élections, poker, guerre commerciale, allocation de ressources. Cette dualité entre coopération et compétition est omniprésente en économie, en sciences politiques et en informatique (mécanismes de vote, smart contracts, réseaux). Le prix Nobel d'économie a été décerné à des théoriciens des jeux à sept reprises entre 1994 et 2020 — c'est un domaine vivant et influent.

Cette série vous forme sur deux axes complémentaires. Le premier est **pratique** : simuler des jeux avec Nashpy et OpenSpiel, calculer des équilibres de Nash, organiser des tournois itératifs (dilemme du prisonnier, Axelrod), et explorer les algorithmes modernes (CFR, Deep CFR). Le second est **formel** : prouver des résultats en Lean 4 — existence de Nash (Brouwer/Kakutani), théorème d'Arrow, valeur de Shapley. À la fin, vous maîtriserez aussi bien la théorie des jeux coopératifs (Shapley, Core) que non-coopératifs (Nash, SPE), et vous saurez formaliser ces résultats dans un assistant de preuve.

**À qui s'adresse cette série** : étudiants en économie, informatique et mathématiques appliquées. Les notebooks Python (principaux + side tracks c/d/f) utilisent Nashpy, OpenSpiel et Z3. Les side tracks Lean (b/e) requièrent WSL + elan. Aucun prérequis en théorie des jeux : les concepts sont introduits progressivement depuis les matrices de gains. Une familiarité avec l'algèbre linéaire et les probabilités de base est utile.

## Parcours d'apprentissage

### Phase 1 : Jeux statiques et equilibres (Notebooks 1-6, ~5h)

Le parcours commence par le setup (Nashpy, OpenSpiel) et les jeux sous forme normale (matrices de gains, dominance, meilleure réponse). Le notebook 3 (Topology2x2) classifie les jeux 2x2 selon la table périodique de Robinson-Goforth, une perspective géométrique unique. Les notebooks 4-4b-4c plongent dans l'équilibre de Nash : calcul en stratégies pures et mixtes, algorithme de Lemke-Howson, et preuve formelle d'existence via Brouwer et Kakutani en Lean 4. Le notebook 5 (ZeroSum) démontre le théorème minimax et la dualité LP. Le notebook 6 (EvolutionTrust) montre comment la coopération émerge dans les tournois itérés (Axelrod, replicator dynamics). À l'issue de cette phase, vous comprenez les trois piliers : Nash, minimax, et évolution.

### Phase 2 : Jeux dynamiques et information incomplete (Notebooks 7-12, ~5h30)

La Phase 2 enrichit le modèle avec le temps et l'incertitude. Les notebooks 7-9 couvrent les jeux extensifs (arbres de jeu, ensembles d'information), les jeux combinatoires (Nim, Sprague-Grundy, avec formalisation Lean), et l'induction arrière (mille-pattes, escalade). Les notebooks 10-12 abordent les concepts subtils : induction avant et sous-jeux parfaits, jeux bayésiens (information incomplète, types, croyances), et jeux de réputation (signaling, engagement). Cette phase présuppose la Phase 1 (Nash, matrices de gains).

### Phase 3 : Frontieres — algorithmes, cooperation, mecanismes (Notebooks 13-17, ~7h)

La Phase 3 couvre les sujets avancés et les applications. Le notebook 13 (CFR) introduit Counterfactual Regret Minimization et ses variantes (MCCFR, Deep CFR), au cœur du poker AI moderne. Le notebook 14 (Differential Games) explore les jeux continus (Stackelberg, boucle ouverte/fermée). Les notebooks 15-15b-15c couvrent la théorie coopérative : valeur de Shapley (avec axiomes formels en Lean), Core, Bondareva-Shapley. Les notebooks 16-16b-16c-16d-16e-16f constituent le bloc le plus riche : design de mécanismes (révélation, VCG), choix social (Arrow, Sen en Lean), et encodage SAT/Z3 des impossibilités. Le notebook 17 (Multi-Agent RL) relie la théorie des jeux à l'apprentissage par renforcement (NFSP, PSRO, AlphaZero).

## Structure

**17 notebooks principaux** + **12 side tracks** (b = Lean, c = Python approfondissement, d/e/f = Social Choice) = **29 notebooks**

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
| 16d | [GameTheory-16d-SocialChoice-SAT](GameTheory-16d-SocialChoice-SAT.ipynb) | Python | Arrow encode en SAT, z3, UNSAT | 50 min |
| 16e | [GameTheory-16e-SocialChoiceLean-Tour](GameTheory-16e-SocialChoiceLean-Tour.ipynb) | Lean 4 | Tour DominikPeters, definitions simplifiees | 40 min |
| 16f | [GameTheory-16f-SocialChoice-Z3](GameTheory-16f-SocialChoice-Z3.ipynb) | Python | Arrow/Gibbard-Satterthwaite via Z3 solver | 45 min |
| 17 | [GameTheory-17-MultiAgent-RL](GameTheory-17-MultiAgent-RL.ipynb) | Python | NFSP, PSRO, AlphaZero intro | 55 min |

**Duree totale** : ~19h15

## Navigation et Side Tracks

Les **side tracks** approfondissent les concepts du notebook principal :

| Track | Type | Description |
|-------|------|-------------|
| **b** | Lean 4 | Formalisation mathematique, preuves formelles |
| **c** | Python | Approfondissement, exemples avances, visualisations |
| **d** | Python | Social Choice as SAT/CSP (z3, Arrow encoding) |
| **e** | Lean 4 | Tour des resultats DominikPeters/SocialChoiceLean |
| **f** | Python | Social Choice via Z3 solver (Arrow, Gibbard-Satterthwaite) |

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
| 16d | SocialChoice-SAT | ~20 | 2 | **COMPLET** |
| 16e | SocialChoiceLean-Tour | ~24 | 0 | **COMPLET** |
| 16f | SocialChoice-Z3 | ~20 | 2 | **COMPLET** |
| 17 | MultiAgent-RL | ~35 | 3 | **COMPLET** |

Tous les notebooks incluent :
- Navigation header/footer avec liens
- Plan avec liens ancres
- Tableaux recapitulatifs
- Exercices avec solutions completes

## Progression recommandee

### Decouvreur (fondements statiques, ~5h)

Commencez par les notebooks 1 (Setup) et 2 (NormalForm) pour comprendre les matrices de gains et la dominance strategique. Le notebook 4 (NashEquilibrium) introduit le concept central de la serie : l'equilibre de Nash, pur et mixte. Le notebook 5 (ZeroSum-Minimax) complete avec le theoreme minimax de Von Neumann et la programmation lineaire. Ces quatre notebooks suffisent pour comprendre les bases de la theorie des jeux non-cooperatifs.

### Praticien (jeux dynamiques et Lean, ~10h)

Poursuivez avec les jeux dynamiques : notebook 7 (formes extensives), 9 (induction arriere), 10 (induction avant et SPE). Le notebook 6 (EvolutionTrust) offre une pause rafraichissante avec le tournoi d'Axelrod. Les side tracks Lean (2b, 4b) vous initient a la formalisation des resultats en assistant de preuve. A ce stade, vous etes capable de modeliser des interactions strategiques complexes et de les verifier formellement.

### Expert (applications avancees et choix social, ~19h)

Les notebooks 13 (CFR), 15 (jeux cooperatifs, Shapley), et 16 (mechanisme design, Arrow) ouvrent les frontieres de la discipline. Les side tracks Social Choice (16b-16f) approfondissent le theoreme d'Arrow via Lean, SAT et Z3. Le notebook 17 (Multi-Agent RL) fait le pont avec l'apprentissage par renforcement.

## Quick Start

```bash
# 1. Installer les dependances Python (notebooks 1-12, 14-16)
pip install -r MyIA.AI.Notebooks/GameTheory/requirements.txt

# 2. Premier notebook
jupyter notebook GameTheory-1-Setup.ipynb

# 3. Puis GameTheory-2 (formes normales, matrices de gains)
```

Pour les notebooks Lean (2b, 4b, 8b, 15b, 16b) : installer le kernel `Lean 4 (WSL)` via `scripts/setup_wsl_lean4.sh`.
Pour GT-13/17 (OpenSpiel) : installer le kernel `GameTheory WSL` via `scripts/setup_wsl_openspiel.sh`.

---

## Prerequisites

- Connaissances de base en logique et mathematiques
- Familiarite avec Python (numpy, matplotlib)
- Pour notebooks Lean (b) : Installation Lean 4 + kernel WSL (voir serie Lean)
- Pour notebooks 13-17 : APIs optionnelles (OpenAI pour AlphaZero)

## Installation

### Installation rapide (Python standard - notebooks 1-12, 14-16)

```bash
pip install -r MyIA.AI.Notebooks/GameTheory/requirements.txt
# Note: open_spiel echouera sur Windows (necessite WSL) - c'est normal pour la majorite des notebooks
```

### Notebooks necessitant WSL (Windows uniquement)

GT-13 (CFR/OpenSpiel) et GT-17 (Multi-Agent RL) necessitent le kernel `Python (GameTheory WSL + OpenSpiel)` :

```bash
# 1. Dans WSL Ubuntu
cd /mnt/d/CoursIA/MyIA.AI.Notebooks/GameTheory/scripts
bash setup_wsl_openspiel.sh
```

```powershell
# 2. Cote Windows (PowerShell)
cd D:\CoursIA\MyIA.AI.Notebooks\GameTheory\scripts
.\setup_wsl_kernel.ps1
```

### Notebooks Lean 4 (2b, 4b, 8b, 15b, 16b)

Ces notebooks necessitent le kernel `Lean 4 (WSL)` :

```bash
# 1. Dans WSL Ubuntu
cd /mnt/d/CoursIA/MyIA.AI.Notebooks/GameTheory/scripts
bash setup_wsl_lean4.sh    # installe elan + Lean 4 + REPL + lean4_jupyter
```

```powershell
# 2. Cote Windows (PowerShell)
cd D:\CoursIA\MyIA.AI.Notebooks\GameTheory\scripts
.\setup_lean4_kernel.ps1   # enregistre le kernel lean4-wsl
```

### Verification

```bash
jupyter kernelspec list
# Doit montrer : python3, gametheory-wsl (optionnel), lean4-wsl (optionnel)
```

Pour les details et le depannage, voir [install_wsl_kernel.md](install_wsl_kernel.md).

### Configuration API (optionnel)

```bash
cp .env.example .env
# Editer .env et ajouter les cles API si necessaire
```

## Ressources externes

### References academiques

| Reference | Couverture |
|-----------|------------|
| Osborne & Rubinstein, *A Course in Game Theory* (1994) | Textbook de reference, notebooks 1-12 |
| Russell & Norvig, *AIMA* 4e ed., ch. 17-18 | Cadre general jeux et mecanismes |
| Nash, "Non-Cooperative Games" (1951) | Notebook 4, equilibre de Nash |
| Von Neumann, "Zur Theorie der Gesellschaftsspiele" (1928) | Notebook 5, minimax |
| Axelrod, "The Evolution of Cooperation" (1984) | Notebook 6, tournoi iterated PD |
| Conway, Berlekamp & Guy, *Winning Ways* (1982) | Notebooks 8, 8b, 8c |
| Geanakoplos, "Three Brief Proofs of Arrow's Impossibility Theorem" (2005) | Notebook 16d, Arrow.lean |
| Sen, "Collective Choice and Social Welfare" (1970) | Notebook 16e, Sen.lean |
| Shapley, "A Value for n-Person Games" (1953) | Notebook 15, Shapley.lean |
| Roth, "The Shapley Value: Essays in Honor of Lloyd S. Shapley" (1988) | Cooperative games |
| Osborne, *An Introduction to Game Theory* (2004) | Alternative textbook |

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
- [asouther4/lean-social-choice](https://github.com/asouther4/lean-social-choice) - Arrow (Lean 3, source originale)
- [DominikPeters/SocialChoiceLean](https://github.com/DominikPeters/SocialChoiceLean) - Gibbard-Satterthwaite, Split Cycle, 15+ regles (Lean 4, MIT)

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
├── GameTheory-16d-SocialChoice-SAT.ipynb
├── GameTheory-16e-SocialChoiceLean-Tour.ipynb
├── GameTheory-16f-SocialChoice-Z3.ipynb
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

## Connections cross-series

### GameTheory et Lean (Verification Formelle)

Les side tracks Lean (16b-16f) formalisent en Lean 4 les resultats theoriques etudies en Python dans les notebooks principaux. Cette dualite Python (simulation) / Lean (preuve formelle) est un fil rouge du curriculum.

| Concept GameTheory | Notebook Python | Formalisation Lean | Statut |
|--------------------|----------------|--------------------|--------|
| Jeux 2x2, strategies | GameTheory-2 | `Game2x2.lean` (notebook 2b) | Prouve |
| Existence Nash | GameTheory-4 | `NashExistence.lean` (notebook 4b) | Prouve |
| Jeux combinatoires | GameTheory-8 | `PGame.lean` (notebook 8b) | Prouve |
| Theoreme d'Arrow | GameTheory-16 | `Arrow.lean` (notebook 16d) | 0 sorry |
| Theoreme de Sen | GameTheory-16 | `Sen.lean` (notebook 16e) | 0 sorry |
| Valeur de Shapley | GameTheory-16b | `Shapley.lean` (cooperative games) | 2 sorry |
| Modeles de vote | GameTheory-16f | `Voting.lean` (Banks, STV) | 4 sorry |

Voir [SymbolicAI/Lean/README.md](../SymbolicAI/Lean/README.md) pour les prerequis Lean (notebooks 1-6 recommandes).

### GameTheory et SmartContracts

Les concepts de theorie des jeux et de choix social apparaissent directement dans les smart contracts :

- **SC-9 DAO Governance** : mecanismes de vote on-chain = application directe du theoreme d'Arrow et des modeles de vote etudies en 16f.
- **SC-17 E2E Verifiable Voting** : le vote electronique verifiable combine les resultats de choix social (Arrow, Banks, STV) avec la cryptographie (ZKP, chiffrement homomorphique).
- **SC-14 Formal Verification** : la verification formelle de smart contracts rejoint les methodes de preuve formelle utilisees pour les formalisations Lean de cette serie.

Voir [SymbolicAI/SmartContracts/README.md](../SymbolicAI/SmartContracts/README.md) pour la serie complete.

## Licence

Voir la licence du repository principal.
