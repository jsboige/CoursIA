# RL - Reinforcement Learning

<!-- CATALOG-STATUS
series: RL
pedagogical_count: 6
breakdown: =6
maturity: ALPHA=5, PRODUCTION=1
-->

Le Reinforcement Learning (apprentissage par renforcement) est la branche de l'IA qui apprend a un agent a prendre des decisions optimales par l'essai et l'erreur, en recevant des recompenses ou des penalites de son environnement. C'est la technologie derriere AlphaGo, les robots de Boston Dynamics, les systemes de recommendation de Netflix, et les voitures autonomes. La ou l'apprentissage supervise predit a partir d'exemples etiquetes et l'apprentissage non supervise decouvre des structures, le RL **agit** : il choisit des actions, observe leurs consequences, et s'ameliore iterativement.

Cette serie couvre les **fondements theoriques** (MDP, equation de Bellman, Q-Learning), les **algorithmes avec reseaux de neurones** (DQN, Policy Gradient, PPO) et les **frameworks de production** (Stable Baselines3). Vous commencerez par entrainer un agent en quelques lignes avec un framework industriel, puis vous implementerez les memes algorithmes depuis zero pour comprendre ce qui se cache sous le capot.

**A qui s'adresse cette serie** : etudiants en IA, developpeurs souhaitant ajouter des capacites decisionnelles a leurs applications, et chercheurs en automatique ou robotique. Prerequis : Python intermediaire et bases en calculus (gradients). Aucune experience RL prealable necessaire pour le notebook 1.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 6 |
| Kernel | Python 3 |
| Duree totale | ~240-280 min |
| Version | Stable Baselines3 2.0.0+ |

## Notebooks

| # | Notebook | Contenu | Durée |
|---|----------|---------|-------|
| 1 | [stable_baseline_1_intro_cartpole](stable_baseline_1_intro_cartpole.ipynb) | Introduction PPO, CartPole | 25-30 min |
| 2 | [stable_baseline_2_wrappers_sauvegarde_callbacks](stable_baseline_2_wrappers_sauvegarde_callbacks.ipynb) | Wrappers, sauvegarde, callbacks | 35-40 min |
| 3 | [stable_baseline_3_experience_replay_dqn](stable_baseline_3_experience_replay_dqn.ipynb) | HER, goal-conditioned RL | 40-45 min |
| 4 | [rl_4_mdp_dp_qlearning](rl_4_mdp_dp_qlearning.ipynb) | MDP, Value/Policy Iteration, Q-Learning tabulaire | 45-50 min |
| 5 | [rl_5_dqn_policy_gradient](rl_5_dqn_policy_gradient.ipynb) | DQN depuis zero, REINFORCE | 50-55 min |
| 6 | [rl_6_multi_agent_rl](rl_6_multi_agent_rl.ipynb) | Multi-Agent RL, PettingZoo, IQL | 45-50 min |

## Contenu detaille

### Notebook 1 - Introduction avec PPO et CartPole

| Section | Contenu |
|---------|---------|
| Stable Baselines3 | Installation, API de base |
| CartPole-v1 | Environnement classique, actions discretes |
| PPO | Proximal Policy Optimization |
| Workflow | Training, Evaluation, Video recording |

### Notebook 2 - Fonctionnalites avancees

| Section | Contenu |
|---------|---------|
| Wrappers Gym | Modification d'environnements |
| Sauvegarde | Save/Load de modeles |
| Multiprocessing | DummyVecEnv, SubprocVecEnv |
| Callbacks | Monitoring, checkpoints automatiques |
| Environnements custom | Creation et validation (check_env) |

### Notebook 3 - Experience Replay et HER

| Section | Contenu |
|---------|---------|
| HER | Hindsight Experience Replay |
| Goal-conditioned RL | Taches avec objectifs |
| Parking-v0 | Environnement highway-env |
| SAC / DDPG | Algorithmes off-policy avec HER |
| Replay buffers | Sauvegarde et chargement |

### Notebook 4 - MDP, Programmation Dynamique et Q-Learning

| Section | Contenu |
|---------|---------|
| MDP | Formalisation $(S, A, P, R, \gamma)$, transitions |
| Value Iteration | Equation de Bellman, convergence |
| Policy Iteration | Evaluation + amelioration de politique |
| Q-Learning tabulaire | Apprentissage model-free, $\varepsilon$-greedy |
| FrozenLake / CliffWalking | Environnements discrets |

### Notebook 5 - DQN et Policy Gradient

| Section | Contenu |
|---------|---------|
| Q-Network | Approximation par reseau de neurones |
| Replay Buffer | Experience replay, decorrelation |
| Target Network | Stabilisation de l'apprentissage |
| REINFORCE | Gradient de politique, baseline |
| Comparaison | Value-based vs policy-based |

### Notebook 6 - Apprentissage Multi-Agent

| Section | Contenu |
|---------|---------|
| Multi-Agent RL | Paradigmes (cooperatif, competitif, mixte) |
| PettingZoo | API AEC, environnements multi-agent |
| IQL | Independent Q-Learning |
| TicTacToe | Jeu a somme nulle, equilibre |
| Self-play | Entrainement agent contre agent |

## Algorithmes couverts

| Algorithme | Type | Notebook | Utilisation |
|------------|------|----------|-------------|
| **PPO** | On-policy | 1, 2 | Controle general, robuste |
| **A2C** | On-policy | 2 | Alternative a PPO |
| **SAC** | Off-policy | 3 | Actions continues |
| **DDPG** | Off-policy | 3 | Actions continues |
| **HER** | Replay strategy | 3 | Goal-conditioned tasks |
| **Value Iteration** | Model-based | 4 | Resolution exacte de MDP |
| **Policy Iteration** | Model-based | 4 | Resolution exacte de MDP |
| **Q-Learning** | Model-free (tabulaire) | 4 | Espaces discrets |
| **DQN** | Off-policy (deep) | 5 | Espaces continus |
| **REINFORCE** | Policy gradient | 5 | Politique directe |
| **IQL** | Multi-agent | 6 | Apprentissage independant |

## Environnements

| Environnement | Type | Notebook |
|---------------|------|----------|
| CartPole-v1 | Controle classique, discret | 1, 5 |
| Pendulum-v1 | Controle continu | 2 |
| Parking-v0 | Goal-conditioned, continu | 3 |
| FrozenLake-v1 | Grille discrete, stochastique | 4 |
| CliffWalking-v1 | Grille, compromis risque/recompense | 4 |
| TicTacToe-v3 | Jeu a somme nulle | 6 |

## Prerequisites

### Connaissances requises

- Python intermediaire (classes, numpy)
- Concepts RL de base (agent, environnement, reward)
- Pas d'experience RL prealable necessaire pour le notebook 1
- Bases PyTorch pour les notebooks 5 (tenseurs, autograd, Module)

### Installation

```bash
# Environnement Python
python -m venv venv
venv\Scripts\activate  # Windows

# Dependances de base (notebooks 1-4)
pip install "stable-baselines3[extra]>=2.0.0a4" gymnasium numpy matplotlib

# Pour le notebook 3 (parking environment)
pip install highway-env moviepy

# Pour le notebook 5 (DQN, REINFORCE)
pip install torch

# Pour le notebook 6 (multi-agent)
pip install "pettingzoo[classic]>=1.24.0"
```

### Dependances

| Package | Version | Utilisation |
|---------|---------|-------------|
| stable-baselines3 | >=2.0.0a4 | Algorithmes RL (notebooks 1-3) |
| gymnasium | latest | Interface environnements |
| numpy | latest | Calcul numerique |
| matplotlib | latest | Visualisation |
| torch | latest | Reseaux de neurones (notebook 5) |
| pettingzoo | >=1.24.0 | Multi-agent (notebook 6) |
| highway-env | latest | Parking-v0 (notebook 3) |
| moviepy | latest | Enregistrement video |

## Parcours recommande

```
Notebook 1 (Bases SB3)
    |
    v
Notebook 4 (Fondements theoriques) ---> Notebook 5 (DQN / Policy Gradient)
    |                                          |
    v                                          v
Notebook 2 (Production features)         Notebook 6 (Multi-Agent)
    |
    v
Notebook 3 (Goal-conditioned RL)
```

| Objectif | Notebooks |
|----------|-----------|
| Decouverte rapide | 1 uniquement |
| Fondations SB3 | 1 + 2 + 3 |
| Fondements theoriques | 4 + 5 + 6 |
| Maitrise complete | 1 a 6 |

### Parcours d'apprentissage

**Phase 1 : Prise en main production (~1h, notebooks 1-2)**

Le notebook 1 pose les bases : vous installez Stable Baselines3, creez votre premier agent PPO sur CartPole, et visualisez ses performances. En 30 minutes, vous avez un agent entraine qui equilibre un baton. Le notebook 2 enrichit cette base avec les outils de production : wrappers pour modifier les environnements, callbacks pour monitorer l'entrainement, et multiprocessing pour accelerer les experiences.

**Phase 2 : Problemes avances (~1.5h, notebook 3)**

Le notebook 3 introduit les taches a objectifs (goal-conditioned RL) avec l'algorithme HER (Hindsight Experience Replay). Vous resoudrez un probleme de parking autonome ou l'agent doit atteindre une position cible. C'est le passage de "equilibrer un baton" a "garer une voiture" — un saut qualitatif qui montre la puissance du RL.

**Phase 3 : Les maths sous le capot (~2.5h, notebooks 4-6)**

Les notebooks 4 a 6 quittent le framework pour implementer les algorithmes depuis zero. Le notebook 4 formalise le probleme RL (MDP, equation de Bellman, Value/Policy Iteration) et introduit le Q-Learning tabulaire sur FrozenLake et CliffWalking. Le notebook 5 passe a l'echelle avec les reseaux de neurones : DQN et REINFORCE implementes en PyTorch pur. Le notebook 6 clot avec le multi-agent : plusieurs agents qui apprennent simultanement, cooperent ou s'affrontent (TicTacToe avec self-play).

## Concepts cles

| Concept | Description | Notebook |
|---------|-------------|----------|
| **Agent** | Entite qui apprend et prend des decisions | 1 |
| **Environnement** | Monde avec lequel l'agent interagit | 1 |
| **Reward** | Signal de feedback pour l'apprentissage | 1 |
| **Policy** | Strategie de l'agent (state vers action) | 1 |
| **Value function** | Estimation des rewards futurs | 4 |
| **MDP** | Formalisation mathematique du probleme RL | 4 |
| **Bellman equation** | Relation de recurrence pour V et Q | 4 |
| **Experience replay** | Reutilisation des experiences passees | 3, 5 |
| **HER** | Reinterpretation d'echecs comme succes | 3 |
| **DQN** | Q-Learning avec approximation neurale | 5 |
| **Policy gradient** | Optimisation directe de la politique | 5 |
| **Multi-agent** | Plusieurs agents apprenant simultanement | 6 |

## Caracteristiques

- **Compatible Windows** : Pas de dependance xvfb
- **Debutant-friendly** : Progression pedagogique
- **Production-ready** : Checkpointing, monitoring (notebooks 1-3)
- **From scratch** : Implementations sans framework (notebooks 4-6)
- **Exercices** : Manipulations et explorations dans chaque notebook

## Ressources

### Documentation

- [Stable Baselines3 Docs](https://stable-baselines3.readthedocs.io/)
- [Gymnasium Docs](https://gymnasium.farama.org/)
- [Highway-env Docs](https://highway-env.readthedocs.io/)
- [PettingZoo Docs](https://pettingzoo.farama.org/)

### Theorie RL

- Sutton & Barto - *Reinforcement Learning: An Introduction* (2nd ed.)
- [Spinning Up in Deep RL](https://spinningup.openai.com/)
- Mnih et al. (2015) - *Human-level control through deep reinforcement learning*, Nature

## Structure des fichiers

```
RL/
├── stable_baseline_1_intro_cartpole.ipynb
├── stable_baseline_2_wrappers_sauvegarde_callbacks.ipynb
├── stable_baseline_3_experience_replay_dqn.ipynb
├── rl_4_mdp_dp_qlearning.ipynb
├── rl_5_dqn_policy_gradient.ipynb
├── rl_6_multi_agent_rl.ipynb
└── README.md
```

## Cross-series Bridges

| Serie | Lien | Connection |
|-------|------|-------------|
| [GameTheory](../GameTheory/README.md) | Jeux bayesiens, equilibre de Nash | Le RL multi-agent (notebook 6) formalise les memes interactions que la theorie des jeux, mais avec apprentissage |
| [ML](../ML/README.md) | Pipelines ML | Le RL s'appuie sur les memes outils (PyTorch, numpy) et suppose la familiarite avec l'entrainement de modeles |
| [QuantConnect](../QuantConnect/README.md) | Trading algorithmique | Les strategies de trading se modelisent comme des problemes RL (actions = acheter/vendre, reward = PnL) |
| [Probas](../Probas/README.md) | Decision bayesienne (notebooks 17-20) | Les MDP du RL generalisent les processus decisionnels de Markov de la serie Probas |
| [Search](../Search/README.md) | Optimisation combinatoire | La planification RL (value/policy iteration) ressemble a la recherche dans un espace d'etats |

## Licence

Voir la licence du repository principal.
