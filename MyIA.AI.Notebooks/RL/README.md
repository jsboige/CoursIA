# RL - Reinforcement Learning

<!-- CATALOG-STATUS
series: RL
pedagogical_count: 10
breakdown: root=10
maturity: PRODUCTION=9, BETA=1
-->

Le Reinforcement Learning (apprentissage par renforcement) est la branche de l'IA qui apprend a un agent a prendre des decisions optimales par l'essai et l'erreur, en recevant des recompenses ou des penalites de son environnement. C'est la technologie derriere AlphaGo, les robots de Boston Dynamics, les systemes de recommendation de Netflix, et les voitures autonomes. La ou l'apprentissage supervise predit a partir d'exemples etiquetes et l'apprentissage non supervise decouvre des structures, le RL **agit** : il choisit des actions, observe leurs consequences, et s'ameliore iterativement.

Cette serie couvre les **fondements theoriques** (bandits, MDP, equation de Bellman, Q-Learning), les **algorithmes avec reseaux de neurones** (DQN, Policy Gradient, PPO) et les **frameworks de production** (Stable Baselines3). Vous commencerez par entrainer un agent en quelques lignes avec un framework industriel, puis vous implementerez les memes algorithmes depuis zero pour comprendre ce qui se cache sous le capot.

**A qui s'adresse cette serie** : etudiants en IA, developpeurs souhaitant ajouter des capacites decisionnelles a leurs applications, et chercheurs en automatique ou robotique. Prerequis : Python intermediaire et bases en calculus (gradients). Aucune experience RL prealable necessaire pour le notebook 1.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 11 |
| Kernel | Python 3 |
| Duree totale | ~450-520 min |
| Version | Stable Baselines3 2.0.0+ |

## Notebooks

| # | Notebook | Contenu | Duree |
|---|----------|---------|-------|
| 1 | [rl_1_intro_cartpole](rl_1_intro_cartpole.ipynb) | Introduction PPO, CartPole | 25-30 min |
| 2 | [rl_2_wrappers_sauvegarde_callbacks](rl_2_wrappers_sauvegarde_callbacks.ipynb) | Wrappers, sauvegarde, callbacks | 35-40 min |
| 3 | [rl_3_experience_replay_dqn](rl_3_experience_replay_dqn.ipynb) | HER, goal-conditioned RL | 40-45 min |
| 4 | [rl_4_multi_armed_bandits](rl_4_multi_armed_bandits.ipynb) | Bandits manchots, exploration vs exploitation, Thompson Sampling | 30-35 min |
| 5 | [rl_5_mdp_dp_qlearning](rl_5_mdp_dp_qlearning.ipynb) | MDP, Value/Policy Iteration, Q-Learning tabulaire | 45-50 min |
| 6 | [rl_6_dqn_policy_gradient](rl_6_dqn_policy_gradient.ipynb) | DQN depuis zero, REINFORCE | 50-55 min |
| 6b | [rl_6b_actor_critic](rl_6b_actor_critic.ipynb) | Actor-Critic (A2C) depuis zero, advantage, entropy bonus | 45-50 min |
| 6c | [rl_6c_ppo_from_scratch](rl_6c_ppo_from_scratch.ipynb) | PPO depuis zero, clipped surrogate, GAE, comparaison A2C vs PPO | 45-50 min |
| 6d | [rl_6d_sac_from_scratch](rl_6d_sac_from_scratch.ipynb) | SAC depuis zero, maximum entropy RL, twin Q-networks, auto-temperature | 45-50 min |
| 7 | [rl_7_multi_agent_rl](rl_7_multi_agent_rl.ipynb) | Multi-Agent RL, PettingZoo, IQL | 45-50 min |
| 8 | [rl_8_model_based_dyna_q](rl_8_model_based_dyna_q.ipynb) | Model-based RL : Dyna-Q, Dyna-Q+, planification, rollouts | 45-50 min |

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

### Notebook 4 - Bandits Manchots et Exploration

| Section | Contenu |
|---------|---------|
| Multi-armed bandit | Probleme fondamental exploration vs exploitation |
| Strategies naives | Aléatoire, greedy, epsilon-greedy |
| Strategies intelligentes | Decaying epsilon-greedy, Thompson Sampling |
| Analyse | Comparaison regret, visualisation des estimations |

### Notebook 5 - MDP, Programmation Dynamique et Q-Learning

| Section | Contenu |
|---------|---------|
| MDP | Formalisation $(S, A, P, R, \gamma)$, transitions |
| Value Iteration | Equation de Bellman, convergence |
| Policy Iteration | Evaluation + amelioration de politique |
| Q-Learning tabulaire | Apprentissage model-free, $\varepsilon$-greedy |
| FrozenLake / CliffWalking | Environnements discrets |

### Notebook 6 - DQN et Policy Gradient

| Section | Contenu |
|---------|---------|
| Q-Network | Approximation par reseau de neurones |
| Replay Buffer | Experience replay, decorrelation |
| Target Network | Stabilisation de l'apprentissage |
| REINFORCE | Gradient de politique, baseline |
| Comparaison | Value-based vs policy-based |

### Notebook 6b - Actor-Critic (A2C)

| Section | Contenu |
|---------|---------|
| Actor-Critic | Paradigme combinant value-based et policy-based |
| CriticNetwork | Reseau de valeur V(s) |
| ActorNetwork | Politique parametree pi(a\|s) |
| A2C | Advantage Actor-Critic, calcul de l'avantage |
| Entropy bonus | Exploration via maximisation d'entropie |
| Comparaison | A2C vs REINFORCE (reduction de variance) |

### Notebook 6c - PPO depuis zero

| Section | Contenu |
|---------|---------|
| Clipped surrogate | Ratio de probabilite, objectif clippe, visualisation |
| PPO Agent | Implementation complete avec mini-lots et epochs |
| GAE | Generalized Advantage Estimation (lambda=0.95) |
| Comparaison | PPO vs A2C (stabilite, efficacite d'echantillonnage) |

### Notebook 6d - SAC depuis zero

| Section | Contenu |
|---------|---------|
| Maximum Entropy RL | Objectif avec bonus d'entropie, exploration automatique |
| Gaussian Policy | Politique stochastique avec tanh squashing |
| Twin Q-Networks | Double critique pour reduire la surestimation |
| Auto-temperature | Temperature alpha apprise automatiquement |
| Reparameterization | Trick pour gradient dans l'action |
| Pendulum-v1 | Environnement continu de reference |

### Notebook 7 - Apprentissage Multi-Agent

| Section | Contenu |
|---------|---------|
| Multi-Agent RL | Paradigmes (cooperatif, competitif, mixte) |
| PettingZoo | API AEC, environnements multi-agent |
| IQL | Independent Q-Learning |
| TicTacToe | Jeu a somme nulle, equilibre |
| Self-play | Entrainement agent contre agent |

### Notebook 8 - Model-Based RL : Dyna-Q et planification

| Section | Contenu |
|---------|---------|
| Model-free vs model-based | Compromis calcul vs experience, sample efficiency |
| Modele du monde | Apprentissage tabulaire des transitions (s,a) -> (r,s') |
| Dyna-Q | Q-Learning + planification sur experience simulee (Sutton & Barto ch. 8) |
| Blocking Maze / Dyna-Q+ | Environnement changeant, bonus d'exploration kappa*sqrt(tau) |
| Decision-time planning | Rollouts, pont vers MCTS / AlphaZero / MuZero |
| Exercices | Shortcut Maze, prioritized sweeping, sensibilite de kappa |

## Algorithmes couverts

| Algorithme | Type | Notebook | Utilisation |
|------------|------|----------|-------------|
| **PPO** | On-policy | 1, 2, 6c | Controle general, robuste |
| **A2C** | On-policy | 2, 6b | Actor-Critic depuis zero et via SB3 |
| **GAE** | Advantage | 6c | Generalized Advantage Estimation |
| **SAC** | Off-policy | 3, 6d | Actions continues, maximum entropy |
| **DDPG** | Off-policy | 3 | Actions continues |
| **HER** | Replay strategy | 3 | Goal-conditioned tasks |
| **Epsilon-greedy** | Exploration | 4 | Strategie d'exploration basique |
| **Thompson Sampling** | Exploration | 4 | Exploration bayesienne |
| **Value Iteration** | Model-based | 5 | Resolution exacte de MDP |
| **Policy Iteration** | Model-based | 5 | Resolution exacte de MDP |
| **Q-Learning** | Model-free (tabulaire) | 5 | Espaces discrets |
| **Dyna-Q** | Model-based | 8 | Planification sur modele appris, sample efficiency |
| **Dyna-Q+** | Model-based | 8 | Environnements non-stationnaires, bonus d'exploration |
| **Rollout planning** | Decision-time | 8 | Simulation vers l'avant, porte vers MCTS |
| **DQN** | Off-policy (deep) | 6 | Espaces continus |
| **REINFORCE** | Policy gradient | 6 | Politique directe |
| **IQL** | Multi-agent | 7 | Apprentissage independant |

## Environnements

| Environnement | Type | Notebook |
|---------------|------|----------|
| CartPole-v1 | Controle classique, discret | 1, 6, 6b, 6c |
| Pendulum-v1 | Controle continu | 2, 6d |
| Parking-v0 | Goal-conditioned, continu | 3 |
| GaussianBandit | Bandit stochastique | 4 |
| FrozenLake-v1 | Grille discrete, stochastique | 5 |
| CliffWalking-v1 | Grille, compromis risque/recompense | 5 |
| TicTacToe-v3 | Jeu a somme nulle | 7 |
| Dyna Maze / Blocking Maze | Grilles deterministes et changeantes (numpy pur) | 8 |

## Prerequisites

### Connaissances requises

- Python intermediaire (classes, numpy)
- Concepts RL de base (agent, environnement, reward)
- Pas d'experience RL prealable necessaire pour le notebook 1
- Bases PyTorch pour les notebooks 6, 6b, 6c, 6d (tenseurs, autograd, Module)

### Installation

```bash
# Environnement Python
python -m venv venv
venv\Scripts\activate  # Windows

# Dependances de base (notebooks 1-4)
pip install "stable-baselines3[extra]>=2.0.0a4" gymnasium numpy pandas matplotlib

# Pour le notebook 3 (parking environment)
pip install highway-env moviepy

# Pour le notebook 4 (bandits — pas de dependance supplementaire)

# Pour les notebooks 6, 6b, 6c, 6d (DQN, REINFORCE, A2C, PPO, SAC)
pip install torch

# Pour le notebook 7 (multi-agent)
pip install "pettingzoo[classic]>=1.24.0"
```

### Dependances

| Package | Version | Utilisation |
|---------|---------|-------------|
| stable-baselines3 | >=2.0.0a4 | Algorithmes RL (notebooks 1-3) |
| gymnasium | latest | Interface environnements |
| numpy | latest | Calcul numerique |
| pandas | >=2.0 | Tableaux de resultats (notebook 5) |
| matplotlib | latest | Visualisation |
| torch | latest | Reseaux de neurones (notebooks 6, 6b, 6c, 6d) |
| pettingzoo | >=1.24.0 | Multi-agent (notebook 7) |
| highway-env | latest | Parking-v0 (notebook 3) |
| moviepy | latest | Enregistrement video |

## Parcours recommande

```
Notebook 1 (Bases SB3)
    |
    v
Notebook 4 (Bandits) ---> Notebook 5 (MDP / Q-Learning) ---> Notebook 6 (DQN / REINFORCE)
    |                                                          |
    v                                                          v
Notebook 2 (Production features)                           Notebook 6b (A2C) ---> Notebook 6c (PPO)
    |                                                                               |
    v                                                                               v
Notebook 3 (Goal-conditioned RL)                                                 Notebook 7 (Multi-Agent)
```

| Objectif | Notebooks |
|----------|-----------|
| Decouverte rapide | 1 uniquement |
| Exploration et bandits | 4 uniquement |
| Fondations SB3 | 1 + 2 + 3 |
| Fondements theoriques | 4 + 5 + 6 + 7 + 8 |
| Maitrise complete | 1 a 8 |

### Parcours d'apprentissage

**Phase 1 : Prise en main production (~1h, notebooks 1-2)**

Le notebook 1 pose les bases : vous installez Stable Baselines3, creez votre premier agent PPO sur CartPole, et visualisez ses performances. En 30 minutes, vous avez un agent entraine qui equilibre un baton. Le notebook 2 enrichit cette base avec les outils de production : wrappers pour modifier les environnements, callbacks pour monitorer l'entrainement, et multiprocessing pour accelerer les experiences.

**Phase 2 : Problemes avances (~1.5h, notebook 3)**

Le notebook 3 introduit les taches a objectifs (goal-conditioned RL) avec l'algorithme HER (Hindsight Experience Replay). Vous resoudrez un probleme de parking autonome ou l'agent doit atteindre une position cible. C'est le passage de "equilibrer un baton" a "garer une voiture" — un saut qualitatif qui montre la puissance du RL.

**Phase 3 : Exploration et bandits (~30min, notebook 4)**

Le notebook 4 pose la question fondatrice du RL : comment choisir entre explorer de nouvelles options et exploiter ce qui fonctionne deja ? Vous implementerez des strategies d'exploration (epsilon-greedy, decaying epsilon, Thompson Sampling) sur un probleme de bandits manchots et comparerez leur regret cumule.

**Phase 4 : Les maths sous le capot (~4.5h, notebooks 5-7)**

Les notebooks 5 a 7 quittent le framework pour implementer les algorithmes depuis zero. Le notebook 5 formalise le probleme RL (MDP, equation de Bellman, Value/Policy Iteration) et introduit le Q-Learning tabulaire sur FrozenLake et CliffWalking. Le notebook 6 passe a l'echelle avec les reseaux de neurones : DQN et REINFORCE implementes en PyTorch pur. Le notebook 6b introduit l'architecture Actor-Critic (A2C). Le notebook 6c pousse plus loin avec PPO et son mecanisme de clipping, introduit GAE, et compare les approches. Le notebook 6d approfondit avec SAC (Soft Actor-Critic) et le framework maximum entropy pour les actions continues. Le notebook 7 aborde le multi-agent : plusieurs agents qui apprennent simultanement, cooperent ou s'affrontent (TicTacToe avec self-play). Le notebook 8 ouvre la voie model-based : apprendre un modele du monde et planifier dessus (Dyna-Q, Dyna-Q+, rollouts), avec les ponts vers MCTS, AlphaZero et MuZero.

## Concepts cles

| Concept | Description | Notebook |
|---------|-------------|----------|
| **Agent** | Entite qui apprend et prend des decisions | 1 |
| **Environnement** | Monde avec lequel l'agent interagit | 1 |
| **Reward** | Signal de feedback pour l'apprentissage | 1 |
| **Policy** | Strategie de l'agent (state vers action) | 1 |
| **Value function** | Estimation des rewards futurs | 5 |
| **MDP** | Formalisation mathematique du probleme RL | 5 |
| **Bellman equation** | Relation de recurrence pour V et Q | 5 |
| **Exploration vs exploitation** | Compromis entre tester et exploiter | 4 |
| **Regret** | Mesure de performance cumulative en bandit | 4 |
| **Thompson Sampling** | Exploration bayesienne optimale | 4 |
| **Experience replay** | Reutilisation des experiences passees | 3, 6 |
| **Clipped surrogate** | Mecanisme central de PPO | 6c |
| **GAE** | Compromis biais-variance pour l'avantage | 6c |
| **HER** | Reinterpretation d'echecs comme succes | 3 |
| **DQN** | Q-Learning avec approximation neurale | 6 |
| **Actor-Critic** | Combinaison politique + valeur | 6b |
| **Advantage** | Reduction de variance A_t = R_t - V(s) | 6b |
| **Maximum entropy RL** | Maximisation recompense + entropie | 6d |
| **SAC** | Soft Actor-Critic, off-policy continu | 6d |
| **Twin Q-networks** | Double critique anti-surestimation | 6d |
| **Policy gradient** | Optimisation directe de la politique | 6 |
| **Multi-agent** | Plusieurs agents apprenant simultanement | 7 |
| **Model-based RL** | Apprendre un modele du monde et planifier dessus | 8 |
| **Dyna** | Entrelacement apprentissage direct / planification | 8 |
| **Sample efficiency** | Echanger du calcul contre de l'experience reelle | 8 |
| **Decision-time planning** | Rollouts et MCTS depuis l'etat courant | 8 |

## Caracteristiques

- **Compatible Windows** : Pas de dependance xvfb
- **Debutant-friendly** : Progression pedagogique
- **Production-ready** : Checkpointing, monitoring (notebooks 1-3)
- **From scratch** : Implementations sans framework (notebooks 4-7)
- **Exercices** : Manipulations et explorations dans chaque notebook

## FAQ

### Quelle est la difference entre RL et apprentissage supervise ?

L'apprentissage **supervise** apprend a partir de donnees etiquetees (entree -> sortie correcte). Le RL apprend par **interaction** : l'agent prend des actions, recoit des recompenses/penalites, et ajuste sa strategie. Il n'y a pas de "bonne reponse" fournie — l'agent doit decouvrir quelles actions maximisent la recompense cumulee. Le RL est pertinent quand le probleme est sequentiel (une action affecte les futures observations).

### Faut-il un GPU pour les notebooks ?

Non. Les notebooks 1-4 (SB3 intro, wrappers, bandits, DQN from scratch) et 7-8 (multi-agent, curriculum) tournent sur CPU avec les environnements simples (CartPole, MountainCar). Les notebooks 5-6 (Policy Gradient, PPO from scratch) beneficient d'un GPU pour les reseaux plus profonds mais restent executables en CPU (plus lent). Environnements Atari (optionnel) : GPU recommande.

### Qu'est-ce qu'un MDP et pourquoi est-ce central ?

Un **MDP** (Markov Decision Process) est le modele mathematique du RL : un ensemble d'etats S, d'actions A, de transitions T(s'|s,a), de recompenses R(s,a), et d'un facteur d'actualisation gamma. Tout probleme de RL se formalise comme un MDP. L'equation de Bellman (notebook 3) definit recursivement la valeur optimale. Si vous avez fait la serie Probas, les MDP generalisent les chaines de Markov avec des decisions.

### Quelle est la difference entre on-policy et off-policy ?

**On-policy** (PPO, A2C, REINFORCE) : l'apprentissage utilise uniquement les donnees collectees par la politique courante. Plus stable mais moins sample-efficient. **Off-policy** (DQN, SAC, DDPG) : l'apprentissage peut reutiliser des donnees passees stockees dans un replay buffer. Plus sample-efficient mais potentiellement moins stable. Le notebook 6 compare DQN (off-policy) et REINFORCE (on-policy) sur le meme environnement.

### Pourquoi commencer par Stable Baselines3 plutot que par les algorithmes from scratch ?

Stable Baselines3 permet de resoudre un probleme reel en quelques lignes, ce qui donne une intuition concreten avant d'etudier la theorie. L'approche "framework d'abord, maths ensuite" evite le piege de la theorie abstraite sans application. Les notebooks 4-7 deconstruisent ensuite les memes algorithmes pour comprendre ce qui se passe sous le capot.

### Quelle est la difference entre value-based et policy-based ?

**Value-based** (Q-Learning, DQN) : on apprend a estimer la valeur de chaque action dans chaque etat, puis on choisit l'action avec la plus haute valeur. Adapté aux espaces d'actions discrets. **Policy-based** (REINFORCE, PPO) : on optimise directement la politique (probabilite de choisir chaque action). Adapté aux espaces continus et aux politiques stochastiques. **Actor-Critic** (A2C, SAC) combine les deux : l'acteur choisit l'action, le critique estime la valeur.

### Qu'est-ce que l'experience replay et pourquoi est-ce important ?

L'experience replay (notebook 6) stocke les transitions (etat, action, reward, etat_suivant) dans un buffer et re-echantillonne aleatoirement pendant l'apprentissage. Cela casse les correlations temporelles entre experiences consecutives et ameliore l'efficacite en reutilisant chaque experience plusieurs fois. Sans replay buffer, les agents off-policy comme DQN seraient instables. HER (notebook 3) etend ce concept en re-interpretant les echecs comme des succes par changement d'objectif.

### Comment choisir entre DQN et PPO pour un nouveau probleme ?

- **Espace d'actions discret** et petit : DQN est simple et efficace (notebooks 5-6)
- **Espace d'actions continu** : PPO ou SAC (notebooks 1-2, 3)
- **Stabilite prioritaire** : PPO est le choix par defaut dans l'industrie (clipping prevents large policy updates)
- **Sample efficiency** : SAC (off-policy) apprend plus vite en nombre d'interactions, mais PPO (on-policy) est souvent plus robuste en hyperparametres

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
├── rl_1_intro_cartpole.ipynb
├── rl_2_wrappers_sauvegarde_callbacks.ipynb
├── rl_3_experience_replay_dqn.ipynb
├── rl_4_multi_armed_bandits.ipynb
├── rl_5_mdp_dp_qlearning.ipynb
├── rl_6_dqn_policy_gradient.ipynb
├── rl_6b_actor_critic.ipynb
├── rl_6c_ppo_from_scratch.ipynb
├── rl_6d_sac_from_scratch.ipynb
├── rl_7_multi_agent_rl.ipynb
├── rl_8_model_based_dyna_q.ipynb
└── README.md
```

## Cross-series Bridges

| Serie | Lien | Connection |
|-------|------|-------------|
| [GameTheory](../GameTheory/README.md) | Jeux bayesiens, equilibre de Nash | Le RL multi-agent (notebook 7) formalise les memes interactions que la theorie des jeux, mais avec apprentissage |
| [ML](../ML/README.md) | Pipelines ML | Le RL s'appuie sur les memes outils (PyTorch, numpy) et suppose la familiarite avec l'entrainement de modeles |
| [QuantConnect](../QuantConnect/README.md) | Trading algorithmique | Les strategies de trading se modelisent comme des problemes RL (actions = acheter/vendre, reward = PnL) |
| [Probas](../Probas/README.md) | Decision bayesienne (notebooks 17-20) | Les MDP du RL generalisent les processus decisionnels de Markov de la serie Probas |
| [Search](../Search/README.md) | Optimisation combinatoire | La planification RL (value/policy iteration) ressemble a la recherche dans un espace d'etats |

## Licence

Voir la licence du repository principal.
