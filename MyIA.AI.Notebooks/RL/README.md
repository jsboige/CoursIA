# RL - Reinforcement Learning

Introduction au Reinforcement Learning (apprentissage par renforcement) avec **Stable Baselines3**, une bibliotheque Python offrant des implementations fiables d'algorithmes RL.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 3 |
| Kernel | Python 3 |
| Duree totale | ~100-115 min |

## Notebooks

| # | Notebook | Contenu | Duree |
|---|----------|---------|-------|
| 1 | [stable_baseline_1_intro_cartpole](stable_baseline_1_intro_cartpole.ipynb) | Introduction PPO, CartPole | 25-30 min |
| 2 | [stable_baseline_2_wrappers_sauvegarde_callbacks](stable_baseline_2_wrappers_sauvegarde_callbacks.ipynb) | Wrappers, sauvegarde, callbacks | 35-40 min |
| 3 | [stable_baseline_3_experience_replay_dqn](stable_baseline_3_experience_replay_dqn.ipynb) | HER, goal-conditioned RL | 40-45 min |

## Contenu detaille

### Notebook 1 - Introduction avec PPO et CartPole

| Section | Contenu |
|---------|---------|
| Stable Baselines3 | Installation, API de base |
| CartPole-v1 | Environnement classique, actions discretes |
| PPO | Proximal Policy Optimization |
| Workflow | Training → Evaluation → Video recording |

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

## Algorithmes couverts

| Algorithme | Type | Notebook | Utilisation |
|------------|------|----------|-------------|
| **PPO** | On-policy | 1, 2 | Controle general, robuste |
| **A2C** | On-policy | 2 | Alternative a PPO |
| **SAC** | Off-policy | 3 | Actions continues |
| **DDPG** | Off-policy | 3 | Actions continues |
| **HER** | Replay strategy | 3 | Goal-conditioned tasks |

## Environnements

| Environnement | Type | Notebook |
|---------------|------|----------|
| CartPole-v1 | Controle classique, discret | 1 |
| Pendulum-v1 | Controle continu | 2 |
| Parking-v0 | Goal-conditioned, continu | 3 |

## Prerequisites

### Connaissances requises

- Python intermediaire (classes, numpy)
- Concepts RL de base (agent, environnement, reward)
- Pas d'experience RL prealable necessaire pour le notebook 1

### Installation

```bash
# Environnement Python
python -m venv venv
venv\Scripts\activate  # Windows

# Dependances de base
pip install "stable-baselines3[extra]>=2.0.0a4" gymnasium

# Pour le notebook 3 (parking environment)
pip install highway-env moviepy
```

### Dependances

| Package | Version | Utilisation |
|---------|---------|-------------|
| stable-baselines3 | >=2.0.0a4 | Algorithmes RL |
| gymnasium | latest | Interface environnements |
| highway-env | latest | Parking-v0 (notebook 3) |
| moviepy | latest | Enregistrement video |

## Parcours recommande

```
Notebook 1 (Bases)
    ↓
Notebook 2 (Production features)
    ↓
Notebook 3 (Goal-conditioned RL)
```

| Objectif | Notebooks |
|----------|-----------|
| Decouverte rapide | 1 uniquement |
| Fondations completes | 1 + 2 |
| Maitrise | 1 + 2 + 3 |

## Concepts cles

| Concept | Description |
|---------|-------------|
| **Agent** | Entite qui apprend et prend des decisions |
| **Environnement** | Monde avec lequel l'agent interagit |
| **Reward** | Signal de feedback pour l'apprentissage |
| **Policy** | Strategie de l'agent (state → action) |
| **Value function** | Estimation des rewards futurs |
| **Experience replay** | Reutilisation des experiences passees |
| **HER** | Reinterpretation d'echecs comme succes |

## Caracteristiques

- **Compatible Windows** : Pas de dependance xvfb
- **Debutant-friendly** : Progression pedagogique
- **Production-ready** : Checkpointing, monitoring
- **Hyperparametres** : Commentaires pour experimentation

## Ressources

### Documentation

- [Stable Baselines3 Docs](https://stable-baselines3.readthedocs.io/)
- [Gymnasium Docs](https://gymnasium.farama.org/)
- [Highway-env Docs](https://highway-env.readthedocs.io/)

### Theorie RL

- Sutton & Barto - *Reinforcement Learning: An Introduction* (2nd ed.)
- [Spinning Up in Deep RL](https://spinningup.openai.com/)

## Structure des fichiers

```
RL/
├── stable_baseline_1_intro_cartpole.ipynb
├── stable_baseline_2_wrappers_sauvegarde_callbacks.ipynb
├── stable_baseline_3_experience_replay_dqn.ipynb
└── README.md
```

## Licence

Voir la licence du repository principal.
