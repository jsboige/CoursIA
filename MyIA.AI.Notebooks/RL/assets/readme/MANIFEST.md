# MANIFEST des figures README

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

## rl4-bandits.png

- **Source** : notebook `rl_4_multi_armed_bandits.ipynb` (cellule 30, output 0)
- **Alt-text (FR)** : Bandits multi-bras : fréquence de sélection du meilleur bras (moyenne mobile 50) comparée entre stratégies (Greedy, epsilon-greedy 0.1/0.01, UCB c=2, aléatoire) sur 2000 pas.
- **Poids** : 76.1 KB (PIL optimisé)

## rl5-mdp-qlearning.png

- **Source** : notebook `rl_5_mdp_dp_qlearning.ipynb` (cellule 22, output 0)
- **Alt-text (FR)** : Q-Learning tabulaire sur FrozenLake : récompense moyenne lissée (fenêtre 500) croissant de 0 à ~0.9 sur ~4500 épisodes.
- **Poids** : 29.8 KB (PIL optimisé)

## rl10-reward-shaping.png

- **Source** : notebook `rl_10_reward_shaping.ipynb` (cellule 8, output 0)
- **Alt-text (FR)** : Reward shaping : vitesse d'apprentissage comparée (baseline sparse, potential-based, heuristique, curriculum), return en moyenne mobile 50 avec seuil de convergence à -30.
- **Poids** : 49.4 KB (PIL optimisé)

## rl12-distributional.png

- **Source** : notebook `rl_12_distributional_rl.ipynb` (cellule 16, output 0)
- **Alt-text (FR)** : C51 sur CartPole-v1 : courbe d'apprentissage (retour par épisode + moyenne glissante 20 culminant vers ~160) contre baseline aléatoire, ~300 épisodes.
- **Poids** : 71.8 KB (PIL optimisé)

## rl13-curiosity.png

- **Source** : notebook `rl_13_curiosity_exploration.ipynb` (cellule 12, output 0)
- **Alt-text (FR)** : Exploration par curiosité (RND) : récompense extrinsèque lissée (epsilon-greedy bloqué ~0.1 vs RND ~0.96) et histogramme des visites d'états sur la chaîne-piège.
- **Poids** : 52.3 KB (PIL optimisé)

## rl11-pomdp.png

- **Source** : notebook `rl_11_pomdp.ipynb` (cellule 15, output 1)
- **Alt-text (FR)** : POMDP Tiger Problem : récompense moyenne de six méthodes sur 5 seeds (Random -46.0, Open immédiat -6.2, Listen x1/x2, Q-MDP, Belief Q), diagramme en barres avec écart-types.
- **Poids** : 26.6 KB (PIL optimisé)
