import json

notebooks = [
    {
        'path': r'D:\Dev\CoursIA\MyIA.AI.Notebooks\GameTheory\GameTheory-7-ExtensiveForm.ipynb',
        'exercise': {
            'md': '''---

## Exercice : Construction d'un arbre de jeu

**Objectifs** :
1. Construire un arbre de jeu sequentiel a 3 joueurs
2. Identifier les ensembles d'information
3. Calculer les equilibres de Nash en strategies comportementales

**Contexte** : Trois firmes (A, B, C) choisissent sequentiellement d'entrer ou non sur un marche. La firme A decide en premier, puis B observe le choix de A, puis C observe les choix de A et B.

**Questions** :
1. Dessinez l'arbre de jeu complet avec les gains
2. Quels sont les ensembles d'information ?
3. Trouvez l'equilibre de Nash en strategies comportementales
''',
            'code': '''# Exercice : Construction d'arbre de jeu

# TODO: Definir la structure de l'arbre
# Chaque noeud: {'player': int, 'children': dict, 'payoffs': tuple}

# tree = {
#     'player': 0,  # Joueur A (racine)
#     'actions': {
#         'Enter': {...},
#         'Stay': {...}
#     }
# }

# TODO: Implementer une fonction pour afficher l'arbre
# def print_tree(node, indent=0):
#     ...

# TODO: Implementer la recherche d'equilibres (backward induction)
# def find_equilibrium(tree):
#     ...

# TODO: Afficher l'equilibre trouve
# equilibrium = find_equilibrium(tree)
# print(f"Equilibre: {equilibrium}")
'''
        }
    },
    {
        'path': r'D:\Dev\CoursIA\MyIA.AI.Notebooks\GameTheory\GameTheory-9-BackwardInduction.ipynb',
        'exercise': {
            'md': '''---

## Exercice : Backward Induction sur un jeu sequentiel

**Objectifs** :
1. Appliquer l'algorithme de backward induction
2. Identifier l'equilibre parfait en sous-jeux (SPE)
3. Comparer avec l'equilibre de Nash standard

**Contexte** : Un jeu d'ultimatum modifie avec 3 tours. Le proposeur offre une fraction x, le repondeur accepte ou refuse. Si refus, le proposeur peut faire une nouvelle offre.

**Questions** :
1. Tracez l'arbre et appliquez backward induction
2. L'equilibre est-il unique ?
3. Comment le resultat change-t-il avec un horizon infini ?
''',
            'code': '''# Exercice : Backward Induction

# TODO: Definir le jeu d'ultimatum a 3 tours
# Etats: (tour, offre_actuelle, reponse)
# Actions: accepter/refuser, ajuster offre

# class UltimatumGame:
#     def __init__(self, total_value=100, rounds=3):
#         ...
#
#     def get_subgame_perfect_equilibrium(self):
#         # Backward induction
#         ...

# TODO: Implementer backward induction
# game = UltimatumGame(rounds=3)
# spe = game.get_subgame_perfect_equilibrium()

# TODO: Analyser la sensibilite au nombre de tours
# for rounds in [2, 3, 5, 10]:
#     game = UltimatumGame(rounds=rounds)
#     print(f"Rounds={rounds}: SPE = {game.get_subgame_perfect_equilibrium()}")
'''
        }
    },
    {
        'path': r'D:\Dev\CoursIA\MyIA.AI.Notebooks\GameTheory\GameTheory-10-ForwardInduction-SPE.ipynb',
        'exercise': {
            'md': '''---

## Exercice : Identification des SPE

**Objectifs** :
1. Distinguer Nash equilibria des SPE
2. Appliquer forward induction pour eliminer les equilibres non credibles
3. Analyser un jeu de signaux

**Contexte** : Un jeu d'entree sur un marche avec signal. L'entrant peut signaler fort ou faible. L'incumbent observe le signal et decide de combattre ou accommoder.

**Questions** :
1. Identifiez tous les equilibres de Nash
2. Lesquels sont des SPE ?
3. Comment forward induction selectionne-t-elle l'equilibre ?
''',
            'code': '''# Exercice : Forward Induction et SPE

# TODO: Modeliser le jeu d'entree avec signaux
# Joueur 1 (Entrant): signaler 'Fort' ou 'Faible', puis entrer ou non
# Joueur 2 (Incumbent): observer signal, combattre ou accommoder

# payoffs = {
#     ('Fort', 'Enter', 'Fight'): (p1, p2),
#     ('Fort', 'Enter', 'Accommodate'): (p1, p2),
#     ...
# }

# TODO: Trouver tous les equilibres de Nash
# def find_all_nash(payoffs):
#     ...

# TODO: Filtrer pour garder seulement les SPE
# def filter_spe(nash_equilibria):
#     ...

# TODO: Appliquer forward induction
# def forward_induction_selection(spe_list):
#     ...

# print(f"Equilibres Nash: {find_all_nash(payoffs)}")
# print(f"SPE: {filter_spe(...)}")
# print(f"Selection forward: {forward_induction_selection(...)}")
'''
        }
    },
    {
        'path': r'D:\Dev\CoursIA\MyIA.AI.Notebooks\GameTheory\GameTheory-11-BayesianGames.ipynb',
        'exercise': {
            'md': '''---

## Exercice : Calcul d'un BNE (Bayesian Nash Equilibrium)

**Objectifs** :
1. Modeliser un jeu avec information incomplete
2. Calculer les croyances a priori
3. Trouver l'equilibre Bayesien

**Contexte** : Enchere first-price a deux joueurs. Chaque joueur a une valeur privee v_i ~ U[0,1]. Les joueurs soumettent des offres b_i simultanement.

**Questions** :
1. Quelle est la strategie optimale d'encheres ?
2. Quel est l'equilibre Bayesien symetrique ?
3. Comment le resultat change-t-il avec N joueurs ?
''',
            'code': '''# Exercice : Enchere Bayesienne

import numpy as np
from scipy import integrate

# TODO: Definir le jeu d'enchere
# class FirstPriceAuction:
#     def __init__(self, n_players=2):
#         self.n = n_players
#
#     def expected_payoff(self, bid, value, strategy_other):
#         # Calculer le gain espere
#         ...

# TODO: Trouver la strategie d'equilibre symetrique
# Pour une enchere first-price: b*(v) = (n-1)/n * v

# def equilibrium_bid(value, n_players):
#     return (n_players - 1) / n_players * value

# TODO: Verifier que c'est un BNE
# def verify_bne(strategy, n_players):
#     # Pour chaque valeur v, verifier que la strategie est optimale
#     ...

# TODO: Simulation Monte Carlo
# n_sim = 10000
# values = np.random.uniform(0, 1, (n_sim, 2))
# bids = equilibrium_bid(values, 2)
# winner = np.argmax(bids, axis=1)
# ...
'''
        }
    },
    {
        'path': r'D:\Dev\CoursIA\MyIA.AI.Notebooks\GameTheory\GameTheory-12-ReputationGames.ipynb',
        'exercise': {
            'md': '''---

## Exercice : Paradoxe de la chaine de magasins

**Objectifs** :
1. Modeliser le paradoxe de Selten
2. Analyser l'effet de reputation avec types imperfaits
3. Comparer equilibrium theorique vs comportement observe

**Contexte** : Une chaine de magasins fait face a N entrants potentiels. L'incumbent peut etre "rationnel" (accommoder) ou "dur" (toujours combattre). Les entrants ne connaissent pas le type exact.

**Questions** :
1. Quel est l'equilibre avec information complete ?
2. Comment la possibilite d'etre "dur" change-t-elle l'equilibre ?
3. Combien de periodes l'incumbent rationnel maintient-il sa reputation ?
''',
            'code': '''# Exercice : Chain Store Paradox avec reputation

import numpy as np

# TODO: Definir les parametres du jeu
# N_ENTRANTS = 20
# P_HARD = 0.3  # Probabilite a priori que l'incumbent soit "dur"
#
# PAYOFFS = {
#     'hard': {'Fight': 0, 'Accommodate': -1},
#     'rational': {'Fight': -2, 'Accommodate': 1},
#     'entrant': {'Enter_if_fight': -2, 'Enter_if_accommodate': 2, 'Stay': 0}
# }

# TODO: Implementer la mise a jour des croyances (Bayes)
# def update_belief(prior, action):
#     # Si l'incumbent combat, augmenter P(hard)
#     # P(hard | Fight) = P(Fight | hard) * P(hard) / P(Fight)
#     ...

# TODO: Simuler le jeu avec mise a jour des croyances
# def simulate_chain_store(p_hard, n_entrants):
#     ...

# TODO: Analyser l'effet de la reputation
# for p in [0.1, 0.3, 0.5]:
#     result = simulate_chain_store(p, N_ENTRANTS)
#     print(f"P(hard)={p}: {result['fights']} combats sur {N_ENTRANTS}")
'''
        }
    },
    {
        'path': r'D:\Dev\CoursIA\MyIA.AI.Notebooks\GameTheory\GameTheory-14-DifferentialGames.ipynb',
        'exercise': {
            'md': '''---

## Exercice : Jeu differentiel linear-quadratic

**Objectifs** :
1. Formuler un jeu differentiel LQ
2. Resoudre les equations de Hamilton-Jacobi-Bellman
3. Comparer solution en boucle ouverte vs feedback

**Contexte** : Duopole avec ajustement dynamique des prix. Chaque firme ajuste son prix p_i(t) pour maximiser son profit integre, avec cout d'ajustement.

**Questions** :
1. Ecrivez les equations HJB pour chaque joueur
2. Quelle est la strategie feedback d'equilibre ?
3. Comment le cout d'ajustement affecte-t-il la dynamique ?
''',
            'code': '''# Exercice : Duopole dynamique LQ

import numpy as np
from scipy.integrate import solve_ivp

# TODO: Definir les parametres du duopole
# RHO = 0.95  # Facteur d'actualisation
# ALPHA = 1.0  # Sensibilite de la demande
# C = 0.5  # Cout marginal
# KAPPA = 0.1  # Cout d'ajustement

# TODO: Formuler le probleme LQ
# Etat: x(t) = [p1(t), p2(t)]
# Controle: u_i(t) = dp_i/dt
# Dynamique: dx/dt = u
# Objectif: max integral exp(-rho*t) * [profit_i - kappa*u_i^2] dt

# TODO: Resoudre les equations HJB
# Les strategies feedback sont lineaires: u_i = K * x
# Les equations Riccati donnent K

# def solve_lq_game(A, B, Q, R, rho):
#     # Resoudre le systeme d'equations de Riccati couplees
#     ...

# TODO: Simuler la trajectoire d'equilibre
# def simulate_equilibrium(x0, T, K):
#     ...

# TODO: Comparer avec la solution en boucle ouverte (Nash OL)
# print("Solution feedback vs open-loop:")
# ...
'''
        }
    }
]

for nb_info in notebooks:
    path = nb_info['path']

    try:
        with open(path, 'r', encoding='utf-8') as f:
            nb = json.load(f)

        # Create exercise cells
        md_cell = {
            'cell_type': 'markdown',
            'metadata': {},
            'source': nb_info['exercise']['md'].splitlines(keepends=True)
        }
        code_cell = {
            'cell_type': 'code',
            'metadata': {},
            'source': nb_info['exercise']['code'].splitlines(keepends=True),
            'execution_count': None,
            'outputs': []
        }

        # Insert before last cell
        nb['cells'].insert(-1, md_cell)
        nb['cells'].insert(-1, code_cell)

        # Save
        with open(path, 'w', encoding='utf-8') as f:
            json.dump(nb, f, ensure_ascii=False, indent=1)

        print(f"OK: {path.split(chr(92))[-1]}")
    except FileNotFoundError:
        print(f"NOT FOUND: {path}")
    except Exception as e:
        print(f"ERROR: {path} - {e}")

print("\nDone!")
