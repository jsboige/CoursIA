# -*- coding: utf-8 -*-
"""Tests du module examples/prisoners_dilemma.py (GameTheory-2/4).

Backing notebooks : GameTheory-2-NormalForm.ipynb, GameTheory-4-NashEquilibrium.ipynb.

Le module expose trois fonctions : ``create_prisoners_dilemma`` (matrices de
gains canoniques), ``analyze_dominance`` (detection de stratégies strictement
dominantes, logique pure sans dependance), ``find_nash_equilibria`` (equilibres
de Nash via nashpy). Ces tests assertent des **invariants de theorie des jeux
connus** (pas seulement l'absence de crash) :

1. La structure canonique du Dilemme du Prisonnier : T > R > P > S (Temtpation,
   Reward, Punishment, Sucker) — l'inegalite qui DEFINIT un PD.
2. La symetrie : le PD canonique est un jeu symetrique (B = A^T).
3. La dominance stricte : Defect domine strictement Cooperate pour les DEUX
   joueurs (pourquoi (D,D) est l'issue rationnelle individualiste).
4. Un jeu SANS dominance (matching pennies) -> analyse vide (c'est un jeu a
   strategie mixte, pas de dominance pure).
5. La dominance peut etre asymetrique (un seul joueur domine).
6. L'equilibre de Nash du PD canonique est l'unique equilibre pur (D, D) —
   Pareto-inferieur a (C,C), coeur du paradoxe.

nashpy (outil SOTA de calcul d'equilibres) est installe localement (regle F) ;
``find_nash_equilibria`` renvoie ``None`` si nashpy est absent (degradation
honnete, contrat teste).
"""

import sys
from pathlib import Path

import numpy as np
import pytest

# Rendre le sous-repertoire examples/ importable (pas de __init__.py).
sys.path.insert(0, str(Path(__file__).parent.parent / "examples"))

import prisoners_dilemma as pd  # noqa: E402


# ----------------------------------------------------------- structure canonique
def test_create_prisoners_dilemma_canonical_values():
    """Les matrices canoniques portent T=5, R=3, P=1, S=0 (l'exemple standard
    du module). A = joueur ligne, B = joueur colonne."""
    A, B = pd.create_prisoners_dilemma()
    assert A.shape == (2, 2) and B.shape == (2, 2)
    # A[ligne, colonne] : C/C=3, C/D=0, D/C=5, D/D=1
    assert np.array_equal(A, [[3, 0], [5, 1]])
    # B[ligne, colonne] : C/C=3, C/D=5, D/C=0, D/D=1
    assert np.array_equal(B, [[3, 5], [0, 1]])


def test_create_prisoners_dilemma_satisfies_pd_inequality():
    """L'inegalite T > R > P > S DEFINIT un Dilemme du Prisonnier. Sans elle,
    ce n'est pas un PD (les incitations a faire defection s'effondrent)."""
    A, _ = pd.create_prisoners_dilemma()
    T = A[1, 0]   # Temptation (Defect vs Cooperate)
    R = A[0, 0]   # Reward (Cooperate vs Cooperate)
    P = A[1, 1]   # Punishment (Defect vs Defect)
    S = A[0, 1]   # Sucker (Cooperate vs Defect)
    assert T > R > P > S


def test_create_prisoners_dilemma_is_symmetric():
    """Le PD canonique est un jeu SYMETRIQUE : les deux joueurs ont la meme
    structure de gains, B = A transpose."""
    A, B = pd.create_prisoners_dilemma()
    assert np.array_equal(B, A.T)


# ----------------------------------------------------------- dominance
def test_analyze_dominance_detects_both_players():
    """Sur le PD canonique, Defect domine STRICTEMENT Cooperate pour les deux
    joueurs -> 2 constats."""
    A, B = pd.create_prisoners_dilemma()
    results = pd.analyze_dominance(A, B)
    assert len(results) == 2
    assert all("strictly dominates" in r for r in results)
    assert any("Player 1" in r for r in results)
    assert any("Player 2" in r for r in results)


def test_analyze_dominance_no_dominance_in_matching_pennies():
    """Matching pennies est un jeu a somme nulle SANS dominance stricte (chaque
    joueur a interet a etre imprevisible -> strategie mixte). L'analyse doit
    etre vide."""
    Mp = np.array([[1, -1], [-1, 1]])   # joueur ligne
    Mn = np.array([[-1, 1], [1, -1]])   # joueur colonne (somme nulle)
    assert pd.analyze_dominance(Mp, Mn) == []


def test_analyze_dominance_asymmetric_single_player():
    """Un jeu ou seul le joueur 1 a une strategie dominante -> 1 seul constat.
    Construction : joueur 1 a D > C dans les deux colonnes ; joueur 2 est
    indifferent (pas de dominance)."""
    # joueur 1 (A) : Defect bat Cooperate dans les deux colonnes (5>3, 4>2)
    A = np.array([[3, 2], [5, 4]])
    # joueur 2 (B) : pas de dominance (C bat D dans col? on rend indiff.)
    B = np.array([[2, 1], [1, 2]])   # B[0,1]=1 > B[0,0]=2 ? non ; B[1,1]=2 > B[1,0]=1
    results = pd.analyze_dominance(A, B)
    assert len(results) == 1
    assert "Player 1" in results[0]
    assert "Player 2" not in results[0]


# ----------------------------------------------------------- equilibre de Nash
@pytest.mark.skipif(not pd.HAS_NASHPY, reason="nashpy requis pour l'equilibre de Nash")
def test_find_nash_equilibria_pd_is_defect_defect():
    """L'unique equilibre de Nash du PD canonique est (Defect, Defect) pur --
    la strategie mixte [0 C, 1 D] pour les deux joueurs. C'est le paradoxe :
    (D,D) est Pareto-inferieur a (C,C) mais est l'issue rationnelle."""
    A, B = pd.create_prisoners_dilemma()
    equilibria = pd.find_nash_equilibria(A, B)
    assert equilibria is not None
    assert len(equilibria) == 1
    s1, s2 = equilibria[0]
    # (D, D) pur : probabilite 1 sur Defect (index 1) pour les deux.
    assert np.allclose(s1, [0.0, 1.0])
    assert np.allclose(s2, [0.0, 1.0])


def test_find_nash_equilibria_returns_list_type():
    """find_nash_equilibria renvoie une liste (eventuellement vide) quand
    nashpy est disponible, None sinon (degradation honnete du module)."""
    A, B = pd.create_prisoners_dilemma()
    result = pd.find_nash_equilibria(A, B)
    if pd.HAS_NASHPY:
        assert isinstance(result, list)
    else:
        assert result is None
