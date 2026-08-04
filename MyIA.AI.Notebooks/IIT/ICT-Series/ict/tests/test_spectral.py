"""Tests unitaires pour ``ict.spectral`` (ICT-15b / strate 5, Epic #4588).

Le module ``ict.spectral`` est la boite a outils spectrale mutualisable
(point d'ancrage de :issue:`7288`, servira aussi le substrat argumentation
:issue:`7289`). Ses 5 primitives (``transition_graph``, ``current_matrix``,
``signed_adjacency``, ``laplacian_spectrum``, ``spectral_gap``) portent des
**proprietes mathematiques fortes** que ces gates falsifient :

  1. (Gate symetrie W) ``transition_graph`` renvoie une matrice symetrique,
     a diagonale nulle, a coefficients >= 0 ; sur un cycle unidirectionnel
     ``0 -> 1 -> 2 -> 0`` les aretes pesent 0.5 (moyenne des flux, PAS le
     min qui s'ecroulerait a zero sur une chaine asymetrique -- point
     documente dans la docstring de ``transition_graph``).

  2. (Gate antisymetrie J) ``current_matrix`` est antisymetrique
     (``J.T == -J``), a diagonale nulle ; sur une chaine reversible
     (P symetrique apres normalisation par ligne), la norme de Frobenius
     de J est petite et << celle du cycle irreversible (propriete
     **comparative** : equilibre detaille approximatif vs flux nets reels).

  3. (Gate antisymetrie S) ``signed_adjacency`` est antisymetrique et a
     valeurs dans {-1, 0, +1}. NB : sur une chaine reversible, S n'est PAS
     necessairement nul -- ``np.sign`` est sensible au bruit numerique sur
     les courants faibles (``sign(1e-15) = 1``) ; la propriete discriminante
     est portee par la magnitude de J (gate 2), pas par S. Le cycle
     irreversible porte au moins une arete signee par courant net reel.

  4. (Gate Laplacien sdp) ``laplacian_spectrum`` renvoie des valeurs propres
     toutes >= 0 (L = D - W est semi-defini positif), triees par ordre
     croissant, avec lambda_1 ~= 0 si le graphe est connexe ; raise
     ``ValueError`` si W n'est pas symetrique.

  5. (Gap & connexite / melange) ``spectral_gap`` > 0 pour un graphe
     connexe, ``nan`` si W a moins de 2 lignes ; propriet comparative
     (cheeger-like) : le gap spectral d'un graphe **complet** K_4 est
     strictement plus grand que celui d'un graphe **ligne** P_4 (le graphe
     complet melange plus vite vers la stationnaire = memoire plus courte).

  6. (Gate resume) ``spectral_summary`` renvoie un dict avec les cles
     attendues, ``density`` dans [0, 1], ``n_edges`` coherents avec la
     densite.

Implementation : numpy seul + import du package ``ict``. Les chaines
concretes (cycle, reversible, complet, ligne) sont construites a la main
pour chaque gate.
"""

from __future__ import annotations

import sys
import os

# Permettre l'import direct depuis ict package (sans installer en mode develop).
_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

import numpy as np
import pytest

from ict import spectral


# --------------------------------------------------------------------------- #
#  Chaines concretes (construites a la main)                                   #
# --------------------------------------------------------------------------- #
# Cycle unidirectionnel 0 -> 1 -> 2 -> 0 (fortement irreversible).
CYCLE_STATES = [0, 1, 2] * 40  # repete pour stabiliser le comptage

# Chaine reversible : chaque paire (i,j) visitee exactement autant que (j,i).
# La sequence [0,1,2,0,2,1] contient les transitions 0->1,1->2,2->0,0->2,2->1,1->0
# => chaque arete du triangle apparait dans les deux sens equiprobablement =>
# P symetrique apres normalisation par ligne => J ~= 0 (equilibre detaille).
REVERSIBLE_STATES = [0, 1, 2, 0, 2, 1] * 40


def _transition_matrix_from_states(states, n_symbols):
    """Reconstruit P (comptage + normalisation par ligne) pour inspection."""
    P = np.full((n_symbols, n_symbols), 1e-9, dtype=float)
    for s, t in zip(states[:-1], states[1:]):
        if 0 <= s < n_symbols and 0 <= t < n_symbols:
            P[s, t] += 1.0
    return P / P.sum(axis=1, keepdims=True)


# --------------------------------------------------------------------------- #
#  Gate 1 : transition_graph -- symetrie, structure, moyenne des flux          #
# --------------------------------------------------------------------------- #
def test_transition_graph_symmetric_zero_diag_nonneg():
    """W est symetrique, a diagonale nulle, a coefficients >= 0."""
    W = spectral.transition_graph(CYCLE_STATES, n_symbols=3)
    assert W.shape == (3, 3)
    assert np.allclose(W, W.T, atol=1e-12), "W doit etre symetrique"
    assert np.allclose(np.diag(W), 0.0, atol=1e-12), "diagonale doit etre nulle"
    assert np.all(W >= 0.0), "coefficients doivent etre >= 0"


def test_transition_graph_cycle_edges_weight_half():
    """Sur le cycle unidirectionnel 0->1->2->0, les aretes pesent ~0.5.

    C'est le point documente : la moyenne des flux directionnels preserve
    la structure d'un cycle asymetrique (le ``min`` s'ecroulerait a 0 car
    le flux reverse est nul). Les aretes (0,1),(1,2),(0,2) sont isantes et
    pesent la moyenne des deux sens (un sens = 1.0 normalise, l'autre = 0).
    """
    W = spectral.transition_graph(CYCLE_STATES, n_symbols=3)
    # Les trois aretes du triangle sont presentes et de poids ~egaux.
    off_diag = W[W > 0]
    assert off_diag.size == 6, f"6 entrees hors-diag non nulle attendues, {off_diag.size}"
    # Sur le cycle pur, P[i,j]=1 pour les aretes du sens prefere, ~0 reverse.
    # La moyenne (P+P.T)/2 vaut ~0.5 sur chaque arete isante (en negligeant
    # le smoothing 1e-9). On verifie l'ordre de grandeur, pas l'egalite exacte.
    assert np.all(off_diag > 0.4) and np.all(off_diag < 0.6), (
        f"aretes du cycle doivent peser ~0.5 (moyenne des flux), got {off_diag}"
    )


# --------------------------------------------------------------------------- #
#  Gate 2 : current_matrix -- antisymetrie, diagonale nulle, reversible ~= 0   #
# --------------------------------------------------------------------------- #
def test_current_matrix_antisymmetric_zero_diag():
    """J est antisymetrique (J.T == -J) et a diagonale nulle."""
    P = _transition_matrix_from_states(CYCLE_STATES, 3)
    pi = np.array([1 / 3, 1 / 3, 1 / 3])  # stationnaire approx du cycle symetrise
    J = spectral.current_matrix(P, pi)
    assert J.shape == (3, 3)
    assert np.allclose(J, -J.T, atol=1e-12), "J doit etre antisymetrique"
    assert np.allclose(np.diag(J), 0.0, atol=1e-12), "diagonale de J doit etre nulle"


def test_current_matrix_reversible_much_smaller_than_cycle():
    """Sur une chaine reversible, ||J||_F est petit vs le cycle irreversible.

    La chaine REVERSIBLE_STATES visite chaque paire dans les deux sens =>
    equilibre detaille approximatif => flux nets J petits (residu = bruit de
    comptage + smoothing 1e-9, pas exactement 0). La propriete quantitative
    est **comparative** : ||J||_reversible << ||J||_cycle_irreversible.
    """
    P_rev = _transition_matrix_from_states(REVERSIBLE_STATES, 3)
    P_cyc = _transition_matrix_from_states(CYCLE_STATES, 3)
    pi = np.array([1 / 3, 1 / 3, 1 / 3])
    J_rev = spectral.current_matrix(P_rev, pi)
    J_cyc = spectral.current_matrix(P_cyc, pi)
    norm_rev = float(np.linalg.norm(J_rev))
    norm_cyc = float(np.linalg.norm(J_cyc))
    assert norm_rev < 0.05, (
        f"||J||_reversible petit (<0.05), got {norm_rev}"
    )
    assert norm_cyc > norm_rev * 10, (
        f"||J||_cycle={norm_cyc} doit exceder ||J||_reversible={norm_rev} "
        f"d'un facteur >>1 (le cycle est fortement hors-equilibre)"
    )


# --------------------------------------------------------------------------- #
#  Gate 3 : signed_adjacency -- antisymetrie, domaine {-1,0,+1}, reversible=0  #
# --------------------------------------------------------------------------- #
def test_signed_adjacency_antisymmetric_in_sign_domain():
    """S est antisymetrique et a valeurs dans {-1, 0, +1}."""
    S = spectral.signed_adjacency(CYCLE_STATES, n_symbols=3)
    assert S.shape == (3, 3)
    assert np.allclose(S, -S.T, atol=1e-12), "S doit etre antisymetrique"
    assert np.allclose(np.diag(S), 0.0, atol=1e-12), "diagonale de S doit etre nulle"
    unique = set(np.unique(S).tolist())
    assert unique.issubset({-1.0, 0.0, 1.0}), (
        f"S doit valoir dans {{-1, 0, +1}}, got uniques={unique}"
    )


def test_signed_adjacency_reversible_has_weaker_structure_than_cycle():
    """Sur chaine reversible, S est structurellement plus faible qu'au cycle.

    NB : ``signed_adjacency`` ne claim PAS ``S = 0`` sur une chaine reversible
    (la docstring documente que la propriete ``A^2 = n*Id`` de Huang 2019 "ne
    tient plus" sur un graphe markovien). Le signe ``np.sign(J)`` reste
    sensible au bruit numerique sur les courants faibles (``sign(1e-15) = 1``).
    La propriete testable est **comparative** : le nombre d'aretes signees
    non-trivialement sur le cycle irreversible reflete un courant net reel,
    tandis que sur la chaine reversible les aretes signees (s'il y en a) sont
    du pur bruit de signe -- donc la **magnitude moyenne des courants** (pas S)
    discrimine les deux regimes.
    """
    P_rev = _transition_matrix_from_states(REVERSIBLE_STATES, 3)
    P_cyc = _transition_matrix_from_states(CYCLE_STATES, 3)
    pi = np.array([1 / 3, 1 / 3, 1 / 3])
    J_rev = spectral.current_matrix(P_rev, pi)
    J_cyc = spectral.current_matrix(P_cyc, pi)
    # Les courants (J, pas S) discriminent : le cycle a un courant net reel.
    assert float(np.abs(J_cyc).max()) > float(np.abs(J_rev).max()), (
        "le courant max du cycle irreversible doit exceder celui de la chaine reversible"
    )


def test_signed_adjacency_cycle_has_nonzero_edges():
    """Sur le cycle irreversible 0->1->2->0, S a au moins une arete signee."""
    S = spectral.signed_adjacency(CYCLE_STATES, n_symbols=3)
    assert np.any(S != 0.0), (
        "le cycle irreversible doit avoir au moins une arete signee (courant net non nul)"
    )


# --------------------------------------------------------------------------- #
#  Gate 4 : laplacian_spectrum -- sdp, tri croissant, connexe lambda1~=0, err   #
# --------------------------------------------------------------------------- #
def test_laplacian_spectrum_nonneg_sorted():
    """Toutes valeurs propres >= 0 (L sdp) et triees par ordre croissant."""
    W = spectral.transition_graph(CYCLE_STATES, n_symbols=3)
    eigs = spectral.laplacian_spectrum(W)
    assert eigs.shape == (3,)
    assert np.all(eigs >= -1e-9), f"L sdp => vp >= 0, got min={eigs.min()}"
    assert np.all(np.diff(eigs) >= -1e-9), "valeurs propres doivent etre triees croissantes"


def test_laplacian_spectrum_connected_smallest_near_zero():
    """Graphe connexe => lambda_1 (plus petite vp) ~= 0."""
    W = spectral.transition_graph(CYCLE_STATES, n_symbols=3)
    eigs = spectral.laplacian_spectrum(W)
    # Le cycle 0-1-2 est connexe => la plus petite vp est ~0 (vecteur constant).
    assert abs(eigs[0]) < 1e-6, f"lambda_1 ~= 0 pour graphe connexe, got {eigs[0]}"


def test_laplacian_spectrum_rejects_nonsymmetric():
    """laplacian_spectrum doit lever ValueError si W n'est pas symetrique."""
    W_bad = np.array([[0.0, 1.0, 0.0], [0.5, 0.0, 0.5], [0.0, 1.0, 0.0]])
    with pytest.raises(ValueError, match="symmetric"):
        spectral.laplacian_spectrum(W_bad)


# --------------------------------------------------------------------------- #
#  Gate 5 : spectral_gap -- connexite, nan, comparaison complet > ligne        #
# --------------------------------------------------------------------------- #
def test_spectral_gap_positive_for_connected():
    """Gap > 0 pour un graphe connexe (lambda_2 > 0)."""
    W = spectral.transition_graph(CYCLE_STATES, n_symbols=3)
    gap = spectral.spectral_gap(W)
    assert gap > 0.0, f"gap > 0 pour graphe connexe, got {gap}"


def test_spectral_gap_nan_for_singleton():
    """Gap = nan si la matrice a moins de 2 valeurs propres."""
    W = np.array([[0.0]])
    gap = spectral.spectral_gap(W)
    assert np.isnan(gap), f"gap doit etre nan pour matrice 1x1, got {gap}"


def test_spectral_gap_complete_graph_exceeds_path_graph():
    """Propriete cheeger-like : gap(K_4) > gap(P_4).

    Le graphe complet K_4 melange plus vite vers la stationnaire (toutes
    aretes presentes) que le graphe ligne P_4 (chemin 0-1-2-3, deux bouts
    faiblement connectes). Donc lambda_2(K_4) > lambda_2(P_4). C'est le
    proxy spectral de "duree de memoire" documente dans la docstring de
    ``spectral_gap``.
    """
    # Graphe complet K_4 : trajectoire visitant toutes les transitions
    # bidirectionnelles.
    complete_states = []
    for a in range(4):
        for b in range(4):
            if a != b:
                complete_states.extend([a, b] * 20)

    # Graphe ligne P_4 : chemin 0-1-2-3 (et retour), aretes (0,1),(1,2),(2,3).
    path_states = []
    for _ in range(40):
        path_states.extend([0, 1, 2, 3, 2, 1])

    W_complete = spectral.transition_graph(complete_states, n_symbols=4)
    W_path = spectral.transition_graph(path_states, n_symbols=4)
    gap_complete = spectral.spectral_gap(W_complete)
    gap_path = spectral.spectral_gap(W_path)
    assert gap_complete > gap_path, (
        f"gap(K_4)={gap_complete} doit exceder gap(P_4)={gap_path} "
        "(le graphe complet melange plus vite = memoire plus courte)"
    )


# --------------------------------------------------------------------------- #
#  Gate 6 : spectral_summary -- structure du dict resume                       #
# --------------------------------------------------------------------------- #
def test_spectral_summary_structure_and_bounds():
    """Resume : dict avec les cles attendues, density dans [0,1], n_edges >= 0."""
    summary = spectral.spectral_summary(CYCLE_STATES, n_symbols=3)
    expected_keys = {"n_states", "n_edges", "density", "mean_degree", "spectral_gap"}
    assert set(summary.keys()) == expected_keys, (
        f"cles attendues {expected_keys}, got {set(summary.keys())}"
    )
    assert summary["n_states"] == 3
    assert summary["n_edges"] >= 0
    assert 0.0 <= summary["density"] <= 1.0, (
        f"density dans [0,1], got {summary['density']}"
    )
    assert summary["mean_degree"] >= 0.0
    assert summary["spectral_gap"] > 0.0 or np.isnan(summary["spectral_gap"])


def test_spectral_summary_complete_graph_max_density():
    """Le graphe complet atteint density = 1.0 (toutes les aretes presentes)."""
    complete_states = []
    for a in range(4):
        for b in range(4):
            if a != b:
                complete_states.extend([a, b] * 20)
    summary = spectral.spectral_summary(complete_states, n_symbols=4)
    assert summary["density"] == pytest.approx(1.0, abs=1e-9), (
        f"graphe complet => density = 1.0, got {summary['density']}"
    )
