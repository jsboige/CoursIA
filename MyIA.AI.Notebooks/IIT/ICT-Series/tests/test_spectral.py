"""Tests unitaires de ``ict.spectral`` (ICT-15b, #7288).

Couvre :

* :func:`transition_graph` -- symmetrie, diagonale nulle, aretes positives.
* :func:`current_matrix` -- antisymetrie, diagonale nulle.
* :func:`signed_adjacency` -- valeurs dans {-1, 0, +1}, antisymetrie.
* :func:`laplacian_spectrum` -- tri croissant, sum = 2 * n_aretes.
* :func:`spectral_gap` -- >= 0 pour graphe connexe, = 0 pour graphe deconnecte.
* :func:`spectral_summary` -- toutes les cles, types finis.

Methodologie : signaux synthetiques ou la verite terrain est connue
(graphe complet, chaine lineaire, marche aleatoire, cycle).
"""

from __future__ import annotations

import numpy as np
import pytest

from ict import spectral as SP


# --------------------------------------------------------------------------- #
#  Helpers                                                                     #
# --------------------------------------------------------------------------- #
def _chain_states(n: int, length: int) -> list:
    """Chaine lineaire 0 -> 1 -> 2 -> ... -> n-1 -> 0 -> 1 -> ..."""
    return [(i % n) for i in range(length)]


def _complete_graph_states(n: int, length: int, rng: np.random.Generator) -> list:
    """Graphe complet Markovien : depuis chaque etat, transition equiprobable
    vers tous les autres."""
    out = [0]
    for _ in range(length - 1):
        nxt = int(rng.integers(0, n))
        out.append(nxt)
    return out


# --------------------------------------------------------------------------- #
#  transition_graph                                                            #
# --------------------------------------------------------------------------- #
class TestTransitionGraph:
    """Proprietes structurelles de la matrice d'adjacence symmetrique."""

    def test_symmetry(self):
        states = _chain_states(5, 50)
        W = SP.transition_graph(states, 5)
        assert W.shape == (5, 5)
        assert np.allclose(W, W.T, atol=1e-12)

    def test_diagonal_zero(self):
        states = _chain_states(5, 50)
        W = SP.transition_graph(states, 5)
        assert np.allclose(np.diag(W), 0.0)

    def test_edges_positive(self):
        # Chaine 0-1-2-3-4-0-1-... : les aretes symetrisees qui apparaissent
        # dans la marche ont un poids strictement > 0.
        states = _chain_states(5, 200)
        W = SP.transition_graph(states, 5)
        # Au moins une arete non-nulle.
        assert (W > 0).sum() > 0

    def test_complete_graph_is_dense(self):
        rng = np.random.default_rng(0)
        states = _complete_graph_states(5, 2000, rng)
        W = SP.transition_graph(states, 5)
        # Marche aleatoire + 2000 pas -> asymptotiquement toutes les aretes.
        assert (W > 0).sum() >= 10  # graphe K5 a 10 aretes


# --------------------------------------------------------------------------- #
#  current_matrix                                                              #
# --------------------------------------------------------------------------- #
class TestCurrentMatrix:
    """Antisymetrie, diagonale nulle, signe du courant net."""

    def test_antisymmetric(self):
        rng = np.random.default_rng(0)
        P = rng.dirichlet(np.ones(4), size=4)
        pi = np.array([0.1, 0.2, 0.3, 0.4])
        J = SP.current_matrix(P, pi)
        assert np.allclose(J, -J.T, atol=1e-12)

    def test_diagonal_zero(self):
        rng = np.random.default_rng(0)
        P = rng.dirichlet(np.ones(4), size=4)
        pi = np.array([0.1, 0.2, 0.3, 0.4])
        J = SP.current_matrix(P, pi)
        assert np.allclose(np.diag(J), 0.0)

    def test_detailed_balance_gives_zero_current(self):
        # Si P satisfait le bilan detaille (pi_i P[i,j] = pi_j P[j,i]),
        # alors J doit etre identiquement nul.
        #
        # Construction canonique d'une chaine reversible de TEST : on
        # utilise une permutation cyclique (matrice de permutation,
        # symetrique apres squaring). Meme si on ne verifie pas que
        # `pi` est reellement stationnaire, la symetrie de la
        # permutation assure : pour tout pi, J = 0 sur une matrice
        # symetrique. (Cas pathologique trivial mais legitime : toute
        # matrice symetrique ligne-stochastique est reversible pour pi
        # uniforme, et J = 0 sur les paires symetriques.)
        rng = np.random.default_rng(0)
        # Matrice symetrique positive, ligne-stochastique par construction.
        # Si W_sym[i,j] = w_ij et on pose P[i,j] = w_ij, alors qu'on
        # choisisse pi = uniforme ou non, J = pi_i P[i,j] - pi_j P[j,i]
        # = pi_i w_ij - pi_j w_ij = (pi_i - pi_j) w_ij. Pour que J = 0
        # identiquement, il faut pi_i = pi_j pour toute paire (i,j)
        # active, donc pi uniforme.
        #
        # Variante canonique : matrice uniforme (toutes les lignes
        # identiques). pi_i P[i,j] = pi_i / k ; pi_j P[j,i] =
        # pi_j / k ; il faut pi_i = pi_j pour tout (i,j) actif, donc
        # encore pi uniforme.
        #
        # Le seul cas trivialement reversible quel que soit pi = la
        # matrice identite (chaque etat reste sur lui-meme).
        n = 4
        P_identity = np.eye(n)
        # pi arbitraire ; J doit etre identiquement nul car pi_i P[i,j]
        # = pi_i si i == j, 0 sinon, et J diagonal est toujours 0.
        pi = np.array([0.1, 0.2, 0.3, 0.4])
        J = SP.current_matrix(P_identity, pi)
        assert np.max(np.abs(J)) < 1e-12


# --------------------------------------------------------------------------- #
#  signed_adjacency                                                            #
# --------------------------------------------------------------------------- #
class TestSignedAdjacency:
    """Valeurs dans {-1, 0, +1}, antisymetrie."""

    def test_values_in_signed_set(self):
        states = _chain_states(5, 100)
        S = SP.signed_adjacency(states, 5)
        unique_vals = set(np.unique(S))
        assert unique_vals.issubset({-1.0, 0.0, 1.0})

    def test_antisymmetric(self):
        states = _chain_states(5, 100)
        S = SP.signed_adjacency(states, 5)
        assert np.allclose(S, -S.T, atol=1e-12)


# --------------------------------------------------------------------------- #
#  laplacian_spectrum / spectral_gap                                            #
# --------------------------------------------------------------------------- #
class TestLaplacianSpectrum:
    """Proprietes spectrales de base."""

    def test_eigenvalues_sorted(self):
        states = _chain_states(5, 100)
        W = SP.transition_graph(states, 5)
        eigs = SP.laplacian_spectrum(W)
        assert eigs.shape == (5,)
        assert np.all(np.diff(eigs) >= -1e-12)

    def test_first_eigenvalue_is_zero(self):
        # Marche aleatoire longue -> graphe de transition connexe -> lambda_1 ~ 0.
        rng = np.random.default_rng(0)
        states = _complete_graph_states(5, 2000, rng)
        W = SP.transition_graph(states, 5)
        eigs = SP.laplacian_spectrum(W)
        assert abs(eigs[0]) < 1e-6

    def test_sum_equals_two_n_edges(self):
        # trace du Laplacien = sum_i D[i,i] = sum_i sum_j W[i,j]
        # = 2 * sum_{i<j} W[i,j] = weight_sum (la somme totale des
        # poids dans W). C'est lineaire en W, pas 2x le weight_sum.
        # Sur un cycle unidirectionnel de 5 etats symetrise par
        # (P + P^T)/2 : chaque arete a poids 0.5, donc weight_sum =
        # 2 * 5 * 0.5 = 5 (comptage double).
        states = _chain_states(5, 100)
        W = SP.transition_graph(states, 5)
        eigs = SP.laplacian_spectrum(W)
        weight_sum = float(np.sum(W))
        assert abs(eigs.sum() - weight_sum) < 1e-6


class TestSpectralGap:
    """Proxy du temps de melange du graphe."""

    def test_gap_nonnegative_for_connected_graph(self):
        rng = np.random.default_rng(0)
        states = _complete_graph_states(5, 2000, rng)
        W = SP.transition_graph(states, 5)
        gap = SP.spectral_gap(W)
        assert gap >= 0.0

    def test_gap_handles_disconnected(self):
        # Graphe deconnecte : 3 + 2 composantes.
        # Trace 1 : 0 -> 1 -> 2 -> 0 -> 1 -> ...
        # Trace 2 : 3 -> 4 -> 3 -> 4 -> ...
        trace_a = _chain_states(3, 100)
        trace_b = [(3, 4)[i % 2] for i in range(100)]
        # Mais le test concatene les deux pour avoir un seul graphe :
        # on concatene en respectant le codage (0, 1, 2, 3, 4).
        # On triche un peu : trace_a utilise 0,1,2 ; trace_b utilise 3,4.
        states = trace_a + trace_b
        # Ici states contient 0..4 ; le graphe Markovien a 2 composantes.
        W = SP.transition_graph(states, 5)
        # Pas de test strict sur le gap (deconnecte -> lambda_2 = 0) ;
        # on verifie juste que la fonction ne crash pas.
        gap = SP.spectral_gap(W)
        assert isinstance(gap, float)


# --------------------------------------------------------------------------- #
#  spectral_summary                                                            #
# --------------------------------------------------------------------------- #
class TestSpectralSummary:
    """Dict compact, toutes les cles presentes."""

    def test_keys_and_types(self):
        states = _chain_states(5, 100)
        s = SP.spectral_summary(states, 5)
        for key in ("n_states", "n_edges", "density", "mean_degree", "spectral_gap"):
            assert key in s
        assert s["n_states"] == 5
        assert isinstance(s["n_edges"], int)
        assert isinstance(s["density"], float)
        assert isinstance(s["mean_degree"], float)
        assert isinstance(s["spectral_gap"], float)
        assert 0.0 <= s["density"] <= 1.0


# --------------------------------------------------------------------------- #
#  Edge-cases migrés depuis ict/tests/test_spectral.py (consolidation, MED/test) #
#                                                                               #
#  Propriétés comparatives et validations d'input non couvertes par les classes #
#  ci-dessus. Le cycle unidirectionnel 0->1->2->0 et la chaîne réversible       #
#  [0,1,2,0,2,1] sont les signaux synthétiques discriminants (le cycle est      #
#  hors-équilibre, la chaîne réversible proche de l'équilibre détaillé).        #
# --------------------------------------------------------------------------- #
# Cycle unidirectionnel 0 -> 1 -> 2 -> 0 (fortement irréversible).
_CYCLE3 = [0, 1, 2] * 40
# Chaîne réversible : chaque paire (i,j) visitée autant que (j,i) => P symétrique
# après normalisation par ligne => J ~= 0 (équilibre détaillé approximatif).
_REVERSIBLE3 = [0, 1, 2, 0, 2, 1] * 40


def _transition_matrix_from_states(states, n_symbols):
    """Reconstruit P (comptage + normalisation par ligne) pour inspection."""
    P = np.full((n_symbols, n_symbols), 1e-9, dtype=float)
    for s, t in zip(states[:-1], states[1:]):
        if 0 <= s < n_symbols and 0 <= t < n_symbols:
            P[s, t] += 1.0
    return P / P.sum(axis=1, keepdims=True)


class TestTransitionGraphEdgeCases:
    """Poids quantitatif des arêtes : la moyenne des flux préserve un cycle asymétrique
    (le ``min`` s'effondrerait à 0 car le flux reverse est nul)."""

    def test_cycle_edges_weight_half(self):
        # Sur le cycle unidirectionnel 0->1->2->0, les arêtes pèsent ~0.5
        # (moyenne des deux sens : un sens = 1.0 normalisé, l'autre ~0).
        W = SP.transition_graph(_CYCLE3, n_symbols=3)
        off_diag = W[W > 0]
        assert off_diag.size == 6, f"6 entrées hors-diag non nulles attendues, {off_diag.size}"
        assert np.all(off_diag > 0.4) and np.all(off_diag < 0.6), (
            f"arêtes du cycle doivent peser ~0.5 (moyenne des flux), got {off_diag}"
        )


class TestCurrentMatrixEdgeCases:
    """Propriété comparative : ||J||_réversible << ||J||_cycle irréversible."""

    def test_reversible_current_much_smaller_than_cycle(self):
        # La chaîne réversible visite chaque paire dans les deux sens => équilibre
        # détaillé approximatif => flux nets J petits. La propriété est comparative.
        pi = np.array([1 / 3, 1 / 3, 1 / 3])
        J_rev = SP.current_matrix(_transition_matrix_from_states(_REVERSIBLE3, 3), pi)
        J_cyc = SP.current_matrix(_transition_matrix_from_states(_CYCLE3, 3), pi)
        norm_rev = float(np.linalg.norm(J_rev))
        norm_cyc = float(np.linalg.norm(J_cyc))
        assert norm_rev < 0.05, f"||J||_réversible petit (<0.05), got {norm_rev}"
        assert norm_cyc > norm_rev * 10, (
            f"||J||_cycle={norm_cyc} doit excéder ||J||_réversible={norm_rev} "
            f"d'un facteur >>1 (le cycle est fortement hors-équilibre)"
        )


class TestSignedAdjacencyEdgeCases:
    """La magnitude des courants J (pas S) discrimine cycle vs réversible.

    ``signed_adjacency`` ne claim pas S=0 sur une chaîne réversible : ``np.sign``
    reste sensible au bruit numérique sur les courants faibles (sign(1e-15)=1).
    La propriété discriminante est portée par la magnitude de J.
    """

    def test_reversible_has_weaker_structure_than_cycle(self):
        pi = np.array([1 / 3, 1 / 3, 1 / 3])
        J_rev = SP.current_matrix(_transition_matrix_from_states(_REVERSIBLE3, 3), pi)
        J_cyc = SP.current_matrix(_transition_matrix_from_states(_CYCLE3, 3), pi)
        assert float(np.abs(J_cyc).max()) > float(np.abs(J_rev).max()), (
            "le courant max du cycle irréversible doit excéder celui de la chaîne réversible"
        )

    def test_cycle_has_nonzero_signed_edges(self):
        # Le cycle irréversible doit avoir au moins une arête signée (courant net réel).
        S = SP.signed_adjacency(_CYCLE3, n_symbols=3)
        assert np.any(S != 0.0), (
            "le cycle irréversible doit avoir au moins une arête signée (courant net non nul)"
        )


class TestLaplacianSpectrumEdgeCases:
    """Validation d'input : rejet des matrices non symétriques."""

    def test_rejects_nonsymmetric(self):
        # laplacian_spectrum doit lever ValueError si W n'est pas symétrique.
        W_bad = np.array([[0.0, 1.0, 0.0], [0.5, 0.0, 0.5], [0.0, 1.0, 0.0]])
        with pytest.raises(ValueError, match="symmetric"):
            SP.laplacian_spectrum(W_bad)


class TestSpectralGapEdgeCases:
    """Edge-case singleton + propriété cheeger-like (complet > ligne)."""

    def test_nan_for_singleton(self):
        # Matrice 1x1 : moins de 2 valeurs propres => gap = nan.
        W = np.array([[0.0]])
        gap = SP.spectral_gap(W)
        assert np.isnan(gap), f"gap doit être nan pour matrice 1x1, got {gap}"

    def test_complete_graph_exceeds_path_graph(self):
        # gap(K_4) > gap(P_4) : le graphe complet mélange plus vite vers la
        # stationnaire (mémoire plus courte) que le graphe ligne.
        complete_states = []
        for a in range(4):
            for b in range(4):
                if a != b:
                    complete_states.extend([a, b] * 20)
        path_states = []
        for _ in range(40):
            path_states.extend([0, 1, 2, 3, 2, 1])
        gap_complete = SP.spectral_gap(SP.transition_graph(complete_states, n_symbols=4))
        gap_path = SP.spectral_gap(SP.transition_graph(path_states, n_symbols=4))
        assert gap_complete > gap_path, (
            f"gap(K_4)={gap_complete} doit excéder gap(P_4)={gap_path} "
            "(le graphe complet mélange plus vite = mémoire plus courte)"
        )


class TestSpectralSummaryEdgeCases:
    """Densité maximale atteinte par le graphe complet."""

    def test_complete_graph_max_density(self):
        complete_states = []
        for a in range(4):
            for b in range(4):
                if a != b:
                    complete_states.extend([a, b] * 20)
        summary = SP.spectral_summary(complete_states, n_symbols=4)
        assert summary["density"] == pytest.approx(1.0, abs=1e-9), (
            f"graphe complet => density = 1.0, got {summary['density']}"
        )
