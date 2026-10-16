"""Tests CPU deterministes des regimes generatifs (issue #15478, suivi #20071).

Deux constructions sont couvertes :

- ``NoisedChannel`` : bruit sur le CANAL D'EMISSION du generateur (critere
  « un entrainement complet par niveau de bruit, le temoin rejoue a chaque
  niveau ») ;
- ``ConditionalBench`` : le token du parent selectionne la variante
  d'emission de l'enfant, a marginales appariees (critere « structure
  generative conditionnelle »).

Contre-verifications majeures : les beliefs exacts (y compris le filtre a
emission variant temps-variable) sont confrontes a une ENUMERATION BRUTE des
chemins d'etats sur sequences courtes — le forward ne se valide pas par
lui-meme ; l'appariement des marginales est verifie EXACTEMENT (0.5*(E0+E1)
= E) et empiriquement ; la prime d'information conditionnelle (plancher
conditionnel < plancher aveugle aux variants) est mesuree, pas supposee.
"""

from __future__ import annotations

import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import numpy as np
import pytest

from ict.bench_factorise import (
    ConditionalBench,
    Mess3,
    Mess3Canonical,
    Mess3_ObsCoupled,
    NoisedChannel,
    ProcessError,
    RRXOR,
    conditional_child_floor,
    cyclic_perturbation,
)


GAMMAS = (0.0, 0.15, 0.4, 0.75, 1.0)

# NOTE : ce fichier est volontairement SANS torch. Les tests qui exigent la
# couche de mesure (bayes_floor sur les processus bruites) vivent dans
# test_factor_geometry_trained.py : importer torch ici, en tete de paquet
# (ordre alphabetique), fait crasher l'import torch/_dynamo d'un fichier
# ulterieur sous Windows (segv mesure, cf registre).


# ---------------------------------------------------------------------------
# NoisedChannel : parametrage
# ---------------------------------------------------------------------------


def test_gamma_hors_domaine_refuse():
    for bad in (-0.1, 1.3, 2.0):
        with pytest.raises(ProcessError):
            NoisedChannel(Mess3(), gamma=bad)


def test_processus_continu_refuse():
    # emissions gaussiennes : ni matrice ni tenseur, rien a bruiter
    with pytest.raises(ProcessError):
        NoisedChannel(Mess3_ObsCoupled(std=0.2), gamma=0.5)


def test_gamma_zero_reproduit_les_parametres():
    assert np.allclose(NoisedChannel(Mess3(), 0.0).emission_matrix(), Mess3().emission_matrix())
    assert np.allclose(NoisedChannel(RRXOR(), 0.0).edge_tensor(), RRXOR().edge_tensor())


def test_gamma_un_rend_les_emissions_muettes():
    e = NoisedChannel(Mess3(), 1.0).emission_matrix()
    assert np.allclose(e, 1.0 / 3.0)
    w = NoisedChannel(RRXOR(), 1.0).edge_tensor()
    for i in range(5):
        for j in range(5):
            m = w[i, j, :].sum()
            if m > 0:
                # chaque arete : masse inchangee, distribution uniforme sur y
                assert w[i, j, 0] == pytest.approx(m / 2.0)
                assert w[i, j, 1] == pytest.approx(m / 2.0)


@pytest.mark.parametrize("gamma", GAMMAS)
def test_lignes_stochastiques(gamma):
    e = NoisedChannel(Mess3(), gamma).emission_matrix()
    assert np.allclose(e.sum(axis=1), 1.0)
    assert (e >= -1e-12).all()
    w = NoisedChannel(RRXOR(), gamma).edge_tensor()
    assert (w >= -1e-12).all()


@pytest.mark.parametrize("gamma", GAMMAS)
def test_transitions_mealy_preservees_exactement(gamma):
    # le critere du regime : la dynamique latente est INTACTE, seul le canal
    # d'emission se degrade — la matrice somme du tenseur bruite est T a
    # l'identique, pour tout gamma
    t_ref = RRXOR().transition_matrix()
    w = NoisedChannel(RRXOR(), gamma).edge_tensor()
    assert np.allclose(w.sum(axis=2), t_ref, atol=1e-12)
    # et la matrice deleguee est celle du processus d'origine
    assert np.allclose(NoisedChannel(RRXOR(), gamma).transition_matrix(), t_ref)


# Les tests de plancher (bayes_floor croissant en gamma, endpoint gamma=1)
# vivent dans test_factor_geometry_trained.py : ils exigent la couche de
# mesure, et ce fichier reste volontairement sans torch (cf NOTE d'en-tete).


# ---------------------------------------------------------------------------
# NoisedChannel : echantillonnage et filtration
# ---------------------------------------------------------------------------


def test_sample_reproductible_et_formes():
    for proc in (Mess3(), RRXOR()):
        noised = NoisedChannel(proc, 0.3)
        s1, o1 = noised.sample(200, seed=5)
        s2, o2 = noised.sample(200, seed=5)
        assert np.array_equal(s1, s2) and np.array_equal(o1, o2)
        assert s1.shape == o1.shape == (200,)
        assert set(np.unique(s1)) <= set(range(proc.n_states))


def test_marginales_empiriques_suivent_le_canal_bruite():
    # la LOI des observations est celle du canal degrade : pi @ E_gamma
    for proc, q in ((Mess3(), 3), (RRXOR(), 2)):
        noised = NoisedChannel(proc, 0.5)
        _, obs = noised.sample(40_000, seed=31)
        counts = np.bincount(obs, minlength=q) / len(obs)
        pi = noised.stationary()
        if hasattr(proc, "emission_matrix"):
            target = pi @ noised.emission_matrix()
        else:
            w = noised.edge_tensor()
            target = pi @ w.sum(axis=1)
        assert np.allclose(counts, target, atol=0.02)


def _brute_beliefs_moore(pi, t, e, obs):
    """Enumeration brute de TOUS les chemins d'etats : P(s_k | y_0..y_k) FILTRE.

    Accumulation par PREFIXE : au pas k, seule la probabilite du chemin
    jusqu'a k entre en jeu (le chemin complet donnerait le LISSE
    P(s_k | y_0..y_n), une quantite differente).
    """
    n_states = len(pi)
    n = len(obs)
    marginals = np.zeros((n, n_states))
    for path in np.ndindex(*(n_states,) * n):
        p = pi[path[0]] * e[path[0], obs[0]]
        marginals[0, path[0]] += p
        for k in range(1, n):
            p *= t[path[k - 1], path[k]] * e[path[k], obs[k]]
            marginals[k, path[k]] += p
    return marginals / marginals.sum(axis=1, keepdims=True)


def test_beliefs_moore_vs_enumeration_brute():
    noised = NoisedChannel(Mess3(), 0.4)
    _, obs = noised.sample(5, seed=41)  # 3^5 = 243 chemins
    fast = noised.beliefs(obs)
    brute = _brute_beliefs_moore(
        noised.stationary(), noised.transition_matrix(), noised.emission_matrix(), obs
    )
    assert np.allclose(fast, brute, atol=1e-10)


def _brute_beliefs_mealy(pi, w, obs):
    """Enumeration brute des chemins d'ARETES : belief FILTRE sur l'etat d'arrivee."""
    n_states = w.shape[0]
    n = len(obs)
    marginals = np.zeros((n, n_states))
    # chemin = (s0 source, s1..sn arrivals) ; 5^5 = 3125 chemins pour n=4
    for path in np.ndindex(*(n_states,) * (n + 1)):
        p = pi[path[0]]
        for k in range(n):
            p *= w[path[k], path[k + 1], obs[k]]
            marginals[k, path[k + 1]] += p  # prefixe : filtre, pas lissage
    total = marginals.sum(axis=1, keepdims=True)
    if (total == 0).any():
        return None
    return marginals / total


def test_beliefs_mealy_vs_enumeration_brute():
    noised = NoisedChannel(RRXOR(), 0.35)
    _, obs = noised.sample(4, seed=43)  # 5^5 = 3125 chemins
    fast = noised.beliefs(obs)
    brute = _brute_beliefs_mealy(noised.stationary(), noised.edge_tensor(), obs)
    assert brute is not None
    assert np.allclose(fast, brute, atol=1e-10)


def test_beliefs_refuse_alphabet_hors_domaine():
    noised = NoisedChannel(Mess3(), 0.2)
    with pytest.raises(ProcessError):
        noised.beliefs(np.array([0, 7, 1]))


# ---------------------------------------------------------------------------
# ConditionalBench : construction et appariement exact
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class _SkewedParent:
    """Parent a tokens NON equiprobables : doit etre refuse a la construction."""

    def sample(self, n, seed):
        rng = np.random.default_rng(seed)
        s = rng.choice(3, p=self.stationary())
        out_s = np.empty(n, dtype=np.int64)
        out_y = np.empty(n, dtype=np.int64)
        t = self.transition_matrix()
        e = self.emission_matrix()
        for k in range(n):
            out_s[k] = s
            out_y[k] = rng.choice(3, p=e[s])
            s = rng.choice(3, p=t[s])
        return out_s, out_y

    def beliefs(self, obs):
        raise ProcessError("inutilise dans ce test")

    def transition_matrix(self):
        t = np.zeros((3, 3))
        for i in range(3):
            t[i, i] = 0.9
            t[i, (i + 1) % 3] = 0.1
        return t

    def stationary(self):
        return np.array([0.8, 0.1, 0.1])

    def emission_matrix(self):
        e = np.full((3, 3), 0.1)
        e[0, 0] = 0.8
        e[1, 1] = 0.8
        e[2, 2] = 0.8
        return e

    n_states: int = 3
    name: str = "skewed"


def test_appariement_exact_des_variantes():
    bench = ConditionalBench(Mess3(), Mess3(), kappa=0.2)
    variants = bench.emission_variants()
    assert len(variants) == 3
    for v in variants:
        assert np.allclose(v.sum(axis=1), 1.0)
        assert (v >= -1e-12).all()
    # l'egalite est EXACTE, pas asymptotique : c'est le coeur du critere.
    # Les q rotations de colonnes d'une ligne de somme nulle s'annulent :
    # le melange uniforme des variantes reconstruit E a l'identique
    assert np.allclose(np.mean(np.stack(variants, axis=0), axis=0),
                       Mess3().emission_matrix(), atol=1e-15)
    assert np.allclose(bench.marginal_child(), Mess3().emission_matrix(), atol=1e-15)


def test_kappa_excessif_refuse():
    # Mess3 : plus petite entree 0.25, donc kappa > 0.25 casse la stochasticite
    with pytest.raises(ProcessError):
        ConditionalBench(Mess3(), Mess3(), kappa=0.3)


def test_parent_a_tokens_non_equiprobables_refuse():
    with pytest.raises(ProcessError):
        ConditionalBench(_SkewedParent(), Mess3(), kappa=0.1)


def test_enfant_non_moore_refuse():
    with pytest.raises(ProcessError):
        ConditionalBench(Mess3(), RRXOR(), kappa=0.1)


def test_alphabets_desalignes_refuses():
    # parent binaire (RRXOR), enfant ternaire : le token ne peut indexer
    # les variants
    with pytest.raises(ProcessError):
        ConditionalBench(RRXOR(), Mess3(), kappa=0.1)


def test_perturbation_cyclique_somme_nulle():
    d = cyclic_perturbation(3)
    assert np.allclose(d.sum(axis=1), 0.0)
    assert d[0, 1] == 1.0 and d[0, 2] == -1.0
    assert d[1, 2] == 1.0 and d[1, 0] == -1.0
    with pytest.raises(ProcessError):
        cyclic_perturbation(2)


# ---------------------------------------------------------------------------
# ConditionalBench : loi jointe — dependance presente, marginales intactes
# ---------------------------------------------------------------------------


def test_sample_reproductible_et_cles():
    bench = ConditionalBench(Mess3(), Mess3(), kappa=0.2)
    r1 = bench.sample(300, seed_parent=3, seed_child=4)
    r2 = bench.sample(300, seed_parent=3, seed_child=4)
    assert np.array_equal(r1["obs_a"], r2["obs_a"])
    assert np.array_equal(r1["obs_b"], r2["obs_b"])
    assert set(r1) == {"obs_a", "obs_b", "states_a", "states_b", "variant_tokens"}
    assert set(np.unique(r1["obs_b"])) <= {0, 1, 2}


def test_marginal_enfant_appariee_empiriquement():
    # la marginal de l'enfant, prise SEULE, est celle du Mess3 independant :
    # comparee a la fois a la theorie (pi @ E) et a un tirage independant
    bench = ConditionalBench(Mess3(), Mess3(), kappa=0.2)
    r = bench.sample(60_000, seed_parent=7, seed_child=8)
    counts = np.bincount(r["obs_b"], minlength=3) / len(r["obs_b"])
    pi = Mess3().stationary()
    assert np.allclose(counts, pi @ Mess3().emission_matrix(), atol=0.01)
    _, obs_free = Mess3().sample(60_000, seed=9)
    counts_free = np.bincount(obs_free, minlength=3) / len(obs_free)
    assert np.allclose(counts, counts_free, atol=0.02)


def test_dependance_jointe_mesurable():
    # La TV instantanee P(obs_b | obs_a = v) est NULLE par construction (E
    # circulant : chaque variant a une marginal uniforme) — c'est l'appariement
    # des marginales pris au serieux, pas un defaut. La dependance vit dans le
    # PREDITIF : a histoire egale (belief sur l'etat enfant reconstruit depuis
    # le passe de l'enfant SEUL), le token parent change la loi du prochain
    # symbole enfant. C'est cette quantite que le modele peut apprendre.
    bench = ConditionalBench(Mess3(), Mess3(), kappa=0.2)
    r = bench.sample(20_000, seed_parent=91, seed_child=92)
    child = Mess3()
    t = child.transition_matrix()
    variants = bench.emission_variants()
    # belief approche sur l'etat enfant, depuis le PASSE de l'enfant seul
    bel_hist = child.beliefs(r["obs_b"][:-1]) @ t
    diffs = []
    for k in range(0, 20_000 - 1, 7):
        pv = [bel_hist[k] @ variants[v] for v in range(3)]
        diffs.append(max(np.abs(pv[i] - pv[j]).max() for i in range(3) for j in range(i + 1, 3)))
    # mesure de reference (diag 09/10, seed 91/92) : p95 = 0.312, mediane = 0.174
    assert np.percentile(diffs, 95) > 0.1
    # et la TV instantanee est bien nulle : la preuve que les marginales
    # restent appariees MEME conditionnellement au token
    for v in range(3):
        sel = r["obs_a"] == v
        assert sel.sum() > 5_000
        cond_v = np.bincount(r["obs_b"][sel], minlength=3) / sel.sum()
        assert np.allclose(cond_v, 1.0 / 3.0, atol=0.02)


def _brute_beliefs_enfant(pi, t, variants, obs_b, tokens):
    """Enumeration brute avec emission VARIANT TEMPS-VARIABLE (filtre par prefixe)."""
    n_states = len(pi)
    n = len(obs_b)
    marginals = np.zeros((n, n_states))
    for path in np.ndindex(*(n_states,) * n):
        p = pi[path[0]] * variants[int(tokens[0]) % len(variants)][path[0], obs_b[0]]
        marginals[0, path[0]] += p
        for k in range(1, n):
            p *= (t[path[k - 1], path[k]]
                  * variants[int(tokens[k]) % len(variants)][path[k], obs_b[k]])
            marginals[k, path[k]] += p
    tot = marginals.sum(axis=1, keepdims=True)
    if (tot == 0).any():
        return None
    return marginals / tot


def test_beliefs_enfant_vs_enumeration_brute():
    bench = ConditionalBench(Mess3(), Mess3(), kappa=0.2)
    r = bench.sample(5, seed_parent=51, seed_child=52)
    fast = bench.beliefs(r["obs_a"], r["obs_b"])["belief_b"]
    child = Mess3()
    brute = _brute_beliefs_enfant(
        child.stationary(), child.transition_matrix(),
        bench.emission_variants(), r["obs_b"], r["obs_a"],
    )
    assert brute is not None
    assert np.allclose(fast, brute, atol=1e-10)


def test_beliefs_parent_inchanges():
    # le parent ignore l'enfant : sa filtration est exactement celle du
    # processus seul sur les memes observations
    bench = ConditionalBench(Mess3(), Mess3(), kappa=0.2)
    r = bench.sample(500, seed_parent=61, seed_child=62)
    solo = Mess3().beliefs(r["obs_a"])
    assert np.allclose(bench.beliefs(r["obs_a"], r["obs_b"])["belief_a"], solo, atol=1e-12)


def test_plancher_conditionnel_strictement_meilleur_qu_aveugle():
    # la prime d'information conditionnelle, MESUREE : le filtre qui connait
    # la variante (token parent observe) bat le filtre aveugle (meme emission
    # marginale E a chaque pas) sur les MEMES donnees
    bench = ConditionalBench(Mess3(), Mess3(), kappa=0.2)
    r = bench.sample(30_000, seed_parent=71, seed_child=72)
    child = Mess3()
    t = child.transition_matrix()
    e = child.emission_matrix()
    cond = conditional_child_floor(
        r["obs_b"], r["obs_a"], t, bench.emission_variants(), child.stationary(), burn=32
    )
    blind = conditional_child_floor(
        r["obs_b"], r["obs_a"], t, (e, e, e), child.stationary(), burn=32
    )
    assert cond < blind
    assert blind - cond > 0.01  # n'est pas un artefact numerique
