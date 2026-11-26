"""Tests de la **porte de detection** exportee par ``ict.valence`` (G3, #28306).

Le point 2 de l'arbitrage du coordinateur (24/11 01:05Z, sur la note de
conception v3 du capstone du palier 08) : ``gate: Optional[np.ndarray] = None``
sur ``simulate_reactive`` et ``simulate_phat``, avec ``None`` qui garde le
comportement d'origine **bit pour bit**.

Le test central ne compare donc pas l'organe a lui-meme (une fonction qui
renverrait toujours la meme chose passerait) : il porte un **oracle** — la
boucle d'origine, recopiete dans ce fichier, avant l'ajout du parametre — et
exige l'egalite **bit pour bit** (``np.array_equal``, pas ``allclose``) entre
l'oracle et l'organe appele sans porte et avec ``gate=None`` explicite.

Ce que la porte doit pouvoir faire, et pas davantage :

* 0 = « rien n'a ete detecte a cet instant » : l'animat ne bouge pas ;
* 1 = « tout est detecte » : exactement le comportement d'origine ;
* entre 0 et 1 = un pas raccourci (la decision d'approche est **multipliee**
  par le poids, pas remplacee) ;
* une porte malformee est **refusee**, jamais tronquee en silence.

Numpy + pytest, CPU uniquement.
"""

from __future__ import annotations

import os
import sys

# Permettre l'import direct depuis ict package (sans installer en mode develop).
_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

import numpy as np
import pytest

from ict import valence as V


# --------------------------------------------------------------------------- #
#  Oracle : la boucle d'origine, avant l'ajout du parametre `gate`            #
# --------------------------------------------------------------------------- #

def _oracle_reactive(source_traj, size, start, n_steps, step=0.8, obstacles=None):
    """Copie fidele de ``simulate_reactive`` avant l'export ``gate``."""
    pos = np.asarray(start, dtype=float).copy()
    traj = np.empty((n_steps, 2), dtype=float)
    for t in range(n_steps):
        g = V.valence_gradient(pos, source_traj[t], obstacles)
        n = float(np.linalg.norm(g))
        if n > 1e-9:
            pos = pos + step * (g / n)
        traj[t] = V._clip_to_bounds(pos, size)
    return traj


def _oracle_phat(source_traj, size, start, n_steps, lead=4, alpha=0.25,
                 step=0.8, obstacles=None):
    """Copie fidele de ``simulate_phat`` avant l'export ``gate``."""
    pos = np.asarray(start, dtype=float).copy()
    traj = np.empty((n_steps, 2), dtype=float)
    for t in range(n_steps):
        dist = float(np.linalg.norm(np.asarray(source_traj[t]) - pos))
        lead_meet = max(1, int(round(dist / max(step, 1e-9))))
        lead_meet = min(lead_meet, lead * 2)
        target = V.predict_source(source_traj, t, lead=lead_meet, alpha=alpha)
        desired = target - pos
        nd = float(np.linalg.norm(desired))
        desired = desired / nd if nd > 1e-9 else np.zeros(2)
        repl = V._obstacle_repulsion(pos, obstacles)
        move = desired + 0.5 * repl
        nm = float(np.linalg.norm(move))
        if nm > 1e-9:
            pos = pos + step * (move / nm)
        traj[t] = V._clip_to_bounds(pos, size)
    return traj


# --------------------------------------------------------------------------- #
#  Scene de reference : graine fixee, obstacles, regime non trivial            #
# --------------------------------------------------------------------------- #

SIZE = 32
N_STEPS = 60


def _scene():
    """Une source erratique (le regime ou p_hat perd) sur une graine fixee."""
    rng = np.random.default_rng(7)
    src = V.source_trajectory("erratique", N_STEPS, SIZE, rng=rng)
    obstacles = np.array([[10.0, 10.0], [20.0, 20.0]])
    start = np.array([2.0, 2.0])
    return src, obstacles, start


# --------------------------------------------------------------------------- #
#  Le comportement par defaut n'a pas bouge (bit pour bit)                   #
# --------------------------------------------------------------------------- #

def test_reactive_sans_porte_est_identique_a_l_oracle():
    src, obstacles, start = _scene()
    attendu = _oracle_reactive(src, SIZE, start, N_STEPS, obstacles=obstacles)
    obtenu = V.simulate_reactive(src, SIZE, start, N_STEPS, obstacles=obstacles)
    assert np.array_equal(attendu, obtenu)


def test_reactive_avec_gate_none_explicite_est_identique_a_l_oracle():
    src, obstacles, start = _scene()
    attendu = _oracle_reactive(src, SIZE, start, N_STEPS, obstacles=obstacles)
    obtenu = V.simulate_reactive(src, SIZE, start, N_STEPS,
                                 obstacles=obstacles, gate=None)
    assert np.array_equal(attendu, obtenu)


def test_phat_sans_porte_est_identique_a_l_oracle():
    src, obstacles, start = _scene()
    attendu = _oracle_phat(src, SIZE, start, N_STEPS, obstacles=obstacles)
    obtenu = V.simulate_phat(src, SIZE, start, N_STEPS, obstacles=obstacles)
    assert np.array_equal(attendu, obtenu)


def test_phat_avec_gate_none_explicite_est_identique_a_l_oracle():
    src, obstacles, start = _scene()
    attendu = _oracle_phat(src, SIZE, start, N_STEPS, obstacles=obstacles)
    obtenu = V.simulate_phat(src, SIZE, start, N_STEPS,
                             obstacles=obstacles, gate=None)
    assert np.array_equal(attendu, obtenu)


def test_porte_tout_a_un_ne_change_rien_non_plus():
    """Une porte ouverte vaut l'absence de porte — pas seulement « presque »."""
    src, obstacles, start = _scene()
    ouvert = np.ones(N_STEPS)
    for fn in (V.simulate_reactive, V.simulate_phat):
        sans = fn(src, SIZE, start, N_STEPS, obstacles=obstacles)
        avec = fn(src, SIZE, start, N_STEPS, obstacles=obstacles, gate=ouvert)
        assert np.array_equal(sans, avec)


# --------------------------------------------------------------------------- #
#  Ce que la porte change exactement                                           #
# --------------------------------------------------------------------------- #

def test_porte_nulle_immobilise_l_animat():
    """Porte a 0 : rien n'est detecte, l'animat ne fait aucun pas."""
    src, obstacles, start = _scene()
    nulle = np.zeros(N_STEPS)
    for fn in (V.simulate_reactive, V.simulate_phat):
        tr = fn(src, SIZE, start, N_STEPS, obstacles=obstacles, gate=nulle)
        assert np.allclose(tr, np.clip(start, 0.0, SIZE - 1))


def test_porte_partielle_reduit_le_pas_de_la_meme_facon():
    """Le poids multiplie le pas : a 0.5, le deplacement est half, pas nul."""
    src, obstacles, start = _scene()
    for fn in (V.simulate_reactive, V.simulate_phat):
        libre = fn(src, SIZE, start, N_STEPS, obstacles=obstacles)
        demi = fn(src, SIZE, start, N_STEPS, obstacles=obstacles,
                  gate=np.full(N_STEPS, 0.5))
        d_libre = float(np.linalg.norm(libre[0] - start))
        d_demi = float(np.linalg.norm(demi[0] - start))
        assert d_libre > 0.0
        assert d_demi == pytest.approx(0.5 * d_libre, rel=1e-12)


def test_porte_appliquee_a_un_seul_instant_agit_a_cet_instant_seul():
    """La porte est temporelle : un pas bloque, les autres libres."""
    src, obstacles, start = _scene()
    weights = np.ones(N_STEPS)
    weights[0] = 0.0
    tr = V.simulate_reactive(src, SIZE, start, N_STEPS,
                             obstacles=obstacles, gate=weights)
    assert np.allclose(tr[0], np.clip(start, 0.0, SIZE - 1))


# --------------------------------------------------------------------------- #
#  Une porte malformee est refusee, jamais tronquee                          #
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("fn", [V.simulate_reactive, V.simulate_phat])
def test_porte_trop_courte_est_refusee(fn):
    src, obstacles, start = _scene()
    with pytest.raises(ValueError):
        fn(src, SIZE, start, N_STEPS, obstacles=obstacles,
           gate=np.ones(N_STEPS - 1))


@pytest.mark.parametrize("fn", [V.simulate_reactive, V.simulate_phat])
def test_porte_hors_bornes_est_refusee(fn):
    src, obstacles, start = _scene()
    for mauvaise in (np.full(N_STEPS, 1.5), np.full(N_STEPS, -0.1)):
        with pytest.raises(ValueError):
            fn(src, SIZE, start, N_STEPS, obstacles=obstacles, gate=mauvaise)


@pytest.mark.parametrize("fn", [V.simulate_reactive, V.simulate_phat])
def test_porte_non_finie_est_refusee(fn):
    src, obstacles, start = _scene()
    with pytest.raises(ValueError):
        fn(src, SIZE, start, N_STEPS, obstacles=obstacles,
           gate=np.full(N_STEPS, np.nan))


@pytest.mark.parametrize("fn", [V.simulate_reactive, V.simulate_phat])
def test_porte_non_vectorielle_est_refusee(fn):
    src, obstacles, start = _scene()
    with pytest.raises(ValueError):
        fn(src, SIZE, start, N_STEPS, obstacles=obstacles,
           gate=np.ones((N_STEPS, 1)))


def test_une_porte_refusee_ne_laisse_pas_d_etat_dans_l_organe():
    """Apres un refus, le comportement par defaut reste intact."""
    src, obstacles, start = _scene()
    with pytest.raises(ValueError):
        V.simulate_reactive(src, SIZE, start, N_STEPS,
                            obstacles=obstacles, gate=np.ones(3))
    attendu = _oracle_reactive(src, SIZE, start, N_STEPS, obstacles=obstacles)
    obtenu = V.simulate_reactive(src, SIZE, start, N_STEPS, obstacles=obstacles)
    assert np.array_equal(attendu, obtenu)
