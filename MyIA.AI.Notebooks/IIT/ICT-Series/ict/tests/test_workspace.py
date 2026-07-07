"""Tests unitaires pour ``ict.workspace`` (ICT-24, strate 5, Epic #4588 / #5635).

Le module :mod:`ict.workspace` est l'avant-dernier substrat avant le notebook
capstone ICT-24 (WorkspaceIgnition). Il pose les 5 primitives qui relient
les activations continues multi-niches aux scalaires d'emergence causale
discrets du :mod:`ict.synthesis`. La batterie de tests verifie **chacune
de ces primitives sur un substrat synthetique GPU-free** : un AR(1) avec
saut de moyenne tire de :func:`ict.feature_dynamics.simulate_neutral_transition`
le **hub plante** (un feature unique dont l'activation est tiree du AR(1)
synthetique, les autres features sont du bruit plat). C'est l'inverse de
ce qu'on fait sur du reel : sur du AR(1) on SAIT qui doit dominer -- on
peut donc tester la falsifiabilite de la methode.

Les 8 gates falsifiables :

  1. (Gate forme) la matrice d'activations de Workspace est validee en
     forme ``(T, N, F)`` ; un tenseur de rang 2 leve ``ValueError``.

  2. (Gate ignition) sur le hub plante (feature 0 = AR(1), autres = bruit
     plat faible), ``ignition_step`` retourne en majorite ``winners[:, :] == 0``
     dans **toutes** les niches (winner-take-all capture le hub).

  3. (Gate hub_of_influence) sur le meme hub plante, le top-1 de
     ``hub_of_influence`` est la feature 0 dans toutes les niches.

  4. (Gate co-location diagonale) la diagonale de ``co_rate`` vaut 1.0
     par construction (une feature est co-allumee avec elle-meme
     partout ou elle s'allume).

  5. (Gate co-location symetrie) la matrice ``co_count`` est symetrique
     et la matrice ``co_rate`` aussi (aux erreurs flottantes pres).

  6. (Gate emergence_gain verbatim) le retour de ``event_triggered_battery``
     contient les **memes cles** que ``ict.synthesis.emergence_gain``
     (import verbatim) ; ``credited`` est un booleen ; ``ec_gain``,
     ``fe_gain``, ``k_gain`` sont des floats ; ``n_states >= 1``.

  7. (Gate bornes strictes discretisation) ``n_bins >= 2`` ; appeler
     ``event_triggered_battery`` avec ``n_bins = 1`` leve ``ValueError``.

  8. (Gate verbatim) l'attribut ``ict.workspace.emergence_gain`` **n'existe
     pas** (on n'a pas redefini localement ; on importe depuis synthesis).
     C'est le test anti-regression par excellence : si un futur dev tente
     de copier emergence_gain dans workspace.py, ce gate echoue
     bruyamment.

Implementation : aucune dependance externe ; un seul import numpy + import
du package ``ict``. Le substrat AR(1) est tire de ``simulate_neutral_transition``
qui est deja dans :mod:`ict.feature_dynamics` -- on ne reinvente pas la
roue, on branche.

CPU 1 cycle : la totalite du fichier doit passer en moins de 5 secondes
sur une machine standard (un seul ``rng`` maitre, des panels de 200 pas
de temps au plus).
"""

from __future__ import annotations

import sys
import os

# Permettre l'import direct depuis ict package (sans installer en mode develop).
# On ajoute le PARENT du package ict (et non `ict/` lui-meme, sinon Python
# chercherait `ict/ict/__init__.py`) -- d'ou le double `dirname`.
_HERE = os.path.dirname(os.path.abspath(__file__))
_ICT_PKG = os.path.dirname(_HERE)                  # = .../ict
_PARENT_OF_ICT = os.path.dirname(_ICT_PKG)         # = .../ICT-Series
if _PARENT_OF_ICT not in sys.path:
    sys.path.insert(0, _PARENT_OF_ICT)

import numpy as np
import pytest

from ict import workspace
from ict import feature_dynamics
from ict import synthesis


def _rng_for(seed: int) -> np.random.Generator:
    return np.random.default_rng(seed)


def _make_workspace_hub_planted(
    n_steps: int = 200,
    n_niches: int = 3,
    n_features: int = 4,
    hub_index: int = 0,
    transition_at: int = 100,
    noise_floor: float = 0.05,
    seed: int = 0,
) -> workspace.Workspace:
    """Construit un Workspace avec un hub plante en feature ``hub_index``.

    Le hub est tire de :func:`ict.feature_dynamics.simulate_neutral_transition`
    : un AR(1) avec saut de moyenne a ``transition_at`` (pre_mean=0,
    post_mean=1). Les ``n_features - 1`` autres features sont du **bruit
    plat** centre sur zero avec un ecart-type ``noise_floor`` << hub_mean.
    Le winner-take-all doit donc elire la feature ``hub_index`` dans
    toutes les niches (et pas une autre par accident).

    C'est le substrat synthetique de reference : GPU-free, CPU 1 cycle,
    deterministic pour une seed fixee. Toute la batterie de tests
    s'appuie dessus.
    """
    rng = _rng_for(seed)
    # Si transition_at depasse n_steps, forcer au milieu du panel -- sinon
    # simulate_neutral_transition leve IndexError (le regime post demarre hors borne).
    eff_transition_at = min(transition_at, max(1, n_steps // 2))
    trace, _ = feature_dynamics.simulate_neutral_transition(
        n_tokens=n_steps,
        transition_at=eff_transition_at,
        pre_mean=0.0,
        post_mean=1.0,
        pre_ar1=0.7,
        post_ar1=0.85,
        sigma=0.2,
        seed=seed,
    )
    # On rend le hub *positif* (centrage) pour que argmax soit stable
    # meme si la trace AR(1) passe temporairement sous zero avant le saut.
    trace_centered = trace - trace.min() + 1e-3
    activations = np.zeros((n_steps, n_niches, n_features), dtype=float)
    for i in range(n_niches):
        for j in range(n_features):
            if j == hub_index:
                activations[:, i, j] = trace_centered
            else:
                activations[:, i, j] = noise_floor * rng.standard_normal(n_steps)
    niche_names = [f"niche_{i}" for i in range(n_niches)]
    feature_names = [f"f_{j}" for j in range(n_features)]
    return workspace.Workspace(
        activations=activations,
        niche_names=niche_names,
        feature_names=feature_names,
    )


# --------------------------------------------------------------------------- #
#  Gate 1 : forme de la matrice d'activations
# --------------------------------------------------------------------------- #
def test_workspace_rejects_non_3d_activations():
    """Un tenseur de rang 2 leve ``ValueError`` (forme (T, N, F) requise)."""
    bad = np.zeros((10, 4))
    with pytest.raises(ValueError, match="forme"):
        workspace.Workspace(activations=bad)


def test_workspace_rejects_mismatched_feature_names():
    """niche_names / feature_names de longueur incorrecte leve ``ValueError``."""
    a = np.zeros((5, 2, 3))
    with pytest.raises(ValueError, match="feature_names"):
        workspace.Workspace(
            activations=a,
            niche_names=["a", "b"],
            feature_names=["only_one"],
        )


def test_workspace_default_names_are_generated():
    """niche_names et feature_names par defaut sont remplis automatiquement."""
    a = np.zeros((5, 2, 3))
    ws = workspace.Workspace(activations=a)
    assert ws.niche_names == ["niche_0", "niche_1"]
    assert ws.feature_names == ["f_0", "f_1", "f_2"]
    assert ws.n_steps == 5 and ws.n_niches == 2 and ws.n_features == 3


# --------------------------------------------------------------------------- #
#  Gate 2 : ignition_step capte le hub plante
# --------------------------------------------------------------------------- #
def test_ignition_step_captures_planted_hub():
    """Winner-take-all elit la feature hub dans toutes les niches.

    Hub plante en feature 0 (AR(1) post_mean=1), autres features en bruit
    plat (sigma=0.05). Le seuil "above_threshold" peut etre modeste
    (top-15%), mais on s'attend a ce que les winners soient en majorite
    0 partout -- sinon winner-take-all ne tient pas sa promesse.
    """
    ws = _make_workspace_hub_planted(
        n_steps=200, n_niches=3, n_features=4, hub_index=0, seed=42
    )
    ign = workspace.ignition_step(ws, threshold_quantile=0.5)
    winners = ign["winners"]
    # Part de winners == 0 (le hub) dans toutes les niches
    hub_rate = float((winners == 0).mean())
    assert hub_rate >= 0.95, (
        f"hub plante non elu : winners==0 seulement {hub_rate:.3f} des cas "
        f"(attendu >= 0.95)"
    )
    # Intensites strictement positives
    assert np.all(ign["intensities"] >= 0)
    # above_threshold est un booleen numpy
    assert ign["above_threshold"].dtype == bool


# --------------------------------------------------------------------------- #
#  Gate 3 : hub_of_influence identifie le bon hub
# --------------------------------------------------------------------------- #
def test_hub_of_influence_identifies_planted_hub():
    """Top-1 du hub_of_influence = feature 0 (le hub AR(1) plante)."""
    ws = _make_workspace_hub_planted(
        n_steps=200, n_niches=3, n_features=4, hub_index=0, seed=42
    )
    hub = workspace.hub_of_influence(ws, top_k=3)
    top1 = int(hub["top_k"][0])
    assert top1 == 0, f"top-1 hub devrait etre feature 0, recu {top1}"
    # L'activation moyenne du top-1 depasse largement celle du top-3
    assert hub["top_k_mean"][0] > 2 * hub["top_k_mean"][-1], (
        f"hub trop peu dominant : mean[0]={hub['top_k_mean'][0]:.3f}, "
        f"mean[-1]={hub['top_k_mean'][-1]:.3f}"
    )
    # Noms correspondants
    assert hub["top_k_names"][0] == "f_0"


# --------------------------------------------------------------------------- #
#  Gate 4 : diagonale de co_rate = taux d'ignition par feature
# --------------------------------------------------------------------------- #
def test_co_location_diagonal_is_ignition_rate():
    """La diagonale de ``co_rate`` vaut le taux d'ignition par feature.

    Pour une feature ``j``, ``co_count[j, j]`` compte les (t, niche) ou
    ``j`` est gagnante ; divise par ``n_ignitions`` = ``T*N`` (chaque
    pas/niche elit exactement une feature), on obtient le **taux
    d'ignition**. Sur le hub plante, la feature 0 doit elire quasiment
    toujours (taux proche de 1) et les autres quasiment jamais (taux
    proche de 0). C'est la falsifiabilite sur donnees plantees.
    """
    ws = _make_workspace_hub_planted(
        n_steps=150, n_niches=2, n_features=3, hub_index=0, seed=7
    )
    co = workspace.co_location_ignitions(ws)
    diag = np.diag(co["co_rate"])
    # Hub plante (feature 0) domine -- taux proche de 1
    assert diag[0] >= 0.95, (
        f"hub plante feature 0 non dominant : diag[0]={diag[0]:.3f} (attendu >= 0.95)"
    )
    # Autres features : taux proche de 0 (elles ne gagnent jamais)
    for j in range(1, ws.n_features):
        assert diag[j] <= 0.05, (
            f"feature {j} gagne trop souvent : diag[{j}]={diag[j]:.3f} (attendu <= 0.05)"
        )
    # n_ignitions == T * N (chaque (t, niche) elit exactement 1 feature)
    assert co["n_ignitions"] == ws.n_steps * ws.n_niches


# --------------------------------------------------------------------------- #
#  Gate 5 : co-location symetrie
# --------------------------------------------------------------------------- #
def test_co_location_is_symmetric():
    """``co_count`` et ``co_rate`` sont symetriques."""
    ws = _make_workspace_hub_planted(
        n_steps=150, n_niches=3, n_features=5, hub_index=0, seed=11
    )
    co = workspace.co_location_ignitions(ws)
    assert np.allclose(co["co_count"], co["co_count"].T), "co_count pas symetrique"
    assert np.allclose(co["co_rate"], co["co_rate"].T), "co_rate pas symetrique"
    # Comptes >= 0 partout
    assert (co["co_count"] >= 0).all()


# --------------------------------------------------------------------------- #
#  Gate 6 : emergence_gain est importee verbatim (memes cles / types)
# --------------------------------------------------------------------------- #
def test_event_triggered_battery_matches_emergence_gain_signature():
    """``event_triggered_battery`` retourne les memes cles que ``emergence_gain``.

    Test du caractere verbatim de l'import (acceptance #5635) : si la
    signature de ``ict.synthesis.emergence_gain`` evolue, ce test echoue
    -- forçant une mise a jour explicite plutot qu'un "shadow" local.
    """
    ws = _make_workspace_hub_planted(
        n_steps=120, n_niches=2, n_features=3, hub_index=0, seed=3
    )
    rng = _rng_for(123)
    b = workspace.event_triggered_battery(
        ws, rng=rng, n_shuffles=10, n_bins=4
    )
    # Cles canoniques d'emergence_gain + cles workspace-specifiques
    expected_keys = {
        "ei_real", "ei_shuffled", "ei_gain",
        "ec_real", "ec_shuffled", "ec_gain",
        "credited", "n_states",
        "fe_gain", "k_gain",
        "n_bins", "n_ignitions", "sequence_length",
    }
    assert set(b) == expected_keys, (
        f"signature divergente : manque={expected_keys - set(b)}, "
        f"supplement={set(b) - expected_keys}"
    )
    # Types conformes
    assert isinstance(b["credited"], (bool, np.bool_))
    assert isinstance(b["ec_gain"], float)
    assert isinstance(b["fe_gain"], float)
    assert isinstance(b["k_gain"], float)
    assert b["n_states"] >= 1
    assert b["n_bins"] == 4
    assert b["n_ignitions"] == ws.n_steps * ws.n_niches * ws.n_features
    assert b["sequence_length"] == b["n_ignitions"]


# --------------------------------------------------------------------------- #
#  Gate 7 : bornes strictes de discretisation
# --------------------------------------------------------------------------- #
def test_event_triggered_battery_rejects_n_bins_lt_2():
    """``n_bins = 1`` leve ``ValueError`` (un seul bin ne porte aucune info)."""
    ws = _make_workspace_hub_planted(
        n_steps=80, n_niches=2, n_features=2, hub_index=0, seed=5
    )
    rng = _rng_for(0)
    with pytest.raises(ValueError, match="n_bins"):
        workspace.event_triggered_battery(
            ws, rng=rng, n_shuffles=5, n_bins=1
        )


def test_discretize_handles_constant_feature():
    """Une feature constante est discretisee en 0 partout (deterministe)."""
    a = np.zeros((10, 2, 3))
    a[:, :, 1] = 1.0  # feature 1 constante non-nulle
    ws = workspace.Workspace(activations=a)
    disc = workspace._discretize_workspace(ws, n_bins=4)
    # Feature 0 et 1 constantes -> 0 ; feature 2 constante -> 0
    assert disc.shape == (10, 2, 3)
    assert np.all(disc[:, :, 0] == 0)
    assert np.all(disc[:, :, 1] == 0)
    assert np.all(disc[:, :, 2] == 0)


# --------------------------------------------------------------------------- #
#  Gate 8 : emergence_gain n'est PAS redefinie localement (anti-regression)
# --------------------------------------------------------------------------- #
def test_emergence_gain_is_not_redefined_in_workspace():
    """``ict.workspace`` n'expose pas ``emergence_gain`` localement.

    C'est le gate anti-regression par excellence. Si un futur dev copie
    emergence_gain dans workspace.py pour gagner du temps (au lieu de
    l'importer), ce test attrape la deviation immediatement.
    """
    assert not hasattr(workspace, "emergence_gain"), (
        "ict.workspace definit emergence_gain localement -- "
        "c'est INTERDIT (acceptance #5635). Importer depuis ict.synthesis "
        "plutot que redefinir."
    )
    # Import confirme -- synthesis.emergence_gain reste la source canonique.
    assert hasattr(synthesis, "emergence_gain")