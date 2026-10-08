"""Tests du module :mod:`ict.strate6_s1_adoption` (J1 #7291, Epic #4588).

Chaque test valide une propriété falsifiable du banc S1 « adoption
polyconvictionnelle », numérotée par *gate* pour le cross-reference avec le
pré-enregistrement J1 (issue #7291, c.6007595872). Pattern hérite de
``test_reversibility_budget.py`` : bootstrap ``sys.path`` module-level, sans
fixtures, tolérances commentées.
"""

from __future__ import annotations

import os
import sys

import numpy as np
import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from ict.strate6_s1_adoption import (  # noqa: E402
    PolyAdoptionGame,
    anchor_state,
    analyze_sweep,
    convention_alphabet,
    effective_alterity,
)


def _rng(seed: int) -> np.random.Generator:
    return np.random.default_rng(seed)


# --------------------------------------------------------------------------- #
#  Gate A : alphabet de conventions fixe, déterministe, injectif               #
# --------------------------------------------------------------------------- #


def test_alphabet_deterministe_et_injectif():
    """Deux appels donnent le même alphabet ; C1 = identité ; 8 conventions distinctes."""
    a1 = convention_alphabet()
    a2 = convention_alphabet()
    assert np.array_equal(a1, a2)
    assert list(a1[0, 0]) == [0, 1, 2, 3] and list(a1[0, 1]) == [0, 1, 2, 3]
    sigles = {tuple(a1[c, 0]) for c in range(a1.shape[0])}
    assert len(sigles) == 8


def test_alphabet_refuse_impossible():
    """8 bijections exigent n_states! >= 8 : n_states=3 (6 bijections) doit refuser."""
    with pytest.raises(ValueError):
        convention_alphabet(n_states=3, n_conventions=8)


# --------------------------------------------------------------------------- #
#  Gate B : constitution du banc (bras k, vecteur d'adoption initial)          #
# --------------------------------------------------------------------------- #


def test_bras_k1_sommet_c1():
    """k=1 : les 32 épinglés sont sur C1, les 16 flotteurs sans convention."""
    g = PolyAdoptionGame(1, rng=_rng(42))
    x = g.adoption_vector()
    # 32/48 = 0.667 sur C1, 0 partout ailleurs ; somme 0.667 (flotteurs -1).
    assert x[0] == pytest.approx(32 / 48, abs=1e-12)
    assert x[1:] == pytest.approx(np.zeros(7), abs=1e-12)


def test_bras_k8_uniforme():
    """k=8 : 4 épinglés par convention -> 8 composantes égales à 4/48."""
    g = PolyAdoptionGame(8, rng=_rng(42))
    x = g.adoption_vector()
    assert x == pytest.approx(np.full(8, 4 / 48), abs=1e-12)


def test_validation_k():
    """k > alphabet, ou n_pinned non divisible par k : refus explicite."""
    with pytest.raises(ValueError):
        PolyAdoptionGame(9, rng=_rng(0))
    with pytest.raises(ValueError):
        PolyAdoptionGame(3, rng=_rng(0))  # 32 % 3 != 0


def test_epingles_n_apprennent_pas():
    """Après entraînement court, les Q des épinglés restent au motif fort/faible."""
    g = PolyAdoptionGame(1, rng=_rng(1))
    before = g.Q_s[0].copy()
    g.train(200)
    assert np.array_equal(g.Q_s[0], before)


# --------------------------------------------------------------------------- #
#  Gate C : synthesize réalise exactement la cible (granularité 1/48)          #
# --------------------------------------------------------------------------- #


def test_synthesize_exact():
    """Une cible atteignable est réalisée à la granularité près (écart L2 ~ 0)."""
    g = PolyAdoptionGame(1, rng=_rng(42))
    target = np.zeros(8)
    target[0], target[2] = 0.5, 0.5
    g.synthesize(target, anchor_assign=g.agent_convention.copy())
    x = g.adoption_vector()
    # Tolérance : arrondi round(x*48) par composante -> erreur <= 1/48 par axe.
    assert np.linalg.norm(x - target) <= np.sqrt(8) / 48


def test_synthesize_reservoir_unassigned():
    """Les agents sans convention comblent les déficits (cible pleine hors ancre)."""
    g = PolyAdoptionGame(1, rng=_rng(42))
    target = np.zeros(8)
    target[:6] = 1.0 / 6.0  # 8 agents par convention, 6 conventions
    g.synthesize(target, anchor_assign=g.agent_convention.copy())
    x = g.adoption_vector()
    assert x[6:] == pytest.approx(np.zeros(2), abs=1e-12)
    assert x[:6] == pytest.approx(np.full(6, 8 / 48), abs=1e-12)


def test_synthesize_deterministe():
    """Même banque (seed), même cible -> Q identiques (aucun tirage dans la réalisation)."""
    ga = PolyAdoptionGame(4, rng=_rng(3))
    gb = PolyAdoptionGame(4, rng=_rng(3))
    target = np.zeros(8)
    target[1], target[3] = 0.25, 0.75
    ga.synthesize(target, anchor_assign=ga.agent_convention.copy())
    gb.synthesize(target, anchor_assign=gb.agent_convention.copy())
    assert np.array_equal(ga.Q_s, gb.Q_s) and np.array_equal(ga.Q_r, gb.Q_r)


def test_synthesize_refuse_mauvaise_dimension():
    with pytest.raises(ValueError):
        g = PolyAdoptionGame(1, rng=_rng(0))
        g.synthesize(np.zeros(7), anchor_assign=g.agent_convention.copy())


# --------------------------------------------------------------------------- #
#  Gate D : mesures clause 1 (A(Sigma) = exp(H), bassins)                      #
# --------------------------------------------------------------------------- #


def test_effective_alterity_extremes():
    """Sommet -> A=1 ; uniforme 8 -> A=8 ; 50/50 -> A=2."""
    vertex = np.zeros(8)
    vertex[0] = 1.0
    assert effective_alterity(vertex)["A_expH"] == pytest.approx(1.0, abs=1e-12)
    assert effective_alterity(np.full(8, 1 / 8))["A_expH"] == pytest.approx(8.0, abs=1e-12)
    half = np.zeros(8)
    half[0] = half[1] = 0.5
    assert effective_alterity(half)["A_expH"] == pytest.approx(2.0, abs=1e-12)


def test_basins_seuil_masses():
    """Bassins = composantes d'ancre de masse >= 0.05."""
    anchor = np.zeros(8)
    anchor[0], anchor[1], anchor[2] = 0.4, 0.3, 0.04
    result = effective_alterity(anchor)
    assert result["basins"] == 2  # 0.04 < seuil


# --------------------------------------------------------------------------- #
#  Gate E : dynamique et adaptateur vers l'organe budget (ICT-18b)             #
# --------------------------------------------------------------------------- #


def test_advance_windows_trajectoire():
    """advance_windows rend un point par fenêtre, dimension 8, dans [0, 1]."""
    g = PolyAdoptionGame(2, rng=_rng(5))
    traj = g.advance_windows(3, window=10)
    assert len(traj) == 3
    for x in traj:
        assert x.shape == (8,)
        assert np.all(x >= 0.0) and np.all(x <= 1.0)


def test_make_step_fn_synthese_puis_continuite():
    """Le premier appel synthétise depuis x0 ; les appels suivants avancent la
    VRAIE configuration (contrat observable : dimension 8, bornes [0, 1],
    dynamique continue — jamais de re-synthèse intermédiaire)."""
    g = PolyAdoptionGame(2, rng=_rng(11))
    anchor, assign = anchor_state(g, n_rounds=400, anneal_to=0.1)
    step = g.make_step_fn(assign, window=20)
    x1 = step(anchor)  # premier appel : synthèse depuis l'ancre
    x2 = step(x1)      # second appel : avance de la configuration synthétisée
    assert x1.shape == (8,) and x2.shape == (8,)
    assert np.all(x2 >= 0.0) and np.all(x2 <= 1.0)


def test_make_step_fn_reproductible():
    """Deux bancs identiques (seed) donnent la même trajectoire de step_fn."""
    trajectories = []
    for _ in range(2):
        g = PolyAdoptionGame(2, rng=_rng(21))
        _, assign = anchor_state(g, n_rounds=300, anneal_to=0.1)
        step = g.make_step_fn(assign, window=20)
        x = g.adoption_vector()
        traj = [step(x) for _ in range(3)]
        trajectories.append(traj)
    for a, b in zip(trajectories[0], trajectories[1]):
        assert np.array_equal(a, b)


def test_integration_state_space_budget():
    """Intégration avec l'organe ICT-18b : B(r, tau) est dans [0, 1].

    Garde du contrat adaptateur : l'organe itère ``x = step_fn(x)`` sur
    PLUSIEURS échantillons avec la MÊME fonction — chaque échantillon doit
    repartir de SON point perturbé (re-synthèse), pas continuer le jeu du
    précédent. À gros rayon (r=0.5) sur bras MONO, au moins une perturbation
    réalise un déplacement au-delà de la consigne et y reste gelée (agents
    épinglés déplacés : le mécanisme du contre-régime) — donc B < 1.0.
    Version antérieure défaillante : B=1.0 partout (closure partagée)."""
    from ict.reversibility_budget import state_space_budget

    g = PolyAdoptionGame(1, rng=_rng(33))
    anchor, assign = anchor_state(g, n_rounds=1500, anneal_to=0.1)
    step = g.make_step_fn(assign, window=10)
    # Petit rayon : la perturbation reste dans la consigne -> B = 1.0.
    b_petit = state_space_budget(
        step,
        anchor,
        radius=0.02,
        tau=3,
        n_samples=5,
        rng=_rng(0),
        consigne_radius=0.10,
        bounds=(0.0, 1.0),
    )
    assert b_petit == pytest.approx(1.0, abs=1e-12)
    # Gros rayon : au moins un échantillon gelé hors consigne -> B < 1.0.
    # Déterministe (rng seedé) : la valeur mesurée est 0.75.
    b_gros = state_space_budget(
        step,
        anchor,
        radius=0.50,
        tau=3,
        n_samples=8,
        rng=_rng(0),
        consigne_radius=0.10,
        bounds=(0.0, 1.0),
    )
    assert 0.0 <= b_gros < 1.0


# --------------------------------------------------------------------------- #
#  Gate F : entraînement — l'ancre absorbe les flotteurs (bras k=1)            #
# --------------------------------------------------------------------------- #


def test_ancre_k1_absorbe_flotteurs():
    """Après entraînement, bras k=1 : la masse de l'ancre sur C1 dépasse 32/48
    (des flotteurs ont adopté la convention unique — la cascade du docstring)."""
    g = PolyAdoptionGame(1, rng=_rng(100))
    anchor, _ = anchor_state(g, n_rounds=1500, anneal_to=0.1)
    assert anchor[0] > 32 / 48


# --------------------------------------------------------------------------- #
#  Gate G : analyse pre-enregistree -- l'arbre de decision sur donnees         #
#  synthetiques a verdict calcule a la main (le contrat est le verdict).       #
# --------------------------------------------------------------------------- #


_RADII = (0.05, 0.10, 0.15, 0.25, 0.35, 0.50)


def _write_synth_jsonl(path, arms, n_seeds=20):
    """Ecrit un JSONL synthetique : memes courbes B pour tous les seeds du bras."""
    import json as _json

    lines = []
    for k, a_val, b_curve in arms:
        for seed in range(n_seeds):
            lines.append(
                _json.dumps(
                    {
                        "k": k,
                        "seed": seed,
                        "anchor": [1.0] + [0.0] * 7,
                        "A_expH": a_val,
                        "basins": 1,
                        "radii": list(_RADII),
                        "B": list(b_curve),
                        "params": {
                            "n_rounds": 4000,
                            "window": 50,
                            "tau": 15,
                            "n_samples": 40,
                            "consigne_radius": 0.10,
                        },
                    }
                )
            )
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")


def test_analyse_verdict_reelle():
    """Curves concues pour tomber dans TOUTES les bandes -> ALTERITE_BUDGET_REELLE.

    Verifie a la main : B_MONO(0.05)=1.0 dans [0.90,1.00], deltaB=0.05 dans
    [0.02,0.25], r*_MONO=0.35 (B=0.5 a r=0.25 n'est PAS strictement < 0.50) dans
    [0.15,0.45], r*_COOP8=None (>0.60) dans [0.30,>0.60], pentes fenetre commune
    [0.35,0.50] : MONO |0.2-0.1|/0.15=0.667 vs COOP8 |0.82-0.8|/0.15=0.133
    (ratio 5.0 >= 1.5), A medians dans les bandes H5, tau(A,r*) > 0."""
    import tempfile
    from pathlib import Path

    arms = [
        (1, 1.0, [1.0, 1.0, 0.9, 0.5, 0.2, 0.1]),
        (2, 1.8, [1.0, 0.98, 0.95, 0.8, 0.6, 0.45]),
        (4, 3.4, [1.0, 0.99, 0.97, 0.9, 0.8, 0.7]),
        (8, 6.0, [0.95, 0.93, 0.9, 0.85, 0.82, 0.8]),
    ]
    with tempfile.TemporaryDirectory() as tmp:
        p = Path(tmp) / "sweep.jsonl"
        _write_synth_jsonl(p, arms)
        res = analyze_sweep(str(p))
    assert res["verdict"] == "ALTERITE_BUDGET_REELLE", res["verdict"]
    assert res["H1"]["ok"] and res["H2"]["ok"] and res["H3"]["ok"]
    assert res["H4"]["ok"] and res["H4"]["tau_kendall"] > 0
    assert res["H5"]["ok"]
    # Controles chiffres cles (tolerance : interpolation lineaire exacte).
    assert res["H2"]["r_star_MONO"] == pytest.approx(0.35)
    assert res["H3"]["ratio"] == pytest.approx((0.2 - 0.1) / (0.82 - 0.8), rel=1e-3)
    assert res["completeness"]["complete"] is True


def test_analyse_verdict_non_discriminant():
    """A(2) hors bande -> H5 echoue -> NON_DISCRIMINANT (arret, pas de verdict these)."""
    import tempfile
    from pathlib import Path

    arms = [
        (1, 1.0, [1.0, 1.0, 0.9, 0.5, 0.2, 0.1]),
        (2, 1.2, [1.0, 0.98, 0.95, 0.8, 0.6, 0.45]),  # 1.2 hors [1.5 ; 2.0]
        (4, 3.4, [1.0, 0.99, 0.97, 0.9, 0.8, 0.7]),
        (8, 6.0, [0.95, 0.93, 0.9, 0.85, 0.82, 0.8]),
    ]
    with tempfile.TemporaryDirectory() as tmp:
        p = Path(tmp) / "sweep.jsonl"
        _write_synth_jsonl(p, arms)
        res = analyze_sweep(str(p))
    assert res["H5"]["ok"] is False
    assert res["verdict"] == "NON_DISCRIMINANT"


def test_analyse_verdict_incomplet():
    """Sweep non termine (< 20 seeds/bras) -> verdict NON EMISSIBLE, jamais de demi-verdict."""
    import tempfile
    from pathlib import Path

    arms = [
        (1, 1.0, [1.0, 1.0, 0.9, 0.5, 0.2, 0.1]),
        (8, 6.0, [0.95, 0.93, 0.9, 0.85, 0.82, 0.8]),
    ]
    with tempfile.TemporaryDirectory() as tmp:
        p = Path(tmp) / "sweep.jsonl"
        _write_synth_jsonl(p, arms, n_seeds=3)
        res = analyze_sweep(str(p))
    assert "INCOMPLET" in res["verdict"]
    assert res["completeness"]["complete"] is False
