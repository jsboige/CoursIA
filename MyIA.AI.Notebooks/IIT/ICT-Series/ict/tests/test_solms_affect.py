"""Tests unitaires pour ``ict.solms_affect`` (tranche Solms & Friston 2018, Epic #8182).

Le module formalise la theise operationnelle de la source primaire (Solms &
Friston 2018, Front Psychol 9:2714) : la forme elementaire de la conscience est
l'**affect**, genere par un processus **homéostatique** (subcortical) formalise en
minimisation d'energie libre -- une **baisse** de l'incertitude attendue
``dU`` est sentie comme **plaisir** -- et dissociable des **contents** corticaux
(dissociation level/contents).

Le surrogate pre-enregistre (``docs/ict/solms-affect-pre-enregistrement.md``)
oppose deux architectures sur le meme terrain :
    * **H1 (Solms)** -- l'affect est genere par la dynamique ``-k_a dU``
      (subcortical) ; les contents sont une lecture corticale ``x @ W``.
    * **H0 (null)** -- l'affect est un readout cortical des contents ``w_a . c``.

La prediction signature (P1) : en H1 le level survit a l'ablation corticale
(conscience sans cortex), alors qu'en H0 il s'eteint. Les 5 predictions
pre-enregistees P1-P5 portent sur les graines d'etude (0, 1, 7, 42, 99).

Gates falsifiables (numerotes) :
    1.  ``homeostatic_trajectory`` : shapes + ``dU`` prend les deux signes.
    2.  ``affect_subcortical`` : ``a = -k_a dU`` (plaisir quand ``dU < 0``).
    3.  ``affect_cortical`` : ``a = w_a . c`` ; ``c = 0`` -> ``a = 0``.
    4.  ``content_readout`` : shapes ; ``x = 0`` -> ``c = 0``.
    5.  ``run_arm`` : signatures d'ablation (contents/affect supprimes).
    6.  ``case_verdict`` : structure du dict + verdict dans l'ensemble.
    7.  P1 : le level survit a l'ablation corticale (chaque graine).
    8.  P2 : l'affect suit le mecanisme energie-libre (médiane ``>= 0.7``).
    9.  P3 : specificite subcorticale (chaque graine).
    10. P4 : discrimination H1/H0 (médiane).
    11. P5 : corticalite des contents (chaque graine).
    12. ``verdict_robust_across_seeds`` : verdict SUPPORTED (cible) + structure.
    13. Determinisme : ``run_study`` deux fois -> resultats identiques.
    14. Le JSON committe ``solms_affect_results.json`` est reproductible.
"""

from __future__ import annotations

import json
import os
import sys

# Permettre l'import direct depuis le package ``ict`` (sans install develop).
_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

import numpy as np
import pytest

from ict import solms_affect as sa


def _rng(seed: int) -> np.random.Generator:
    return np.random.default_rng(seed)


# --------------------------------------------------------------------------- #
#  Gate 1 : homeostatic_trajectory -- shapes + dU prend les deux signes        #
# --------------------------------------------------------------------------- #


def test_homeostatic_trajectory_shapes_and_two_sign_dU():
    """La trajectoire renvoie ``x`` de forme ``(T, d)``, ``U`` et ``dU`` de forme
    ``(T,)``, et ``dU`` doit prendre les deux signes (le terrain fait monter et
    descendre l'incertitude attendue -- condition du mecanisme energie-libre)."""
    x, U, dU = sa.homeostatic_trajectory(d=4, T=200, rng=_rng(0))
    assert x.shape == (200, 4)
    assert U.shape == (200,)
    assert dU.shape == (200,)
    assert np.isfinite(x).all() and np.isfinite(U).all() and np.isfinite(dU).all()
    # dU doit avoir de la variance et les deux signes (sinon le terrain est
    # degene et P2 serait non-testable).
    assert float(np.std(dU)) > 0.0, "dU constant : terrain degene"
    assert dU.min() < 0.0 < dU.max(), "dU ne prend pas les deux signes"


# --------------------------------------------------------------------------- #
#  Gate 2 : affect_subcortical -- a = -k_a dU (plaisir quand dU < 0)           #
# --------------------------------------------------------------------------- #


def test_affect_subcortical_sign_follows_minus_dU():
    """``affect_subcortical(dU, k_a) = -k_a * dU``. Une baisse d'incertitude
    (``dU < 0``) est sentie comme plaisir (``a > 0``) ; une hausse (``dU > 0``)
    comme desplaisir (``a < 0``). C'est la citation 2, traduite."""
    dU = np.array([-1.0, 0.0, 1.0, -2.0, 0.5])
    a = sa.affect_subcortical(dU, k_a=2.0)
    np.testing.assert_allclose(a, -2.0 * dU)
    # Signe : dU<0 -> a>0 (plaisir) ; dU>0 -> a<0 (desplaisir).
    assert a[0] > 0.0 and a[2] < 0.0 and a[3] > 0.0 and a[4] < 0.0
    assert a[1] == 0.0


# --------------------------------------------------------------------------- #
#  Gate 3 : affect_cortical -- a = w_a . c ; c = 0 -> a = 0 (null)             #
# --------------------------------------------------------------------------- #


def test_affect_cortical_zero_when_content_zero():
    """L'affect H0 est un readout cortical des contents : ``a = w_a . c``.
    Si le cortex est retire (``c = 0``), l'affect s'eteint strictement --
    c'est la propriete qui distingue H0 de H1 (P4)."""
    c = np.array([[1.0, 2.0], [3.0, 4.0]])
    w_a = np.array([1.0, -1.0])
    a = sa.affect_cortical(c, w_a)
    np.testing.assert_allclose(a, [1.0 * 1.0 + -1.0 * 2.0, 1.0 * 3.0 + -1.0 * 4.0])
    # c = 0 -> a = 0 strictement.
    a0 = sa.affect_cortical(np.zeros((3, 2)), w_a)
    np.testing.assert_allclose(a0, 0.0)


# --------------------------------------------------------------------------- #
#  Gate 4 : content_readout -- shapes ; x = 0 -> c = 0                          #
# --------------------------------------------------------------------------- #


def test_content_readout_shapes_and_zero():
    """``content_readout(x, W) = x @ W`` de forme ``(T, m)`` ; ``x = 0`` -> ``c = 0``."""
    x = np.array([[1.0, 0.0, 1.0, 1.0], [0.0, 2.0, 1.0, 0.0]])
    W = np.arange(4 * 8, dtype=float).reshape(4, 8)
    c = sa.content_readout(x, W)
    assert c.shape == (2, 8)
    # x = 0 -> c = 0.
    c0 = sa.content_readout(np.zeros((3, 4)), W)
    np.testing.assert_allclose(c0, 0.0)


# --------------------------------------------------------------------------- #
#  Gate 5 : run_arm -- signatures d'ablation                                   #
# --------------------------------------------------------------------------- #


def test_run_arm_ablation_signatures():
    """Signatures d'ablation d'un bras H1 :
      * ``no_cortex``    -> contents supprimes (``content_rich == 0``), affect intact.
      * ``no_subcortex`` -> affect supprime (``feel == 0``).
    Et pour le null H0 : ``no_cortex`` -> affect supprime (``feel == 0``)."""
    rng = _rng(0)
    x, U, dU = sa.homeostatic_trajectory(d=4, T=120, rng=rng)
    W = rng.standard_normal((4, 8))
    w_a = rng.standard_normal(8)

    intact = sa.run_arm("h1", "none", x, dU, W, w_a, rng=rng)
    no_cortex = sa.run_arm("h1", "no_cortex", x, dU, W, w_a, rng=rng)
    no_subcortex = sa.run_arm("h1", "no_subcortex", x, dU, W, w_a, rng=rng)

    # intacts : les deux canaux actifs.
    assert intact["feel"] > 0.0 and intact["content_rich"] > 0.0
    # no_cortex : contents a zero, affect (subcortical) intact.
    assert no_cortex["content_rich"] == 0.0
    assert no_cortex["feel"] > 0.0
    # no_subcortex : affect a zero.
    assert no_subcortex["feel"] == 0.0

    # null H0 : l'affect etant un readout cortical, il s'eteint avec le cortex.
    h0_no_cortex = sa.run_arm("h0", "no_cortex", x, dU, W, w_a, rng=rng)
    assert h0_no_cortex["feel"] == 0.0
    h0_intact = sa.run_arm("h0", "none", x, dU, W, w_a, rng=rng)
    assert h0_intact["feel"] > 0.0


# --------------------------------------------------------------------------- #
#  Gate 6 : case_verdict -- structure du dict + verdict dans l'ensemble        #
# --------------------------------------------------------------------------- #


def test_case_verdict_structure():
    """``case_verdict`` renvoie toutes les cles documentees, avec les bons types,
    et un verdict de graine dans {PASS, PARTIAL}."""
    out = sa.case_verdict(seed=0)
    expected = {
        "seed", "feel_ratio_nocortex", "feel_ratio_nosubcortex",
        "content_ratio_nocortex", "h0_feel_ratio_nocortex",
        "dissociation_contrast", "valence_tracks_dU",
        "p1", "p2", "p3", "p4", "p5", "verdict",
    }
    assert set(out.keys()) == expected, (
        f"cles attendues {expected}, recues {set(out.keys())}"
    )
    assert isinstance(out["seed"], int)
    for k in ("p1", "p2", "p3", "p4", "p5"):
        assert isinstance(out[k], bool)
    for k in ("feel_ratio_nocortex", "valence_tracks_dU", "dissociation_contrast"):
        assert isinstance(out[k], float)
    assert out["verdict"] in {"PASS", "PARTIAL"}


# --------------------------------------------------------------------------- #
#  Gates 7-11 : les 5 predictions pre-enregistrées (cibles)                    #
# --------------------------------------------------------------------------- #


def test_p1_level_survives_cortical_ablation():
    """P1 (cible, « conscience sans cortex ») : le level survit a l'ablation
    corticale sur **chaque** graine d'etude : ``feel(no_cortex)/feel(intact) >= 0.5``."""
    for seed in (0, 1, 7, 42, 99):
        out = sa.case_verdict(seed=seed)
        assert out["p1"] is True, (
            f"seed={seed} : P1 (level survit a l'ablation corticale) tombe -- "
            f"feel_ratio_nocortex={out['feel_ratio_nocortex']:.3f} < 0.5"
        )
        assert out["feel_ratio_nocortex"] >= 0.5


def test_p2_affect_tracks_free_energy_mechanism():
    """P2 : l'affect suit le mecanisme energie-libre -- la médiane des graines de
    ``corr(a, -dU)`` est ``>= 0.7`` (la citation 2, mesuree, non triviale)."""
    vals = [sa.case_verdict(seed=s)["valence_tracks_dU"] for s in (0, 1, 7, 42, 99)]
    med = float(np.median(vals))
    assert med >= 0.7, f"P2 : mediana corr(a, -dU) = {med:.3f} < 0.7"
    # Et c'est une correlation reelle, pas 1.0 triviale (bruit de mesure present).
    assert med < 1.0


def test_p3_subcortical_specificity():
    """P3 : l'affect est specifique au generateur subcortical -- le retirer
    supprime le feel sur **chaque** graine : ratio <= 0.2."""
    for seed in (0, 1, 7, 42, 99):
        out = sa.case_verdict(seed=seed)
        assert out["p3"] is True, (
            f"seed={seed} : P3 (specificite subcorticale) tombe -- "
            f"feel_ratio_nosubcortex={out['feel_ratio_nosubcortex']:.3f} > 0.2"
        )
        assert out["feel_ratio_nosubcortex"] <= 0.2


def test_p4_h1_vs_h0_discrimination():
    """P4 : la dissociation est specifique a l'architecture H1 -- le contraste
    ``[H1 no_cortex/intact] - [H0 no_cortex/intact]`` a la médiane est ``>= 0.3``
    (H1 survit ~1.0, H0 s'eteint 0.0)."""
    vals = [sa.case_verdict(seed=s)["dissociation_contrast"] for s in (0, 1, 7, 42, 99)]
    med = float(np.median(vals))
    assert med >= 0.3, f"P4 : mediana contraste H1/H0 = {med:.3f} < 0.3"


def test_p5_content_is_cortical():
    """P5 : les contents sont corticaux -- l'ablation corticale les supprime sur
    **chaque** graine : ratio <= 0.3."""
    for seed in (0, 1, 7, 42, 99):
        out = sa.case_verdict(seed=seed)
        assert out["p5"] is True, (
            f"seed={seed} : P5 (corticalite des contents) tombe -- "
            f"content_ratio_nocortex={out['content_ratio_nocortex']:.3f} > 0.3"
        )
        assert out["content_ratio_nocortex"] <= 0.3


# --------------------------------------------------------------------------- #
#  Gate 12 : verdict_robust_across_seeds -- SUPPORTED (cible) + structure       #
# --------------------------------------------------------------------------- #


def test_verdict_robust_supported_and_structure():
    """Sur les 5 graines d'etude, le verdict agregé est ``SUPPORTED`` (cible
    pre-enregistree) et la structure du dict est complete."""
    out = sa.verdict_robust_across_seeds(seeds=(0, 1, 7, 42, 99))
    expected = {
        "seeds", "per_seed", "p1_each_seed", "p2_median", "p3_each_seed",
        "p4_median", "p5_each_seed", "verdict",
    }
    assert set(out.keys()) == expected, (
        f"cles attendues {expected}, recues {set(out.keys())}"
    )
    assert list(out["seeds"]) == [0, 1, 7, 42, 99]
    assert len(out["per_seed"]) == 5
    for flag in ("p1_each_seed", "p2_median", "p3_each_seed", "p4_median", "p5_each_seed"):
        assert out[flag] is True, f"{flag} = False (cible pre-enregistree non tenue)"
    assert out["verdict"] == "SUPPORTED"


# --------------------------------------------------------------------------- #
#  Gate 13 : determinisme -- run_study deux fois -> resultats identiques        #
# --------------------------------------------------------------------------- #


def test_run_study_determinism():
    """``run_study`` est deterministe : deux executions sur les memes graines
    rendent des dictionnaires identiques (les champs numeriques bit-a-bit)."""
    r1 = sa.run_study(seeds=(0, 1, 7))
    r2 = sa.run_study(seeds=(0, 1, 7))
    assert r1["verdict"] == r2["verdict"]
    for a, b in zip(r1["per_seed"], r2["per_seed"]):
        for k in ("feel_ratio_nocortex", "valence_tracks_dU", "dissociation_contrast"):
            assert a[k] == b[k], f"non-determinisme sur {k} : {a[k]} != {b[k]}"


# --------------------------------------------------------------------------- #
#  Gate 14 : le JSON committe est reproductible                                #
# --------------------------------------------------------------------------- #


def test_committed_results_json_reproducible():
    """Le ``solms_affect_results.json`` committe (produit par execution reelle)
    est chargeable, porte le verdict ``SUPPORTED``, et ses valeurs par graine
    correspondent a un ``run_study`` frais (reproductibilite de l'artefact)."""
    json_path = os.path.join(_ROOT, "solms_affect_results.json")
    assert os.path.exists(json_path), "solms_affect_results.json manquant (a generer)"
    with open(json_path, encoding="utf-8") as fh:
        committed = json.load(fh)

    assert committed["verdict"] == "SUPPORTED"
    assert committed["seeds"] == [0, 1, 7, 42, 99]

    fresh = sa.run_study(seeds=(0, 1, 7, 42, 99))
    for c, f in zip(committed["per_seed"], fresh["per_seed"]):
        for k in ("feel_ratio_nocortex", "valence_tracks_dU", "dissociation_contrast"):
            assert c[k] == f[k], (
                f"JSON committe non reproductible : {k} committe={c[k]} != "
                f"frais={f[k]} (re-execute le module pour regenerer le JSON)"
            )
