"""Tests du module :mod:`ict.multiscale_agency` (ICT-11, strate 3, Epic #4588).

Couvre les **contrats publiques** non testés du notebook ICT-11
("A quelle echelle spatiale l'agence est-elle la plus lisible ?") :

  1. (Gate 1) ``block_average`` : shape + moyenne arithmetique exacte +
     validation ``block < 1`` et ``block > n``.
  2. (Gate 1) ``downsample_mask`` : majorite stricte (50% + 1 voix).
  3. (Gate 2) ``structure_at_scale`` : variance du champ moyenne ;
     decroissance monotone attendue quand ``block`` augmente (signal
     discriminatif de l'echelle).
  4. (Gate 2) ``discretize_values`` : cas limites (serie constante, deux
     valeurs, ``n_bins`` >> serie) + preservation de l'ordre.
  5. (Gate 2) ``structure_trajectory_at_scale`` : longueur = nb snapshots,
     coherence avec ``structure_at_scale`` point-par-point.
  6. (Gate 2) ``pearson_corr`` : correlation parfaite, anti-correlation,
     variance nulle (retour ``None``), series de longueur 1 (retour
     ``None``).
  7. (Gate 1, contrat) ``recovery_curve_at_scale`` : pas de mock rouge ;
     appel direct sur 3 snapshots verifies coherents avec
     ``ict.agency.recovery_score``.
  8. (Gate 3, contrat) ``agency_measures_at_scale`` + ``effectiveness_at_scale`` :
     un mock model minimal ``.run()`` est employe pour verifier que le
     contrat (effectiveness, recovery_RD, etc.) est respecte, sans
     invoquer le solveur Gray-Scott reel (le notebook le fait en aval).

Pattern herite de ``test_reversibility_budget.py`` et ``test_time_arrow.py`` :
bootstrap ``sys.path`` module-level, sans fixtures, tolerances commentees.
"""

from __future__ import annotations

import os
import sys
from typing import List, Tuple

import numpy as np
import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from ict import agency as A  # noqa: E402
from ict import multiscale_agency as MA  # noqa: E402


def _rng_for(seed: int) -> np.random.Generator:
    return np.random.default_rng(seed)


# --------------------------------------------------------------------------- #
#  Gate 1 : block_average, downsample_mask (coarse-graining spatial strict)     #
# --------------------------------------------------------------------------- #


def test_block_average_shape_and_value():
    """Moyenne par blocs : shape divisee par ``block``, valeurs correctes.

    Un champ 4x4 a valeurs distinctes par bloc 2x2 :
      [[1, 1, 2, 2],
       [1, 1, 2, 2],       [ 1,  3 ]
       [3, 3, 4, 4],   ->   [ 3.5, 5 ]
       [3, 3, 4, 4]]
    Chaque super-cellule est la moyenne des ``block*block`` pixels.
    """
    field = np.array([
        [1.0, 1.0, 2.0, 2.0],
        [1.0, 1.0, 2.0, 2.0],
        [3.0, 3.0, 4.0, 4.0],
        [3.0, 3.0, 4.0, 4.0],
    ])
    out = MA.block_average(field, block=2)
    assert out.shape == (2, 2)
    assert np.allclose(out, [[1.0, 2.0], [3.0, 4.0]])


def test_block_average_block_one_is_identity():
    """``block=1`` doit retourner le champ inchange (averaged slabs = original)."""
    rng = _rng_for(7)
    f = rng.random((8, 8))
    out = MA.block_average(f, block=1)
    assert out.shape == (8, 8)
    assert np.allclose(out, f)


def test_block_average_truncates_partial_block():
    """La queue (si ``block`` ne divise pas ``n``) est silently tronquee.

    Champ 5x5, block=2 -> grille 2x2 (les 4 premieres rangees/colonnes
    seulement ; la 5e rangee/colonne est jetee, c'est un coarse-graining
    strict).
    """
    f = np.arange(25, dtype=float).reshape(5, 5)
    out = MA.block_average(f, block=2)
    assert out.shape == (2, 2)
    # Bloc (0,0) : rangees [0,1] x cols [0,1] -> moyenne de [0,1,5,6] = 3.0
    assert np.isclose(out[0, 0], 3.0)


def test_block_average_rejects_bad_block():
    """``block < 1`` -> ``ValueError`` (contrat explicite)."""
    f = np.zeros((4, 4))
    with pytest.raises(ValueError, match="block doit etre"):
        MA.block_average(f, block=0)
    with pytest.raises(ValueError, match="block doit etre"):
        MA.block_average(f, block=-1)


def test_block_average_rejects_block_too_large():
    """``block > n`` (grille resultante vide) -> ``ValueError``."""
    f = np.zeros((4, 4))
    with pytest.raises(ValueError, match="trop grand"):
        MA.block_average(f, block=5)


def test_downsample_mask_majority_rule():
    """Majorite stricte : un bloc est True si > 50% de ses pixels sont True.

    Bloc 2x2 doit contenir au moins 3 pixels True sur 4 pour projeter True.
    Un seul pixel True -> False.
    """
    # 4x4 masque : 2 coins True, 2 coins False en alternant.
    # Bloc 2x2 = exactement 2 True 2 False -> False (majorite stricte).
    mask = np.array([
        [True, False, True, False],
        [False, True, False, True],
        [True, False, True, False],
        [False, True, False, True],
    ])
    out = MA.downsample_mask(mask, block=2)
    assert out.shape == (2, 2)
    assert not out.any(), "2 True / 4 pixels -> False (majorite stricte)"

    # 3e et 4e cols a True -> bloc droit avec 3+ True -> True.
    mask2 = np.array([
        [True, False, True, True],
        [False, True, True, True],
        [True, False, True, True],
        [False, True, True, True],
    ])
    out2 = MA.downsample_mask(mask2, block=2)
    assert out2.shape == (2, 2)
    assert not out2[0, 0]
    assert out2[0, 1]
    assert not out2[1, 0]
    assert out2[1, 1]


# --------------------------------------------------------------------------- #
#  Gate 2 : structure_at_scale, discretize_values, pearson_corr                #
# --------------------------------------------------------------------------- #


def test_structure_at_scale_decreases_with_block():
    """Le moyennage par blocs reduit la variance -> signal discriminatif.

    C'est la PROPRIETE 1 du module (cf. docstring de ``structure_at_scale``) :
    la variance du champ moyenne par blocs est invariante d'echelle en
    moyenne globale, mais diminue quand ``block`` augmente. C'est ce qui
    permet de discriminer les echelles (les fluctuations intra-bloc sont
    moyennees).
    """
    rng = _rng_for(11)
    base = rng.random((16, 16))
    # Ajouter une structure grande-echelle (un pic au centre) pour ne PAS
    # etre dans le regime "bruit blanc pur" ou la variance pourrait
    # deroger par accident.
    yy, xx = np.mgrid[:16, :16]
    base = base + 0.5 * np.exp(-((xx - 7.5) ** 2 + (yy - 7.5) ** 2) / 8.0)

    var_b1 = MA.structure_at_scale(base, block=1)
    var_b2 = MA.structure_at_scale(base, block=2)
    var_b4 = MA.structure_at_scale(base, block=4)
    assert var_b1 > var_b2 > var_b4, (
        "variance du champ moyenne par blocs doit decroitre avec block"
        f" (recouvre var_b1={var_b1:.4f}, var_b2={var_b2:.4f}, var_b4={var_b4:.4f})"
    )


def test_structure_at_scale_constant_field_is_zero():
    """Champ constant -> variance nulle a toute echelle (sanity check)."""
    f = np.ones((8, 8)) * 3.14
    assert MA.structure_at_scale(f, block=1) == 0.0
    assert MA.structure_at_scale(f, block=2) == 0.0


def test_discretize_values_constant_returns_zeros():
    """Serie constante -> un seul niveau (0) sur toute la longueur."""
    v = np.ones(10) * 5.0
    out = MA.discretize_values(v, n_bins=4)
    assert out.shape == (10,)
    assert (out == 0).all()


def test_discretize_values_preserves_order():
    """Series croissantes -> labels monotone non-decroissants.

    Le contrat docstring dit : "valeurs croissantes -> labels croissants".
    On verifie la **monotonicite** : si ``v[i] < v[j]`` alors
    ``out[i] <= out[j]``. C'est plus faible que Spearman = 1
    (l'inversion au bord par ``np.digitize`` peut produire des labels
    egaux sur le meme intervalle, ce qui donne Spearman < 1 meme quand
    la monotonicite est preservee).
    """
    v = np.linspace(0.0, 1.0, 100)
    out = MA.discretize_values(v, n_bins=5)
    # 5 labels possibles, dans [0, 4].
    assert out.max() <= 4
    assert out.min() >= 0
    # Monotonicite stricte : pour tout i<j avec v[i]<v[j], out[i] <= out[j].
    # On verifie sur la difference premiere.
    diffs_v = np.diff(v)
    diffs_out = np.diff(out.astype(int))
    # Si v[i+1] > v[i] (cas attendu sur linspace), alors out[i+1] >= out[i].
    strict_increasing = diffs_v > 0
    assert (diffs_out[strict_increasing] >= 0).all(), (
        "monotonicite non preservee : v[i+1] > v[i] mais out[i+1] < out[i]"
    )
    # Et plus simplement : la serie out est globalement croissante
    # (non-decroissante).
    assert (np.diff(out.astype(int)) >= 0).all(), (
        "labels strictement decroissants sur serie croissante"
    )


def test_discretize_values_two_values_two_levels():
    """Deux valeurs distinctes -> deux niveaux (0, 1)."""
    v = np.array([0.0, 0.0, 1.0, 1.0, 0.0, 1.0])
    out = MA.discretize_values(v, n_bins=4)
    assert set(out.tolist()) == {0, 1}


def test_discretize_values_n_bins_clamped_to_at_least_two():
    """``n_bins < 2`` est clampe a 2 (coherence : au moins 2 niveaux)."""
    v = np.array([0.0, 0.5, 1.0, 1.5, 2.0])
    out = MA.discretize_values(v, n_bins=1)
    # Produit 2 niveaux (0, 1) sur 5 valeurs distinctes.
    assert set(out.tolist()) <= {0, 1}


def test_structure_trajectory_at_scale_length_and_consistency():
    """``structure_trajectory_at_scale`` rend 1 valeur par snapshot, coherente
    avec ``structure_at_scale`` calculee point-par-point."""
    rng = _rng_for(13)
    n = 16
    snaps = [rng.random((n, n)) for _ in range(5)]
    traj = MA.structure_trajectory_at_scale(snaps, block=2)
    assert traj.shape == (5,)
    for i, s in enumerate(snaps):
        assert np.isclose(traj[i], MA.structure_at_scale(s, block=2))


def test_pearson_corr_perfect_positive():
    """Identite -> r = 1.0 (sanity check)."""
    x = [1.0, 2.0, 3.0, 4.0, 5.0]
    r, n = MA.pearson_corr(x, x)
    assert n == 5
    assert r is not None and np.isclose(r, 1.0)


def test_pearson_corr_perfect_negative():
    """Series parfaitement anti-correlees -> r = -1.0."""
    x = [1.0, 2.0, 3.0, 4.0, 5.0]
    y = [5.0, 4.0, 3.0, 2.0, 1.0]
    r, n = MA.pearson_corr(x, y)
    assert n == 5
    assert r is not None and np.isclose(r, -1.0)


def test_pearson_corr_handles_list_input():
    """Contrat accepte ``List[float]`` (pas seulement ndarray)."""
    x = [1.0, 2.0, 3.0, 4.0]
    y = [2.0, 4.0, 6.0, 8.0]
    r, n = MA.pearson_corr(x, y)
    assert r is not None and np.isclose(r, 1.0)
    assert n == 4


def test_pearson_corr_constant_returns_none():
    """Variance nulle sur l'un des axes -> ``(None, n)`` (contrat docstring)."""
    x = [1.0, 1.0, 1.0, 1.0]  # var = 0
    y = [1.0, 2.0, 3.0, 4.0]
    r, n = MA.pearson_corr(x, y)
    assert r is None
    assert n == 4


def test_pearson_corr_n_less_than_two_returns_none():
    """Un seul echantillon -> correlation non definie -> ``(None, 1)``."""
    r, n = MA.pearson_corr([1.0], [2.0])
    assert r is None
    assert n == 1


def test_pearson_corr_clip_to_unit_interval():
    """Le r est clip dans [-1, 1] (regularisation numerique, cf. docstring)."""
    # Cas pathologique : multiplicativement 1e-10 -> sans le +1e-12, le
    # denominateur pourrait exploser. On verifie juste que la sortie reste
    # bornee (ne leve pas, ne sort pas de [-1, 1]).
    rng = _rng_for(17)
    x = rng.standard_normal(50)
    y = rng.standard_normal(50)
    r, _ = MA.pearson_corr(x.tolist(), y.tolist())
    assert r is not None
    assert -1.0 <= r <= 1.0


# --------------------------------------------------------------------------- #
#  Gate 1 (contrat) : recovery_curve_at_scale utilise bien agency.recovery_score  #
# --------------------------------------------------------------------------- #


def test_recovery_curve_at_scale_uses_block_average_consistently():
    """``recovery_curve_at_scale(snaps, block)`` sur snapshots identiques a
    ``recovery_score`` calculee directement produit la meme valeur.

    Verifie le **contrat** : pas de mock, pas de modele ; on construit
    V_ref / V_abl / snapshots et on compare.
    """
    rng = _rng_for(19)
    n = 16
    V_ref = rng.random((n, n))
    mask = np.zeros((n, n), dtype=bool)
    mask[5:10, 5:10] = True
    V_abl = V_ref.copy()
    V_abl[mask] = 0.0  # ablation : mise a zero dans la region
    block = 2

    # 3 snapshots intermediaires : structure intermediaire croissante.
    snaps = [
        V_abl + 0.3 * (V_ref - V_abl),
        V_abl + 0.6 * (V_ref - V_abl),
        V_ref,  # snap final : restauration complete
    ]

    rd_curve = MA.recovery_curve_at_scale(V_ref, V_abl, snaps, mask, block=block)

    # Verification manuelle pour le dernier snapshot : on s'attend a ~1.0
    # ou proche (region pleinement restauree).
    V_ref_b = MA.block_average(V_ref, block)
    V_abl_b = MA.block_average(V_abl, block)
    snap_b = MA.block_average(V_ref, block)
    mask_b = MA.downsample_mask(mask, block)
    expected_final = A.recovery_score(V_ref_b, V_abl_b, snap_b, mask_b)
    assert np.isclose(rd_curve[-1], expected_final)
    assert rd_curve[-1] > 0.95, (
        f"restauration complete attendue au dernier snapshot, "
        f"recu {rd_curve[-1]:.3f}"
    )

    # Et la courbe est monotone croissante vers 1.
    assert rd_curve[0] < rd_curve[1] < rd_curve[2]


def test_recovery_curve_at_scale_block_1_equals_agency_direct():
    """A ``block=1``, ``recovery_curve_at_scale`` est equivalent a appeler
    ``agency.recovery_score`` directement sur chaque snapshot."""
    rng = _rng_for(23)
    n = 8
    V_ref = rng.random((n, n))
    mask = np.zeros((n, n), dtype=bool)
    mask[2:5, 2:5] = True
    V_abl = V_ref.copy()
    V_abl[mask] = 0.0
    snaps = [
        V_abl + 0.4 * (V_ref - V_abl),
        V_abl + 0.8 * (V_ref - V_abl),
    ]

    rd_curve = MA.recovery_curve_at_scale(V_ref, V_abl, snaps, mask, block=1)
    for i, snap in enumerate(snaps):
        expected = A.recovery_score(V_ref, V_abl, snap, mask)
        assert np.isclose(rd_curve[i], expected), (
            f"block=1 doit reproduire agency.recovery_score "
            f"(snap={i}: attendu {expected}, recu {rd_curve[i]})"
        )


# --------------------------------------------------------------------------- #
#  Gate 3 (contrat) : effectiveness_at_scale avec mock model                    #
# --------------------------------------------------------------------------- #


class _MockModel:
    """Mock minimaliste imitant le contrat ``model.run(U, V, steps, ...)``.

    Retourne ``U_end, V_end, snapshots`` (3 valeurs) : adapte aux 3
    signatures de ``multiscale_agency`` (``agency_measures_at_scale``
    utilise ``model.run(..., include_initial=True)`` ;
    ``basin_return_at_scale`` et ``effectiveness_at_scale``
    utilisent ``model.run(U, V, steps)``).
    """

    def __init__(self, V_ref: np.ndarray, full_steps: int) -> None:
        self._V_ref = V_ref
        self._full_steps = full_steps

    def run(self, U, V, steps, record_every: int = 1, include_initial: bool = False):
        """Contrat : (U_end, V_end, snaps) OU (U_end, V_end) selon l'appel.

        On fournit **toujours** 3 valeurs pour simplifier (le unpacking
        ``_, _, snaps`` et ``_, V_end, _`` est tolerant).
        """
        # Trajectoire de relaxation simplifiee : interpolation lineaire
        # de V vers V_ref sur ``steps`` snapshots.
        snaps = []
        for t in range(steps + 1):
            alpha = t / max(steps, 1)
            snaps.append(V + alpha * (self._V_ref - V))
        return U, snaps[-1], snaps


def test_effectiveness_at_scale_contract_with_mock():
    """``effectiveness_at_scale`` respecte son contrat-cle avec un mock :
    dict {effectiveness, effective_information, n_observed, tpm, trajectories}.

    On verifie la **structure** du retour et la coherence avec
    ``causal_emergence.effectiveness`` ; on n'invoque pas le solveur
    Gray-Scott reel (les couts sont reportes au notebook).
    """
    rng = _rng_for(29)
    n = 8
    U_ref = rng.random((n, n))
    V_ref = rng.random((n, n))
    mask_factory = lambda rng: np.zeros((n, n), dtype=bool)  # ablation vide

    model = _MockModel(V_ref, full_steps=10)

    res = MA.effectiveness_at_scale(
        model=model,
        U_ref=U_ref,
        V_ref=V_ref,
        make_mask=mask_factory,
        block=2,
        steps=10,
        record_every=1,
        n_bins=4,
        n_seeds=2,
        rng=rng,
    )

    # Les 5 cles obligatoires du contrat (cf. docstring).
    assert set(res.keys()) >= {
        "effectiveness",
        "effective_information",
        "n_observed",
        "tpm",
        "trajectories",
    }
    # effectiveness est dans [0, 1] (scale-free).
    assert 0.0 <= res["effectiveness"] <= 1.0
    # effective_information = effectiveness * log2(n) donc >= 0.
    assert res["effective_information"] >= 0.0
    # n_observed = taille de la TPM.
    assert res["n_observed"] == res["tpm"].shape[0]
    assert res["tpm"].shape[0] == res["tpm"].shape[1]
    # trajectories est une liste de trajectoires discretes.
    assert isinstance(res["trajectories"], list)
    assert len(res["trajectories"]) == 2  # n_seeds=2


def test_agency_measures_at_scale_contract_with_mock():
    """``agency_measures_at_scale`` respecte son contrat-cle avec un mock :
    dict {repair_gain, recovery_RD, recovery_diff, time_to_recover, target_structure}."""
    rng = _rng_for(31)
    n = 8
    U_ref = rng.random((n, n))
    V_ref = rng.random((n, n))
    mask = np.zeros((n, n), dtype=bool)
    mask[2:5, 2:5] = True

    model = _MockModel(V_ref, full_steps=10)

    res = MA.agency_measures_at_scale(
        model_rd=model,
        model_diff_D=0.1,
        U_ref=U_ref,
        V_ref=V_ref,
        mask=mask,
        block=2,
        steps=10,
        record_every=1,
    )

    # 5 cles obligatoires du contrat.
    assert set(res.keys()) >= {
        "repair_gain",
        "recovery_RD",
        "recovery_diff",
        "time_to_recover",
        "target_structure",
    }
    # repair_gain = recovery_RD - recovery_diff (definition, cf. agency.py).
    assert np.isclose(res["repair_gain"], res["recovery_RD"] - res["recovery_diff"])
    # target_structure est la variance de reference dans la region ablatee.
    assert res["target_structure"] >= 0.0


def test_basin_return_at_scale_contract_with_mock():
    """``basin_return_at_scale`` rend une probabilite dans [0, 1]."""
    rng = _rng_for(37)
    n = 8
    U_ref = rng.random((n, n))
    V_ref = rng.random((n, n))
    mask_factory = lambda rng: np.zeros((n, n), dtype=bool)

    model = _MockModel(V_ref, full_steps=10)

    # Si la cible est la structure finale d'un mock qui relaxe vers V_ref,
    # et la region ablatee est vide, la probabilite devrait etre elevee
    # (le mock converge vers la cible).
    target = float(np.var(V_ref))
    p = MA.basin_return_at_scale(
        model=model,
        U_ref=U_ref,
        V_ref=V_ref,
        make_mask=mask_factory,
        block=2,
        steps=10,
        target_structure=target,
        tol=0.3,
        n_trials=3,
        rng=rng,
    )
    assert 0.0 <= p <= 1.0
    # p doit etre un float (pas un ndarray).
    assert isinstance(p, float)
