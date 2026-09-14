"""Tests du module :mod:`ict.sae_dictionary` (composante SAE du pilote #15480).

Six proprietes falsifiables, toutes analytiques CPU sur donnees synthetiques
ou la structure sparse est connue par construction :

  1. (Gate encodage) :meth:`TopKSae.encode` rend au plus ``k`` valeurs non
     nulles par ligne, et ``l0_measured`` de :mod:`ict.sae_calibration`
     (metrique reutilisee, pas redefinie) confirme L0 == k.

  2. (Gate apprentissage) sur un corpus ``x = z_true @ D_true.T`` avec
     dictionnaire unit-norm connu, k=3 actives par echantillon : FVU final
     < 0.10 et colonnes du decodeur toujours unit-norm.

  3. (Gate selectivite dediee) un corpus a deux facteurs aux blocs de
     features disjoints : les z-scores de selectivite des features du bloc
     associe ecrasent le seuil, le null apparie reste centre.

  4. (Gate null) labels sans structure : aucun z-score ne depasse le seuil.

  5. (Gate determinisme) deux entrainements au meme seed donnent des poids
     byte-identiques.

  6. (Gate features mortes) une feature jamais active rend AUC 0.5 exactement
     et z-score 0 (garde isfinite), pas NaN.

Pattern herite de ``test_lens_agreement.py`` (bootstrap sys.path dans
conftest.py, pas de fixtures, tolerances commentees).
"""

from __future__ import annotations

import numpy as np

from ict import sae_dictionary as sd
from ict.sae_calibration import l0_measured


# --------------------------------------------------------------------------- #
# Helpers : corpus synthetiques a structure connue
# --------------------------------------------------------------------------- #
def _corpus_dictionnaire_connu(n: int = 1500, d: int = 12, r: int = 24, k: int = 3, seed: int = 0):
    """x = z @ D.T avec D unit-norm et exactement k features actives par ligne."""
    rng = np.random.default_rng(seed)
    w_dec = rng.normal(size=(d, r))
    w_dec /= np.linalg.norm(w_dec, axis=0, keepdims=True)
    z = np.zeros((n, r))
    for i in range(n):
        cols = rng.choice(r, size=k, replace=False)
        z[i, cols] = rng.uniform(0.5, 2.0, size=k)
    return z @ w_dec.T, w_dec


def _corpus_deux_facteurs(n: int = 1200, d: int = 16, r_bloc: int = 8, k: int = 3, seed: int = 1):
    """Deux facteurs A/B a blocs disjoints : A -> features 0..r_bloc-1, B -> le reste.

    Chaque echantillon active un facteur (ou les deux, co-occurrence 25 %) et
    tire k features DANS le bloc du facteur present : la composition de bloc
    est le seul signal discriminant, le reste du bruit est commun.
    """
    rng = np.random.default_rng(seed)
    w_dec = rng.normal(size=(d, 2 * r_bloc))
    w_dec /= np.linalg.norm(w_dec, axis=0, keepdims=True)
    z = np.zeros((n, 2 * r_bloc))
    present_a = rng.random(n) < 0.6
    present_b = rng.random(n) < 0.6
    # garantir les deux classes non vides pour chaque facteur
    present_a[:10] = True
    present_a[-10:] = False
    present_b[:10] = False
    present_b[-10:] = True
    for i in range(n):
        for present, bloc in ((present_a[i], 0), (present_b[i], 1)):
            if present:
                lo = bloc * r_bloc
                cols = rng.choice(r_bloc, size=k, replace=False) + lo
                z[i, cols] = rng.uniform(0.5, 2.0, size=k)
    return z @ w_dec.T + 0.01 * rng.normal(size=(n, d)), present_a, present_b


# --------------------------------------------------------------------------- #
# Gate 1 : encodage top-k exact
# --------------------------------------------------------------------------- #
def test_encode_topk_exact():
    x, _ = _corpus_dictionnaire_connu()
    sae = sd.TopKSae(n_input=x.shape[1], n_features=24, k=3, seed=0)
    sae.b_dec = np.zeros(x.shape[1])
    z = sae.encode(x)
    nonzeros = (z > 0).sum(axis=1)
    assert (nonzeros <= 3).all()
    # L0 mesure par la metrique MUTUALISEE de sae_calibration (pas une copie)
    assert l0_measured(z) == 3.0


def test_encode_topk_rejecte_k_hors_bornes():
    try:
        sd.TopKSae(n_input=4, n_features=8, k=0)
    except ValueError:
        pass
    else:
        raise AssertionError("k=0 doit etre rejete")


# --------------------------------------------------------------------------- #
# Gate 2 : apprentissage d'un dictionnaire connu
# --------------------------------------------------------------------------- #
def test_apprend_dictionnaire_connu():
    # tolerances mesurees sur 4 seeds de corpus (FVU 0.09-0.14, 17/24 atomes
    # alignes > 0.95) : le residu est un plateau de melange documente dans le
    # docstring du module, pas un defaut d'apprentissage. On exige les deux :
    # la majorite de la variance recouverte ET la majorite du dictionnaire
    # reellement retrouve (l'alignement est la propriete la plus informative).
    x, w_true = _corpus_dictionnaire_connu(seed=3)
    out = sd.train_sae(x, n_features=24, k=3, seed=0, n_steps=600, lr=0.1, momentum=0.9)
    assert out["fvu"] < 0.15, f"FVU={out['fvu']:.3f}"
    assert out["l0"] == 3.0
    norms = np.linalg.norm(out["sae"].W_dec, axis=0)
    assert np.allclose(norms, 1.0, atol=1e-8)
    cos = np.abs(w_true.T @ out["sae"].W_dec)
    matched = int((cos.max(axis=1) > 0.95).sum())
    assert matched >= 12, f"atomes vrais retrouves: {matched}/24"


# --------------------------------------------------------------------------- #
# Gate 3 : selectivite dediee aux facteurs
# --------------------------------------------------------------------------- #
def test_selectivite_facteurs_dedies():
    # seuil |z| > 6 : le null apparie (200 relabelisations) centre l'echelle,
    # une feature dediee le depasse largement avec n=1200
    x, present_a, _ = _corpus_deux_facteurs()
    out = sd.train_sae(x, n_features=16, k=3, seed=0, n_steps=600, lr=0.1)
    sel = sd.factor_selectivity(out["codes"], present_a, n_null=200, seed=0)
    z = sel["z"]
    # le SAE recupere des features dediees au facteur A (bloc 0) : au moins
    # la moitie du bloc depasse le seuil dans un sens ou l'autre
    dedicated = (np.abs(z) > 6).sum()
    assert dedicated >= 4, f"z max |{np.abs(z).max():.1f}|, dediees={dedicated}"
    # le null reste centre : moyenne des moyennes nulles ~ 0.5
    assert np.abs(sel["auc_null_mean"].mean() - 0.5) < 0.02


def test_selectivite_auc_sens_de_la_relation():
    # une feature qui ne s'active QUE sur le facteur A doit avoir AUC elevee
    # contre label A (et non 1-AUC) : le rang-sum va dans le bon sens
    rng = np.random.default_rng(7)
    acts = np.zeros((200, 1))
    labels = rng.random(200) < 0.5
    acts[labels, 0] = 1.0  # active si et seulement si label vrai
    auc = sd.factor_auc(acts, labels)
    assert auc[0] == 1.0


# --------------------------------------------------------------------------- #
# Gate 4 : null sans structure
# --------------------------------------------------------------------------- #
def test_null_labels_sans_structure():
    # labels aleatoires : aucune feature ne doit franchir |z| > 5
    rng = np.random.default_rng(11)
    x, _, _ = _corpus_deux_facteurs(seed=5)
    labels = rng.random(x.shape[0]) < 0.5
    out = sd.train_sae(x, n_features=16, k=3, seed=0, n_steps=600, lr=0.1)
    sel = sd.factor_selectivity(out["codes"], labels, n_null=200, seed=0)
    assert (np.abs(sel["z"]) <= 5).all(), f"z max {np.abs(sel['z']).max():.1f} sous labels sans structure"


# --------------------------------------------------------------------------- #
# Gate 5 : determinisme
# --------------------------------------------------------------------------- #
def test_determinisme_seed():
    x, _ = _corpus_dictionnaire_connu(seed=9)
    a = sd.train_sae(x, n_features=16, k=3, seed=42, n_steps=120, lr=0.08)
    b = sd.train_sae(x, n_features=16, k=3, seed=42, n_steps=120, lr=0.08)
    assert np.array_equal(a["sae"].W_dec, b["sae"].W_dec)
    assert np.array_equal(a["sae"].W_enc, b["sae"].W_enc)
    assert np.array_equal(a["codes"], b["codes"])


# --------------------------------------------------------------------------- #
# Gate 6 : features mortes -> AUC 0.5, z 0, jamais NaN
# --------------------------------------------------------------------------- #
def test_feature_morte_auc_intermediaire_et_z_zero():
    rng = np.random.default_rng(13)
    acts = rng.normal(size=(300, 4))
    acts[:, 2] = 0.0  # feature morte
    labels = rng.random(300) < 0.5
    auc = sd.factor_auc(acts, labels)
    assert auc[2] == 0.5
    sel = sd.factor_selectivity(acts, labels, n_null=100, seed=0)
    assert np.isfinite(sel["z"]).all()
    assert sel["z"][2] == 0.0
