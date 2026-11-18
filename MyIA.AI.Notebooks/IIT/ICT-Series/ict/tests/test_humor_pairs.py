# -*- coding: utf-8 -*-
"""Tests des couches corpus + mesure de humor_pairs (#14035, tranche 1)."""
from __future__ import annotations

import json
import os
from pathlib import Path

import numpy as np
import pytest

from ict.humor_pairs import (
    LABELS,
    _common_prefix_len,
    banc_humour_path,
    build_pairs,
    build_prompts_json,
    label_distribution,
    load_corpus_dur,
    measure_global_max_null,
    measure_humor_differential,
    validate_corpus,
    validate_pairs,
)

# Depuis l'extraction #20316, le corpus vit dans l'organe GameTheory/humour_banc
# (fichiers committes) : aucun secret, aucun reseau -- ces tests tournent partout.


@pytest.fixture(scope="module")
def corpus() -> list[dict]:
    return load_corpus_dur()


# Les deux tests de rejet ne chargent pas le corpus : pas de cle requise.


def test_banc_humour_path_exists() -> None:
    assert banc_humour_path().exists(), f"banc humour manquant : {banc_humour_path()}"


def test_load_corpus_dur_contract(corpus: list[dict]) -> None:
    # Le banc consolide declare >= 100 instances annotees manuellement.
    assert len(corpus) >= 100
    validate_corpus(corpus)  # leve si champs/taxonomie/unicite violent le contrat


def test_corpus_identity_against_derivation() -> None:
    # Temoin d'identite #20316 : le corpus committé doit etre EGAL a la
    # derivation rejouee depuis le snapshot Argumentum (heuristiques + seed 42).
    from ict.humor_pairs import _organ

    _organ.assert_corpus_identity()


def test_label_distribution_sums_to_corpus(corpus: list[dict]) -> None:
    dist = label_distribution(corpus)
    assert sum(dist.values()) == len(corpus)
    assert set(dist) <= set(LABELS)


def test_load_corpus_dur_cwd_independent(tmp_path: Path) -> None:
    # Regression (pre-extraction) : la cellule 26 du banc resolvait son cache
    # Argumentum en chemin relatif — fetch reseau depuis un cwd sans cache.
    # L'organe est ancre sur __file__ : le chargement doit rester cwd-independant.
    prev = Path.cwd()
    os.chdir(tmp_path)
    try:
        corpus = load_corpus_dur()
    finally:
        os.chdir(prev)
    assert len(corpus) >= 100


def test_validate_corpus_rejects_bad_label() -> None:
    bad = [{"id": "x", "texte": "t", "features": {}, "label": "drole", "justification": "", "source": "s"}]
    with pytest.raises(AssertionError, match="hors taxonomie"):
        validate_corpus(bad, min_size=1)


def test_validate_corpus_rejects_duplicate_ids() -> None:
    inst = {"id": "x", "texte": "t", "features": {}, "label": "rien", "justification": "", "source": "s"}
    with pytest.raises(AssertionError, match="dupliques"):
        validate_corpus([inst, dict(inst)], min_size=1)


def test_build_pairs_contract(corpus: list[dict]) -> None:
    # 28 blagues (p01/p17 exclues, textes committes malformes) + 2 one-liners
    # edge-case = 30 paires, plancher protocolaire #14035 atteint.
    pairs = build_pairs(corpus)
    assert len(pairs) == 30
    validate_pairs(pairs)  # min_pairs=30 par defaut


def test_build_prompts_json_contract(corpus: list[dict]) -> None:
    payload = build_prompts_json(build_pairs(corpus))
    assert set(payload) == {"humour", "unfun", "ctrl_edit"}
    n = len(payload["humour"])
    assert n == 30 and all(len(payload[s]) == n for s in payload)
    assert all(isinstance(t, str) and t for s in payload.values() for t in s)
    # Le setup est prefixe commun exact : les variants ne different que du
    # cote de la punchline (zone d'edition disjoncte).
    assert all(
        p["unfun"].startswith(p["setup"]) and p["ctrl_edit"].startswith(p["setup"])
        for p in build_pairs(corpus)
    )


# --------------------------------------------------------------------------- #
# Couche mesure : fixture synthetique au format de trace exact (schema
# ``{set}__{i}__{topk_ids|topk_vals|tokens}`` + ``__meta__`` legacy lens='sae').
# --------------------------------------------------------------------------- #

_D_SAE = 64
_K = 8
_N_PAIRS_SYN = 12
_SHIFT_FEATS = (3, 5, 7)


def _write_synthetic_traces(path: Path, *, shift: bool, seed: int = 42) -> None:
    """Trace synthetique : prefixe commun de 3 tokens, zone de 3 tokens.

    Tous les tokens portent les memes k=8 features de base [0..7] avec des
    valeurs aleatoires par prompt. Si ``shift``, chaque token de zone humour
    porte en plus +2.0 sur les features (3, 5, 7) — shift systematique a
    direction constante, le signal exact que la jambe feature-z doit voir.
    """
    rng = np.random.default_rng(seed)
    meta = {
        "lens": "sae", "d_sae": _D_SAE, "k": _K, "layer": 12,
        "stage": "smoke", "variant": "synthetic", "model": "synthetic",
        "sae_repo": "synthetic", "seed": seed,
    }
    arrays: dict[str, np.ndarray] = {"__meta__": np.array(json.dumps(meta))}
    for s, zone_suffix in (("humour", "H"), ("unfun", "U"), ("ctrl_edit", "C")):
        for i in range(_N_PAIRS_SYN):
            base = rng.uniform(0.5, 1.5, size=(6, _K)).astype(np.float32)
            if shift and s == "humour":
                base[4:, [3, 5, 7]] += np.float32(2.0)
            arrays[f"{s}__{i}__topk_ids"] = np.tile(
                np.arange(_K, dtype=np.int32), (6, 1)
            )
            arrays[f"{s}__{i}__topk_vals"] = base
            arrays[f"{s}__{i}__tokens"] = np.array(
                ["<s>", "pre", "fix", "P", f"{zone_suffix}{i}", "."]
            )
    np.savez(path, **arrays)


def _syn_pairs() -> list[dict[str, str]]:
    # Seule la longueur compte pour la mesure (elle indexe les traces par i).
    return [
        {"id": f"syn-{i:02d}", "setup": "s", "humour": "h",
         "unfun": "u", "ctrl_edit": "c"}
        for i in range(_N_PAIRS_SYN)
    ]


def test_common_prefix_len() -> None:
    a = ["x", "y", "z", "w"]
    assert _common_prefix_len(a, ["x", "y", "q", "w"]) == 2
    assert _common_prefix_len(a, a) == 4
    assert _common_prefix_len(a, ["x"]) == 1


def test_measure_detects_systematic_shift_via_feature_z(tmp_path: Path) -> None:
    # Ecart #14035 c.5743512349 fige en regression : un shift systematique a
    # direction constante est INVISIBLE au null croise (le brassage des unfun
    # entre paires ne touche pas la composante constante) — delta_pair ne peut
    # pas depasser p99 — mais la jambe feature-z (flip de signe intra-paire)
    # DOIT le detecter : >= 3 features |z| > 3, toutes du meme cote.
    tr = tmp_path / "syn_shift.npz"
    _write_synthetic_traces(tr, shift=True)
    res = measure_humor_differential(
        tr, _syn_pairs(), n_draws=256, seed=42
    )
    assert res["n_features_over3"] >= 3
    assert res["n_over3_positive"] >= 3
    assert res["n_over3_negative"] == 0
    # Les features injectees dominent le top : (3, 5, 7) en tete.
    top_ids = {f for f, _ in res["top_features"][:3]}
    assert top_ids == set(_SHIFT_FEATS)
    # La jambe delta_pair ne peut PAS franchir le null croise dans ce regime.
    assert res["delta_pair"] <= res["null_p99"]
    assert res["verdict"] == "INCONCLUSIVE"


def test_measure_inconclusive_on_pure_noise(tmp_path: Path) -> None:
    tr = tmp_path / "syn_noise.npz"
    _write_synthetic_traces(tr, shift=False)
    res = measure_humor_differential(
        tr, _syn_pairs(), n_draws=256, seed=42
    )
    assert res["n_features_over3"] < 3
    assert res["verdict"] == "INCONCLUSIVE"
    assert res["ratio_vs_ctrl"] < 1.5


# --------------------------------------------------------------------------- #
# Null global sur le maximum : le seuil 3 sigma face au null lui-meme.
#
# Un compte de features au-dela de 3 sigma ne se lit pas sans la loi du
# maximum que le null atteint sur le meme dictionnaire : sur la fixture
# synthetique, le seuil n'est atteint par AUCUN tirage du null, et le max
# observe d'un bruit pur se situe au milieu de la distribution du null.
# --------------------------------------------------------------------------- #


def test_with_null_max_does_not_change_the_measured_values(tmp_path: Path) -> None:
    # Garde anti-regression : les statistiques du null sur le maximum sont
    # lues DANS le tableau de null deja calcule -- l'option ne doit rien
    # changer aux valeurs du verdict pre-registre (meme graine, meme suite).
    tr = tmp_path / "syn_shift.npz"
    _write_synthetic_traces(tr, shift=True)
    ref = measure_humor_differential(tr, _syn_pairs(), n_draws=256, seed=42)
    aug = measure_humor_differential(
        tr, _syn_pairs(), n_draws=256, seed=42, with_null_max=True
    )
    for key in (
        "delta_pair", "delta_ctrl", "null_p99", "ratio_vs_ctrl",
        "n_features_over3", "n_over3_positive", "n_over3_negative", "verdict",
    ):
        assert aug[key] == ref[key], f"{key} a bouge avec with_null_max"
    assert aug["top_features"] == ref["top_features"]
    assert len(aug["null_max_absz"]) == 256
    assert len(aug["null_over3"]) == 256


def test_global_max_null_on_pure_noise_is_the_null_typical_outcome(
    tmp_path: Path,
) -> None:
    tr = tmp_path / "syn_noise.npz"
    _write_synthetic_traces(tr, shift=False)
    res = measure_global_max_null(tr, _syn_pairs(), n_draws=256, seed=42)
    # Le null n'atteint jamais le seuil sur ce dictionnaire : le zero observe
    # est l'issue typique du null, il ne distingue rien.
    assert res["null_features_over_seuil"]["frac_draws_with_one"] == 0.0
    assert res["seuil_atteignable_sous_null"] is False
    assert res["p_zero_under_null"] == 1.0
    assert res["n_features_over_seuil_observe"] == 0
    assert res["verdict"] == "ABSENCE_NON_INFORMATIVE"
    # Le max observe est au milieu de la distribution du null (pas un extreme).
    assert res["p_max_null_ge_observe"] > 0.05
    assert res["z_max_observed"] < res["null_max_absz"]["q95"]


def test_global_max_null_detects_the_shift_beyond_the_null_range(
    tmp_path: Path,
) -> None:
    tr = tmp_path / "syn_shift.npz"
    _write_synthetic_traces(tr, shift=True)
    res = measure_global_max_null(tr, _syn_pairs(), n_draws=256, seed=42)
    # Le shift sort de la plage du null : aucun tirage n'atteint le maximum
    # observe (p = 0), et le verdict le dit explicitement.
    assert res["n_features_over_seuil_observe"] >= 3
    assert res["p_max_null_ge_observe"] == 0.0
    assert res["verdict"] == "SIGNAL_HORS_NULL"
    # Le meme shift reste invisible a la jambe delta_pair (verdict pre-registre
    # INCONCLUSIVE) : c'est bien la lecture sur le maximum qui tranche.
    assert res["verdict_measure"] == "INCONCLUSIVE"


def test_le_taux_de_depassement_decrit_le_null_et_non_une_puissance(
    tmp_path: Path,
) -> None:
    """``frac_draws_with_one`` vaut P_H0(max|z| > seuil), PAS une puissance.

    Le cas shift fournit le contre-exemple qui le demontre : le null n'atteint
    jamais le seuil (taux = 0) alors que les DONNEES produisent plusieurs
    features au-dela. Un chiffre de puissance n'aurait pas pu decrire les deux
    a la fois : il parle du null, jamais de la capacite a rejeter une
    alternative qu'il n'explicite pas.
    """
    tr = tmp_path / "syn_shift_puissance.npz"
    _write_synthetic_traces(tr, shift=True)
    res = measure_global_max_null(tr, _syn_pairs(), n_draws=256, seed=42)
    assert res["null_features_over_seuil"]["frac_draws_with_one"] == 0.0
    assert res["n_features_over_seuil_observe"] >= 3
    # Le complement est exact : le taux et son complement se lisent sur le null.
    assert res["null_features_over_seuil"]["frac_draws_with_one"] + res[
        "p_zero_under_null"
    ] == 1.0
    # Aucune grandeur de puissance n'est exposee par l'API : le module ne
    # pretends pas estimer une sensibilite qu'il ne mesure pas.
    assert not any(
        "puissance" in cle or "power" in cle for cle in res
    ), sorted(res)


def test_sur_pure_bruit_le_taux_decrit_le_null_et_son_complement(
    tmp_path: Path,
) -> None:
    tr = tmp_path / "syn_noise_taux.npz"
    _write_synthetic_traces(tr, shift=False)
    res = measure_global_max_null(tr, _syn_pairs(), n_draws=256, seed=42)
    taux = res["null_features_over_seuil"]["frac_draws_with_one"]
    # Sur ce dictionnaire le null atteint parfois le seuil : c'est cette
    # reference qui rend un compte observe interpretable.
    assert 0.0 <= taux <= 1.0
    assert res["p_zero_under_null"] == pytest.approx(1.0 - taux)
    assert res["n_features_over_seuil_observe"] == 0
    # Le verdict qualifie l'observation ; il ne conclut rien sur une
    # sensibilite de l'instrument.
    assert res["verdict"] == "ABSENCE_NON_INFORMATIVE"
