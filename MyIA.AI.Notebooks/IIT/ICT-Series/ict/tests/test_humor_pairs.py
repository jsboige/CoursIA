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
    build_pairs,
    build_prompts_json,
    gt24b_path,
    label_distribution,
    load_corpus_dur,
    measure_humor_differential,
    validate_corpus,
    validate_pairs,
)

# Les cellules endpoint de GT-24b exigent la cle OpenRouter (presente dans
# .secrets/master.env sur les machines du cluster, absente en CI sans secrets).
# Le corpus lui-meme est deterministe et n'appelle jamais l'API.
_NEEDS_KEY = pytest.mark.skipif(
    not os.environ.get("OPENROUTER_API_KEY"),
    reason="cle OPENROUTER_API_KEY requise par les cellules endpoint de GT-24b",
)


@pytest.fixture(scope="module")
def corpus() -> list[dict]:
    return load_corpus_dur()


# Les deux tests de rejet ne chargent pas le corpus : pas de cle requise.


def test_gt24b_path_exists() -> None:
    assert gt24b_path().exists(), f"GT-24b manquant : {gt24b_path()}"


@_NEEDS_KEY
def test_load_corpus_dur_contract(corpus: list[dict]) -> None:
    # Le banc consolide declare >= 100 instances annotees manuellement.
    assert len(corpus) >= 100
    validate_corpus(corpus)  # leve si champs/taxonomie/unicite violent le contrat


@_NEEDS_KEY
def test_label_distribution_sums_to_corpus(corpus: list[dict]) -> None:
    dist = label_distribution(corpus)
    assert sum(dist.values()) == len(corpus)
    assert set(dist) <= set(LABELS)


@_NEEDS_KEY
def test_load_corpus_dur_cwd_independent(tmp_path: Path) -> None:
    # Regression : la cellule 4 de GT-24b resout son cache Argumentum en chemin
    # relatif — depuis un cwd sans cache, elle declenchait un fetch reseau.
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


@_NEEDS_KEY
def test_build_pairs_contract(corpus: list[dict]) -> None:
    # 28 blagues (p01/p17 exclues, textes committes malformes) + 2 one-liners
    # edge-case = 30 paires, plancher protocolaire #14035 atteint.
    pairs = build_pairs(corpus)
    assert len(pairs) == 30
    validate_pairs(pairs)  # min_pairs=30 par defaut


@_NEEDS_KEY
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
