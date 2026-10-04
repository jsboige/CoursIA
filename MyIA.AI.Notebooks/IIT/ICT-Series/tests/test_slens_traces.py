"""Contrôle du module S-Lens sur capture dense (#17740)."""

import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import slens_traces  # noqa: E402


def build_dense(prompts):
    """prompts : {(set, i): {"tokens", "resid"}} -> structure dense sans fichier."""
    return {"meta": {"d_model": prompts[("a", 0)]["resid"].shape[1]},
            "prompts": prompts}


def decodable_prompts(dim=16, n_tokens=60, noise=0.01, seed=5):
    """Résidus où la position est portée linéairement par la dim 0."""
    rng = np.random.default_rng(seed)
    prompts = {}
    for key in (("a", 0), ("a", 1)):
        resid = rng.standard_normal((n_tokens, dim)) * noise
        resid[:, 0] = np.arange(n_tokens, dtype=np.float64)
        prompts[key] = {"tokens": np.array([f"t{i}" for i in range(n_tokens)]),
                        "resid": resid}
    return prompts


def test_position_decodable_pooled():
    result = slens_traces.measure_slens(build_dense(decodable_prompts()),
                                        seed=0)
    assert result["status"] == "measured"
    assert result["pooled"]["r2"] > 0.95
    assert result["pooled"]["n_test"] > 0
    # Le contrôle shuffle (étiquettes du train permutées) retombe au plancher.
    assert result["shuffle_control"]["r2"] < 0.2


def test_position_extrapolation_harder_than_interpolation():
    result = slens_traces.measure_slens(build_dense(decodable_prompts()),
                                        seed=0)
    # Split contiguous par prompt : positions held-out non vues au train.
    # La lecture reste linéaire exacte ici (dim 0 = position), donc R2 haut
    # aussi par prompt — ce test fixe la convention, pas la difficulté.
    for item in result["per_prompt"]:
        assert item["r2"] > 0.9


def test_isotropic_noise_stays_low():
    rng = np.random.default_rng(11)
    prompts = {}
    for key in (("a", 0), ("a", 1)):
        prompts[key] = {"tokens": np.array([f"t{i}" for i in range(60)]),
                        "resid": rng.standard_normal((60, 16))}
    result = slens_traces.measure_slens(build_dense(prompts), seed=0)
    assert result["pooled"]["r2"] < 0.5
    assert result["shuffle_control"]["r2"] < 0.5


def test_short_prompt_excluded_from_per_prompt():
    rng = np.random.default_rng(2)
    prompts = decodable_prompts()
    prompts[("b", 0)] = {"tokens": np.array(["x", "y", "y2"]),
                         "resid": rng.standard_normal((3, 16))}
    result = slens_traces.measure_slens(build_dense(prompts), seed=0)
    listed = {tuple(item["prompt"]) for item in result["per_prompt"]}
    assert ("b", 0) not in listed
    assert ("a", 0) in listed
