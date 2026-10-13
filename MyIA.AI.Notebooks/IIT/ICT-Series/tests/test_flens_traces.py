"""Contrôle du module F-Lens sur capture dense (#17740)."""

import json
import os
import sys

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import flens_traces  # noqa: E402
from ict.factor_geometry import make_factor_bases, synthesize_activations  # noqa: E402


def write_dense(path, prompts, meta_overrides=None):
    """Écrit une capture dense minimale ; prompts : {(set, i): {"tokens","resid"}}."""
    arrays = {}
    d_model = None
    for (set_name, idx), p in prompts.items():
        arrays[f"{set_name}__{idx}__tokens"] = np.asarray(p["tokens"], str)
        arrays[f"{set_name}__{idx}__resid"] = np.asarray(p["resid"], np.float16)
        d_model = np.asarray(p["resid"]).shape[1]
    meta = {"model": "m", "layer": 16, "seed": 42, "variant": "trained",
            "d_model": int(d_model)}
    meta.update(meta_overrides or {})
    arrays["__meta__"] = np.array(json.dumps(meta))
    np.savez_compressed(path, **arrays)


def synthetic_prompts(dim=32, n_tokens=60, noise=0.05, seed=7):
    """4 prompts : jeu alpha sur le facteur 0, jeu beta sur le facteur 1."""
    bases, _ = make_factor_bases(4, dim, rng=np.random.default_rng(seed))
    out = {}
    for key, factor in {(("alpha", 0), 0), (("alpha", 1), 0),
                        (("beta", 0), 1), (("beta", 1), 1)}:
        x, _ = synthesize_activations([bases[factor]], n_tokens,
                                      noise_var=noise,
                                      rng=np.random.default_rng(seed + factor))
        out[key] = {"tokens": np.array([f"t{i}" for i in range(n_tokens)]),
                    "resid": x}
    return out


def test_load_dense_roundtrip(tmp_path):
    path = tmp_path / "dense.npz"
    write_dense(path, synthetic_prompts())
    dense = flens_traces.load_dense(path)
    assert set(dense["prompts"]) == {("alpha", 0), ("alpha", 1),
                                     ("beta", 0), ("beta", 1)}
    resid = dense["prompts"][("alpha", 0)]["resid"]
    assert resid.dtype == np.float32 and resid.shape == (60, 32)
    assert dense["meta"]["d_model"] == 32


@pytest.mark.parametrize("field", ["model", "layer", "seed", "variant", "d_model"])
def test_load_dense_missing_meta_refused(tmp_path, field):
    path = tmp_path / "dense.npz"
    write_dense(path, synthetic_prompts(), meta_overrides={field: None})
    with pytest.raises(ValueError, match=field):
        flens_traces.load_dense(path)


def test_load_dense_partial_trace_refused(tmp_path):
    path = tmp_path / "dense.npz"
    write_dense(path, synthetic_prompts())
    z = dict(np.load(path, allow_pickle=False))
    z.pop("alpha__0__resid")
    np.savez_compressed(path, **z)
    with pytest.raises(ValueError, match="alpha__0"):
        flens_traces.load_dense(path)


def test_load_dense_shape_mismatch_refused(tmp_path):
    prompts = synthetic_prompts()
    original = prompts[("alpha", 0)]
    prompts[("alpha", 0)] = {"tokens": original["tokens"][:-3],
                             "resid": original["resid"]}
    path = tmp_path / "dense.npz"
    write_dense(path, prompts)
    with pytest.raises(ValueError, match="incoherent"):
        flens_traces.load_dense(path)


def test_measure_flens_recovers_factor_structure():
    prompts = synthetic_prompts()
    dense = {"meta": {"d_model": 32}, "prompts": prompts}
    result = flens_traces.measure_flens(dense, top_k=8, n_null=50)
    assert result["status"] == "measured"
    # NC@90 proche du facteur (8 dims de signal) pour chaque prompt.
    for item in result["per_prompt"]:
        assert item["nc_at"]["90"] <= 12
    # Intra-jeu : meme facteur -> alignement au-dela de la nulle appariee.
    alignment = result["alignment"]
    assert alignment["verdicts"]["same_set_beyond_null_q95"] is True
    assert alignment["same_set"]["frobenius_alignment"]["mean"] > \
        alignment["null_paired"]["frobenius_alignment"]["q95"]
    # Inter-jeux : facteurs orthogonaux -> pas au-dela de la nulle.
    assert alignment["verdicts"]["cross_set_beyond_null_q95"] is False
    assert alignment["cross_set"]["frobenius_alignment"]["mean"] < \
        alignment["same_set"]["frobenius_alignment"]["mean"]


def test_measure_flens_isotropic_noise_stays_at_null():
    rng = np.random.default_rng(3)
    prompts = {}
    for key in {("alpha", 0), ("alpha", 1), ("beta", 0), ("beta", 1)}:
        prompts[key] = {"tokens": np.array([f"t{i}" for i in range(60)]),
                        "resid": rng.standard_normal((60, 32))}
    result = flens_traces.measure_flens(
        {"meta": {"d_model": 32}, "prompts": prompts}, top_k=8, n_null=50)
    alignment = result["alignment"]
    assert alignment["verdicts"]["same_set_beyond_null_q95"] is False
    # NC@90 proche du plein rang relatif : aucune structure factorisee nette.
    assert result["per_prompt"][0]["nc_at"]["90"] > 12


def test_null_pairs_match_real_pair_code_path():
    nulls = flens_traces.null_pairs(dim=32, top_k=8, n_nulls=30, seed=1)
    assert nulls["frobenius_alignment"].shape == (30,)
    assert (nulls["max_principal_angle_deg"] > 0).all()
    assert (nulls["max_principal_angle_deg"] <= 90.0 + 1e-6).all()


def test_null_pairs_top_k_bounds():
    with pytest.raises(ValueError, match="top_k"):
        flens_traces.null_pairs(dim=32, top_k=0, n_nulls=2)
