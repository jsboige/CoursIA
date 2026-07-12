"""Tests de l'adaptateur de traces SAE (ICT-21, #5101). GPU-free.

Couvrent :
* le round-trip ``.npz`` -> :func:`ict.sae_traces.load_traces` (sans pickle) ;
* la selection differentielle : les features PLANTEES discriminantes ressortent,
  la feature toujours-active (forte en absolu, nulle en variance inter-jeux)
  est ecartee ;
* l'exactitude de :func:`densify` (le sparse top-k est exhaustif : hors top-k
  l'activation vaut exactement zero) ;
* les garde-fous de :func:`binarize_quantile` et :func:`states_from_panel` ;
* si les traces reelles committees sont presentes, un test d'integration
  verifie leur schema (meta, shapes, L0).
"""

import json
import os
import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import sae_traces as st  # noqa: E402

D_SAE = 1000
K = 5
T = 40


# --------------------------------------------------------------------------- #
# Fixture : npz synthetique avec structure differentielle plantee
# --------------------------------------------------------------------------- #
@pytest.fixture()
def synthetic_npz(tmp_path):
    """Deux jeux x deux prompts. Feature 7 active seulement dans le jeu A,
    feature 13 seulement dans le jeu B, feature 2 active PARTOUT (forte en
    absolu, non differentielle). Le reste = ids aleatoires faibles."""
    rng = np.random.default_rng(0)
    arrays = {}
    for set_name, planted, val in (("setA", 7, 5.0), ("setB", 13, 4.0)):
        for i in range(2):
            ids = rng.integers(20, D_SAE, size=(T, K)).astype(np.int32)
            vals = rng.uniform(0.05, 0.3, size=(T, K)).astype(np.float16)
            ids[:, 0] = 2                      # toujours active, partout
            vals[:, 0] = 10.0
            ids[:, 1] = planted                # discriminante du jeu
            vals[:, 1] = val
            arrays[f"{set_name}__{i}__topk_ids"] = ids
            arrays[f"{set_name}__{i}__topk_vals"] = vals
            arrays[f"{set_name}__{i}__tokens"] = np.array(
                [f"tok{t}" for t in range(T)], dtype=str)
    meta = {"d_sae": D_SAE, "k": K, "layer": 16, "variant": "synthetic"}
    arrays["__meta__"] = np.array(json.dumps(meta))
    path = tmp_path / "synthetic.npz"
    np.savez_compressed(path, **arrays)
    return path


def test_load_traces_roundtrip(synthetic_npz):
    tr = st.load_traces(synthetic_npz)
    assert tr["meta"]["d_sae"] == D_SAE
    assert set(tr["prompts"]) == {("setA", 0), ("setA", 1), ("setB", 0), ("setB", 1)}
    e = tr["prompts"][("setA", 0)]
    assert e["ids"].shape == (T, K) and e["ids"].dtype == np.int32
    assert e["vals"].shape == (T, K) and e["vals"].dtype == np.float32
    assert e["tokens"].shape == (T,)


def test_differential_features_finds_planted_not_ubiquitous(synthetic_npz):
    tr = st.load_traces(synthetic_npz)
    top = set(st.differential_features(tr, k=2).tolist())
    assert top == {7, 13}, top
    # la feature 2 (tres forte partout) a une variance inter-jeux ~0 :
    top64 = st.differential_features(tr, k=64).tolist()
    assert top64.index(7) < 2 and top64.index(13) < 2
    means = st.mean_activation_by_set(tr)
    stack = np.stack(list(means.values()))
    assert stack.var(axis=0)[2] < 1e-6


def test_densify_exact(synthetic_npz):
    tr = st.load_traces(synthetic_npz)
    e = tr["prompts"][("setB", 1)]
    feats = np.array([13, 2, 999])            # plantee, ubiquitaire, jamais vue
    dense = st.densify(e["ids"], e["vals"], feats)
    assert dense.shape == (T, 3)
    assert np.allclose(dense[:, 0], e["vals"][:, 1])     # feature 13 en col 0
    assert np.allclose(dense[:, 1], e["vals"][:, 0])     # feature 2 en col 1
    assert np.all(dense[:, 2] == 0.0)                    # hors top-k => 0 exact


def test_acts_topk_panels_shapes(synthetic_npz):
    tr = st.load_traces(synthetic_npz)
    feats = st.differential_features(tr, k=4)
    panels = st.acts_topk_panels(tr, feats)
    assert set(panels) == set(tr["prompts"])
    assert all(p.shape == (T, 4) for p in panels.values())


def test_binarize_quantile_guards():
    dense = np.zeros((10, 2), dtype=np.float32)
    dense[:5, 0] = [1, 2, 3, 4, 5]
    bits = st.binarize_quantile(dense, q=0.5)
    assert bits[:, 1].sum() == 0                         # jamais active -> False
    assert 0 < bits[:, 0].sum() < 5                      # seuil sur positifs seuls
    with pytest.raises(ValueError):
        st.binarize_quantile(dense, q=1.0)


def test_states_from_panel_bijective_and_capped():
    bits = np.array([[0, 0], [1, 0], [0, 1], [1, 1], [1, 0]], dtype=bool)
    states = st.states_from_panel(bits)
    assert states.tolist() == [0, 1, 2, 3, 1]
    with pytest.raises(ValueError):
        st.states_from_panel(np.zeros((3, 21), dtype=bool))


# --------------------------------------------------------------------------- #
# Integration : schema des traces reelles committees (si presentes)
# --------------------------------------------------------------------------- #
REAL = Path(__file__).parent.parent / "traces"


@pytest.mark.parametrize("variant", ["trained", "control"])
def test_real_traces_schema(variant):
    path = REAL / f"ict21_sae_layer16_{variant}.npz"
    if not path.exists():
        pytest.skip("traces reelles absentes (extraction GPU non committee ici)")
    tr = st.load_traces(path)
    assert tr["meta"]["variant"] == variant
    assert tr["meta"]["k"] == 50 and tr["meta"]["d_sae"] == 65536
    assert len(tr["prompts"]) == 20                      # 5 jeux x 4 prompts
    for e in tr["prompts"].values():
        T_i, k = e["ids"].shape
        assert k == 50 and e["vals"].shape == (T_i, 50)
        # L0 = 50 observe a l'extraction : toutes les valeurs du top-50 > 0
        assert (e["vals"] > 0).all()
