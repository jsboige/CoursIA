"""Tests unitaires pour le garde-fou non-fini de ``ict.sae_traces.load_traces`` (#12388).

Le defaut BOS-inf du run 8B-Qwen3 : un token (position 0) portait un residu
dont TOUT le top-k SAE etait inf/nan. La trace commitee aurait contamine les
panneaux differentiels (46/64 filtre-a-la-main vs 14/64 contamine). Le
correctif agit aux deux bouts :

* producteur : ``extract_sae_traces.py`` EXCLUT les positions non-finies a la
  capture (aligne ids/vals/tokens) et abort au-dela de 5 % ;
* consommateur : ``load_traces`` REFUSE une trace qui porte encore des vals
  non-finies — c'est une trace PRE-correctif, il faut la regenerer.

Ces tests attestent le contrat consommateur sur de vrais fichiers ``.npz``
(ecrits en tmp, relus sans pickle — meme schema que les traces commitees).
"""

import json

import numpy as np
import pytest

from ict import sae_traces as st


def _write_trace(path, vals):
    arrays = {
        "setA__0__topk_ids": np.array([[0, 1], [2, 3]], dtype=np.int32),
        "setA__0__topk_vals": np.array(vals, dtype=np.float16),
        "setA__0__tokens": np.array(["a", "b"], dtype=str),
    }
    meta = json.dumps({"d_sae": 4, "k": 2, "layer": 18, "variant": "test"})
    np.savez(path, __meta__=meta, **arrays)


def test_load_traces_accepts_finite_trace(tmp_path):
    """Cas nominal : une trace propre (0 val non-finie) passe la garde."""
    p = tmp_path / "clean.npz"
    _write_trace(p, [[1.0, 0.5], [0.8, 0.2]])
    out = st.load_traces(p)
    assert ("setA", 0) in out["prompts"]
    assert out["meta"]["layer"] == 18


def test_load_traces_refuses_nonfinite_vals_with_value_error(tmp_path):
    """Defaut BOS-inf : une val non-finie (inf/nan) fait refuser la trace.

    Le refus porte le diagnostic : trace pre-correctif, regenerer — pas un
    message generique qui laisserait chercher la cause.
    """
    p = tmp_path / "bos_inf.npz"
    _write_trace(p, [[float("inf"), float("inf")], [0.8, 0.2]])
    with pytest.raises(ValueError, match="non-finies.*regenerer"):
        st.load_traces(p)


def test_load_traces_refuses_nan_vals(tmp_path):
    """Variante nan du meme defaut : la garde couvre inf ET nan."""
    p = tmp_path / "nan.npz"
    _write_trace(p, [[float("nan"), 0.5], [0.8, 0.2]])
    with pytest.raises(ValueError, match="non-finies"):
        st.load_traces(p)
