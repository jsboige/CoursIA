"""Contrôle du contraste entre lentilles sur les mêmes prompts (#17740)."""

import os
import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import geometry_contrast as gc  # noqa: E402


TRACES = Path(__file__).parent.parent / "traces"


def test_committed_traces_report_separate_verdicts():
    result = gc.contrast(TRACES)
    assert result["substrate"] == {
        "model": "Qwen/Qwen3.5-9B-Base", "layer": 16, "seed": 42, "prompts": 20
    }
    assert result["sae_jlens"]["counts"] == {
        "colocalized": 0, "dissociated": 0, "chance": 4, "undefined": 16
    }
    assert len(result["sae_jlens"]["per_prompt"]) == 20
    assert result["f_lens"]["status"] == "not_comparable"
    assert result["s_lens"]["status"] == "not_comparable"
    assert "score" not in result


def _pair(monkeypatch, *, field=None, value=None, prompt=None):
    tokens = np.array(["one", "two", "three"])
    meta = {"model": "same", "layer": 16, "seed": 42, "variant": "trained"}
    sae = {"meta": dict(meta), "prompts": {("set", 0): {"tokens": tokens}}}
    jlens = {"meta": dict(meta), "prompts": {("set", 0): {"tokens": tokens.copy()}}}
    if field is not None:
        jlens["meta"][field] = value
    if prompt is not None:
        jlens["prompts"][("set", 0)]["tokens"] = np.asarray(prompt)
    monkeypatch.setattr(gc.sae_traces, "load_traces", lambda path: sae)
    monkeypatch.setattr(gc.jlens_traces, "load_traces", lambda path: jlens)
    return sae, jlens


@pytest.mark.parametrize("field,value", [
    ("model", "other"), ("layer", 17), ("seed", 7), ("variant", "control")
])
def test_mismatched_manifest_refused(monkeypatch, field, value):
    _pair(monkeypatch, field=field, value=value)
    with pytest.raises(ValueError, match=field):
        gc.contrast(TRACES)


def test_missing_provenance_refused(monkeypatch):
    sae, jlens = _pair(monkeypatch)
    del sae["meta"]["seed"]
    del jlens["meta"]["seed"]
    with pytest.raises(ValueError, match="seed"):
        gc.contrast(TRACES)


def test_different_prompt_tokens_refused(monkeypatch):
    _pair(monkeypatch, prompt=["one", "DIFFERENT", "three"])
    with pytest.raises(ValueError, match="tokens"):
        gc.contrast(TRACES)


def test_partial_prompts_refused(monkeypatch):
    _, jlens = _pair(monkeypatch)
    jlens["prompts"].clear()
    with pytest.raises(ValueError, match="prompts"):
        gc.contrast(TRACES)


def test_skipped_prompt_refused(monkeypatch):
    _pair(monkeypatch)
    monkeypatch.setattr(gc, "colocalize_lenses", lambda *args, **kwargs: {
        "n_skipped": 1, "n_prompts": 0
    })
    with pytest.raises(ValueError, match="non comparés"):
        gc.contrast(TRACES)


def test_invalid_null_count_refused():
    with pytest.raises(ValueError, match="n_null"):
        gc.contrast(TRACES, n_null=1)
