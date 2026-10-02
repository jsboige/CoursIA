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


# --------------------------------------------------------------------------- #
# Capture dense (#17740) : F-Lens et S-Lens mesurés sur le même substrat,
# ou absences explicites — jamais d'accord nul par silence.
# --------------------------------------------------------------------------- #

def _colocalize_stub(*args, **kwargs):
    return {
        "n_skipped": 0, "n_prompts": 1, "n_colocalized": 0,
        "n_dissociated": 0, "n_chance": 0, "n_undefined": 1,
        "per_prompt": [{"prompt": ("set", 0), "verdict": "undefined",
                        "n_ign_a": 0, "n_ign_b": 0}],
    }


def _write_dense(path, *, tokens=None, meta_overrides=None):
    import json
    tokens = np.array(tokens if tokens is not None
                      else ["one", "two", "three", "four", "five",
                             "six", "seven", "eight"])
    meta = {"model": "same", "layer": 16, "seed": 42,
            "variant": "trained", "d_model": 8}
    meta.update(meta_overrides or {})
    rng = np.random.default_rng(0)
    np.savez_compressed(
        path,
        **{"set__0__tokens": tokens.astype(str),
           "set__0__resid": rng.standard_normal((len(tokens), 8)
                                                ).astype(np.float16),
           "__meta__": np.array(json.dumps(meta))})


def test_dense_absent_keeps_absences_explicit(monkeypatch, tmp_path):
    _pair(monkeypatch)
    monkeypatch.setattr(gc, "colocalize_lenses", _colocalize_stub)
    result = gc.contrast(TRACES, dense=tmp_path / "absent.npz")
    assert result["f_lens"]["status"] == "not_comparable"
    assert result["s_lens"]["status"] == "not_comparable"
    assert "per_set_summary" not in result


def test_dense_measured_when_aligned(monkeypatch, tmp_path):
    # Paire sae/jlens de 8 tokens, alignée avec la capture dense par défaut
    # (le split S-Lens pooled exige plus de 3 tokens pour un R2 défini).
    tokens = np.array(["one", "two", "three", "four", "five",
                       "six", "seven", "eight"])
    meta = {"model": "same", "layer": 16, "seed": 42, "variant": "trained"}
    sae = {"meta": dict(meta), "prompts": {("set", 0): {"tokens": tokens}}}
    jlens = {"meta": dict(meta),
             "prompts": {("set", 0): {"tokens": tokens.copy()}}}
    monkeypatch.setattr(gc.sae_traces, "load_traces", lambda path: sae)
    monkeypatch.setattr(gc.jlens_traces, "load_traces", lambda path: jlens)
    monkeypatch.setattr(gc, "colocalize_lenses", _colocalize_stub)
    dense_path = tmp_path / "dense.npz"
    _write_dense(dense_path)
    result = gc.contrast(TRACES, dense=dense_path)
    assert result["f_lens"]["status"] == "measured"
    assert result["s_lens"]["status"] == "measured"
    assert "cross_instrument_reading" in result
    rows = result["per_set_summary"]
    assert [row["set"] for row in rows] == ["set"]
    assert rows[0]["sae_jlens_verdicts"] == {"undefined": 1}
    assert rows[0]["flens_nc90_mean"] > 0
    assert rows[0]["slens_r2_mean"] is not None


def test_dense_tokens_misaligned_refused(monkeypatch, tmp_path):
    _pair(monkeypatch)
    monkeypatch.setattr(gc, "colocalize_lenses", _colocalize_stub)
    dense_path = tmp_path / "dense.npz"
    _write_dense(dense_path, tokens=["one", "DIFFERENT", "three"])
    with pytest.raises(ValueError, match="tokens"):
        gc.contrast(TRACES, dense=dense_path)


@pytest.mark.parametrize("field,value", [("model", "other"), ("seed", 7)])
def test_dense_meta_misaligned_refused(monkeypatch, tmp_path, field, value):
    _pair(monkeypatch)
    monkeypatch.setattr(gc, "colocalize_lenses", _colocalize_stub)
    dense_path = tmp_path / "dense.npz"
    _write_dense(dense_path, meta_overrides={field: value})
    with pytest.raises(ValueError, match=field):
        gc.contrast(TRACES, dense=dense_path)


# --------------------------------------------------------------------------- #
# Artefact committé (#17740, rapport quadri-instruments) : falsifiabilité —
# les nombres publiés se recalculent depuis l'artefact lui-même (précédent
# test_stratification.control_published), sans ré-exécuter la mesure (le npz
# dense, 16,3 Mo, reste hors dépôt : sa re-exécution exige `regenerate`).
# --------------------------------------------------------------------------- #

import json  # noqa: E402

RUNS = Path(__file__).parent.parent / "runs"
ARTIFACT = RUNS / "quadri_instruments_contrast.json"


@pytest.fixture(scope="module")
def artifact():
    if not ARTIFACT.exists():
        pytest.skip("artefact quadri-instruments non encore committé")
    return json.loads(ARTIFACT.read_text(encoding="utf-8"))


def test_artifact_reports_four_instruments_separately(artifact):
    m = artifact["measurement"]
    for key in ("sae_jlens", "f_lens", "s_lens", "per_set_summary"):
        assert key in m, key
    assert "score" not in m, "aucun score composite: quatre instruments séparés"
    assert m["f_lens"]["status"] == "measured"
    assert m["s_lens"]["status"] == "measured"


def test_artifact_carries_substrate_provenance(artifact):
    sub = artifact["substrate"]
    assert sub["dense_npz"] == "ict25_dense_layer16_trained.npz"
    sha = sub["sha256"]
    assert isinstance(sha, str) and len(sha) == 64
    int(sha, 16)  # empreinte hexadécimale, pas une valeur arbitraire
    assert sub["bytes"] > 0
    assert "regenerate" in artifact and artifact["tool"]["n_null"] >= 200


def test_artifact_counts_recompute_from_per_prompt(artifact):
    sae_jlens = artifact["measurement"]["sae_jlens"]
    recomputed = {"colocalized": 0, "dissociated": 0, "chance": 0,
                  "undefined": 0}
    for row in sae_jlens["per_prompt"]:
        recomputed[row["verdict"]] += 1
    assert recomputed == sae_jlens["counts"], (
        "les comptes publiés ne sont pas la distribution des verdicts par prompt")


def test_artifact_per_set_summary_recomputes(artifact):
    m = artifact["measurement"]
    by_set_sae = {}
    for row in m["sae_jlens"]["per_prompt"]:
        by_set_sae.setdefault(row["prompt"][0], []).append(row["verdict"])
    by_set_flens = {}
    for row in m["f_lens"]["per_prompt"]:
        by_set_flens.setdefault(row["prompt"][0], []).append(row["nc_at"]["90"])
    by_set_slens = {}
    for row in m["s_lens"]["per_prompt"]:
        by_set_slens.setdefault(row["prompt"][0], []).append(row["r2"])
    for row in m["per_set_summary"]:
        name = row["set"]
        # forme publiée : Counter nul-élagué (les comptes à zéro sont omis,
        # cf. geometry_contrast._per_set_summary) — recalculer dans la même forme.
        verdicts = {v: n for v, n in (
            (v, by_set_sae[name].count(v))
            for v in ("colocalized", "dissociated", "chance", "undefined")) if n}
        assert row["sae_jlens_verdicts"] == verdicts
        assert row["flens_nc90_mean"] == pytest.approx(
            sum(by_set_flens[name]) / len(by_set_flens[name]), abs=1e-9)
        assert row["slens_r2_mean"] == pytest.approx(
            sum(by_set_slens[name]) / len(by_set_slens[name]), abs=1e-9)
