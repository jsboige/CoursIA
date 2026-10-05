"""Regressions de ``verify_clamp_traces`` (#19216).

Le controle doit etre capable de REFUSER : un outil de verification qui ne
sait dire que "conforme" ne verifie rien. Chaque test de refus construit donc
le fichier EXACT que le defaut produirait -- un bras clampe identique a sa
reference -- et exige le rouge.

numpy seulement : le module sous test ne touche ni torch ni GPU.
"""
import json
import os
import sys

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
_SERIES = os.path.dirname(_HERE)
sys.path.insert(0, os.path.join(_SERIES, "scripts"))

import verify_clamp_traces as vct


def _meta(model="m", layer=16, scale=1.0, clamp_ids=(1, 2), **extra):
    meta = {
        "model": model, "sae_repo": "sae", "layer": layer, "variant": "trained",
        "seed": 42, "prompt_sets": {"a": 1}, "n_tokens_total": 10,
        "clamp_ids": list(clamp_ids), "clamp_scale": scale,
    }
    meta.update(extra)
    return meta


def _write(path, meta, values=(1.0, 2.0, 3.0), with_meta=True):
    arrays = {"a__topk_ids": np.array(values, dtype=np.float32)}
    if with_meta:
        arrays["__meta__"] = np.array(json.dumps(meta))
    np.savez(path, **arrays)
    return path


def _run(tmp_path, **kw):
    return vct.audit(tmp_path, **kw)


def test_a_clamped_arm_identical_to_its_reference_is_refused(tmp_path):
    """LE defaut de #19216 : le clamp annonce, la trace inchangee."""
    _write(tmp_path / "ref.npz", _meta(clamp_ids=[], scale=1.0))
    _write(tmp_path / "arm.npz", _meta(scale=1.0))
    report = _run(tmp_path)
    assert [v.status for v in report.verdicts] == ["MUET"]
    assert report.failures, "un clamp invisible doit faire echouer le controle"
    assert "0/3" in report.verdicts[0].line()


def test_a_clamped_arm_that_really_differs_passes(tmp_path):
    _write(tmp_path / "ref.npz", _meta(clamp_ids=[], scale=1.0),
           values=(1.0, 2.0, 3.0))
    _write(tmp_path / "arm.npz", _meta(scale=1.0), values=(9.0, 2.0, 3.0))
    report = _run(tmp_path)
    assert [v.status for v in report.verdicts] == ["ok"]
    assert not report.failures


def test_the_alpha_zero_arm_must_stay_identical(tmp_path):
    """alpha=0 est un no-op annonce : identique attendu, divergent refuse."""
    _write(tmp_path / "ref.npz", _meta(clamp_ids=[], scale=1.0))
    _write(tmp_path / "noop.npz", _meta(scale=0.0))
    assert _run(tmp_path).verdicts[0].status == "ok-noop"

    _write(tmp_path / "actif.npz", _meta(scale=0.0), values=(9.0, 2.0, 3.0))
    report = _run(tmp_path)
    statuses = {v.trace.name: v.status for v in report.verdicts}
    assert statuses["actif.npz"] == "NO-OP-ACTIF"
    assert [v.trace.name for v in report.failures] == ["actif.npz"]


def test_the_reference_is_found_by_metadata_not_by_filename(tmp_path):
    """Un nom sans aucun rapport ne doit pas empecher la reference d'etre vue."""
    _write(tmp_path / "zzz_mystere.npz", _meta(clamp_ids=[], scale=1.0),
           values=(1.0, 2.0, 3.0))
    _write(tmp_path / "inoc_x_clamp16.npz", _meta(scale=1.0),
           values=(9.0, 2.0, 3.0))
    v = _run(tmp_path).verdicts[0]
    assert v.reference is not None and v.reference.name == "zzz_mystere.npz"
    assert v.status == "ok"


def test_a_different_layer_is_not_a_reference(tmp_path):
    """Meme modele, autre couche : ce n'est pas la meme extraction."""
    _write(tmp_path / "autre_couche.npz", _meta(layer=17, clamp_ids=[]))
    _write(tmp_path / "arm.npz", _meta(layer=16, scale=1.0))
    v = _run(tmp_path).verdicts[0]
    assert v.status == "SANS-REFERENCE"
    assert v.reference is None


def test_an_ambiguous_reference_is_named_not_guessed(tmp_path):
    _write(tmp_path / "ref_a.npz", _meta(clamp_ids=[], scale=1.0))
    _write(tmp_path / "ref_b.npz", _meta(clamp_ids=[], scale=1.0))
    _write(tmp_path / "arm.npz", _meta(scale=1.0), values=(9.0, 2.0, 3.0))
    report = _run(tmp_path)
    assert report.verdicts[0].status == "AMBIGU"
    assert "ref_a.npz" in report.verdicts[0].detail
    assert "ref_b.npz" in report.verdicts[0].detail
    assert len(report.failures) == 1


def test_a_trace_without_metadata_is_reported_not_silently_skipped(tmp_path):
    _write(tmp_path / "muette.npz", {}, with_meta=False)
    report = _run(tmp_path)
    assert report.skipped == ["muette.npz"]
    assert "muette.npz" in report.as_markdown()


def test_the_noise_floor_bounds_both_faces_of_the_verdict(tmp_path):
    """1 valeur sur 10 000 (1e-4) de part et d'autre du plancher (1e-3).

    Cote alpha=0, ce residu est tolere : un no-op qui laisse bouger une
    valeur flottante reste un no-op. Cote alpha!=0, la MEME part est un
    clamp muet -- sous le plancher, la trace ne porte plus l'intervention
    annoncee. Le plancher n'est pas un confort : il deplace le seuil, il ne
    l'abolit pas.
    """
    _write(tmp_path / "ref.npz", _meta(clamp_ids=[], scale=1.0),
           values=tuple([1.0] * 10_000))
    jitter = [1.0] * 10_000
    jitter[0] = 2.0                   # 1 / 10 000 = 1e-4 < plancher 1e-3
    _write(tmp_path / "noop.npz", _meta(scale=0.0), values=tuple(jitter))
    _write(tmp_path / "clampe.npz", _meta(scale=1.0), values=tuple(jitter))
    statuses = {v.trace.name: v.status for v in _run(tmp_path).verdicts}
    assert statuses["noop.npz"] == "ok-noop"
    assert statuses["clampe.npz"] == "MUET"


def test_a_real_but_weak_divergence_above_the_floor_is_accepted(tmp_path):
    """Un effet faible reste un effet : le plancher ne condamne que le bruit."""
    _write(tmp_path / "ref.npz", _meta(clamp_ids=[], scale=1.0),
           values=tuple([1.0] * 10_000))
    weak = [1.0] * 10_000
    for i in range(100):              # 100 / 10 000 = 1 % > plancher
        weak[i] = 2.0
    _write(tmp_path / "arm.npz", _meta(scale=1.0), values=tuple(weak))
    assert _run(tmp_path).verdicts[0].status == "ok"


def test_a_missing_array_counts_as_a_divergence(tmp_path):
    """Un tableau present d'un seul cote est une difference, pas un silence."""
    np.savez(tmp_path / "ref.npz", a__topk_ids=np.array([1.0, 2.0]),
             b__topk_ids=np.array([1.0]), __meta__=np.array(json.dumps(_meta(clamp_ids=[]))))
    np.savez(tmp_path / "arm.npz", a__topk_ids=np.array([1.0, 2.0]),
             __meta__=np.array(json.dumps(_meta(scale=1.0))))
    v = _run(tmp_path).verdicts[0]
    assert v.differing == 1 and v.total == 3
    assert v.status == "ok"


def test_an_empty_directory_is_not_a_silent_success(tmp_path):
    report = _run(tmp_path)
    assert report.verdicts == [] and report.failures == []


def test_the_cli_exits_non_zero_on_a_mute_arm(tmp_path):
    _write(tmp_path / "ref.npz", _meta(clamp_ids=[], scale=1.0))
    _write(tmp_path / "arm.npz", _meta(scale=1.0))
    assert vct.main(["--traces-dir", str(tmp_path)]) == 1


def test_the_cli_exits_zero_on_a_healthy_corpus(tmp_path):
    _write(tmp_path / "ref.npz", _meta(clamp_ids=[], scale=1.0))
    _write(tmp_path / "arm.npz", _meta(scale=1.0), values=(9.0, 2.0, 3.0))
    assert vct.main(["--traces-dir", str(tmp_path), "--json"]) == 0


def test_a_missing_directory_is_a_named_failure(tmp_path):
    assert vct.main(["--traces-dir", str(tmp_path / "absent")]) == 2
