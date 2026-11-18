"""The cluster manifest must describe the bytes on disk (#19104).

The artifact was written without `newline=`, so on Windows `json.dump`'s LF became
CRLF on disk, while `_write_cluster_manifest` declared two fields that disagree:

- `artifact.bytes` from `out_path.stat().st_size` -- the RAW bytes, CRLF included;
- `artifact.sha256` from `_sha256_text(out_path.read_text(...))` -- and `read_text`
  normalises CRLF -> LF.

A reader running `sha256sum` on the artifact got a disagreement while the pipeline
was correct -- the aggregate looked falsifiable without being so, which is exactly
what the manifest exists to guarantee. The defect is silent on Linux, which is why
the write sites are guarded by AST (platform-independent) as well as by behaviour.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
from pathlib import Path

import pytest

from dlinear_vol import _write_cluster_manifest as dlinear_manifest
from m15_lstm_rv import _write_cluster_manifest as m15_manifest

SCRIPTS = Path(__file__).resolve().parent.parent

# Every module that declares a manifest anchored on an artifact hash.
MANIFEST_MODULES = (
    "dlinear_vol.py",
    "m13_ms_har.py",
    "merge_m13_partials.py",
    "m15_lstm_rv.py",
)


def _write_cluster_manifest_calls(tree: ast.AST) -> list[ast.Call]:
    return [
        node
        for node in ast.walk(tree)
        if isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "_write_cluster_manifest"
    ]


def _writes_to(target_src: str, tree: ast.AST, source: str) -> list[ast.Call]:
    """Calls writing the artifact the manifest is anchored on.

    ``p.write_text(data, ...)`` targets ``p`` (the attribute's receiver), while
    ``open(p, "w", ...)`` targets the first positional argument.
    """
    out = []
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        func = node.func
        if isinstance(func, ast.Attribute) and func.attr == "write_text":
            if ast.get_source_segment(source, func.value) == target_src:
                out.append(node)
        elif isinstance(func, ast.Name) and func.id == "open" and node.args:
            if ast.get_source_segment(source, node.args[0]) != target_src:
                continue
            mode = ast.get_source_segment(source, node.args[1]) if len(node.args) > 1 else None
            if mode is not None and "w" in mode:
                out.append(node)
    return out


@pytest.mark.parametrize("module", MANIFEST_MODULES)
def test_manifest_artifact_is_written_with_lf_newlines(module: str) -> None:
    """The artifact's bytes on disk must BE the canonical text the hash covers."""
    source = (SCRIPTS / module).read_text(encoding="utf-8")
    tree = ast.parse(source)

    calls = _write_cluster_manifest_calls(tree)
    assert len(calls) == 1, f"{module}: expected exactly one manifest call"

    call = calls[0]
    # manifest_path, all_rows, agg, out_path, args, elapsed_s
    target_arg = call.args[3]
    target_src = ast.get_source_segment(source, target_arg)
    assert target_src is not None

    writes = _writes_to(target_src, tree, source)
    assert writes, f"{module}: no write of the manifest artifact {target_src!r}"

    for write in writes:
        kwargs = {kw.arg: ast.get_source_segment(source, kw.value) for kw in write.keywords}
        assert kwargs.get("newline") == '"\\n"', (
            f"{module}: write of {target_src!r} must pass newline='\\n' -- "
            "otherwise the window text mode translates LF to CRLF and "
            "artifact.bytes stops describing artifact.sha256"
        )
        assert kwargs.get("encoding") == '"utf-8"', (
            f"{module}: write of {target_src!r} must pin encoding='utf-8'"
        )


def _args(**overrides: object) -> argparse.Namespace:
    base = {
        "horizons": [1, 5, 10],
        "seeds": [0, 7, 42, 99],
        "seq_len": 22,
        "n_splits": 5,
        "refit_every": 22,
        "epochs": 50,
        "decompose": True,
        "debias": True,
        "loss_fn": "mse",
        "hidden_size": 64,
        "fee_bps": 5,
        "window": 22,
    }
    base.update(overrides)
    return argparse.Namespace(**base)


_ROWS = [{
    "coin": "BTC",
    "horizon": 1,
    "seed": 0,
    "dm_cal_n_aligned": 100,
    "dm_target_gap_max": 0.0,
    "calibrated_dm_verdict": "OK",
}]


@pytest.mark.parametrize(
    "writer,agg",
    [
        (dlinear_manifest, []),
        (m15_manifest, {"BTC|h=1": {}}),
    ],
    ids=["dlinear_vol", "m15_lstm_rv"],
)
def test_declared_bytes_and_sha256_match_the_file_on_disk(writer, agg, tmp_path: Path) -> None:
    """End-to-end contract: read the manifest back and check it against the file."""
    artifact = tmp_path / "results.json"
    payload = json.dumps({"rows": _ROWS, "aggregated": []}, indent=2, default=str)
    # the fixed write form -- what the modules now use
    artifact.write_text(payload, encoding="utf-8", newline="\n")

    manifest_path = tmp_path / "manifest.json"
    writer(manifest_path, _ROWS, agg, artifact, _args(), 1.0)

    declared = json.loads(manifest_path.read_text(encoding="utf-8"))["artifact"]
    raw = artifact.read_bytes()

    assert declared["bytes"] == len(raw), "artifact.bytes does not describe the file"
    assert declared["sha256"] == hashlib.sha256(raw).hexdigest(), (
        "artifact.sha256 does not describe the file -- a reader running sha256sum "
        "on it would get a disagreement"
    )
    assert declared["bytes"] == len(payload.encode("utf-8"))
