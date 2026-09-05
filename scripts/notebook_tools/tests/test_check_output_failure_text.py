"""Tests for check_output_failure_text.py — capability-downgrade axis (#14603).

Pins the couple contract: a capability value regression AND a witness-line
disappearance on a byte-identical-source cell is the finding; each half
alone, a changed source, a same-tier value wiggle, and the restoration
(upgrade) direction are all silent. No network, no kernel.
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_output_failure_text import (CAPABILITY_VALUE_RE,
                                       CAPABILITY_WITNESS_PATTERNS,
                                       capability_downgrades)


def cell(source, out_text):
    return {"cell_type": "code", "source": source,
            "outputs": [{"output_type": "stream", "name": "stdout",
                         "text": out_text}]}


def nb(*cells):
    return {"cells": list(cells), "metadata": {}, "nbformat": 4,
            "nbformat_minor": 5}


GPU_SRC = "print(info)\nprint(f'VRAM utilisee : {v:.2f} GB')"
GPU_OUT = "Device : cuda\nVRAM utilisee : 0.64 GB"
CPU_OUT = "Device : cpu"


def test_couple_fires():
    got = capability_downgrades(nb(cell(GPU_SRC, GPU_OUT)),
                                nb(cell(GPU_SRC, CPU_OUT)))
    assert len(got) == 1
    assert got[0]["cell"] == 0
    assert got[0]["base"] == "cuda"
    assert got[0]["head"] == "cpu"


def test_legit_reexec_silent():
    wiggle = "Device : cuda\nVRAM utilisee : 0.63 GB"
    assert capability_downgrades(nb(cell(GPU_SRC, GPU_OUT)),
                                 nb(cell(GPU_SRC, wiggle))) == []


def test_changed_source_silent():
    assert capability_downgrades(
        nb(cell(GPU_SRC, GPU_OUT)),
        nb(cell(GPU_SRC + "\nprint('cpu fallback')", CPU_OUT))) == []


def test_value_regression_without_witness_loss_silent():
    kept = "Device : cpu\nVRAM utilisee : 0.00 GB"
    assert capability_downgrades(nb(cell(GPU_SRC, GPU_OUT)),
                                 nb(cell(GPU_SRC, kept))) == []


def test_witness_loss_without_value_regression_silent():
    assert capability_downgrades(nb(cell(GPU_SRC, GPU_OUT)),
                                 nb(cell(GPU_SRC, "Device : cuda"))) == []


def test_upgrade_silent():
    # Restoration direction of #14262: cpu -> cuda with the witness line
    # APPEARING must never fire.
    assert capability_downgrades(nb(cell(GPU_SRC, CPU_OUT)),
                                 nb(cell(GPU_SRC, GPU_OUT))) == []


def test_markdown_cells_ignored():
    # Same index, but the base cell is markdown: index-matched comparison
    # must skip non-code cells, not crash.
    assert capability_downgrades(
        nb({"cell_type": "markdown", "source": GPU_SRC,
            "outputs": []}, cell(GPU_SRC, GPU_OUT)),
        nb(cell(GPU_SRC, CPU_OUT))) == []


def test_value_extraction_witnessed_forms():
    for text, expected in (
            ("Mode : batch, Device : cuda", {"cuda"}),
            ("Device : cpu", {"cpu"}),
            ("Device: CUDA", {"cuda"}),
            ("device='cuda:0'", {"cuda"}),
            ("torch.device('cuda:0')", set()),
            ("VRAM utilisee : 0.64 GB", set())):
        assert CAPABILITY_VALUE_RE.search(text) is not None or not expected
        got = set()
        for m in CAPABILITY_VALUE_RE.finditer(text):
            v = m.group(1).lower().split(":")[0].strip()
            got.add(v)
        assert got == expected, text


def test_witness_patterns_match_measured_lines():
    # Closed, witnessed set -- measured on origin/main 2026-09-04.
    for line in ("VRAM utilisee : 0.64 GB",
                 "GPU : NVIDIA GeForce RTX 3090 (24.0 GB VRAM)",
                 "24.0 GB VRAM)"):
        assert any(p.search(line) for p in CAPABILITY_WITNESS_PATTERNS), line


def test_founding_fixture_fires():
    """The #14262 founding pair, pinned as a fixture because the degraded
    head is branch-side history of a squash-merged PR (absent from fresh
    clones). Both cells must fire; the sources must be byte-identical so
    the finding cannot be an artifact of a source change."""
    fx = (Path(__file__).parent / "fixtures"
          / "demucs_downgrade_pair_14603.json")
    blob = json.loads(fx.read_text(encoding="utf-8"))
    assert blob["provenance"]["founding_pr"] == 14262
    for b, h in zip(blob["base_cells"], blob["head_cells"]):
        assert b["source"] == h["source"]
    got = capability_downgrades({"cells": blob["base_cells"]},
                                {"cells": blob["head_cells"]})
    assert len(got) == 2
    assert all(g["base"] == "cuda" and g["head"] == "cpu"
               and g["witness_lost"] >= 1 for g in got)
