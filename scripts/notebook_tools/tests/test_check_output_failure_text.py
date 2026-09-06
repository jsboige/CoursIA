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
                                       _sample_location,
                                       CAPABILITY_WITNESS_PATTERNS,
                                       capability_downgrades,
                                       metadata_texts,
                                       scan)


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


# --- #14513: MACHINE_PATH extended to document/cell metadata ---------------
# The output-only predicate was blind to metadata; a machine path in
# metadata.path passed the gate green (#14272 / #13891). The REAL leaked
# value is the positive control.

DUP_PATH = ("C:\\dev\\CoursIA-cycle-32\\MyIA.AI.Notebooks\\"
            "GenAI\\PostTraining")


def test_metadata_texts_yields_string_values():
    cells = {"cells": [
        {"cell_type": "code", "metadata": {"path": DUP_PATH}, "outputs": []},
        {"cell_type": "markdown", "metadata": {"tags": ["x"]}, "outputs": []}],
        "metadata": {"path": DUP_PATH, "kernelspec": {"name": "python3"}}}
    locs = list(metadata_texts(cells))
    assert ("doc:path", DUP_PATH) in locs
    assert ("cell[0]:path", DUP_PATH) in locs
    # dicts are not scanned; tags is a list.
    assert not any(l.startswith("doc:kernelspec") for l, _ in locs)


def test_metadata_path_machine_fires():
    nb_ = {"cells": [], "metadata": {"path": DUP_PATH}}
    hits = [loc for loc, _ in scan(nb_)["MACHINE_PATH"]]
    assert "doc:path" in hits


def test_cell_metadata_machine_fires():
    cell = {"cell_type": "code", "source": "print(1)",
            "metadata": {"path": DUP_PATH}, "outputs": []}
    hits = [loc for loc, _ in scan({"cells": [cell], "metadata": {}})
            ["MACHINE_PATH"]]
    assert "cell[0]:path" in hits


def test_metadata_path_clean_silent():
    # No metadata, and a repo-relative value (the shape the pre-commit hook
    # and convention leave in place) must stay silent.
    assert scan({"cells": [], "metadata": {}})["MACHINE_PATH"] == []
    rel = {"cells": [], "metadata": {"path": (
        "MyIA.AI.Notebooks/GenAI/PostTraining/"
        "PT_11c_grpo_qwen17_rlvr.ipynb")}}
    assert scan(rel)["MACHINE_PATH"] == []


def test_metadata_papermill_paths_silent():
    # Precaution 1 of #14513: input_path/output_path normalized to a
    # repo-relative path or basename must never fire retroactively.
    pm = {"input_path": ("MyIA.AI.Notebooks/GenAI/PostTraining/"
                         "PT_11c_grpo_qwen17_rlvr.ipynb"),
          "output_path": "PT_11c_grpo_qwen17_rlvr.ipynb"}
    assert scan({"cells": [], "metadata": {"papermill": pm}})["MACHINE_PATH"] == []


def test_metadata_non_string_silent():
    # Document metadata is scanned for STRING values only -- dicts (kernelspec,
    # language_info) and ints are not machine paths by construction.
    nb_ = {"cells": [], "metadata": {
        "kernelspec": {"name": "python3", "display_name": "Python 3"},
        "language_info": {"name": "python"},
        "toc": 3}}
    assert scan(nb_)["MACHINE_PATH"] == []


def test_output_paths_still_scanned_alongside_metadata():
    # The extension must not regress the original output surface: an output
    # path AND a metadata path both fire, with distinct locations.
    cell = {"cell_type": "code", "source": "print(1)",
            "metadata": {"path": DUP_PATH},
            "outputs": [{"output_type": "stream", "text": DUP_PATH}]}
    nb_ = {"cells": [cell], "metadata": {"path": DUP_PATH}}
    hits = scan(nb_)["MACHINE_PATH"]
    locs = [loc for loc, _ in hits]
    assert "doc:path" in locs
    assert "cell[0]:path" in locs
    assert 0 in locs  # output hit keeps its cell index


def test_sample_location_renders_each_shape_once():
    # Les trois formes que scan() produit cote a cote (cf. le test ci-dessus)
    # doivent s'imprimer telles quelles. Sans le tri, l'imprimeur FAIL
    # enveloppait tout dans cell[...] : un hit metadata de document sortait
    # "cell[doc:path]" et un hit metadata de cellule "cell[cell[0]:path]".
    assert _sample_location(0) == "cell[0]"        # hit d'output : index entier
    assert _sample_location("doc:path") == "doc:path"
    assert _sample_location("cell[0]:path") == "cell[0]:path"


def test_sample_location_no_double_wrapping_on_real_scan_output():
    # Controle positif sur les localisations REELLES de scan(), pas sur des
    # litteraux : aucune sortie ne doit contenir "cell[cell[" ni "cell[doc:".
    cell_ = {"cell_type": "code", "source": "print(1)",
             "metadata": {"path": DUP_PATH},
             "outputs": [{"output_type": "stream", "text": DUP_PATH}]}
    nb_ = {"cells": [cell_], "metadata": {"path": DUP_PATH}}
    rendered = [_sample_location(loc) for loc, _ in scan(nb_)["MACHINE_PATH"]]
    assert rendered, "le controle positif doit produire des hits"
    for r in rendered:
        assert "cell[cell[" not in r
        assert "cell[doc:" not in r
