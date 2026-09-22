"""Unit tests for check_kernel_drift.py.

We test the pure functions (no git, no filesystem) and provide a small
end-to-end harness using tmp_path + a fake git that exposes two blobs.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import check_kernel_drift as ckd


def _nb(kernel_name, lang_version, code_outputs):
    """Build a minimal notebook JSON dict."""
    return {
        "cells": [
            {
                "cell_type": "code",
                "execution_count": 1,
                "outputs": [{"output_type": "stream", "name": "stdout",
                             "text": code_outputs}],
            }
        ],
        "metadata": {
            "kernelspec": {"name": kernel_name, "display_name": "Python"},
            "language_info": {"version": lang_version},
        },
    }


def test_kernel_info_extracts_fields():
    nb = _nb("python3", "3.11.16", [])
    info = ckd.kernel_info(nb)
    assert info["kernelspec_name"] == "python3"
    assert info["language_version"] == "3.11.16"
    assert info["kernelspec_display"] == "Python"


def test_kernel_info_missing_fields():
    nb = {"metadata": {}}
    info = ckd.kernel_info(nb)
    assert info == {"kernelspec_name": "", "language_version": "",
                    "kernelspec_display": ""}


def test_diff_kernel_no_change():
    a = {"language_version": "3.11.16", "kernelspec_name": "python3"}
    b = {"language_version": "3.11.16", "kernelspec_name": "python3"}
    assert ckd.diff_kernel(a, b) == []


def test_diff_kernel_python_version_change():
    a = {"language_version": "3.11.16", "kernelspec_name": "python3"}
    b = {"language_version": "3.13.3", "kernelspec_name": "python3"}
    diffs = ckd.diff_kernel(a, b)
    assert len(diffs) == 1
    assert "language_info.version" in diffs[0]
    assert "3.11.16" in diffs[0] and "3.13.3" in diffs[0]


def test_diff_kernel_kernelspec_change():
    a = {"language_version": "3.11.16", "kernelspec_name": "python3"}
    b = {"language_version": "3.11.16", "kernelspec_name": "python311"}
    diffs = ckd.diff_kernel(a, b)
    assert len(diffs) == 1
    assert "kernelspec.name" in diffs[0]


def test_diff_kernel_both_change():
    a = {"language_version": "3.11.16", "kernelspec_name": "python3"}
    b = {"language_version": "3.13.3", "kernelspec_name": "python3"}
    diffs = ckd.diff_kernel(a, b)
    # Only version differs; kernelspec.name identical.
    assert len(diffs) == 1


# --- #17371: patch-level language_info.version drift is not a regression ---


def test_version_prefix_shapes():
    assert ckd._version_prefix("3.13.3") == "3.13"
    assert ckd._version_prefix("3.13.15") == "3.13"
    assert ckd._version_prefix("3.13.15rc1") == "3.13"
    assert ckd._version_prefix("3.13") == "3.13"
    assert ckd._version_prefix("3") == "3"
    assert ckd._version_prefix("") == ""


def test_diff_kernel_patch_level_drift_not_flagged():
    # Measured on #16858: base stamp 3.13.3, fresh re-exec under the
    # project venv 3.13.15 -- same kernel, same repr() semantics.
    a = {"language_version": "3.13.3", "kernelspec_name": "python3"}
    b = {"language_version": "3.13.15", "kernelspec_name": "python3"}
    assert ckd.diff_kernel(a, b) == []


def test_diff_kernel_patch_drift_with_rc_suffix_not_flagged():
    a = {"language_version": "3.13.3", "kernelspec_name": "python3"}
    b = {"language_version": "3.13.15rc1", "kernelspec_name": "python3"}
    assert ckd.diff_kernel(a, b) == []


def test_diff_kernel_minor_change_still_flagged():
    a = {"language_version": "3.11.16", "kernelspec_name": "python3"}
    b = {"language_version": "3.13.15", "kernelspec_name": "python3"}
    diffs = ckd.diff_kernel(a, b)
    assert len(diffs) == 1
    assert "3.11.16" in diffs[0] and "3.13.15" in diffs[0]
    assert "3.11 -> 3.13" in diffs[0]


def test_diff_kernel_major_change_still_flagged():
    a = {"language_version": "2.7.18", "kernelspec_name": "python3"}
    b = {"language_version": "3.13.15", "kernelspec_name": "python3"}
    diffs = ckd.diff_kernel(a, b)
    assert len(diffs) == 1


def test_diff_kernel_empty_vs_full_version_flagged():
    a = {"language_version": "", "kernelspec_name": "python3"}
    b = {"language_version": "3.13.15", "kernelspec_name": "python3"}
    assert len(ckd.diff_kernel(a, b)) == 1


def test_float_signatures_matches_array_shape():
    nb = _nb("python3", "3.13.3",
             ["n=5: distances = [1.0, 0.9999999999999999, 1.0, 1.0, 1.0]\n"])
    sig = ckd.float_signatures(nb)
    assert len(sig) == 1
    assert len(sig[0]) == 1  # one array-shaped match
    assert "0.9999999999999999" in sig[0][0]


def test_float_signatures_ignores_non_code_cells():
    nb = {
        "cells": [
            {"cell_type": "markdown", "source": ["[1.0, 1.0, 1.0]"]},
            {"cell_type": "code", "outputs": [], "execution_count": 1},
        ],
        "metadata": {"kernelspec": {}, "language_info": {}},
    }
    sig = ckd.float_signatures(nb)
    assert sig == ((),)


def test_float_signatures_empty():
    nb = _nb("python3", "3.11.16", [])
    assert ckd.float_signatures(nb) == ((),)


def test_diff_signatures_identical():
    a = (("[1.0, 1.0, 1.0]",),)
    b = (("[1.0, 1.0, 1.0]",),)
    assert ckd.diff_signatures(a, b) == []


def test_diff_signatures_float_drift():
    # NumPy 1.x: [1.0, 1.0, ...]
    # NumPy 2.x: [1.0, 0.9999999999999999, 1.0, ...]
    a = (("[1.0, 1.0, 1.0, 1.0, 1.0]",),)
    b = (("[1.0, 0.9999999999999999, 1.0, 1.0, 1.0]",),)
    assert ckd.diff_signatures(a, b) == [0]


def test_diff_signatures_added_cell():
    a = (("[1.0, 1.0]",),)
    b = (("[1.0, 1.0]",), ("[2.0, 2.0]",))
    assert ckd.diff_signatures(a, b) == [1]


def test_diff_signatures_removed_cell():
    a = (("[1.0, 1.0]",), ("[2.0, 2.0]",))
    b = (("[1.0, 1.0]",),)
    assert ckd.diff_signatures(a, b) == [1]


def test_diff_signatures_complex_float_with_exponent():
    a = (("[-1.5e+00, 2.5e-01, 3.14159]",),)
    b = (("[-1.5e+00, 2.5000000000000004e-01, 3.14159]",),)
    assert ckd.diff_signatures(a, b) == [0]


def _nb_ids(cells):
    """Build a notebook from (cell_id, output_text) code cells.

    ``output_text`` None means "the cell has no output at all" (the shape of
    papermill's `injected-parameters` cell, and of a parameters cell).
    """
    return {
        "cells": [
            {
                "cell_type": "code",
                "id": cid,
                "execution_count": 1,
                "outputs": ([] if text is None else
                            [{"output_type": "stream", "name": "stdout",
                              "text": text}]),
            }
            for cid, text in cells
        ],
        "metadata": {
            "kernelspec": {"name": "python3", "display_name": "Python 3"},
            "language_info": {"version": "3.13.3"},
        },
    }


def _id_aligned_diffs(base_cells, head_cells):
    """Run diff_signatures through the id-aligned branch (notebooks given)."""
    base = _nb_ids(base_cells)
    head = _nb_ids(head_cells)
    return ckd.diff_signatures(ckd.float_signatures(base),
                               ckd.float_signatures(head),
                               base_nb=base, head_nb=head)


def test_diff_signatures_added_empty_cell_not_reported():
    """#17232 founding instance (PR #17145).

    Papermill replaces its `injected-parameters` cell on every re-execution,
    and nbformat 4.5 hands the replacement a fresh cell id. The added cell
    carries no output at all, so it cannot be a float-repr drift: the pair
    (one id removed, one id added) is the normal fingerprint of a
    re-execution, not a regression.
    """
    assert _id_aligned_diffs(
        [("params", None), ("c-work", "ok\n")],
        [("params-new", None), ("c-work", "ok\n")],
    ) == []


def test_diff_signatures_added_cell_with_float_still_reported():
    """Positive control: the fix must not blind the gate.

    An added cell that really produces a float array is still a drift.
    """
    assert _id_aligned_diffs(
        [("c1", "[1.0, 1.0]\n")],
        [("c1", "[1.0, 1.0]\n"), ("c2", "[2.0, 2.0]\n")],
    ) == ["c2"]


def test_diff_signatures_added_empty_cell_does_not_mask_a_real_drift():
    """An empty added cell must not mask drift on a common cell."""
    assert _id_aligned_diffs(
        [("c1", "[1.0, 1.0]\n"), ("c2", "[2.0, 2.0]\n")],
        [("params-new", None), ("c1", "[1.0, 0.9999999999999999]\n"),
         ("c2", "[2.0, 2.0]\n")],
    ) == ["c1"]


def test_diff_signatures_added_mixed_only_float_ones_reported():
    """Among several added cells, only those carrying a signature report."""
    assert _id_aligned_diffs(
        [("c1", "ok\n")],
        [("c1", "ok\n"), ("injected", None), ("c3", "[3.0, 3.0]\n")],
    ) == ["c3"]

