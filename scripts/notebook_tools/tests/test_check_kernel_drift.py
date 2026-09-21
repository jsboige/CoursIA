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


def _nb_cells(cells):
    """Build a notebook from (id, outputs) code-cell tuples."""
    return {
        "cells": [
            {
                "cell_type": "code",
                "id": cid,
                "execution_count": 1,
                "outputs": outputs,
            }
            for cid, outputs in cells
        ],
        "metadata": {"kernelspec": {}, "language_info": {}},
    }


def _stream_out(text):
    return [{"output_type": "stream", "name": "stdout", "text": text}]


def test_added_cell_without_signature_is_not_drift():
    # Founding instance of #17232: papermill replaces the
    # injected-parameters cell under a fresh nbformat id. The added
    # cell carries no float output, so it cannot be float-repr drift.
    # The common cell keeps the id-aligned branch active (a notebook
    # with zero common ids would fall back to ordinal alignment).
    common_out = _stream_out("v = [1.0, 1.0]\n")
    base = _nb_cells([
        ("2a6a4d49", _stream_out("params set\n")),
        ("keep", common_out),
    ])
    head = _nb_cells([
        ("bec0f46c", _stream_out("params set\n")),
        ("keep", common_out),
    ])
    base_sig = ckd.float_signatures(base)
    head_sig = ckd.float_signatures(head)
    assert ckd.diff_signatures(base_sig, head_sig, base_nb=base,
                               head_nb=head) == []


def test_added_cell_with_float_output_still_flagged():
    # Positive control: an added code cell that produces a tabular
    # float output keeps being reported.
    base = _nb_cells([("a", _stream_out("x = [1.0, 1.0]\n"))])
    head = _nb_cells([
        ("a", _stream_out("x = [1.0, 1.0]\n")),
        ("b", _stream_out("y = [2.0, 3.0]\n")),
    ])
    base_sig = ckd.float_signatures(base)
    head_sig = ckd.float_signatures(head)
    assert ckd.diff_signatures(base_sig, head_sig, base_nb=base,
                               head_nb=head) == ["b"]


def test_added_empty_cell_does_not_shift_common_alignment():
    # An added no-output cell inserted BEFORE a common cell must not
    # misalign the common cell: comparison stays id-driven, and the
    # common cell's own signature is looked up at its own ordinal.
    base = _nb_cells([("keep", _stream_out("v = [1.0, 1.0]\n"))])
    head = _nb_cells([
        ("new-empty", []),
        ("keep", _stream_out("v = [1.0, 1.0]\n")),
    ])
    base_sig = ckd.float_signatures(base)
    head_sig = ckd.float_signatures(head)
    # Drift on "keep" would signal an ordinal shift; the correct
    # result flags nothing.
    assert ckd.diff_signatures(base_sig, head_sig, base_nb=base,
                               head_nb=head) == []


def test_removed_injected_parameters_not_reported_either():
    # The removal side of the papermill replacement: the base-only id
    # disappears from the id maps entirely, so it contributes no diff
    # (removals were already silent; this pins the invariant).
    base = _nb_cells([
        ("2a6a4d49", _stream_out("params set\n")),
        ("keep", _stream_out("v = [1.0, 1.0]\n")),
    ])
    head = _nb_cells([("keep", _stream_out("v = [1.0, 1.0]\n"))])
    base_sig = ckd.float_signatures(base)
    head_sig = ckd.float_signatures(head)
    assert ckd.diff_signatures(base_sig, head_sig, base_nb=base,
                               head_nb=head) == []
