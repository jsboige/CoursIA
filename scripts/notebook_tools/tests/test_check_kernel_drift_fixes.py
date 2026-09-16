"""Red-first tests for the 6 defects identified in PR #16082.

Defects:
1. body exemption: `## Diagnostic dérive` should exempt kernel drift
2. signature alignment: by cell id (stable) + fallback ordinal
3. main() called twice: --json should emit ONE JSON document
4. git fail-closed: blob/diff errors should NOT silently skip notebooks
5. float_signatures: text/plain as LIST should not raise TypeError
6. workflow: pull_request.types should include [opened, synchronize, edited, reopened]
"""

import json
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import check_kernel_drift as ckd


# === Defect 1: body exemption ===

def _make_body_with_derive(content):
    return content + "\n\n## Diagnostic dérive\nsome text\n"


def test_body_has_derive_exemption():
    """If body contains '## Diagnostic dérive', exemption applies."""
    body = _make_body_with_derive("## Summary\nFix")
    assert ckd.body_has_derive_exemption(body) is True


def test_body_no_derive_no_exemption():
    """If body lacks '## Diagnostic dérive', no exemption."""
    body = "## Summary\nFix without diagnostic"
    assert ckd.body_has_derive_exemption(body) is False


def test_body_empty_no_exemption():
    """Empty body: no exemption."""
    assert ckd.body_has_derive_exemption("") is False


# === Defect 5: float_signatures normalization ===

def test_float_signatures_text_plain_list():
    """text/plain as LIST (1409/1430 corpus) should not raise TypeError."""
    nb = {
        "cells": [
            {
                "cell_type": "code",
                "execution_count": 1,
                "outputs": [{
                    "output_type": "execute_result",
                    "data": {"text/plain": ["[1.0, 1.0, 1.0]\n"]},
                    "metadata": {},
                }],
            }
        ],
        "metadata": {},
    }
    sig = ckd.float_signatures(nb)
    assert sig == (("[1.0, 1.0, 1.0]",),), \
        f"Expected single cell with one match, got {sig}"


def test_float_signatures_text_plain_string():
    """text/plain as plain string still works."""
    nb = {
        "cells": [
            {
                "cell_type": "code",
                "execution_count": 1,
                "outputs": [{
                    "output_type": "execute_result",
                    "data": {"text/plain": "[1.0, 1.0, 1.0]"},
                    "metadata": {},
                }],
            }
        ],
        "metadata": {},
    }
    sig = ckd.float_signatures(nb)
    assert sig == (("[1.0, 1.0, 1.0]",),), \
        f"Expected single cell with one match, got {sig}"


def test_float_signatures_stream_string():
    """Stream text as plain string."""
    nb = {
        "cells": [
            {
                "cell_type": "code",
                "execution_count": 1,
                "outputs": [{
                    "output_type": "stream",
                    "name": "stdout",
                    "text": "[1.0, 1.0, 1.0]\n",
                }],
            }
        ],
        "metadata": {},
    }
    sig = ckd.float_signatures(nb)
    assert sig == (("[1.0, 1.0, 1.0]",),), f"got {sig}"


def test_float_signatures_stream_list():
    """Stream text as list of strings (common with Papermill)."""
    nb = {
        "cells": [
            {
                "cell_type": "code",
                "execution_count": 1,
                "outputs": [{
                    "output_type": "stream",
                    "name": "stdout",
                    "text": ["[1.0, 1.0, 1.0]", " more\n"],
                }],
            }
        ],
        "metadata": {},
    }
    sig = ckd.float_signatures(nb)
    assert sig == (("[1.0, 1.0, 1.0]",),), f"got {sig}"


# === Defect 2: signature alignment by cell id ===

def test_diff_signatures_by_cell_id_stable():
    """Insertion of a new cell before an unchanged cell should NOT report drift."""
    base_nb = {
        "cells": [
            {"id": "abc", "cell_type": "code", "outputs": [{"text": "[1.0, 1.0]"}]},
            {"id": "def", "cell_type": "code", "outputs": [{"text": "[2.0, 2.0]"}]},
        ],
    }
    head_nb = {
        "cells": [
            {"id": "new", "cell_type": "code", "outputs": [{"text": "[9.0, 9.0]"}]},
            {"id": "abc", "cell_type": "code", "outputs": [{"text": "[1.0, 1.0]"}]},
            {"id": "def", "cell_type": "code", "outputs": [{"text": "[2.0, 2.0]"}]},
        ],
    }
    base_sig = ckd.float_signatures(base_nb)
    head_sig = ckd.float_signatures(head_nb)
    diffs = ckd.diff_signatures(base_sig, head_sig, base_nb=base_nb, head_nb=head_nb)
    # abc and def unchanged, only 'new' added (by id)
    assert diffs == ["new"], \
        f"Expected only 'new' as drift, got {diffs}"


def test_diff_signatures_fallback_ordinal():
    """When no cell id, fall back to ordinal (legacy behavior)."""
    base_sig = (("[1.0, 1.0]",), ("[2.0, 2.0]",))
    head_sig = (("[1.0, 1.0]",), ("[2.5, 2.5]",))  # cell 1 changed
    diffs = ckd.diff_signatures(base_sig, head_sig)
    assert diffs == [1]


def test_diff_signatures_unchanged_with_id_alignment():
    """Cells unchanged by id should not be flagged even if ordinal shifts."""
    base_nb = {
        "cells": [
            {"id": "x", "outputs": [{"text": "[1.0, 1.0]"}]},
            {"id": "y", "outputs": [{"text": "[2.0, 2.0]"}]},
        ],
    }
    head_nb = {
        "cells": [
            {"id": "x", "outputs": [{"text": "[1.0, 1.0]"}]},
            {"id": "y", "outputs": [{"text": "[2.0, 2.0]"}]},
        ],
    }
    diffs = ckd.diff_signatures(
        ckd.float_signatures(base_nb),
        ckd.float_signatures(head_nb),
        base_nb=base_nb, head_nb=head_nb,
    )
    assert diffs == []


# === Defect 3: main() called twice produces single JSON ===

def test_main_json_called_once(tmp_path, monkeypatch, capsys):
    """When --json is used, exactly one JSON document is printed."""
    # Mock git so no real repo is needed
    monkeypatch.setattr(ckd, "git", lambda *args, cwd=None: None)
    # Mock read_blob to return minimal nb with no diff
    monkeypatch.setattr(ckd, "read_blob", lambda *a, **kw: {
        "cells": [], "metadata": {"kernelspec": {}, "language_info": {}},
    })
    monkeypatch.setattr(ckd, "changed_notebooks", lambda *a, **kw: ["fake.ipynb"])
    monkeypatch.setattr(ckd, "resolve_base", lambda *a, **kw: "HEAD")

    rc = ckd.main_with_args(["origin/main", "--json"])
    captured = capsys.readouterr()
    # Parse the output as JSON — must succeed for a single object
    try:
        obj = json.loads(captured.out)
        assert "findings" in obj
    except json.JSONDecodeError as e:
        pytest.fail(f"Output is not valid single JSON: {e}\nOutput was:\n{captured.out}")


# === Defect 4: git fail-closed ===

def test_git_returns_none_raises():
    """If git() fails (tool error), should NOT silently return None for caller."""
    # The new behavior: git_fail_closed() raises on subprocess error
    with pytest.raises(RuntimeError):
        ckd.git_fail_closed("nonexistent-git-command-12345")


# === Defect 6: workflow pulls edited events ===

def test_workflow_pull_request_types():
    """The workflow should declare pull_request.types including 'edited'."""
    # Path: tests/ -> notebook_tools/ -> scripts/ -> repo_root
    yml = Path(__file__).resolve().parents[3] / ".github" / "workflows" / "notebook-kernel-drift-guard.yml"
    if not yml.exists():
        pytest.skip(f"workflow file not present at {yml}")
    content = yml.read_text(encoding="utf-8")
    # The new contract: pull_request.types includes 'edited'
    assert "edited" in content, \
        "workflow must include 'edited' in pull_request.types"
