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


def test_body_derive_suffix_parenthetical_exempts():
    """Suffix form '## Diagnostic derive (C.4)' exempts (cas vecu #17220).

    The strict end-of-line anchor used to reject the parenthetical
    qualifier, so a PR whose C.4 section was properly written but suffixed
    with '(C.4)' silently lost the exemption.
    """
    body = "## Summary\nFix\n\n## Diagnostic derive (C.4)\nverdict CAUSE_FIXED\n"
    assert ckd.body_has_derive_exemption(body) is True


def test_body_derive_suffix_parenthetical_accented_exempts():
    """Accented suffix form '## Diagnostic dérive (C.4)' exempts."""
    body = "## Summary\nFix\n\n## Diagnostic dérive (C.4)\nverdict CAUSE_FIXED\n"
    assert ckd.body_has_derive_exemption(body) is True


def test_body_derive_trailing_garbage_no_exemption():
    """Arbitrary trailing text (not a single parenthetical) stays rejected."""
    body = "## Summary\nFix\n\n## Diagnostic derive and other notes\n"
    assert ckd.body_has_derive_exemption(body) is False


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


def test_diff_signatures_no_ids_production_path():
    """Regression c.681: when BOTH base_nb and head_nb lack cell ids,
    diff_signatures must take the ordinal fallback (NOT return []).

    Reproduces jsboige CONCERNS d008d8b8fa: the production path always
    passes base_nb/head_nb (l.327 _run), and for legacy notebooks
    without cell ids both _code_index_by_id maps are empty -> 'common'
    is empty -> the previous guard `not common and (base_ids or
    head_ids)` was falsy on empty maps and returned []. The fix c.681
    removes the `(base_ids or head_ids)` clause so the fallback fires
    whenever 'common' is empty.
    """
    base_nb = {
        "cells": [
            {"cell_type": "code", "outputs": [{"text": "[1.0, 1.0, 1.0]"}]},
            {"cell_type": "code", "outputs": [{"text": "[2.0, 2.0, 2.0]"}]},
        ],
    }
    head_nb = {
        "cells": [
            {"cell_type": "code", "outputs": [{"text": "[1.0, 0.9999999999999999, 1.0]"}]},
            {"cell_type": "code", "outputs": [{"text": "[2.0, 2.0, 2.0]"}]},
        ],
    }
    base_sig = ckd.float_signatures(base_nb)
    head_sig = ckd.float_signatures(head_nb)
    # Production path: pass notebooks (legacy no-ids case)
    diffs = ckd.diff_signatures(base_sig, head_sig, base_nb=base_nb, head_nb=head_nb)
    # Cell 0 has a float drift (1.0 vs 0.999...); cell 1 unchanged.
    # Without the fix, diffs == [] (false negative).
    assert diffs == [0], (
        f"Without the fix, diff_signatures returns [] for legacy no-id "
        f"notebooks with real float drift. Got {diffs} instead of [0]."
    )


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


def test_workflow_defines_pr_body_env():
    """The workflow MUST set PR_BODY in the env: block of the kernel-drift step.

    Fix v2 (post-NanoClaw review #16466): without `PR_BODY: ${{ github.event.pull_request.body }}`
    in env, the `if [ -n "$PR_BODY" ]; then printf '%s' "$PR_BODY" > "$PR_BODY_FILE"`
    branch never fires in CI (PR_BODY is unset), so the `## Diagnostic dérive`
    exemption can never activate. C.4 acceptance of #15650 becomes unreachable.
    """
    yml = Path(__file__).resolve().parents[3] / ".github" / "workflows" / "notebook-kernel-drift-guard.yml"
    if not yml.exists():
        pytest.skip(f"workflow file not present at {yml}")
    content = yml.read_text(encoding="utf-8")
    # The env: block of the kernel-drift step MUST contain PR_BODY
    # pointing at github.event.pull_request.body.
    assert "PR_BODY:" in content, \
        "workflow env: block must declare PR_BODY so the body exemption can fire"
    # And it must source it from the pull_request event body (not an empty literal).
    assert "github.event.pull_request.body" in content, \
        "PR_BODY must source github.event.pull_request.body, not an empty literal"


def test_body_has_derive_exemption_case_insensitive():
    """The regex must be case-insensitive (header in lowercase should also match)."""
    body = "## diagnostic dérive\nblah\n"
    assert ckd.body_has_derive_exemption(body) is True


def test_body_has_derive_exemption_unaccented():
    """The regex must tolerate 'derive' without accent."""
    body = "## Diagnostic derive\nblah\n"
    assert ckd.body_has_derive_exemption(body) is True


# === Defect 1 v2: end-to-end branchement test (PR_BODY_FILE -> _run() -> exit 0) ===

def test_run_reads_pr_body_file_and_exempts(tmp_path, monkeypatch, capsys):
    """End-to-end: when PR_BODY_FILE points to a real file with '## Diagnostic dérive',
    _run() reads it, sets body_exempts=True, and the resulting JSON carries
    body_exempts=True even with a stub notebook that produces drift.

    This is the maillon cassé identified by NanoClaw in #16466 review: the previous
    fix added the function but never tested the branch from PR_BODY_FILE -> _run().
    Without this test, a regression of the env var wiring (defect 1 v1) would be
    invisible to the test suite.
    """
    # Write a real PR body with the diagnostic section
    pr_body_file = tmp_path / "pr_body"
    pr_body_file.write_text(
        "## Summary\nFix kernel drift\n\n## Diagnostic dérive\n"
        "Cell 12 and 14 drift due to numpy 2.x repr change.\n",
        encoding="utf-8",
    )
    monkeypatch.setenv("PR_BODY_FILE", str(pr_body_file))

    # Stub a notebook with kernel drift so the gate would otherwise fail
    drift_nb = {
        "cells": [],
        "metadata": {
            "kernelspec": {"name": "python3", "display_name": "Python"},
            "language_info": {"version": "3.11.16"},
        },
    }

    # Mock the git side so the script doesn't need a real repo
    monkeypatch.setattr(ckd, "git", lambda *args, cwd=None: "")
    monkeypatch.setattr(ckd, "resolve_base", lambda base, cwd=None: base)
    monkeypatch.setattr(ckd, "changed_notebooks", lambda base, cwd=None: ["x.ipynb"])
    monkeypatch.setattr(ckd, "read_blob", lambda *a, **kw: drift_nb)

    # Run with --json to inspect the result
    rc = ckd.main_with_args(["origin/main", "--json"])
    captured = capsys.readouterr()
    obj = json.loads(captured.out)
    # The exemption must have fired -- otherwise the branchement is still broken
    assert obj["body_exempts"] is True, \
        f"PR body exemption did not fire: body_exempts={obj['body_exempts']!r}"


def test_run_no_pr_body_file_exemption_false(tmp_path, monkeypatch, capsys):
    """Negative control: when PR_BODY_FILE points to a non-existent path,
    body_exempts must be False (no false positives on missing branchement)."""
    monkeypatch.setenv("PR_BODY_FILE", str(tmp_path / "does_not_exist"))

    monkeypatch.setattr(ckd, "git", lambda *args, cwd=None: "")
    monkeypatch.setattr(ckd, "resolve_base", lambda base, cwd=None: base)
    monkeypatch.setattr(ckd, "changed_notebooks", lambda base, cwd=None: [])
    monkeypatch.setattr(ckd, "read_blob", lambda *a, **kw: None)

    rc = ckd.main_with_args(["origin/main", "--json"])
    captured = capsys.readouterr()
    obj = json.loads(captured.out)
    assert obj["body_exempts"] is False


# === Defect 7 (PR #16466 NanoClaw review, exact-head 637a64ca):
# _cell_index_by_id walked ALL cells while float_signatures only emits
# one tuple per code cell. The id->ordinal map and the signature tuple
# were indexed in two different spaces, producing false-positive
# markdown drifts and missed real code drifts in the same notebook.
#
# Fix: _code_index_by_id walks code cells only, so the ordinals match
# float_signatures' code-only ordinals.
#
# The 4 tests below pin each scenario called out in NanoClaw's repro. ===


def _mk_md(cid, source="Titre"):
    return {
        "cell_type": "markdown",
        "id": cid,
        "metadata": {},
        "source": [source],
    }


def _mk_code(cid, src, sig_text):
    """Code cell with one float-array-shaped output."""
    return {
        "cell_type": "code",
        "id": cid,
        "metadata": {},
        "execution_count": 1,
        "source": [src],
        "outputs": [{
            "output_type": "display_data",
            "data": {"text/plain": sig_text},
            "metadata": {},
        }],
    }


def test_diff_signatures_md_before_modified_code():
    """[markdown, code-drift]: drift must be reported on the code cell,
    NOT on the markdown cell.

    Pre-fix: ``_cell_index_by_id`` registered both ids with their
    notebook-ordinal (md=0, code=1). ``float_signatures`` produced only
    the code tuple, but ``diff_signatures`` indexed it via the markdown
    id (0), comparing the code signature to itself and missing the drift.
    Worse: when a second code cell existed, its id resolved to a
    *different* code signature — the markdown phantom was listed as
    drift and the real code drift was missed.
    """
    base_nb = {
        "cells": [
            _mk_md("md-1", "Titre original"),
            _mk_code("code-1", "print([1.0, 1.0, 1.0])",
                     "[1.0, 1.0, 1.0]"),
        ],
        "metadata": {},
    }
    head_nb = {
        "cells": [
            _mk_md("md-1", "Titre MODIFIÉ"),
            _mk_code("code-1", "print([1.0, 1.0, 1.0])",
                     "[1.0, 0.9999999999999999, 1.0]"),
        ],
        "metadata": {},
    }
    diffs = ckd.diff_signatures(
        ckd.float_signatures(base_nb),
        ckd.float_signatures(head_nb),
        base_nb=base_nb, head_nb=head_nb,
    )
    assert diffs == ["code-1"], (
        f"expected only the code cell to drift, got {diffs} "
        "(pre-fix bug: markdown was reported as drift, code drift missed)"
    )


def test_diff_signatures_md_inserted_unchanged_code():
    """[markdown inserted before unchanged code]: must report no drift.

    Pre-fix: the inserted markdown shifted the code id to ordinal 1 in
    ``_cell_index_by_id`` while ``float_signatures`` still emitted only
    one tuple — the comparison was made against the wrong slot and the
    unchanged code was spuriously listed as drift.
    """
    S0 = "[1.0, 1.0, 1.0]"
    base_nb = {
        "cells": [
            _mk_code("code-1", "print([1.0, 1.0, 1.0])", S0),
        ],
        "metadata": {},
    }
    head_nb = {
        "cells": [
            _mk_md("md-inserted", "Section insérée"),
            _mk_code("code-1", "print([1.0, 1.0, 1.0])", S0),
        ],
        "metadata": {},
    }
    diffs = ckd.diff_signatures(
        ckd.float_signatures(base_nb),
        ckd.float_signatures(head_nb),
        base_nb=base_nb, head_nb=head_nb,
    )
    assert diffs == [], (
        f"expected no drift (markdown-only insertion, code unchanged), "
        f"got {diffs}"
    )


def test_diff_signatures_new_code_added_mixte_unchanged():
    """[existing code unchanged, new code appended]: drift must be the
    NEW code cell only.

    Pre-fix: ``_cell_index_by_id`` indexed markdown before the existing
    code, shifting its ordinal by +1 vs ``float_signatures``. The
    unchanged code was reported as drift and the new code also appeared
    as drift (double-counted).
    """
    base_nb = {
        "cells": [
            _mk_md("md-1", "Titre"),
            _mk_code("code-1", "x = 1.0", ""),  # no float output
        ],
        "metadata": {},
    }
    head_nb = {
        "cells": [
            _mk_md("md-1", "Titre"),
            _mk_code("code-1", "x = 1.0", ""),
            _mk_code("code-2", "print([1.0, 2.0, 3.0])",
                     "[1.0, 2.0, 3.0]"),
        ],
        "metadata": {},
    }
    diffs = ckd.diff_signatures(
        ckd.float_signatures(base_nb),
        ckd.float_signatures(head_nb),
        base_nb=base_nb, head_nb=head_nb,
    )
    assert diffs == ["code-2"], (
        f"expected only the newly added code cell, got {diffs} "
        "(pre-fix bug: code-1 was spuriously listed as drift)"
    )


def test_diff_signatures_mixte_unchanged_two_codes_drifted():
    """[markdown-1, code-1 (drift), markdown-2, code-2 (drift)]:
    drift must be exactly ['code-1', 'code-2'] — markdown invisible.

    This is the EXACT NanoClaw repro for #16466: with markdown between
    two code cells, the pre-fix map registered md-1 at ordinal 0, code-1
    at 1, md-2 at 2, code-2 at 3 — but ``float_signatures`` only had
    2 entries (code-1 and code-2). The diff compared code-1's
    signature to base_sig[1] (= code-2) and head_sig[1] (= code-2),
    spuriously reporting md-1 as drift while missing code-2's drift.
    """
    base_nb = {
        "cells": [
            _mk_md("md-1", "Titre"),
            _mk_code("code-1", "print([1.0, 1.0, 1.0])",
                     "[1.0, 1.0, 1.0]"),
            _mk_md("md-2", "Sous-titre"),
            _mk_code("code-2", "print([2.0, 2.0])", "[2.0, 2.0]"),
        ],
        "metadata": {},
    }
    head_nb = {
        "cells": [
            _mk_md("md-1", "Titre inchangé"),
            _mk_code("code-1", "print([1.0, 1.0, 1.0])",
                     "[1.0, 0.9999999999999999, 1.0]"),
            _mk_md("md-2", "Sous-titre inchangé"),
            _mk_code("code-2", "print([2.0, 2.0])",
                     "[2.0, 1.9999999999999998]"),
        ],
        "metadata": {},
    }
    diffs = ckd.diff_signatures(
        ckd.float_signatures(base_nb),
        ckd.float_signatures(head_nb),
        base_nb=base_nb, head_nb=head_nb,
    )
    assert diffs == ["code-1", "code-2"], (
        f"expected exactly the two drifted code cells, got {diffs} "
        "(pre-fix bug: md-1 spuriously listed, code-2 drift missed)"
    )
