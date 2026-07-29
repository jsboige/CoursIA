"""Ratchet contract for the render-suite CI gates (#8884 motif).

Every detector gate runs its ``python scripts/notebook_tools/detect_*.py`` call
under ``bash -e`` (the GitHub Actions Ubuntu default: ``bash --noprofile --norc
-eo pipefail {0}``). Under errexit, a bare ``out=$(cmd)`` that exits non-zero
aborts the **whole step** before the following ``rc=$?`` is read -- which makes
the ``rc=1`` / ``rc=2`` branches below it unreachable dead code. A real finding
then surfaces as a bare anonymous ``exit 1``, indistinguishable from the
detector crashing, and the gate can never *name* the notebook it caught.

This is the defect #8884 filed against ``degenerate-figure-gate`` (fixed in
#8886) and that the same issue's "Portée" carved out for the render-suite
siblings. The fix is the ``&& rc=0 || rc=$?`` tail (membership in a ``&&``/``||``
list is exempt from errexit, and ``$?`` reads the real detector exit code).

A unit test cannot observe another job's interpreter -- that is the crack #8884
fell through (the detector library tests stayed green while the workflow was
broken in CI). So this ratchet asserts against the **workflow FILE**, not the
detector. Reverting any gate to the errexit-unsafe form turns this file red
instead of silently disarming the gate.

Auto-discovers the render-suite via ``{svg,degenerate}*-gate.yml`` so a gate
added later with the bug is caught here automatically.
"""

from __future__ import annotations

import pathlib

import pytest

_WF_DIR = (
    pathlib.Path(__file__).resolve().parents[3]
    / ".github"
    / "workflows"
)

# The render-suite: figure/SVG-quality gates that all run a detect_*.py call
# under bash -e. Discovered by glob so future render-suite gates are covered.
_RENDER_SUITE = sorted(
    list(_WF_DIR.glob("svg-*-gate.yml")) + list(_WF_DIR.glob("degenerate-*-gate.yml"))
)


def _detector_invocation(text: str) -> str | None:
    """Return the ``out=$(python ... detect_*.py ...)`` line, or None.

    ``cell_order_ci.py`` and other non-detect invocations are intentionally not
    matched -- this ratchet scopes the #8884 detector motif.
    """
    for line in text.splitlines():
        s = line.strip()
        if "out=$(" in s and "detect_" in s and "scripts/notebook_tools" in s:
            return s
    return None


@pytest.mark.parametrize("workflow", _RENDER_SUITE, ids=lambda p: p.stem)
def test_render_suite_gate_invocation_is_errexit_safe(workflow: pathlib.Path):
    """Each render-suite gate must read the detector exit code under ``bash -e``.

    The ``out=$(...) && rc=0 || rc=$?`` form preserves the real exit code: a
    bare ``out=$(cmd)`` aborts the step on non-zero before ``rc=$?`` is read.
    """
    assert workflow.is_file(), f"render-suite gate missing: {workflow}"
    text = workflow.read_text(encoding="utf-8")
    invocation = _detector_invocation(text)
    assert invocation is not None, (
        f"{workflow.name}: expected an `out=$(... detect_*.py ...)` invocation"
    )
    assert "&& rc=0 || rc=$?" in invocation, (
        f"{workflow.name}: errexit-unsafe invocation {invocation!r} -- under "
        "`bash -e` a bare `out=$(cmd)` aborts before `rc=$?` is read, making the "
        "rc=1/rc=2 branches dead code. Use `out=$(...) && rc=0 || rc=$?`."
    )
    # `|| true` would make `$?` read 0 from `true` itself: rc always 0, so the
    # gate could never fire at all -- strictly worse than the original bug.
    assert "|| true" not in invocation, (
        f"{workflow.name}: `|| true` makes rc always 0 and permanently disarms "
        "the gate; use `&& rc=0 || rc=$?`."
    )


def test_render_suite_discovered_at_least_the_known_gates():
    """Guard against the glob silently matching nothing (e.g. a rename).

    If this fails, either the glob pattern drifted or every render-suite gate
    was renamed -- the parametrize above would then run zero cases and look
    green for the wrong reason.
    """
    stems = {p.stem for p in _RENDER_SUITE}
    expected = {
        "svg-decimal-comma-gate",
        "svg-empty-display-gate",
        "svg-broken-geometry-gate",
        "svg-offscreen-flat-gate",
        "degenerate-figure-gate",
    }
    missing = expected - stems
    assert not missing, (
        f"render-suite glob no longer matches known gates: {sorted(missing)}; "
        "the parametrize would run zero cases and hide regressions"
    )
