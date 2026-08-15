"""Ratchet contract for the detector CI gates (#8884 motif).

Every detector gate runs its ``python scripts/notebook_tools/<detector>.py`` call
under ``bash -e`` (the GitHub Actions Ubuntu default: ``bash --noprofile --norc
-eo pipefail {0}``). Under errexit, a bare ``out=$(cmd)`` that exits non-zero
aborts the **whole step** before the following ``rc=$?`` is read -- which makes
the ``rc=1`` / ``rc=2`` branches below it unreachable dead code. A real finding
then surfaces as a bare anonymous ``exit 1``, indistinguishable from the
detector crashing, and the gate can never *name* the notebook it caught.

This is the defect #8884 filed against ``degenerate-figure-gate`` (fixed in
#8886). The same issue's "Portée" anticipated the render-suite siblings (fixed
in #8890) and the remaining detector gates (fixed alongside this ratchet's
generalization). The fix is the ``&& rc=0 || rc=$?`` tail (membership in a
``&&``/``||`` list is exempt from errexit, and ``$?`` reads the real detector
exit code).

A unit test cannot observe another job's interpreter -- that is the crack #8884
fell through (the detector library tests stayed green while the workflow was
broken in CI). So this ratchet asserts against the **workflow FILE**, not the
detector. Reverting any gate to the errexit-unsafe form turns this file red
instead of silently disarming the gate.

Auto-discovers EVERY ``*-gate.yml`` that captures a detector exit into a shell
variable (``out=$(python scripts/notebook_tools/...)``), so a gate added later
with the bug is caught here automatically -- render-suite or not.
"""

from __future__ import annotations

import pathlib

import pytest

_WF_DIR = (
    pathlib.Path(__file__).resolve().parents[3]
    / ".github"
    / "workflows"
)


def _detector_invocation(text: str) -> str | None:
    """Return the ``out=$(python scripts/notebook_tools/<x>.py ...)`` line, or None.

    The #8884 motif is specifically capturing a detector/ci-script exit into a
    shell variable then reading ``rc=$?``. Any ``scripts/notebook_tools`` script
    invoked this way is in scope (``detect_*.py`` detectors AND ``cell_order_ci``).
    """
    for line in text.splitlines():
        s = line.strip()
        if "out=$(" in s and "scripts/notebook_tools" in s and "python" in s:
            return s
    return None


def _detector_gates() -> list[pathlib.Path]:
    """Every ``*-gate.yml`` that has a detector-capture invocation."""
    found = []
    for wf in sorted(_WF_DIR.glob("*-gate.yml")):
        text = wf.read_text(encoding="utf-8")
        if _detector_invocation(text) is not None:
            found.append(wf)
    return found


_DETECTOR_GATES = _detector_gates()


@pytest.mark.parametrize("workflow", _DETECTOR_GATES, ids=lambda p: p.stem)
def test_detector_gate_invocation_is_errexit_safe(workflow: pathlib.Path):
    """Each detector gate must read the detector exit code under ``bash -e``.

    The ``out=$(...) && rc=0 || rc=$?`` form preserves the real exit code: a
    bare ``out=$(cmd)`` aborts the step on non-zero before ``rc=$?`` is read.
    """
    assert workflow.is_file(), f"detector gate missing: {workflow}"
    text = workflow.read_text(encoding="utf-8")
    invocation = _detector_invocation(text)
    assert invocation is not None, (
        f"{workflow.name}: expected an `out=$(python scripts/notebook_tools/...)` "
        "invocation"
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


def test_discovery_covers_all_known_detector_gates():
    """Guard against the discovery silently matching nothing (e.g. a rename).

    If this fails, either the glob/filter drifted or every detector gate was
    renamed -- the parametrize above would then run zero cases and look green
    for the wrong reason. The known set spans the render-suite (svg/degenerate,
    #8890) and the remaining detector gates fixed alongside this generalization.
    """
    stems = {p.stem for p in _DETECTOR_GATES}
    expected = {
        # render-suite (#8890 / #8886)
        "svg-decimal-comma-gate",
        "svg-empty-display-gate",
        "svg-broken-geometry-gate",
        "svg-offscreen-flat-gate",
        "degenerate-figure-gate",
        # remaining detector gates (this PR)
        "bare-cross-dir-load-gate",
        "manifest-description-visuelle-gate",
        "md-content-loss-gate",
        "cell-order-gate",
    }
    missing = expected - stems
    assert not missing, (
        f"detector-gate discovery no longer matches known gates: {sorted(missing)}; "
        "the parametrize would run fewer cases and could hide regressions"
    )
