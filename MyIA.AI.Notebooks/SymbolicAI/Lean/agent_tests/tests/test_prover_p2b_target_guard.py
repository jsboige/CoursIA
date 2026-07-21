"""Unit tests for #7477 P2b — launcher target-line guard.

The launcher reads ``demo['line']`` (an INT) and aims the whole run at it.
DEMO descriptions also embed two human-authored markers that ``line`` can
drift away from after edits shift line numbers:

  - ``"CURRENT TARGET = ... L<N>"``  -> the intended target line
  - ``"DO NOT TARGET <token>"``      -> regions/lines to avoid

Founding forensic (DEMO 62): a baseline run burned its whole remaining budget
on a DO-NOT-TARGET line (NW L2970) while the description said CURRENT TARGET =
ne (L2973). #6871 re-pointed the ``line`` field nw->ne by hand, but nothing
prevented the stale-``line`` class of bug from recurring.

``run_prover_bg._resolve_target_line`` is the guard: it parses the markers and
returns ``(resolved_line, warnings)``. Conservative contract exercised here:

  * no marker        -> line unchanged, no warning (no-op on clean DEMOs)
  * AGREE            -> line unchanged, no warning
  * single DISAGREE  -> redirect to CURRENT TARGET line + warning
  * ambiguous parse  -> line unchanged + warning (do not guess)
  * DO NOT TARGET    -> informational warning (region name, not acted on)

Run from ``agent_tests/``::

    python -m pytest tests/test_prover_p2b_target_guard.py -q
"""

from __future__ import annotations

import sys
from pathlib import Path

# Make `prover/` importable regardless of how pytest was invoked (same
# bootstrap convention as tests/test_prover_correctly_refused.py).
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

from prover import run_prover_bg  # noqa: E402


# ──────────────────────────────────────────────────────────────────────────
# _resolve_target_line — the P2b reconciliation contract
# ──────────────────────────────────────────────────────────────────────────


def _resolve(demo, line):
    """Thin wrapper so each test reads as the verdict for one scenario."""
    return run_prover_bg._resolve_target_line(demo, line)


# --- no marker: total no-op (the guard must not perturb clean DEMOs) ------


def test_no_description_is_noop():
    """A DEMO without a description field leaves the line untouched."""
    resolved, warnings = _resolve({"name": "X"}, line=500)
    assert resolved == 500
    assert warnings == []


def test_empty_description_is_noop():
    """An empty description leaves the line untouched."""
    resolved, warnings = _resolve({"description": ""}, line=500)
    assert resolved == 500
    assert warnings == []


def test_description_without_markers_is_noop():
    """A description with neither CURRENT TARGET nor DO NOT TARGET is a no-op."""
    resolved, warnings = _resolve(
        {"description": "Prove foo. The sorry is at L446. Use div_le_iff."},
        line=446,
    )
    assert resolved == 446
    assert warnings == []


# --- AGREE: line field already matches the description intent ------------


def test_current_target_agrees_no_redirect():
    """When the line field already equals the CURRENT TARGET line, no redirect
    and no warning. (This is DEMO 62 today: line=2973, CURRENT TARGET=ne L2973.)"""
    demo = {
        "line": 2973,
        "description": "NW STATUS - DO NOT TARGET NW. CURRENT TARGET = ne quadrant (L2973): prove.",
    }
    resolved, warnings = _resolve(demo, line=2973)
    assert resolved == 2973
    # DO NOT TARGET NW is still surfaced (informational), but no disagreement.
    assert any("DO NOT TARGET" in w for w in warnings)
    assert not any("redirecting" in w for w in warnings)


# --- single DISAGREE: redirect to the description's CURRENT TARGET -------


def test_current_target_disagreement_redirects():
    """A stale line field that disagrees with a single CURRENT TARGET line is
    redirected, with a warning citing both numbers. This is the founding
    forensic class: description moved on, the INT field did not."""
    demo = {
        "line": 2970,  # stale (was nw, before #6871 re-pointed)
        "description": "CURRENT TARGET = ne quadrant (L2973): from hypothesis.",
    }
    resolved, warnings = _resolve(demo, line=2970)
    assert resolved == 2973
    assert len(warnings) == 1
    assert "2973" in warnings[0] and "2970" in warnings[0]
    assert "redirecting" in warnings[0]


def test_current_target_does_not_infer_missing_line():
    """A DEMO whose `line` field is None is left None even when the
    description states a CURRENT TARGET. The guard's contract is to reconcile
    a *disagreement* (a stale INT field), not to infer a missing one — a
    multi-sorry agent-driven DEMO may legitimately omit `line`, and silently
    pinning it from the description could mask a config error or mis-target
    the run. None cannot disagree, so there is nothing to reconcile."""
    demo = {"description": "CURRENT TARGET = se quadrant (L2977): prove."}
    resolved, warnings = _resolve(demo, line=None)
    assert resolved is None  # not inferred
    assert warnings == []    # no disagreement to warn about


# --- ambiguous parse: do not guess ---------------------------------------


def test_multiple_current_target_lines_does_not_redirect():
    """When the description carries more than one CURRENT TARGET line number,
    the guard refuses to guess — line unchanged, ambiguity surfaced."""
    demo = {
        "line": 2973,
        "description": (
            "CURRENT TARGET = ne quadrant (L2973): prove. "
            "Earlier we had CURRENT TARGET = nw (L2970) but that is factored."
        ),
    }
    resolved, warnings = _resolve(demo, line=2973)
    assert resolved == 2973  # unchanged
    assert any("ambiguous" in w for w in warnings)


# --- DO NOT TARGET: informational only -----------------------------------


def test_do_not_target_token_stripped_clean():
    """The DO NOT TARGET token is captured without trailing punctuation
    (region name only), so the warning reads cleanly."""
    demo = {
        "line": 2973,
        "description": "NW STATUS - DO NOT TARGET NW: factored. No CURRENT TARGET marker.",
    }
    resolved, warnings = _resolve(demo, line=2973)
    assert resolved == 2973
    dnt = [w for w in warnings if "DO NOT TARGET" in w]
    assert len(dnt) == 1
    assert "NW" in dnt[0]
    assert "NW:" not in dnt[0]  # trailing colon stripped, not captured


def test_do_not_target_line_label_informative():
    """A 'DO NOT TARGET L2970' style marker is surfaced as information; the
    guard does not map it to the line field (the association is too fragile),
    so a line that happens to equal it is NOT auto-redirected on that basis
    alone."""
    demo = {
        "line": 2970,
        "description": "DO NOT TARGET L2970 (factored into a private lemma).",
    }
    resolved, warnings = _resolve(demo, line=2970)
    assert resolved == 2970  # no CURRENT TARGET -> no redirect basis
    assert any("DO NOT TARGET" in w for w in warnings)
