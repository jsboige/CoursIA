"""Tests for #24545: the ``proof_latched`` latch must not survive a second sorry.

The defect (#24545, point 1): ``VerifyExecutor`` latches
``tactic_tools.proof_latched = True`` after a verified, persisted proof, and
nothing ever reset it. A session that proved sorry A and then worked on
sorry B therefore reported ``proof_found=True`` for the whole session once the
supervisor's reasoning deadline fired during B -- while B was still ``sorry``
on disk.

The defect (#24545, point 2): ``_deadline_keeps_latched_proof`` promised a
policy decision but reduced to ``bool(getattr(tactic_tools, "proof_latched",
False))`` -- it had no access to the sorry it was about to report.

The fix binds the latch to the sorry it proves (``proof_latched_for_line``),
drops it when the session moves on to another sorry, and makes the deadline
branch DECIDE against the file: the latched line must hold no ``sorry`` now,
and the real-sorry count must be strictly below the session baseline.

Offline: the verifier is mocked, no lake.
"""

import asyncio
from types import SimpleNamespace
from unittest.mock import AsyncMock

from prover.provers import _deadline_keeps_latched_proof
from prover.state import SorryContext

# Two real sorrys, far enough apart that the P5 relocation (30 lines) cannot
# confuse them.
TWO_SORRY_SRC = (
    "theorem first : 1 + 1 = 2 := by sorry\n"
    "\n"
    "theorem second (n : Nat) : 0 + n = n := by sorry\n"
)


def _tools(filepath=None, latched_line=None, baseline=None):
    """A TacticTools-shaped double exposing exactly what the deadline branch
    reads: the latch flag, its target line, the file, the session baseline."""
    tools = SimpleNamespace(
        proof_latched=False,
        proof_latched_for_line=None,
        _filepath=filepath,
        _original_sorry_count=baseline,
        reset_stagnation=lambda: None,
    )

    def _latch_proof(line):
        tools.proof_latched = True
        tools.proof_latched_for_line = int(line)

    tools.latch_proof = _latch_proof
    if latched_line is not None:
        _latch_proof(latched_line)
    return tools


def _run(executor, msg):
    ctx = AsyncMock()
    ctx.yield_output = AsyncMock()
    ctx.send_message = AsyncMock()
    asyncio.run(executor.handle(msg, ctx))
    return ctx


def _kb(tmp_path):
    from prover.knowledge import ProofKnowledgeBase
    return ProofKnowledgeBase(path=tmp_path / "kb.json")


# ── the deadline branch now DECIDES ────────────────────────────────────────

def test_deadline_helper_drops_a_latch_without_a_target():
    """A latch that names no sorry cannot be checked against the file: the
    deadline must not report a proof it cannot locate."""
    tools = _tools(filepath="whatever.lean")
    tools.proof_latched = True
    tools.proof_latched_for_line = None
    assert _deadline_keeps_latched_proof(tools) is False


def test_deadline_helper_drops_a_latch_whose_sorry_is_still_on_disk(tmp_path):
    """The latched line still holds a ``sorry``: the proof did not survive."""
    f = tmp_path / "T.lean"
    f.write_text(TWO_SORRY_SRC, encoding="utf-8")
    tools = _tools(filepath=str(f), latched_line=1, baseline=2)
    # line 1 still holds "sorry" -> the latch is void
    assert _deadline_keeps_latched_proof(tools) is False


def test_deadline_helper_keeps_a_latch_whose_sorry_is_gone(tmp_path):
    """The latched line is clear AND the sorry count dropped below the
    session baseline: the proof survived, the deadline may keep it."""
    f = tmp_path / "T.lean"
    f.write_text(
        "theorem first : 1 + 1 = 2 := by rfl\n"
        "\n"
        "theorem second (n : Nat) : 0 + n = n := by sorry\n",
        encoding="utf-8",
    )
    tools = _tools(filepath=str(f), latched_line=1, baseline=2)
    assert _deadline_keeps_latched_proof(tools) is True


def test_deadline_helper_drops_a_latch_when_the_count_did_not_drop(tmp_path):
    """The latched line is clear but the sorry COUNT is unchanged: the lines
    merely shifted, nothing was proved -- the same oracle the in-place latch
    uses (workflow.py:1249)."""
    f = tmp_path / "T.lean"
    f.write_text(
        "theorem first : 1 + 1 = 2 := by\n"
        "  rfl\n"
        "\n"
        "theorem second (n : Nat) : 0 + n = n := by sorry\n"
        "theorem third : True := by sorry\n",
        encoding="utf-8",
    )
    # baseline 2, on disk 2 sorries -> count did not drop
    tools = _tools(filepath=str(f), latched_line=1, baseline=2)
    assert _deadline_keeps_latched_proof(tools) is False


def test_deadline_helper_drops_a_latch_when_the_file_is_unreadable(tmp_path):
    tools = _tools(filepath=str(tmp_path / "absent.lean"),
                   latched_line=1, baseline=2)
    assert _deadline_keeps_latched_proof(tools) is False


# ── the latch does not survive a second sorry ──────────────────────────────

def test_second_sorry_edit_drops_the_latch(tmp_path):
    """THE #24545 SCENARIO: sorry A proved (latch taken), the session then
    works on sorry B. The latch must be dropped, so the deadline branch
    reports the honest outcome for B (still `sorry` on disk)."""
    from prover.state import ProofState
    from prover.tools import TacticTools

    f = tmp_path / "T.lean"
    f.write_text(TWO_SORRY_SRC, encoding="utf-8")
    sctx = SorryContext(filepath=str(f), sorry_line=1, indentation=0,
                        indent_str="", full_file=TWO_SORRY_SRC,
                        goal_state="1 + 1 = 2")
    tt = TacticTools(ProofState(theorem_statement="first"), str(f), sctx)
    tt._original_sorry_count = 2

    # sorry A is proved and latched
    tt.latch_proof(1)
    assert tt.proof_latched is True
    assert tt.proof_latched_for_line == 1

    # the session moves on to sorry B (line 3)
    tt.note_edit_target(3)

    assert tt.proof_latched is False, (
        "the latch must not survive the move to another sorry (#24545)")
    assert tt.proof_latched_for_line is None
    assert _deadline_keeps_latched_proof(tt) is False


def test_an_edit_on_the_latched_line_keeps_the_latch(tmp_path):
    """The continuation of the very same proof keeps the latch."""
    from prover.state import ProofState
    from prover.tools import TacticTools

    f = tmp_path / "T.lean"
    f.write_text(TWO_SORRY_SRC, encoding="utf-8")
    sctx = SorryContext(filepath=str(f), sorry_line=1, indentation=0,
                        indent_str="", full_file=TWO_SORRY_SRC)
    tt = TacticTools(ProofState(theorem_statement="first"), str(f), sctx)
    tt._original_sorry_count = 2
    tt.latch_proof(1)

    tt.note_edit_target(1)

    assert tt.proof_latched is True
    assert tt.proof_latched_for_line == 1


def test_latch_is_bound_to_the_line_it_proves(tmp_path):
    from prover.state import ProofState
    from prover.tools import TacticTools

    f = tmp_path / "T.lean"
    f.write_text(TWO_SORRY_SRC, encoding="utf-8")
    sctx = SorryContext(filepath=str(f), sorry_line=1, indentation=0,
                        indent_str="", full_file=TWO_SORRY_SRC)
    tt = TacticTools(ProofState(theorem_statement="first"), str(f), sctx)
    assert tt.proof_latched is False
    assert tt.proof_latched_for_line is None

    tt.latch_proof(3)
    assert tt.proof_latched is True
    assert tt.proof_latched_for_line == 3

    tt.clear_proof_latch()
    assert tt.proof_latched is False
    assert tt.proof_latched_for_line is None


# ── the verify path binds the latch to the RESOLVED line ───────────────────

def test_verify_success_latches_the_resolved_line(tmp_path, monkeypatch):
    """The P5 relocation inside ``verify_sorry_replacement`` may prove a
    DIFFERENT sorry than the frozen target: the latch must name the line the
    proof actually landed on."""
    import prover.lean_utils as lu
    from prover.workflow import ProofMessage, VerifyExecutor

    src = TWO_SORRY_SRC
    f = tmp_path / "T.lean"
    f.write_text(src, encoding="utf-8")
    monkeypatch.setattr(
        lu, "verify_sorry_replacement",
        lambda **k: {"success": True, "persisted": True, "real_build_ok": True,
                     "resolved_sorry_line": 3},
    )
    sctx = SorryContext(filepath=str(f), sorry_line=1, indentation=0,
                        indent_str="", full_file=src, goal_state="1 + 1 = 2")
    tools = _tools()
    ex = VerifyExecutor(sorry_context=sctx, imports="", tactic_tools=tools,
                        kb=_kb(tmp_path))
    msg = ProofMessage(content="x", tactic="exact Nat.zero_add n", sorry_count=2)
    _run(ex, msg)

    assert msg.proof_found is True
    assert tools.proof_latched is True
    assert tools.proof_latched_for_line == 3, (
        "the latch must name the line the proof landed on, not the frozen "
        "target (#24545)")


def test_verify_failure_does_not_latch(tmp_path, monkeypatch):
    import prover.lean_utils as lu
    from prover.workflow import ProofMessage, VerifyExecutor

    src = TWO_SORRY_SRC
    f = tmp_path / "T.lean"
    f.write_text(src, encoding="utf-8")
    monkeypatch.setattr(
        lu, "verify_sorry_replacement",
        lambda **k: {"success": False, "errors": "type mismatch"},
    )
    sctx = SorryContext(filepath=str(f), sorry_line=1, indentation=0,
                        indent_str="", full_file=src, goal_state="1 + 1 = 2")
    tools = _tools()
    ex = VerifyExecutor(sorry_context=sctx, imports="", tactic_tools=tools,
                        kb=_kb(tmp_path))
    msg = ProofMessage(content="x", tactic="rfl", sorry_count=2)
    _run(ex, msg)

    assert not msg.proof_found
    assert tools.proof_latched is False
    assert tools.proof_latched_for_line is None
