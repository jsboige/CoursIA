"""Tests for #24469 (second defect): a verified proof survives the deadline.

Smoke ``zero_add_smoke`` (2026-11-03, after the inline-sorry splice fix):
VerifyExecutor logged ``PROOF FOUND: exact Nat.zero_add n`` with
``persisted=True real_build_ok=True``, then a TacticAgent compile kept the
workflow alive 22 s more; the supervisor's reasoning deadline fired at its next
poll, cancelled the workflow and reset ``proof_found`` -> RESULT FAILED with
sorry 1 -> 0 on disk. VerifyExecutor now latches ``tactic_tools.proof_latched``
and the deadline branch keeps it. Offline: verifier mocked, no lake.
"""

import asyncio
from types import SimpleNamespace
from unittest.mock import AsyncMock

from prover.provers import _deadline_keeps_latched_proof
from prover.state import SorryContext


def _tools(filepath=None, baseline=None):
    """A TacticTools-shaped double.

    #24545 changed the latch contract: it is now BOUND to the sorry it
    proved (``proof_latched_for_line``), and the deadline branch decides
    against the FILE (the latched line must hold no ``sorry`` and the
    real-sorry count must be below the session baseline). This double
    mirrors that contract so the assertions below keep their meaning; the
    multi-sorry behaviour itself is covered by
    ``test_proof_latch_multisorry.py``.
    """
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
    return tools


def _kb(tmp_path):
    # An isolated KB: the default one is the committed proof_knowledge.json,
    # which a passing verify would otherwise write into.
    from prover.knowledge import ProofKnowledgeBase
    return ProofKnowledgeBase(path=tmp_path / "kb.json")


def _run(executor, msg):
    ctx = AsyncMock()
    ctx.yield_output = AsyncMock()
    ctx.send_message = AsyncMock()
    asyncio.run(executor.handle(msg, ctx))
    return ctx


def test_deadline_helper_defaults_to_no_proof():
    assert _deadline_keeps_latched_proof(None) is False
    assert _deadline_keeps_latched_proof(SimpleNamespace()) is False
    assert _deadline_keeps_latched_proof(_tools()) is False


def test_real_tactic_tools_starts_unlatched(tmp_path):
    from prover.state import ProofState
    from prover.tools import TacticTools

    f = tmp_path / "T.lean"
    f.write_text("theorem t : True := by sorry\n", encoding="utf-8")
    sctx = SorryContext(filepath=str(f), sorry_line=1, indentation=0)
    tt = TacticTools(ProofState(theorem_statement="t"), str(f), sctx)
    assert tt.proof_latched is False
    assert _deadline_keeps_latched_proof(tt) is False


def test_deadline_helper_keeps_a_latched_proof(tmp_path):
    """#24545: the deadline branch DECIDES against the file. A latch is kept
    only when the sorry it names is gone from disk AND the sorry count
    dropped below the session baseline."""
    f = tmp_path / "T.lean"
    f.write_text("theorem t (n : Nat) : 0 + n = n := by sorry\n",
                 encoding="utf-8")
    tools = _tools(filepath=str(f), baseline=1)
    tools.latch_proof(1)
    # the sorry is still on disk -> the latch cannot be honoured
    assert _deadline_keeps_latched_proof(tools) is False

    f.write_text("theorem t (n : Nat) : 0 + n = n := by exact Nat.zero_add n\n",
                 encoding="utf-8")
    assert _deadline_keeps_latched_proof(tools) is True


def test_verify_success_latches_the_proof(tmp_path, monkeypatch):
    import prover.lean_utils as lu
    from prover.workflow import ProofMessage, VerifyExecutor

    src = "theorem t (n : Nat) : 0 + n = n := by sorry\n"
    f = tmp_path / "T.lean"
    f.write_text(src, encoding="utf-8")
    monkeypatch.setattr(
        lu, "verify_sorry_replacement",
        lambda **k: {"success": True, "persisted": True, "real_build_ok": True},
    )
    sctx = SorryContext(filepath=str(f), sorry_line=1, indentation=0,
                        indent_str="", full_file=src, goal_state="0 + n = n")
    tools = _tools()
    ex = VerifyExecutor(sorry_context=sctx, imports="", tactic_tools=tools,
                        kb=_kb(tmp_path))
    msg = ProofMessage(content="x", tactic="exact Nat.zero_add n", sorry_count=1)
    ctx = _run(ex, msg)

    assert msg.proof_found is True
    assert tools.proof_latched is True, "the deadline must be able to see the proof"
    assert tools.proof_latched_for_line == 1, (
        "the latch must name the sorry it proved (#24545)")
    ctx.yield_output.assert_awaited_once()


def test_failed_verify_does_not_latch(tmp_path, monkeypatch):
    import prover.lean_utils as lu
    from prover.workflow import ProofMessage, VerifyExecutor

    src = "theorem t (n : Nat) : 0 + n = n := by sorry\n"
    f = tmp_path / "T.lean"
    f.write_text(src, encoding="utf-8")
    monkeypatch.setattr(
        lu, "verify_sorry_replacement",
        lambda **k: {"success": False, "errors": "type mismatch"},
    )
    sctx = SorryContext(filepath=str(f), sorry_line=1, indentation=0,
                        indent_str="", full_file=src, goal_state="0 + n = n")
    tools = _tools()
    ex = VerifyExecutor(sorry_context=sctx, imports="", tactic_tools=tools,
                        kb=_kb(tmp_path))
    msg = ProofMessage(content="x", tactic="rfl", sorry_count=1)
    _run(ex, msg)

    assert not msg.proof_found
    assert tools.proof_latched is False
