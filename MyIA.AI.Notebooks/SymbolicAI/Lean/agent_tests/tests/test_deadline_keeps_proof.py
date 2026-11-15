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


def _tools():
    return SimpleNamespace(proof_latched=False, reset_stagnation=lambda: None)


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


def test_deadline_helper_keeps_a_latched_proof():
    tools = _tools()
    tools.proof_latched = True
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
