"""Unit tests for ``mine_lean_sessions.py`` degenerate-input guards + happy-path.

Loads the module DIRECTLY by file path (mirrors ``test_lean_utils.py``,
``test_knowledge.py``, ``test_attempt_history.py``), bypassing
``prover/__init__.py`` which cascades the ``agent_framework`` LLM stack
absent on a bare CPU runner. The module is stdlib-only (``json``,
``logging``, ``re``, ``collections``, ``datetime``, ``pathlib``, ``typing``)
and loads cleanly.

These tests pin two things:

1. **Guards (#7596-pattern, G.9):** every public entry point that
   immediately calls a ``Path`` method (``.exists`` / ``.read_text`` /
   ``.write_text`` / ``.glob``) or iterates over a list-shaped argument
   rejects ``None`` / non-Path / non-list with a clear ``ValueError``
   naming the offending argument — converting the OPAQUE ``AttributeError``
   ("NoneType has no attribute 'exists'") / ``TypeError`` ("NoneType is
   not iterable") that an agent-generated ``None`` previously produced
   into a diagnosable message.

2. **Happy-path preservation:** the guards are pure defense-in-depth and
   must not change behavior for valid inputs (load_json on missing file,
   mine_attempt_history on empty dir, dedup on non-overlapping entries).

Run from ``agent_tests/``::

    python -m pytest tests/test_mine_lean_sessions.py -q

See #1453 (prover co-evolution epic), See #7477 (prover harness forensic).
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

_spec = importlib.util.spec_from_file_location(
    "prover_mine_lean_sessions_under_test",
    ROOT / "prover" / "mine_lean_sessions.py",
)
mls = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(mls)


# A reusable temp directory under pytest's tmp_path for happy-path tests.
@pytest.fixture
def empty_dir(tmp_path: Path) -> Path:
    d = tmp_path / "empty_mining"
    d.mkdir()
    return d


# ──────────────────────────────────────────────────────────────────────────
# Guards — Path parameters must reject None / non-Path with clear messages
# ──────────────────────────────────────────────────────────────────────────

class TestPathGuards:
    """Every Path-typed public entry point rejects None/non-Path inputs."""

    @pytest.mark.parametrize(
        "fn,argname",
        [
            (lambda p: mls.load_json(p), "path"),
            (lambda p: mls.save_json(p, {}), "path"),
            (lambda p: mls.mine_attempt_history(p), "history_dir"),
            (lambda p: mls.mine_trace_conversations(p), "traces_dir"),
        ],
    )
    def test_none_raises_value_error(self, fn, argname):
        with pytest.raises(ValueError, match=argname):
            fn(None)

    @pytest.mark.parametrize(
        "fn",
        [
            lambda p: mls.load_json(p),
            lambda p: mls.save_json(p, {}),
            lambda p: mls.mine_attempt_history(p),
            lambda p: mls.mine_trace_conversations(p),
        ],
    )
    def test_non_path_raises_value_error(self, fn):
        with pytest.raises(ValueError, match="pathlib.Path"):
            fn(123)  # type: ignore[arg-type]


# ──────────────────────────────────────────────────────────────────────────
# Guards — List parameters must reject None / non-list with clear messages
# ──────────────────────────────────────────────────────────────────────────

class TestListGuards:
    """Every list-typed public entry point rejects None/non-list inputs."""

    def test_dedup_cookbook_none_existing(self):
        with pytest.raises(ValueError, match="existing"):
            mls.dedup_cookbook(None, [])  # type: ignore[arg-type]

    def test_dedup_cookbook_none_new_entries(self):
        with pytest.raises(ValueError, match="new_entries"):
            mls.dedup_cookbook([], None)  # type: ignore[arg-type]

    def test_dedup_failures_none_existing(self):
        with pytest.raises(ValueError, match="existing"):
            mls.dedup_failures(None, [])  # type: ignore[arg-type]

    def test_dedup_failures_none_new_entries(self):
        with pytest.raises(ValueError, match="new_entries"):
            mls.dedup_failures([], None)  # type: ignore[arg-type]

    def test_extract_successful_patterns_none_successes(self):
        with pytest.raises(ValueError, match="successes"):
            mls._extract_successful_patterns(None, [])  # type: ignore[arg-type]

    def test_extract_successful_patterns_none_failures(self):
        with pytest.raises(ValueError, match="failures"):
            mls._extract_successful_patterns([], None)  # type: ignore[arg-type]

    @pytest.mark.parametrize(
        "bad_input",
        [("a", "b"), {"x": 1}, "string", 42],
    )
    def test_dedup_cookbook_non_list_existing(self, bad_input):
        with pytest.raises(ValueError, match="existing must be a list"):
            mls.dedup_cookbook(bad_input, [])  # type: ignore[arg-type]


# ──────────────────────────────────────────────────────────────────────────
# Guards — run_mining orchestrator
# ──────────────────────────────────────────────────────────────────────────

class TestRunMiningGuards:
    """``run_mining`` is the orchestrator and must guard all Path inputs + jsonl_dir."""

    def test_run_mining_none_history_dir(self, empty_dir):
        with pytest.raises(ValueError, match="history_dir"):
            mls.run_mining(None, empty_dir, empty_dir / "kb.json")

    def test_run_mining_none_traces_dir(self, empty_dir):
        with pytest.raises(ValueError, match="traces_dir"):
            mls.run_mining(empty_dir, None, empty_dir / "kb.json")

    def test_run_mining_none_kb_path(self, empty_dir):
        with pytest.raises(ValueError, match="kb_path"):
            mls.run_mining(empty_dir, empty_dir, None)

    def test_run_mining_jsonl_dir_must_be_path_or_none(self, empty_dir):
        # jsonl_dir is Optional[Path]; explicit non-Path non-None is rejected
        with pytest.raises(ValueError, match="jsonl_dir"):
            mls.run_mining(
                empty_dir, empty_dir, empty_dir / "kb.json", jsonl_dir="not_a_path"
            )


# ──────────────────────────────────────────────────────────────────────────
# Happy-path preservation — guards must not change valid-input behavior
# ──────────────────────────────────────────────────────────────────────────

class TestHappyPath:
    """Guards are pure defense-in-depth — valid inputs keep their behavior."""

    def test_load_json_missing_returns_default(self, empty_dir):
        assert mls.load_json(empty_dir / "does_not_exist.json", default={"k": 1}) == {"k": 1}

    def test_load_json_missing_no_default(self):
        assert mls.load_json(Path(r"C:\does\not\exist\xyz_abc.json")) is None

    def test_mine_attempt_history_empty_dir(self, empty_dir):
        succ, fail = mls.mine_attempt_history(empty_dir)
        assert succ == []
        assert fail == []

    def test_mine_trace_conversations_empty_dir(self, empty_dir):
        cookbook, failed, api = mls.mine_trace_conversations(empty_dir)
        assert cookbook == []
        assert failed == []
        assert api == []

    def test_dedup_cookbook_non_overlapping(self):
        existing = [{"name": "a", "tactic": "omega"}]
        new = [{"name": "b", "tactic": "linarith"}]
        merged = mls.dedup_cookbook(existing, new)
        assert len(merged) == 2

    def test_dedup_cookbook_overlapping_keeps_existing(self):
        existing = [{"name": "a", "tactic": "omega"}]
        new = [{"name": "a", "tactic": "omega"}, {"name": "b", "tactic": "linarith"}]
        merged = mls.dedup_cookbook(existing, new)
        # The duplicate (same name + tactic signature) is dropped
        assert len(merged) == 2
        names = {e["name"] for e in merged}
        assert names == {"a", "b"}

    def test_dedup_failures_non_overlapping(self):
        existing = [{"what_failed": "tactic a"}]
        new = [{"what_failed": "tactic b"}]
        merged = mls.dedup_failures(existing, new)
        assert len(merged) == 2

    def test_save_json_roundtrip(self, tmp_path):
        # save_json must still work on a valid Path (the guard is non-blocking
        # for valid input)
        out = tmp_path / "out.json"
        mls.save_json(out, {"a": [1, 2, 3]})
        assert mls.load_json(out) == {"a": [1, 2, 3]}

    def test_run_mining_dry_run_on_empty(self, tmp_path):
        # End-to-end on an empty workspace — should not crash
        kb = tmp_path / "kb.json"
        stats = mls.run_mining(
            history_dir=tmp_path,
            traces_dir=tmp_path,
            kb_path=kb,
            jsonl_dir=None,
            dry_run=True,
        )
        assert stats["history_files"] == 0
        assert stats["trace_files"] == 0
        assert stats["jsonl_files"] == 0


class TestStrGuards:
    """Boundary guards for text-processing helpers (`_require_str`).

    These functions take ``str`` args and pass them to ``re.finditer`` /
    ``str.split`` / ``str.startswith`` — without a guard, ``None``
    produces ``AttributeError: 'NoneType' object has no attribute
    'split'/'finditer'/'startswith'`` deep inside the loop.
    """

    @pytest.mark.parametrize("fn,argname", [
        (mls._extract_error_patterns, "content"),
        (mls._classify_errors, "text"),
        (mls._extract_tactic_blocks, "text"),
    ])
    def test_none_raises_value_error(self, fn, argname):
        with pytest.raises(ValueError, match=argname):
            fn(None)

    @pytest.mark.parametrize("fn,bad_input", [
        (mls._extract_error_patterns, 123),
        (mls._extract_error_patterns, ["line"]),
        (mls._classify_errors, {"k": "v"}),
        (mls._extract_tactic_blocks, (1, 2)),
    ])
    def test_non_str_raises_value_error(self, fn, bad_input):
        with pytest.raises(ValueError, match="expected str"):
            fn(bad_input)

    @pytest.mark.parametrize("fn", [
        mls._extract_error_patterns,
        mls._classify_errors,
        mls._extract_tactic_blocks,
    ])
    def test_empty_str_raises_value_error(self, fn):
        with pytest.raises(ValueError, match="expected non-empty str"):
            fn("")


class TestExtractFailureLessonsGuard:
    """`_extract_failure_lessons` was missing from the #7596 tranche.

    Without `_require_list`, ``None`` produces ``TypeError: 'NoneType'
    object is not iterable`` deep inside ``Counter()`` / the loop.
    """

    def test_none_raises_value_error(self):
        with pytest.raises(ValueError, match="failures"):
            mls._extract_failure_lessons(None)

    def test_non_list_raises_value_error(self):
        with pytest.raises(ValueError, match="must be a list|expected list"):
            mls._extract_failure_lessons({"k": "v"})

    def test_empty_list_returns_empty(self):
        assert mls._extract_failure_lessons([]) == []