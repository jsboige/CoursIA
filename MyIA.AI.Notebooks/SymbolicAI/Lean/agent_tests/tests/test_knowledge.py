"""Unit tests for prover ``knowledge.py`` degenerate-input guards + happy-path.

Loads ``knowledge.py`` DIRECTLY by file path, bypassing ``prover/__init__.py``
(which cascades the ``agent_framework`` LLM stack, absent on a bare CPU runner).
The module's top level is stdlib-only (``json`` / ``pathlib`` / ``typing`` /
``datetime``), so it loads cleanly anywhere. Mirrors
``tests/test_lean_utils.py``'s file-path load.

These tests pin two things:
  1. **Guards (#7596-pattern, G.9):** every public ``goal`` / ``tactic`` /
     ``name`` entry point rejects ``None`` / non-str / empty with a clear
     ``ValueError`` naming the offending argument — converting the OPAQUE
     ``AttributeError`` ("NoneType has no attribute 'strip'" / "'lower'") that
     an agent-generated None goal/tactic/name (LLM call failed, missing field
     in JSON response, extraction regex returned None) previously produced
     into a diagnosable message. ``goal_signature`` is STATIC and its guard
     also covers the cascade entry points ``lookup`` / ``search_similar`` /
     ``record_success`` (all compute the signature first).
  2. **Happy-path preservation:** the guard is pure defense-in-depth and must
     not change behavior for valid inputs (signature normalization, cookbook
     keyword overlap, failed-approach matching, API substring lookup,
     record/lookup roundtrip).

Reproduced firsthand 9 opaque crashes pre-guard (probe_knowledge.py):
  goal_signature(None/int), cookbook_for_goal(None/int),
  check_avoided(None/int), api_lookup(None), lookup(None),
  search_similar(None) — all AttributeError on .strip/.lower.

Run from ``agent_tests/``:
    python -m pytest tests/test_knowledge.py -q

See #1453 (prover co-evolution epic), See #7477 (prover harness forensic).
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

_spec = importlib.util.spec_from_file_location(
    "prover_knowledge_under_test",
    ROOT / "prover" / "knowledge.py",
)
kb = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(kb)


# ──────────────────────────────────────────────────────────────────────────
# Fixtures: a KB backed by a temp JSON file (never touches the real
# proof_knowledge.json shipped in prover/).
# ──────────────────────────────────────────────────────────────────────────


def _make_kb(tmp_path: Path, *, populate_v3: bool = False) -> "kb.ProofKnowledgeBase":
    """Instantiate a KB on an isolated temp file; optionally seed v3 sections."""
    path = tmp_path / "kb_test.json"
    instance = kb.ProofKnowledgeBase(path=path)
    if populate_v3:
        # Direct structural population (bypasses record_success, which targets
        # the legacy `entries` section — cookbook/failed/mathlib are v3-only).
        instance._data["tactic_cookbook"] = {
            "patterns": [
                {
                    "name": "Fin monoid membership",
                    "category": "type-class",
                    "when": "goal mentions Fin monoid membership",
                    "tactic": "infer_instance",
                },
                {
                    "name": "decidable equality",
                    "category": "decidability",
                    "when": "decidable equality proposition",
                    "tactic": "decide",
                },
            ]
        }
        instance._data["failed_approaches"] = [
            {
                "what_failed": "brute force induction on structure",
                "why": "explodes case count",
                "lesson": "use generalization first",
            }
        ]
        instance._data["mathlib_api"] = {
            "Fin.monoid": "Fin carries a monoid instance under wedge",
            "Nat.rec": "recursor for natural-number induction",
        }
    return instance


@pytest.fixture
def kbx(tmp_path):
    """Empty KB (legacy entries section only)."""
    return _make_kb(tmp_path)


@pytest.fixture
def kbx_v3(tmp_path):
    """KB seeded with cookbook + failed_approaches + mathlib_api (v3)."""
    return _make_kb(tmp_path, populate_v3=True)


# ──────────────────────────────────────────────────────────────────────────
# Happy-path preservation (guards must not change valid-input behavior).
# ──────────────────────────────────────────────────────────────────────────


class TestGoalSignature:
    def test_strips_turnstile_prefix(self):
        assert kb.ProofKnowledgeBase.goal_signature("⊢ n = n") == "n = n"

    def test_strips_pipe_prefix(self):
        assert kb.ProofKnowledgeBase.goal_signature("| n = n") == "n = n"

    def test_lowercases(self):
        assert kb.ProofKnowledgeBase.goal_signature("Foo Bar") == "foo bar"

    def test_truncates_to_200(self):
        sig = kb.ProofKnowledgeBase.goal_signature("x" * 500)
        assert len(sig) == 200

    def test_normal_goal_is_idempotent_lowercase(self):
        assert kb.ProofKnowledgeBase.goal_signature("n = n") == "n = n"


class TestCookbookForGoal:
    def test_returns_patterns_with_overlap(self, kbx_v3):
        # "fin monoid" overlaps >=2 words with pattern "Fin monoid membership"
        result = kbx_v3.cookbook_for_goal("Fin monoid membership goal")
        assert len(result) == 1
        assert result[0]["name"] == "Fin monoid membership"

    def test_returns_empty_when_no_overlap(self, kbx_v3):
        # "totally unrelated keywords here" overlaps <2 with any pattern
        assert kbx_v3.cookbook_for_goal("zzz unrelated keyword") == []

    def test_returns_empty_on_empty_cookbook(self, kbx):
        assert kbx.cookbook_for_goal("Fin monoid") == []

    def test_capped_at_five(self, tmp_path):
        path = tmp_path / "kb_many.json"
        instance = kb.ProofKnowledgeBase(path=path)
        instance._data["tactic_cookbook"] = {
            "patterns": [
                {
                    "name": f"pattern {i}",
                    "category": "cat",
                    "when": "shared keyword goal",
                    "tactic": "tac",
                }
                for i in range(10)
            ]
        }
        result = instance.cookbook_for_goal("shared keyword goal")
        assert len(result) <= 5


class TestCheckAvoided:
    def test_matches_failed_approach_keyword(self, kbx_v3):
        # "induction" appears in "brute force induction on structure" (len>4)
        result = kbx_v3.check_avoided("induction on structure")
        assert result is not None
        assert "induction" in result["what_failed"]

    def test_returns_none_when_no_match(self, kbx_v3):
        assert kbx_v3.check_avoided("simp") is None

    def test_short_keywords_ignored(self, kbx_v3):
        # keyword len<=4 should not match (guard against noise words)
        # "the" is in the failed-approach text but len<=4
        assert kbx_v3.check_avoided("the quick approach") is None


class TestApiLookup:
    def test_substring_match_name_in_key(self, kbx_v3):
        result = kbx_v3.api_lookup("Fin")
        assert result is not None
        assert "monoid" in result

    def test_substring_match_key_in_name(self, kbx_v3):
        result = kbx_v3.api_lookup("Nat.recursor")
        assert result is not None
        assert "recursor" in result

    def test_returns_none_when_no_match(self, kbx_v3):
        assert kbx_v3.api_lookup("ZZZnotpresent") is None


class TestRecordLookupSearchSimilar:
    def test_record_and_lookup_roundtrip(self, kbx):
        kbx.record_success("n = n", tactic="rfl", theorem="eq_self")
        result = kbx.lookup("n = n")
        assert result is not None
        assert result["tactic"] == "rfl"
        assert result["theorem"] == "eq_self"
        assert result["uses"] == 1

    def test_record_increments_uses_on_repeat(self, kbx):
        kbx.record_success("n = n", tactic="rfl")
        kbx.record_success("n = n", tactic="rfl")
        result = kbx.lookup("n = n")
        assert result["uses"] == 2

    def test_search_similar_finds_overlap(self, kbx):
        kbx.record_success("forall n : Nat, n = n", tactic="rfl")
        kbx.record_success("forall m : Nat, m = m", tactic="rfl")
        # Same-shape goals share >=3 keywords after signature normalization
        result = kbx.search_similar("forall k : Nat, k = k")
        assert len(result) >= 1
        assert all("goal_signature" in r for r in result)

    def test_search_similar_empty_when_no_overlap(self, kbx):
        kbx.record_success("forall n : Nat, n = n", tactic="rfl")
        # Disjoint keywords
        assert kbx.search_similar("zzz unrelated keyword here") == []


# ──────────────────────────────────────────────────────────────────────────
# Guards: degenerate inputs raise ValueError naming the arg (NOT opaque
# AttributeError). Pinned firsthand via probe_knowledge.py.
# ──────────────────────────────────────────────────────────────────────────


class TestGoalSignatureGuards:
    @pytest.mark.parametrize("bad", [None, 123, 4.5, ["a"], {"x": 1}])
    def test_rejects_non_str(self, bad):
        with pytest.raises(ValueError, match="goal"):
            kb.ProofKnowledgeBase.goal_signature(bad)

    def test_rejects_empty(self):
        with pytest.raises(ValueError, match="goal"):
            kb.ProofKnowledgeBase.goal_signature("")


class TestCookbookForGoalGuards:
    @pytest.mark.parametrize("bad", [None, 123, ["a"]])
    def test_rejects_non_str(self, kbx, bad):
        with pytest.raises(ValueError, match="goal"):
            kbx.cookbook_for_goal(bad)

    def test_rejects_empty(self, kbx):
        with pytest.raises(ValueError, match="goal"):
            kbx.cookbook_for_goal("")


class TestCheckAvoidedGuards:
    @pytest.mark.parametrize("bad", [None, 123, ["a"]])
    def test_rejects_non_str(self, kbx, bad):
        with pytest.raises(ValueError, match="tactic"):
            kbx.check_avoided(bad)

    def test_rejects_empty(self, kbx):
        with pytest.raises(ValueError, match="tactic"):
            kbx.check_avoided("")


class TestApiLookupGuards:
    @pytest.mark.parametrize("bad", [None, 123, ["a"]])
    def test_rejects_non_str(self, kbx, bad):
        with pytest.raises(ValueError, match="name"):
            kbx.api_lookup(bad)

    def test_rejects_empty(self, kbx):
        with pytest.raises(ValueError, match="name"):
            kbx.api_lookup("")


class TestCascadeGuardsViaGoalSignature:
    """lookup / search_similar / record_success all compute goal_signature
    first — guarding the STATIC goal_signature covers these cascade paths."""

    def test_lookup_rejects_none(self, kbx):
        with pytest.raises(ValueError, match="goal"):
            kbx.lookup(None)

    def test_search_similar_rejects_none(self, kbx):
        with pytest.raises(ValueError, match="goal"):
            kbx.search_similar(None)

    def test_record_success_rejects_none_goal(self, kbx):
        with pytest.raises(ValueError, match="goal"):
            kbx.record_success(None, tactic="rfl")
