"""Unit tests for the launcher DO-NOT-TARGET guard (#7477 P2b, child of #1453).

Covers the two acceptance criteria from the forensic dispatch:
  1. The launcher rejects (or redirects+logs) a target line that falls in a
     region the DEMO description marks ``DO NOT TARGET`` — before launching.
  2. A target outside the region passes.

Pure-stdlib module (``re`` only), loaded self-contained via importlib — no
prover runtime / agent_framework needed.
"""

import importlib.util
from pathlib import Path

import pytest

_DIR = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("target_guard", _DIR / "target_guard.py")
target_guard = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(target_guard)

parse_do_not_target_lines = target_guard.parse_do_not_target_lines
resolve_target_line = target_guard.resolve_target_line
DO_NOT_TARGET_EXIT = target_guard.DO_NOT_TARGET_EXIT


# Faithful excerpt of DEMO 62's description body (config.py), the founder
# case: a quadrant->line map + a DO NOT TARGET NW declaration + a CURRENT
# TARGET. L2970 (NW) is forbidden; L2973 (NE) is the current target.
DEMO_62_DESCRIPTION = (
    "BG-prover target: the p4_succ_membership decomposition = 5 named "
    "sub-sorries. Post-#6869 line numbers: 4 mp quadrant cases "
    "(nw L2970, ne L2973, sw L2975, se L2977) + 1 mpr routing case (L2982).\n"
    "NW STATUS — DO NOT TARGET NW: steps 3-5 are FACTORED as the "
    "sorry-free private theorem p4_nw_shift_lemma (L2846). The nw residual "
    "sorry (L2970) = the G3 bridge consumption, handled on the po-2026 "
    "manual track.\n"
    "CURRENT TARGET = ne quadrant (L2973): prove the RHS membership "
    "disjunct. When the ne case is proved, re-point to sw (L2975), se "
    "(L2977), then mpr (L2982)."
)


# ══════════════════════════════════════════════════════════════════════
# parse_do_not_target_lines
# ══════════════════════════════════════════════════════════════════════

class TestParseDoNotTargetLines:
    def test_demo62_finds_nw_forbidden_line(self):
        # The founder case: NW is marked DO NOT TARGET; NW maps to L2970.
        assert parse_do_not_target_lines(DEMO_62_DESCRIPTION) == {2970}

    def test_demo62_does_not_collect_current_target_or_siblings(self):
        forbidden = parse_do_not_target_lines(DEMO_62_DESCRIPTION)
        # NE (current target), SW, SE, MPR are NOT forbidden — only NW.
        assert 2973 not in forbidden
        assert 2975 not in forbidden
        assert 2977 not in forbidden
        assert 2982 not in forbidden

    def test_demo62_does_not_collect_factored_lemma_line(self):
        # L2846 (the factored lemma location, mentioned in the DO NOT TARGET
        # NW block) is NOT a target locus — it must not be flagged. This is
        # the precision guard against over-collecting from the prose block.
        forbidden = parse_do_not_target_lines(DEMO_62_DESCRIPTION)
        assert 2846 not in forbidden

    def test_direct_form_do_not_target_l(self):
        # A DEMO that names the forbidden line inline (no quadrant map).
        desc = "The sorry at DO NOT TARGET L1234 was already discharged."
        assert parse_do_not_target_lines(desc) == {1234}

    def test_region_form_multiple_forbidden(self):
        desc = (
            "cases (nw L10, ne L20, sw L30). "
            "DO NOT TARGET nw. DO NOT TARGET sw."
        )
        assert parse_do_not_target_lines(desc) == {10, 30}

    def test_quadrant_map_without_do_not_target_marker_forbids_nothing(self):
        # A quadrant->line map alone declares loci but forbids none.
        desc = "cases (nw L10, ne L20). No restriction declared."
        assert parse_do_not_target_lines(desc) == set()

    def test_empty_or_none_description(self):
        assert parse_do_not_target_lines("") == set()
        assert parse_do_not_target_lines(None) == set()

    def test_case_insensitive_marker(self):
        # The direct form is matched case-insensitively (lowercase marker).
        desc = "do not target L500."
        assert parse_do_not_target_lines(desc) == {500}


# ══════════════════════════════════════════════════════════════════════
# resolve_target_line
# ══════════════════════════════════════════════════════════════════════

def _demo62():
    """A DEMO 62-shaped dict for resolve_target_line tests."""
    return {"line": 2973, "description": DEMO_62_DESCRIPTION}


class TestResolveTargetLine:
    def test_demo62_default_line_is_ok(self):
        # The DEMO's own CURRENT TARGET (NE L2973) is allowed.
        line, status = resolve_target_line(_demo62())
        assert status == "ok"
        assert line == 2973

    def test_demo62_override_to_current_target_ok(self):
        line, status = resolve_target_line(_demo62(), override=2973)
        assert status == "ok"
        assert line == 2973

    def test_demo62_override_into_forbidden_redirects(self):
        # Founder case: baseline aimed NW L2970 (forbidden) -> redirected to
        # the DEMO's CURRENT TARGET (NE L2973).
        line, status = resolve_target_line(_demo62(), override=2970)
        assert status == "redirected"
        assert line == 2973

    def test_demo62_override_to_unrelated_line_ok(self):
        # A line that is neither forbidden nor the default passes through.
        line, status = resolve_target_line(_demo62(), override=4000)
        assert status == "ok"
        assert line == 4000

    def test_no_forbidden_declaration_override_passes(self):
        demo = {"line": 100, "description": "Nothing forbidden here."}
        line, status = resolve_target_line(demo, override=999)
        assert status == "ok"
        assert line == 999

    def test_refused_when_default_itself_is_forbidden(self):
        # Config drift: the DEMO default line IS the forbidden locus (the
        # description marks it DO NOT TARGET but the `line` field still
        # points there). No safe CURRENT TARGET -> refuse.
        demo = {"line": 1234, "description": "DO NOT TARGET L1234."}
        line, status = resolve_target_line(demo)
        assert status == "refused"
        assert line is None

    def test_refused_when_override_forbidden_and_no_safe_default(self):
        # Both the override target AND the DEMO default are forbidden -> no
        # safe CURRENT TARGET exists -> refuse. Two regions declared via the
        # quadrant-map + DO-NOT-TARGET convention.
        demo = {
            "line": 1234,
            "description": "cases (nw L1234, ne L999). DO NOT TARGET nw. DO NOT TARGET ne.",
        }
        line, status = resolve_target_line(demo, override=999)
        assert status == "refused"
        assert line is None

    def test_no_line_at_all_is_ok_none(self):
        # A synthetic demo with no target line (synthetic theorem): nothing
        # to enforce, the launcher proceeds with line=None.
        demo = {"description": "DO NOT TARGET L1."}
        line, status = resolve_target_line(demo)
        assert status == "ok"
        assert line is None

    def test_exit_code_sentinel_distinct(self):
        # The refusal exit code must not collide with the launcher's other
        # sentinels (2 bad demo, 3 locked, 130 died).
        assert DO_NOT_TARGET_EXIT == 4
        assert DO_NOT_TARGET_EXIT not in (0, 2, 3, 130)
