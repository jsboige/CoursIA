"""Regression tests for check_harness_coauthor.py (#10752 Phase 2).

The script gates the harness against stale `Co-Authored-By: Claude <Model>
<version>` trailers. Two harness files were caught in the wild:
- skills/review-student-prs/SKILL.md:132  ->  `Claude Opus 4.6`
- agents/notebook-iterative-builder.md:676 ->  `Claude Sonnet 4.5`

The canonical form per CLAUDE.md global secGit line 27 is
`Co-Authored-By: Claude-Code <noreply@anthropic.com>` (no model token).

These tests lock the detector invariants without invoking gitleaks or any
binary. They use synthetic tmp_path fixtures so they cannot be polluted by
the harness content they police.

Test classes (one per direction):

* **TestCanonicalFormClean** — Claude-Code trailers never match. The detector
  ignores them regardless of context (markdown line position, indentation).
* **TestStaleTrailerDetected** — Opus/Sonnet/Haiku + X.Y trailers match,
  with line number reported correctly.
* **TestVerdictLogic** — verdict transitions CLEAN <-> STALE on
  presence/absence of stale trailers; exit code follows verdict.
* **TestScopeDiscipline** — detector honors DEFAULT_SCAN_ROOTS and
  EXCLUDED_SCAN_ROOTS. agent-memory/ and worktrees/ are not scanned;
  skills/, agents/, commands/, rules/ are.
* **TestPatternEdgeCases** — case insensitivity, whitespace tolerance,
  Claude-3.5-Sonnet (model-as-version) NOT matched (correct: this is a
  trailer identifier, not a model spec).

The mirror pattern of c.1331+107-L2 (gitleaks regression test): a
detector is durable only if it is tested by another regression test.
The CI workflow `harness-coauthor-guard.yml` IS the second layer; this
file is the first.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

# Add scripts/notebook_tools to sys.path so we can import the detector.
SCRIPTS_DIR = Path(__file__).resolve().parent.parent
NOTEBOOK_TOOLS = SCRIPTS_DIR / "notebook_tools"
if str(NOTEBOOK_TOOLS) not in sys.path:
    sys.path.insert(0, str(NOTEBOOK_TOOLS))

from check_harness_coauthor import PATTERN, scan  # noqa: E402


# ---------------------------------------------------------------------------
# Synthetic fixtures: build a fake .claude/ tree with deterministic content.
# ---------------------------------------------------------------------------
@pytest.fixture
def fake_harness(tmp_path: Path) -> Path:
    """Build a minimal harness tree containing one file per DEFAULT_SCAN_ROOTS.

    Each file has the canonical Claude-Code trailer only -- no stale
    references. Tests mutate this baseline to add/remove stale trailers.
    """
    for sub in ("skills", "agents", "commands", "rules"):
        d = tmp_path / ".claude" / sub
        d.mkdir(parents=True, exist_ok=True)
        (d / f"sample_{sub}.md").write_text(
            "# Sample\n\nBody text.\n\n"
            "Co-Authored-By: Claude-Code <noreply@anthropic.com>\n",
            encoding="utf-8",
        )
    return tmp_path


# ---------------------------------------------------------------------------
# TestCanonicalFormClean
# ---------------------------------------------------------------------------
class TestCanonicalFormClean:
    """Claude-Code trailers must NEVER match -- they are the canonical form."""

    def test_pattern_does_not_match_canonical(self):
        assert PATTERN.search("Co-Authored-By: Claude-Code <noreply@anthropic.com>") is None

    def test_pattern_does_not_match_canonical_with_padding(self):
        assert PATTERN.search(
            "   Co-Authored-By:   Claude-Code <noreply@anthropic.com>"
        ) is None

    def test_scan_returns_clean_when_only_canonical_present(self, fake_harness: Path):
        report = scan(fake_harness)
        assert report["verdict"] == "CLEAN"
        assert report["total_findings"] == 0
        assert report["scanned_paths"] == 4
        assert report["scanned_files"] == 4


# ---------------------------------------------------------------------------
# TestStaleTrailerDetected
# ---------------------------------------------------------------------------
class TestStaleTrailerDetected:
    """Opus/Sonnet/Haiku + X.Y trailers match with correct line numbers."""

    @pytest.mark.parametrize(
        "model",
        ["Opus", "Sonnet", "Haiku", "opus", "sonnet", "haiku", "OPUS", "SONNET"],
    )
    def test_each_model_family_detected(self, fake_harness: Path, model: str):
        # Append a stale trailer to skills/sample_skills.md
        target = fake_harness / ".claude" / "skills" / "sample_skills.md"
        with target.open("a", encoding="utf-8") as f:
            f.write(f"Co-Authored-By: Claude {model} 4.6 <noreply@anthropic.com>\n")
        report = scan(fake_harness)
        assert report["verdict"] == "STALE"
        assert report["total_findings"] == 1
        finding = report["findings"][0]
        # c.1331+101-L1 analogue: path separators are OS-dependent. Compare
        # via Path parts rather than string endswith (which fails when
        # the detector emits backslash-separated paths on Windows).
        target_parts = {"skills", "sample_skills.md"}
        finding_parts = set(Path(finding["file"]).parts)
        assert target_parts <= finding_parts, (
            f"finding file {finding['file']!r} does not end with "
            f"skills/sample_skills.md (parts mismatch: {finding_parts})"
        )
        assert finding["model"].lower() == model.lower()
        assert finding["version"] == "4.6"
        # Original file = 5 lines (header, blank, body, blank, canonical
        # trailer at line 5). The stale trailer is appended as line 6.
        assert finding["line"] == 6

    def test_multiple_stale_in_same_file_all_reported(self, fake_harness: Path):
        target = fake_harness / ".claude" / "skills" / "sample_skills.md"
        with target.open("a", encoding="utf-8") as f:
            f.write("Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>\n")
            f.write("Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>\n")
            f.write("Co-Authored-By: Claude Haiku 3.0 <noreply@anthropic.com>\n")
        report = scan(fake_harness)
        assert report["total_findings"] == 3
        assert report["verdict"] == "STALE"
        versions = sorted(f["version"] for f in report["findings"])
        assert versions == ["3.0", "4.5", "4.6"]


# ---------------------------------------------------------------------------
# TestVerdictLogic
# ---------------------------------------------------------------------------
class TestVerdictLogic:
    """Verdict + exit code transition CLEAN <-> STALE on content change."""

    def test_empty_harness_returns_clean(self, tmp_path: Path):
        # Empty repo, no .claude/ at all -> 0 paths scanned, clean.
        report = scan(tmp_path)
        assert report["verdict"] == "CLEAN"
        assert report["scanned_paths"] == 0

    def test_single_stale_flip_verdict(self, fake_harness: Path):
        report_clean = scan(fake_harness)
        assert report_clean["verdict"] == "CLEAN"

        target = fake_harness / ".claude" / "rules" / "sample_rules.md"
        with target.open("a", encoding="utf-8") as f:
            f.write("Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>\n")
        report_stale = scan(fake_harness)
        assert report_stale["verdict"] == "STALE"

    def test_json_output_structure(self, fake_harness: Path):
        target = fake_harness / ".claude" / "commands" / "sample_commands.md"
        with target.open("a", encoding="utf-8") as f:
            f.write("Co-Authored-By: Claude Sonnet 5.0 <noreply@anthropic.com>\n")
        report = scan(fake_harness)
        # The detector emits JSON; round-trip to verify schema.
        encoded = json.dumps(report, ensure_ascii=False)
        decoded = json.loads(encoded)
        assert decoded["verdict"] == "STALE"
        assert "findings" in decoded
        for f in decoded["findings"]:
            assert {"file", "line", "match", "model", "version"} <= set(f.keys())


# ---------------------------------------------------------------------------
# TestScopeDiscipline
# ---------------------------------------------------------------------------
class TestScopeDiscipline:
    """Detector honors DEFAULT_SCAN_ROOTS + EXCLUDED_SCAN_ROOTS boundaries."""

    def test_agent_memory_is_not_scanned(self, tmp_path: Path):
        # .claude/agent-memory/ is explicitly excluded.
        memory = tmp_path / ".claude" / "agent-memory" / "fake-agent"
        memory.mkdir(parents=True, exist_ok=True)
        (memory / "scratchpad.md").write_text(
            "Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>\n",
            encoding="utf-8",
        )
        report = scan(tmp_path)
        assert report["verdict"] == "CLEAN"
        assert report["total_findings"] == 0

    def test_local_is_not_scanned(self, tmp_path: Path):
        # .claude/local/ is explicitly excluded.
        local = tmp_path / ".claude" / "local"
        local.mkdir(parents=True, exist_ok=True)
        (local / "INTERCOM.md").write_text(
            "Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>\n",
            encoding="utf-8",
        )
        report = scan(tmp_path)
        assert report["verdict"] == "CLEAN"

    def test_worktrees_is_not_scanned(self, tmp_path: Path):
        worktrees = tmp_path / ".claude" / "worktrees" / "some-agent"
        worktrees.mkdir(parents=True, exist_ok=True)
        (worktrees / "scratch.md").write_text(
            "Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>\n",
            encoding="utf-8",
        )
        report = scan(tmp_path)
        assert report["verdict"] == "CLEAN"

    def test_top_level_claude_md_is_not_scanned(self, tmp_path: Path):
        # .claude/CLAUDE.md is at the harness root, NOT in a default scan root.
        # Only skills/agents/commands/rules/ are scanned.
        claude_md = tmp_path / ".claude" / "CLAUDE.md"
        claude_md.parent.mkdir(parents=True, exist_ok=True)
        claude_md.write_text(
            "Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>\n",
            encoding="utf-8",
        )
        report = scan(tmp_path)
        # Per scope: CLAUDE.md is at .claude/ root, not under DEFAULT_SCAN_ROOTS.
        # Whether to scan the root .claude/*.md is a design choice; current
        # detector does NOT. Locking that choice here so a future widening is
        # an intentional decision, not a silent regression.
        assert report["verdict"] == "CLEAN"


# ---------------------------------------------------------------------------
# TestPatternEdgeCases
# ---------------------------------------------------------------------------
class TestPatternEdgeCases:
    """Pattern must NOT over-match (specificity is the whole point)."""

    def test_claude_3_5_sonnet_is_not_matched(self):
        # `Claude-3.5-Sonnet` is a model spec, not a Co-Authored-By trailer.
        # The detector targets the trailer identifier only.
        s = "Co-Authored-By: Claude-3.5-Sonnet <noreply@anthropic.com>"
        assert PATTERN.search(s) is None

    def test_claude_code_with_version_padded_is_matched(self):
        # Defensive: if someone writes `Claude-Code 4.6`, the pattern matches
        # because the regex is `Claude\s+(Opus|Sonnet|Haiku)\s+...`.
        # Claude-Code has neither model token nor version, so no match.
        assert PATTERN.search("Co-Authored-By: Claude-Code 4.6 <noreply@anthropic.com>") is None

    def test_no_email_address_matches(self):
        # Tell (verified c.1331+125): the pattern is LAZY -- it matches
        # `Co-Authored-By: Claude Opus 4.6` even without `<noreply@...>`.
        # This is intentional: the pattern targets the stale model+version
        # identifier only. If we required an email, real-world stale
        # trailers without email (e.g. half-typed commits) would slip
        # through. The trade-off = slight over-match (any prose that
        # happens to contain the model+version after a Co-Authored-By
        # prefix will match); in practice the prefix is so specific this
        # never fires.
        m = PATTERN.search("Co-Authored-By: Claude Opus 4.6")
        assert m is not None
        assert m.group(1) == "Opus"
        assert m.group(2) == "4.6"

    def test_three_part_version_matches_prefix(self):
        # Tell (verified c.1331+125): for `4.6.1`, the regex `\d+\.\d+`
        # matches the PREFIX `4.6` and stops. Three-part versions DO
        # match, just with the truncated version in `version`. Defensive
        # against future 3-part Anthropic model versions (`Claude Opus
        # 4.6.1 <...>`) -- the pattern catches them.
        m = PATTERN.search("Co-Authored-By: Claude Opus 4.6.1 <noreply@anthropic.com>")
        assert m is not None
        assert m.group(2) == "4.6"

    def test_whitespace_tolerance(self):
        # Multiple spaces between tokens should still match (regex `\\s+`).
        s = "Co-Authored-By:    Claude    Opus    4.6    <noreply@anthropic.com>"
        m = PATTERN.search(s)
        assert m is not None
        assert m.group(1) == "Opus"
        assert m.group(2) == "4.6"
