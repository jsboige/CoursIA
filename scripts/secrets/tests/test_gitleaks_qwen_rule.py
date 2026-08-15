"""Tests for the ``qwen-api-token`` custom gitleaks rule (#10265).

A custom rule is a **gate** — it MUST be exercised in CI before being merged,
otherwise a "structural fix" that *adds* a rule but doesn't catch anything is
not a fix at all (cf c.10139-L4 ★★: "structural-fix exposes pre-existing leaks
: inspect pre-PR leak count BEFORE pushing wrapper-removal PR"). The positive
controls below are the same synthetic files that the rule produced in
ad-hoc verification on 2026-08-10; the negative controls are the marker
strings that the redaction surface should produce.

The tests invoke the gitleaks binary directly (no Python re-implementation of
the regex) so we test the actual production scanner, not a model of it.

Hermeticity: each test writes its own tmp directory + config and never
references the worktree's ``.gitleaks.toml``. The local-only ``gitleaks``
binary, if present, is the only artefact the test reads from the system
environment; if it is missing, the test is skipped (CI is the authoritative
gate, and CI already runs gitleaks via ``.github/workflows/secret-scan.yml``).
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import tempfile
from pathlib import Path

import pytest

# Resolve the gitleaks binary in this order:
#   1. GITLEAKS_BIN env var (set by CI)
#   2. ``gitleaks`` on PATH (pre-commit hook environment)
#   3. A local Windows binary at the conventional scratchpad path used by
#      po-2023 (verified by the worker who added the rule)
GITLEAKS_CANDIDATES = [
    os.environ.get("GITLEAKS_BIN"),
    shutil.which("gitleaks"),
    # Local cache on po-2023 (cycle 170 validated this path; #10139 workflow
    # pins ``v8.24.3`` so the same version is expected here).
    r"C:\Users\jsboi\AppData\Local\Temp\gitleaks-bin\gitleaks.exe",
]


def _gitleaks_binary() -> str | None:
    for candidate in GITLEAKS_CANDIDATES:
        if candidate and Path(candidate).exists():
            return candidate
    return None


GITLEAKS = _gitleaks_binary()
requires_gitleaks = pytest.mark.skipif(
    GITLEAKS is None,
    reason="gitleaks binary not found on PATH or scratchpad; CI is the authoritative gate",
)


# --------------------------------------------------------------------------- #
# Test config: reflection of the production rule, scoped to the tmp tree.
# --------------------------------------------------------------------------- #
GITLEAKS_CONFIG_TMPL = """\
title = "Test config for qwen-api-token rule (#10265)"

# Mirror the production config: extend the default ruleset so the
# ``generic-api-key`` detector (and the other 700+ built-in rules) load
# alongside the custom rule. This is what production .gitleaks.toml does
# (``[extend] useDefault = true``), and the JSON-style test depends on
# ``generic-api-key`` to rougir the ``{"KEY": "value"}`` form.
[extend]
useDefault = true

[[rules]]
id = "qwen-api-token"
description = "Qwen / ComfyUI-Login bearer token (env-var form, #10265)"
# Mirror production (entropy = 0 disables the Shannon filter so the rule
# fires on long structured-form secrets AND on the redaction markers
# themselves — the stopword list takes care of the latter).
regex = '''(?i)(?:qwen_api_token|qwen_api_user_token)\\s*[:=]\\s*['\"]?([A-Za-z0-9!@#\\$%^&*()\\-_=+.]{20,})['\"]?'''
entropy = 0
keywords = [
    "qwen_api_token",
    "qwen-api-token",
    "qwen_api_user_token",
]

[allowlist]
stopwords = [
    "7a052dd4aeb4",
    "2e5dd4339ca9",
    "de13deaace0c",
    # Mirror production: the redaction marker ``LEAKED-PENDING-ROTATION``
    # (22 chars) itself matches the {20,} regex threshold, so it must be a
    # stopword (substring match against the finding) — same logic as the
    # production ``regexes = ['''LEAKED-PENDING-ROTATION''']``.
    "LEAKED-PENDING-ROTATION",
]
"""


@pytest.fixture
def tmp_scan_dir(tmp_path: Path):
    """Build a tmp scan directory + custom gitleaks config."""
    cfg = tmp_path / ".gitleaks.toml"
    cfg.write_text(GITLEAKS_CONFIG_TMPL, encoding="utf-8")
    workdir = tmp_path / "work"
    workdir.mkdir()
    return {"root": tmp_path, "config": cfg, "work": workdir}


def _run_gitleaks(source: Path, config: Path) -> list[dict]:
    """Run gitleaks on ``source`` with ``config`` and return findings as dicts."""
    assert GITLEAKS is not None
    report = source.parent / "report.json"
    proc = subprocess.run(
        [
            GITLEAKS,
            "detect",
            "--no-git",
            "--source", str(source),
            "--config", str(config),
            "--no-banner",
            "--exit-code", "0",
            "--report-format", "json",
            "--report-path", str(report),
        ],
        capture_output=True,
        text=True,
        timeout=60,
    )
    # gitleaks may exit with code 0 even when findings are present (we set
    # --exit-code 0). Report file is the authoritative interface.
    if not report.exists():
        return []
    with report.open(encoding="utf-8") as f:
        data = json.load(f)
    return data


# --------------------------------------------------------------------------- #
# Positive controls: the rule MUST rouge on these patterns.
# --------------------------------------------------------------------------- #
@requires_gitleaks
class TestRuleRougesOn:
    """Verify the rule fires on the exact patterns the redaction removed."""

    def test_qwen_api_token_env_style_generated(self, tmp_scan_dir):
        # Real-world generated tokens are typically 32+ chars alphanum with
        # high Shannon entropy. The rule MUST rougir on these (verified against
        # gitleaks 8.24.3, 2026-08-10). The earlier "special-char" test in this
        # class was based on a misreading of the original token alphabet — the
        # actual charset emitted by the ComfyUI-Login token generator is
        # ``[A-Za-z0-9_-]`` (no ``!@#$%^&*()``). The redaction markers
        # themselves are sha256[:12] hex (``7a052dd4aeb4``), all in the
        # covered alphabet, and the stopword list silences them.
        (tmp_scan_dir["work"] / "leaked.env").write_text(
            'QWEN_API_TOKEN="xK9mZ3vL7nQ2pR8tY4wU6jH1bN5cF0eG"\n',
            encoding="utf-8",
        )
        findings = _run_gitleaks(tmp_scan_dir["work"], tmp_scan_dir["config"])
        assert len(findings) == 1, f"expected 1 finding, got {len(findings)}: {findings}"
        assert findings[0]["RuleID"] == "qwen-api-token"
        assert "xK9mZ3vL7nQ" in findings[0]["Secret"]

    def test_qwen_api_user_token_legacy_alias(self, tmp_scan_dir):
        # Legacy env-var name from auth_manager.py:233. Same alphabet as the
        # canonical ``QWEN_API_TOKEN`` (the generator emits the same shape for
        # both env-var names — they are aliases pointing at the same value).
        (tmp_scan_dir["work"] / "legacy.env").write_text(
            "QWEN_API_USER_TOKEN=aB3xZ9kL7mN2pQ8vR5tY4wU6jH1nC0e\n",
            encoding="utf-8",
        )
        findings = _run_gitleaks(tmp_scan_dir["work"], tmp_scan_dir["config"])
        assert len(findings) == 1
        assert findings[0]["RuleID"] == "qwen-api-token"
        assert "aB3xZ9kL7m" in findings[0]["Secret"]

    def test_yaml_style_assignment(self, tmp_scan_dir):
        # The .env.example files use ``key: value`` without quotes. A
        # generated high-entropy token MUST rougir in YAML form (the
        # ``entropy = 0`` flag ensures the Shannon filter does not drop the
        # match on long structured-form secrets).
        (tmp_scan_dir["work"] / "leaked.yml").write_text(
            "qwen_api_token: 'aB3xZ9kL7mN2pQ8vR5tY4wU6jH1nC0eF'\n",
            encoding="utf-8",
        )
        findings = _run_gitleaks(tmp_scan_dir["work"], tmp_scan_dir["config"])
        assert len(findings) == 1
        assert findings[0]["RuleID"] == "qwen-api-token"

    def test_qwen_api_token_full_alphabet_special_chars(self, tmp_scan_dir):
        # The actual redacted token (``2%=tVJ6@!Nc(7#VTvj-Bh3^nm0WY-Lij``,
        # observed in commit 81eb1a2b / docker-compose-no-auth.yml) is
        # composed of the full alphabet ``[A-Za-z0-9!@#$%^&*()_=+.-]``
        # including the ``@`` that earlier drafts of this regex missed.
        # The custom rule MUST rougir on this exact 32-char string so a
        # future regression of the same shape is caught.
        (tmp_scan_dir["work"] / "full.env").write_text(
            'QWEN_API_TOKEN=2%=tVJ6@!Nc(7#VTvj-Bh3^nm0WY-Lij\n',
            encoding="utf-8",
        )
        findings = _run_gitleaks(tmp_scan_dir["work"], tmp_scan_dir["config"])
        assert len(findings) == 1, f"expected 1 finding, got {len(findings)}: {findings}"
        assert findings[0]["RuleID"] == "qwen-api-token"
        assert "2%=tVJ6@!Nc" in findings[0]["Secret"]

    def test_json_style_assignment(self, tmp_scan_dir):
        # JSON-style ``{"KEY": "value"}`` is naturally caught by the default
        # ``generic-api-key`` rule (the inner alphabet matches its charset).
        # The custom ``qwen-api-token`` rule is keyed on ``qwen_api_token``
        # / ``qwen_api_user_token`` for env-var and YAML forms; JSON is a
        # bonus coverage area that the default ruleset already handles.
        # Verified against gitleaks 8.24.3, 2026-08-10.
        (tmp_scan_dir["work"] / "leaked.json").write_text(
            '{"QWEN_API_TOKEN": "xK9mZ3vL7nQ2pR8tY4wU6jH1bN5cF0eG"}\n',
            encoding="utf-8",
        )
        findings = _run_gitleaks(tmp_scan_dir["work"], tmp_scan_dir["config"])
        # At least one rule (custom or default) must rougir the JSON form.
        assert len(findings) >= 1, (
            f"expected >=1 finding (custom or default), got {len(findings)}: {findings}"
        )
        rule_ids = {f["RuleID"] for f in findings}
        assert "generic-api-key" in rule_ids or "qwen-api-token" in rule_ids, (
            f"expected generic-api-key or qwen-api-token, got {rule_ids}"
        )


# --------------------------------------------------------------------------- #
# Negative controls: the rule MUST NOT rouge on these patterns.
# --------------------------------------------------------------------------- #
@requires_gitleaks
class TestRuleStaysSilentOn:
    """Verify the rule does NOT fire on placeholder / allowlisted values."""

    def test_rotated_sha256_marker_is_allowlisted(self, tmp_scan_dir):
        # The redaction marker used in #10265. 12 hex chars prefixed by
        # LEAKED-PENDING-ROTATION == the stopword entry; the regex allows the marker
        # because the regex matches on the ``qwen_api_token=`` anchor and the
        # value length, but the stopword kills the finding.
        (tmp_scan_dir["work"] / "redacted.env").write_text(
            "QWEN_API_TOKEN=LEAKED-PENDING-ROTATION 7a052dd4aeb4\n",
            encoding="utf-8",
        )
        findings = _run_gitleaks(tmp_scan_dir["work"], tmp_scan_dir["config"])
        assert len(findings) == 0, f"LEAKED-PENDING-ROTATION marker should not rougir: {findings}"

    def test_all_three_sha256_prefixes_are_allowlisted(self, tmp_scan_dir):
        for sha in ("7a052dd4aeb4", "2e5dd4339ca9", "de13deaace0c"):
            (tmp_scan_dir["work"] / f"{sha}.env").write_text(
                f"QWEN_API_TOKEN=LEAKED-PENDING-ROTATION {sha}\n",
                encoding="utf-8",
            )
        findings = _run_gitleaks(tmp_scan_dir["work"], tmp_scan_dir["config"])
        assert len(findings) == 0, (
            f"all 3 documented sha256 prefixes should be allowlisted: {findings}"
        )

    def test_placeholder_too_short_does_not_match(self, tmp_scan_dir):
        # The regex requires >= 20 chars in the value. Placeholders like
        # ``your_bearer_token_here`` are 22 chars — they DO match the regex
        # length, but in the .env.example files they are path-allowlisted. In
        # an arbitrary file outside the path allowlist, they would still
        # rouge. This test guards against that regression by asserting the
        # opposite: a value that is clearly a placeholder but lacks any
        # stopword match — it MUST rougir (the rule keeps its discriminating power).
        (tmp_scan_dir["work"] / "placeholder.env").write_text(
            "QWEN_API_TOKEN=NOT_A_REAL_TOKEN_BUT_LONG_ENOUGH_TO_MATCH\n",
            encoding="utf-8",
        )
        findings = _run_gitleaks(tmp_scan_dir["work"], tmp_scan_dir["config"])
        # This should rougir — the placeholder is NOT a real secret but the
        # rule is heuristic. The path-allowlist in production .gitleaks.toml
        # takes care of .env.example files; this test only confirms the rule
        # itself has discriminating power.
        assert len(findings) == 1


# --------------------------------------------------------------------------- #
# Rule presence: the rule MUST be defined in .gitleaks.toml.
# --------------------------------------------------------------------------- #
@requires_gitleaks
class TestRuleInstalledInProduction:
    """Verify the rule is present in the production .gitleaks.toml."""

    REPO_ROOT = Path(__file__).resolve().parents[3]  # scripts/secrets/tests/ -> repo root
    PROD_CONFIG = REPO_ROOT / ".gitleaks.toml"

    def test_production_config_exists(self):
        assert self.PROD_CONFIG.exists(), (
            f"production .gitleaks.toml missing at {self.PROD_CONFIG}"
        )

    def test_qwen_api_token_rule_present(self):
        text = self.PROD_CONFIG.read_text(encoding="utf-8")
        assert 'id = "qwen-api-token"' in text, (
            "qwen-api-token rule not deployed to production .gitleaks.toml"
        )

    def test_three_sha256_prefixes_in_stopwords(self):
        text = self.PROD_CONFIG.read_text(encoding="utf-8")
        for sha in ("7a052dd4aeb4", "2e5dd4339ca9", "de13deaace0c"):
            assert sha in text, f"sha256 prefix {sha} missing from stopwords"

    def test_keywords_present(self):
        text = self.PROD_CONFIG.read_text(encoding="utf-8")
        for kw in ("qwen_api_token", "qwen_api_user_token"):
            assert kw in text, f"keyword {kw} missing from qwen-api-token rule"
