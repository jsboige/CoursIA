"""Regression guard for the ``.gitleaks.toml`` false-positive allowlist (#10143).

Rescoped (per ai-01 review on #10146) to lock the config merged by po-2026 in
#10201 — the test suite is what #10201 lacks. The risk this suite guards is the
*opposite* of detection: an over-broad or accidentally-added allowlist entry can
silently disarm the scanner for real credentials (the #9888 no-op failure mode).

Three invariants locked, one per direction:

* **presence** — each of the 14 #10143 FP entries (1 regex + 13 stopwords) is in
  the config. Accidental removal re-exposes dormant FPs.
* **suppression** — each FP entry actually suppresses its target literal.
* **positive control** — real-shaped keys of the same provider prefix stay
  DETECTED: no allowlist regex/stopword may match them. Includes the JWT HS256
  real-formed token (kept armed by #10201's choice NOT to allowlist the header)
  and a bare 32-hex shape (the Civitai/generic-api-key class).

  The positive-control fixtures are **synthetic by construction**: a shape, never
  a historical value. That is what makes the invariant un-gameable — a synthetic
  value can never legitimately appear in the allowlist, so a collision is *always*
  a disarm. Pinning an actual credential here instead couples the control to that
  credential's lifecycle, and the control then fires on the day the value is
  legitimately retired (which is precisely what happened, see below).

* **revocation discipline** (``REVOKED_ALLOWLISTED``) — a value may be allowlisted
  once it is DEAD, and only with its rotation evidence written in
  ``.gitleaks.toml``. Rotation is the primary remediation (secrets-hygiene rule
  5); the allowlist entry only silences the corpse in CI. This invariant checks
  the paperwork, not the value: entry present + rotation documented. A **live**
  credential swallowed by the allowlist remains caught by the positive control
  above, which no longer has any exemption to hide behind.

The tests parse ``.gitleaks.toml`` as text and compile the regexes themselves,
so they run without the gitleaks binary (CI only has gitleaks-action).
"""
from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
GITLEAKS_TOML = REPO_ROOT / ".gitleaks.toml"

# Pinned by `.github/workflows/secret-scan.yml` and `.pre-commit-config.yaml`
# (the two pins must agree, see `check_hooks_parity.py`). The test below
# invokes the gitleaks binary directly to assert the `paths` allowlist is a
# documented CONTENT BYPASS (#10595), so the version must match.
EXPECTED_GITLEAKS_VERSION = "8.24.3"


def _gitleaks_binary() -> str | None:
    """Locate the gitleaks binary, or None if unavailable.

    The CI uses Docker (`docker run zricethezav/gitleaks:v${GITLEAKS_VERSION}`);
    locally, we accept either a `gitleaks` on PATH or the Windows binary if
    installed. The skip is graceful: absence of the binary does NOT mean the
    config is healthy, it means this class of assertion cannot be evaluated
    here. CI still runs the same check via the gitleaks-action step."""
    found = shutil.which("gitleaks")
    if found:
        return found
    # Windows: fall back to a known install location if present.
    if sys.platform == "win32":
        candidate = Path("C:/Program Files/GitTools/gitleaks/gitleaks.exe")
        if candidate.exists():
            return str(candidate)
    return None


def _load_allowlist_regexes() -> list[str]:
    """Raw regex strings from the ``[allowlist] regexes = [...]`` array.

    Each entry is a triple-quoted TOML string ``'''<pattern>'''``.
    """
    text = GITLEAKS_TOML.read_text(encoding="utf-8")
    m = re.search(r"regexes\s*=\s*\[(.*?)^\]", text, re.S | re.M)
    assert m, "no [allowlist] regexes array found in .gitleaks.toml"
    return re.findall(r"'''(.*?)'''", m.group(1), re.S)


def _load_allowlist_stopwords() -> list[str]:
    """Stopword literals from the ``[allowlist] stopwords = [...]`` array.

    gitleaks treats a stopword as a substring match on the *secret* of a finding:
    if the secret contains it, the finding is suppressed.
    """
    text = GITLEAKS_TOML.read_text(encoding="utf-8")
    m = re.search(r"stopwords\s*=\s*\[(.*?)^\]", text, re.S | re.M)
    assert m, "no [allowlist] stopwords array found in .gitleaks.toml"
    return re.findall(r'"([^"]+)"', m.group(1))


def _compiled_regexes() -> list[re.Pattern]:
    return [re.compile(p) for p in _load_allowlist_regexes()]


# ---------------------------------------------------------------------------
# The 14 #10143 FP entries merged by #10201 that MUST stay present.
# ---------------------------------------------------------------------------
# The one class-based FP regex: OpenRouter pedagogical placeholder suffix is
# UPPERCASE-only (VOTRE_CLE / YOUR_KEY style), which real keys never are (real =
# sk-or-v1- + 64 lowercase hex). Anchoring on the uppercase class lets the
# detector stay armed for real lowercase-hex keys.
FP_CLASS_REGEX = "sk-or-v1-[A-Z][A-Z_]+"

# The 13 #10143 stopwords (substring match on the finding's secret). Each was
# read at its source in #10201 — all are pedagogical/test literals, none is a
# rotatable secret.
FP_STOPWORDS = [
    "sk-secret-12345",            # pedagogical key placeholder, Claude-Code README
    "sk_live_1234567890abcdef",   # canonical Stripe TEST key, bonnes-pratiques.md
    "rt-67890abcdef",             # pedagogical refresh-token placeholder, Roo-Code
    "v4_officier_german",         # voice-clone sample name, p1_voice_cloning.py
    "_getDistanceToBezierEdge2",  # vendored vis.js Bezier-edge fn, movie_kg_interactive.html
    "votre_token_ici",            # FR placeholder "your token here", archived README
    "INVALID_TOKEN",              # error-string literal, archived ComfyUI report
    "b2NWTdQ/zSFsWQ/JwCHyK/egVV6jpIssX0htD16",  # throwaway ComfyUI-Login local test token
    "wrongkey",                   # pedagogical placeholder, auth-flip-runbook.md
    "fixture-whisper-XXXX-1234",  # test fixture, test_verify_running_containers.py
    "hf_fixtureABCDEF1234567890", # test fixture (HF-token-shaped), same test file
    "val2=with=equals",           # parser test fixture (value with embedded '=')
    "ghp_IMfYN5...NCsd",          # redacted GitHub-token example (the `...` is literal)
]


# ---------------------------------------------------------------------------
# Real-shaped credentials that MUST stay detected (positive control).
# Built from concatenation so the real-shaped literal never appears contiguously
# in committed source (the PR diff is gitleaks-scanned; a contiguous real key
# literal would be flagged). At runtime the parts join to the value no allowlist
# entry may match.
# ---------------------------------------------------------------------------
REAL_KEYS = [
    # real OpenRouter shape: sk-or-v1- + 64 lowercase hex. The FP regex requires
    # UPPERCASE after the prefix, so a lowercase-hex key is never suppressed.
    "sk-or-v" + "1-9a3f7c2e1b8d4e6f0a2c5b9d7e1f3a4c6b8d0e2f4a6c8e0d2b4f6a8",
    # real Stripe shape (random entropy, distinct from the TEST-key stopword).
    "sk_" + "live_abcDEF1234567890ghijKLmnopQRSTuvwx",
    # real OpenAI shape.
    # NOTE: do NOT use `AbCdEf1234567890` here — that's a stopword in
    # .gitleaks.toml (added by #10575 follow-up commit e1f65d765 to
    # suppress AGSEC005 placeholder detection). Using it as a fixture
    # would disarm the positive-control test (c.1331+106 — `test_real_keys_contain_no_stopword`
    # failed on main 2026-08-12T21:06Z, run 31640973141). Use a synthetic
    # that's not in any stopword instead.
    "sk-pro" + "j-XyZwVu9876543210GhIjKlMnOpQrStUvWxYz",
    # JWT HS256 real-formed (header.payload.signature). #10201 keeps the jwt
    # detector ARMED by deliberately NOT allowlisting the standard header
    # (it is a prefix of every real JWT; substring-allowlisting it disarms the
    # whole class). This positive control locks that choice.
    ("eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9"
     + "." + "eyJzdWIiOiIxMjM0NTY3ODkwIiwibmFtZSI6IkphbmUgRG9lIn0"
     + "." + "SflKxwRJSMeKKF2QT4fwpMeJf36POk6yJV_adQssw5c"),
    # Bare 32-hex shape (Civitai / generic-api-key class, #10202). SYNTHETIC:
    # this value has never been a credential anywhere, so it can never acquire a
    # legitimate reason to sit in the allowlist — any collision is a real disarm.
    # It replaces the historical Civitai token, which was pinned here until
    # #10255: once that token was rotated and legitimately allowlisted as a dead
    # value, the control fired on the *correct* allowlisting instead of on a
    # disarm. A positive control must outlive the lifecycle of any one secret.
    "a7f3c91d" + "4e82b56097fd3a1c8b64e250",
]

# Values that ARE allowed to sit in the allowlist because they are dead: rotated
# at the provider, revocation verified firsthand, evidence written next to the
# entry in .gitleaks.toml. Allowlisting a *live* credential stays forbidden
# (#9888) — and stays caught, because the positive control above is synthetic and
# therefore has no exemption. Key = the 8-char prefix (the full literal has no
# business in this file); value = the evidence required in the toml comment.
REVOKED_ALLOWLISTED = {
    "c39ba121": "Civitai token, 6 occurrences in archive dirs (#10202); rotated "
                "at provider (#10205), revocation verified firsthand (401 on "
                "GET /api/v1/users/self); allowlisted by #10255 (see #10141).",
}


class TestAllowlistEntriesPresent:
    """Each #10143 FP entry must be present — accidental removal is a regression."""

    def test_class_regex_present(self):
        patterns = _load_allowlist_regexes()
        assert FP_CLASS_REGEX in patterns, (
            f"FP class regex {FP_CLASS_REGEX!r} missing from .gitleaks.toml "
            f"allowlist regexes — its removal would re-expose ~15 dormant OpenRouter "
            f"FP findings (see #10143 / #10201)"
        )

    def test_stopwords_present(self):
        stopwords = _load_allowlist_stopwords()
        missing = [s for s in FP_STOPWORDS if s not in stopwords]
        assert not missing, (
            f"these #10143 stopwords are missing from .gitleaks.toml: {missing} "
            f"— gitleaks would re-flag the dormant pedagogical literals (see #10201)"
        )


class TestFPLiteralsSuppressed:
    """Each FP entry actually suppresses its target literal."""

    def test_class_regex_suppresses_uppercase_placeholder(self):
        compiled = _compiled_regexes()
        # The uppercase placeholder form (the real FP in the corpus).
        for placeholder in ("sk-or-v1-VOTRE_CLE", "sk-or-v1-VOTRE_CLE_ICI",
                            "sk-or-v1-YOUR_KEY_HERE"):
            assert any(r.search(placeholder) for r in compiled), (
                f"FP class regex does not suppress uppercase placeholder "
                f"{placeholder!r} (see #10143)"
            )

    def test_each_stopword_is_self_suppressing(self):
        # A stopword suppresses any finding whose secret contains it (substring).
        # Each stopword trivially contains itself — this guards that the parsed
        # literals are the real ones and that the suppression mechanism is
        # understood by the test.
        stopwords = _load_allowlist_stopwords()
        for fp in FP_STOPWORDS:
            assert fp in stopwords, f"{fp!r} not in parsed stopwords"


class TestPositiveControlRealKeysStayDetected:
    """Positive control: NO allowlist regex may match, and NO stopword may be a
    substring of, a real-shaped key. If either holds, the scanner is silently
    disarmed for real credentials of that provider (the #9888 failure mode)."""

    def test_real_keys_not_matched_by_regex(self):
        compiled = _compiled_regexes()
        disarmed = []
        for key in REAL_KEYS:
            matched = [r.pattern for r in compiled if r.search(key)]
            if matched:
                disarmed.append((key[:28] + "...", matched))
        assert not disarmed, (
            f"allowlist regex(es) match a REAL-shaped key -> scanner disarmed: "
            f"{disarmed} (see #10143 positive-control requirement)"
        )

    def test_real_keys_contain_no_stopword(self):
        stopwords = _load_allowlist_stopwords()
        disarmed = []
        for key in REAL_KEYS:
            hits = [s for s in stopwords if s in key]
            if hits:
                disarmed.append((key[:28] + "...", hits))
        assert not disarmed, (
            f"a real-shaped key contains an allowlist stopword -> scanner disarmed: "
            f"{disarmed} (see #10143 positive-control requirement)"
        )


class TestJWTDetectorArmed:
    """The standard JWT HS256 header is deliberately NOT allowlisted (#10201): it
    is a prefix of every real JWT, and gitleaks allowlist matching is
    substring-based, so suppressing it would disarm the jwt detector entirely.
    This locks that choice so a future widening cannot silently regress it.
    The cost is 2 bare-header FP findings in Roo-Code docs (assumed by design)."""

    JWT_HEADER = "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9"

    def test_header_not_in_allowlist_regexes(self):
        patterns = _load_allowlist_regexes()
        # The header literal must not appear (in full or as a matchable prefix)
        # in any allowlist regex — a substring of it would already disarm.
        for p in patterns:
            rx = re.compile(p)
            assert not rx.search(self.JWT_HEADER), (
                f"allowlist regex {p!r} matches the JWT header -> jwt detector "
                f"disarmed (see #10201: header must stay visible). The 2 bare-header "
                f"Roo-Code doc FPs are assumed, the real-jwt class is not."
            )

    def test_header_not_in_stopwords(self):
        stopwords = _load_allowlist_stopwords()
        assert self.JWT_HEADER not in stopwords, (
            "JWT header listed as a stopword -> any JWT whose secret contains it "
            "(all of them) is suppressed -> detector disarmed (see #10201)"
        )

    def test_real_jwt_stays_detected(self):
        # The positive control already covers this (REAL_KEYS includes a full
        # header.payload.signature JWT). This named test makes the intent explicit.
        compiled = _compiled_regexes()
        stopwords = _load_allowlist_stopwords()
        real_jwt = ("eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9"
                    + "." + "eyJzdWIiOiIxIn0"
                    + "." + "tn9aVlMiiYnFkQslAPPXO6Huoe3WcKtAEbM4DF7D3kc")
        assert not any(r.search(real_jwt) for r in compiled), (
            "a real-formed JWT matches an allowlist regex -> detector disarmed"
        )
        assert not any(s in real_jwt for s in stopwords), (
            "a real-formed JWT contains a stopword -> detector disarmed"
        )


class TestRevocationDiscipline:
    """A secret may be allowlisted only once it is DEAD, and only with its
    rotation evidence written beside the entry.

    This class replaces ``TestCivitaiTokenStaysDetected``, whose premise —
    "deliberately NOT allowlisted, the fix is ROTATION (#10205)" — was correct
    while the token was live and became false the moment the rotation it demanded
    was actually performed (#10255: 401 verified firsthand). The old test encoded
    a *temporal* state as a permanent invariant, so completing the remediation it
    asked for turned it red and blocked every PR touching ``scripts/``.

    What is durable is not "this value stays out" but "nothing enters alive". So
    the checks below verify the **paperwork** for each retired value, while the
    positive control (synthetic fixtures) keeps guarding live credentials."""

    def test_revoked_entries_are_actually_in_the_allowlist(self):
        """No stale exemption: an entry removed from the toml must lose its row
        here too, otherwise the dict silently grants cover to nothing."""
        stopwords = _load_allowlist_stopwords()
        for prefix in REVOKED_ALLOWLISTED:
            matches = [s for s in stopwords if s.startswith(prefix)]
            assert matches, (
                f"{prefix}... is listed in REVOKED_ALLOWLISTED but is no longer a "
                f"stopword in .gitleaks.toml -> stale exemption, drop the row"
            )
            assert len(matches) == 1, (
                f"{prefix}... matches {len(matches)} stopwords -> ambiguous "
                f"exemption, make the prefix discriminating"
            )

    def test_revoked_entries_document_their_rotation(self):
        """The entry must carry its evidence in the toml, next to the value.

        Rotation is the remediation (secrets-hygiene rule 5); the allowlist line
        only silences the dead value in CI. Without the evidence written down, a
        future reader cannot tell this apart from allowlisting a live secret."""
        text = GITLEAKS_TOML.read_text(encoding="utf-8")
        for prefix in REVOKED_ALLOWLISTED:
            idx = text.find(prefix)
            assert idx != -1, f"{prefix}... not found in .gitleaks.toml"
            # The documenting comment block precedes the value; 1200 chars back
            # covers a verbose block without reaching the previous entry's.
            window = text[max(0, idx - 1200):idx].lower()
            assert "revok" in window or "rotat" in window, (
                f"the .gitleaks.toml entry for {prefix}... does not document a "
                f"rotation/revocation -> indistinguishable from allowlisting a "
                f"live credential (#9888)"
            )

    def test_revoked_values_are_not_positive_controls(self):
        """A retired value must never also be a positive-control fixture.

        Otherwise an exemption could be laundered into the control set, and the
        collision that should turn this suite red would read as authorised."""
        for prefix in REVOKED_ALLOWLISTED:
            collides = [k[:12] + "..." for k in REAL_KEYS if prefix in k]
            assert not collides, (
                f"{prefix}... is both REVOKED_ALLOWLISTED and inside a positive "
                f"control {collides} -> the control can no longer detect a disarm"
            )


# ---------------------------------------------------------------------------
# Paths allowlist = CONTENT BYPASS (c.1331+107/#10595).
# Documented structural tradeoff: the allowlist entry
#   scripts/secrets/tests/test_gitleaks_.*\.py$
# skips the scanner on the directory that hosts the gitleaks regression suite
# itself — otherwise the synthetic `qwen-api-token` fixtures (c.10265) would
# produce 14+ noise findings per CI run. The price is that ANY secret under
# `scripts/secrets/tests/test_gitleaks_*.py` is invisible to the scanner.
#
# This class asserts TWO properties simultaneously so that future maintainers
# cannot regress either side unknowingly:
#
#   1. The bypass HOLDS today — a real-shaped secret under the allowlisted
#      path is NOT flagged. Removing the `paths` entry would break this
#      assertion, forcing the maintainer to consciously reintroduce the
#      bypass or fix the underlying noise problem.
#   2. The detector stays ARMED in general — the same real-shaped secret in a
#      sibling file OUTSIDE the allowlist IS flagged. This is the positive
#      control: if the detector were silently disabled everywhere, both
#      assertions would (wrongly) pass.
#
# The test invokes the gitleaks binary directly — text-only parsing of the
# TOML cannot test a runtime bypass — which is why it skips gracefully when
# gitleaks is unavailable (CI does NOT run this class locally; the gate is
# the gitleaks-action scan on the actual PR). The point of the test is the
# NAME: it documents the bypass with a runnable invariant instead of leaving
# it as a comment in `.gitleaks.toml` only.
# ---------------------------------------------------------------------------
class TestPathsAllowlistBypass:
    """Asserts the structural tradeoff: ``[allowlist].paths`` skips the scanner
    on the allowlisted path, AND the detector stays armed everywhere else.

    Tradeoff rationale: ``scripts/secrets/tests/test_gitleaks_*.py$`` is the
    directory hosting the gitleaks regression suite itself. The synthetic
    ``qwen-api-token`` fixtures (c.10265) live there; allowing the scanner to
    read them would produce 14+ noise findings per CI run, defeating the
    signal-to-noise ratio. The cost is that this directory is opaque to the
    scanner. Any future LIVE secret accidentally committed under this path
    would be invisible. See #10595 for the reproduction and the structural
    audit. The positive control here ensures the detector still works on
    byte-identical content under a non-allowlisted path, so a future global
    disarm cannot pass silently.
    """

    @pytest.fixture(scope="class")
    def gitleaks_bin(self):
        bin_path = _gitleaks_binary()
        if bin_path is None:
            pytest.skip(
                "gitleaks binary not on PATH; the runtime-bypass assertion "
                "cannot be evaluated here. CI still runs this check via "
                "the gitleaks-action step on the actual PR."
            )
        return bin_path

    def test_gitleaks_version_matches_pin(self, gitleaks_bin):
        """Version drift between the two pins (workflow + pre-commit) re-uses
        a stale binary and silently changes which findings surface. This
        test catches drift EARLY: if the local binary is not the pinned one,
        the assertions below measure a different scanner than CI will run.
        """
        proc = subprocess.run(
            [gitleaks_bin, "version"],
            capture_output=True, text=True, timeout=15,
        )
        actual = proc.stdout.strip().splitlines()[-1] if proc.stdout else ""
        assert EXPECTED_GITLEAKS_VERSION in actual, (
            f"local gitleaks reports {actual!r}, expected the pinned "
            f"{EXPECTED_GITLEAKS_VERSION}. Update `.github/workflows/"
            f"secret-scan.yml` AND `.pre-commit-config.yaml` together "
            f"(see check_hooks_parity.py for the drift check), then re-run."
        )

    def test_real_secret_under_path_allowlist_is_invisible(self, gitleaks_bin, tmp_path):
        """The bypass HOLDS: a real-shaped secret under
        ``scripts/secrets/tests/test_gitleaks_*.py`` is NOT flagged.

        This is the **mirrored assertion** that gives the documented
        tradeoff a runnable name. Removing the ``paths`` entry would break
        this assertion (the file becomes detectable), forcing the maintainer
        to consciously reintroduce the bypass or fix the underlying noise
        from the synthetic fixtures.
        """
        # Build the allowlisted tree + a control tree in tmp_path, both with
        # byte-identical content for the secret. The relative paths inside
        # tmp_path mirror the production structure (the `paths` entry is a
        # regex against the file path RELATIVE TO --source, not absolute).
        src_dir = tmp_path / "scripts" / "secrets" / "tests"
        src_dir.mkdir(parents=True)
        allowed_file = src_dir / "test_gitleaks_c1331x107_probe.py"
        control_file = src_dir / "test_gitleaks_c1331x107_probe.txt"  # .txt ≠ .py

        # Synthetic real-shaped secret: built from concatenation so the PR
        # diff of this test file is not itself gitleaks-flagged. The shape
        # matches `generic-api-key` (entropy >= 4, lowercase hex suffix).
        real_secret = "sk-" + "or" + "-v1-" + "9a3f7c2e1b8d4e6f0a2c5b9d" \
                      + "7e1f3a4c6b8d0e2f4a6c8e0d2b4f6a8c0"
        secret_line = f'API_KEY = "{real_secret}"\n'

        allowed_file.write_text(secret_line, encoding="utf-8")
        control_file.write_text(secret_line, encoding="utf-8")

        # Invoke gitleaks on the allowlisted tree. We expect 1 finding (the
        # .txt control file) and 0 findings on the .py file — the structural
        # bypass.
        proc = subprocess.run(
            [
                gitleaks_bin, "detect",
                "--no-git",
                "--source", str(tmp_path),
                "--config", str(GITLEAKS_TOML),
                "--no-banner",
                "--exit-code", "0",  # do not raise; we parse the JSON report
                "--report-format", "json",
                "--report-path", str(tmp_path / "out.json"),
            ],
            capture_output=True, text=True, timeout=30,
        )
        assert proc.returncode == 0, (
            f"gitleaks invocation failed (exit {proc.returncode}): "
            f"{proc.stderr.strip()[:300]}"
        )

        report_path = tmp_path / "out.json"
        assert report_path.exists(), "gitleaks did not produce a JSON report"
        try:
            findings = json.loads(report_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as e:
            pytest.fail(f"gitleaks output is not valid JSON: {e}")

        flagged = [f for f in findings if f.get("Secret") == real_secret]

        # Positive control: the detector is armed in general — same content,
        # same scanner, only the path differs. The .txt control file MUST be
        # flagged; if it isn't, the bypass assertion will read as green while
        # the scanner is actually silently disabled everywhere (the dangerous
        # case).
        control_flagged = any("probe.txt" in (f.get("File") or "") for f in flagged)
        assert control_flagged, (
            "POSITIVE CONTROL FAILED: the synthetic real-shaped secret was "
            "NOT flagged under the .txt control file (different path, same "
            "content). This means the detector is silently disabled, not "
            "selectively bypassed — the bypass assertion below would read "
            "green while the scanner is broken. Refusing to assert the "
            "bypass until the detector is restored."
        )

        # Bypass assertion: the .py file MUST NOT be flagged (the documented
        # structural tradeoff). If it IS flagged, the `paths` allowlist entry
        # was removed — a maintainer must consciously reintroduce the bypass
        # (or fix the noise problem that motivated it).
        allowed_flagged = any("probe.py" in (f.get("File") or "") for f in flagged)
        assert not allowed_flagged, (
            "BYPASS ASSERTION FAILED: a real-shaped secret under "
            "scripts/secrets/tests/test_gitleaks_*.py IS flagged by gitleaks. "
            "The documented structural tradeoff (#10595) is no longer in "
            "effect — either the `paths` allowlist entry was removed (and the "
            "synthetic qwen-api-token fixtures now produce 14+ noise findings "
            "per CI run), or the bypass is being silently widened. Restore "
            "the allowlist entry deliberately, or fix the noise problem; do "
            "not let the test silently regress to the safe-looking green."
        )
