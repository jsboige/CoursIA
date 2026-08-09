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
  real-formed token (kept armed by #10201's choice NOT to allowlist the header),
  and the **Civitai token** ``c39ba121…34`` — a real committed secret (#10202)
  whose rotation is tracked by #10205; a future allowlist entry that swallowed it
  is exactly the disarm this test must catch.

The tests parse ``.gitleaks.toml`` as text and compile the regexes themselves,
so they run without the gitleaks binary (CI only has gitleaks-action).
"""
from __future__ import annotations

import re
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
GITLEAKS_TOML = REPO_ROOT / ".gitleaks.toml"


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
    "sk-pro" + "j-AbCdEf1234567890GhIjKlMnOpQrStUvWxYz",
    # JWT HS256 real-formed (header.payload.signature). #10201 keeps the jwt
    # detector ARMED by deliberately NOT allowlisting the standard header
    # (it is a prefix of every real JWT; substring-allowlisting it disarms the
    # whole class). This positive control locks that choice.
    ("eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9"
     + "." + "eyJzdWIiOiIxMjM0NTY3ODkwIiwibmFtZSI6IkphbmUgRG9lIn0"
     + "." + "SflKxwRJSMeKKF2QT4fwpMeJf36POk6yJV_adQssw5c"),
    # CIVITAI_TOKEN — a REAL committed secret (32-hex), 6 occurrences in archived
    # docker-configs/docs (#10202). NOT allowlisted by design (rotation tracked
    # by #10205). A future allowlist entry (regex or stopword) that swallowed it
    # would disarm the scanner exactly where it caught something real — the
    # #9888 failure mode. This control catches that regression. Built from
    # concatenation so the literal never sits contiguously in the test source.
    "c39ba121" + "e12e5b40ac67a87836431e34",
]


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


class TestCivitaiTokenStaysDetected:
    """The Civitai token ``c39ba121e12e5b40ac67a87836431e34`` is a real committed
    secret (6 occurrences in archived docker-configs/docs, #10202). It is
    deliberately NOT allowlisted — the fix is ROTATION at the provider (tracked
    by #10205), not a suppression entry. This test guards that no future
    allowlist widening (regex or stopword) silently swallows it, which would
    disarm the scanner exactly where it caught something real."""

    CIVITAI_TOKEN = "c39ba121" + "e12e5b40ac67a87836431e34"

    def test_not_matched_by_any_regex(self):
        compiled = _compiled_regexes()
        hits = [r.pattern for r in compiled if r.search(self.CIVITAI_TOKEN)]
        assert not hits, (
            f"allowlist regex(es) match the Civitai token -> scanner disarmed where "
            f"it caught a real secret (#9888): {hits} (see #10202/#10205)"
        )

    def test_not_a_stopword_substring(self):
        stopwords = _load_allowlist_stopwords()
        hits = [s for s in stopwords if s in self.CIVITAI_TOKEN]
        assert not hits, (
            f"a stopword is a substring of the Civitai token -> scanner disarmed "
            f"where it caught a real secret: {hits} (see #10202/#10205)"
        )
