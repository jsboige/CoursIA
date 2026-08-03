"""Tests for scripts/secrets/render_envs.py — centralized secrets propagation.

Covers the dependency-free pure helpers:
- ``parse_kv``: dotenv value normalization (quote stripping, whitespace)
- ``mask``: secret display masking (last-4 reveal)
- ``_source_priority``: service-vs-client canonical-source ranking
- ``read_env``: dotenv parsing (assignment lines, export prefix, comments)

Tests assert the ACTUAL behavior of the code (regression-guard semantics), not
the docstring's claims where they diverge — e.g. ``parse_kv``'s docstring
promises inline-comment stripping that the code does not perform; that gap is
pinned here so a future change (fixing the code OR fixing the docstring) is a
deliberate, reviewed act rather than a silent drift.

Uses ``tmp_path`` for filesystem isolation; never touches real ``.env`` /
``master.env``. Zero source churn.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from render_envs import (  # noqa: E402
    _LINE_RE,
    _source_priority,
    mask,
    parse_kv,
    read_env,
)


# ---------------------------------------------------------------------------
# parse_kv
# ---------------------------------------------------------------------------

class TestParseKv:
    def test_double_quoted_stripped(self):
        assert parse_kv('"sk-secret"') == "sk-secret"

    def test_single_quoted_stripped(self):
        assert parse_kv("'sk-secret'") == "sk-secret"

    def test_unquoted_passthrough(self):
        assert parse_kv("sk-secret") == "sk-secret"

    def test_surrounding_whitespace_stripped(self):
        assert parse_kv("   sk-secret   ") == "sk-secret"

    def test_internal_whitespace_preserved(self):
        assert parse_kv("a b c") == "a b c"

    def test_empty_string(self):
        assert parse_kv("") == ""

    def test_single_char_no_quote_strip(self):
        # len < 2 threshold means a lone quote char is not treated as wrapping.
        assert parse_kv("a") == "a"

    def test_empty_double_quotes_become_empty(self):
        assert parse_kv('""') == ""

    def test_empty_single_quotes_become_empty(self):
        assert parse_kv("''") == ""

    def test_mismatched_quotes_not_stripped(self):
        # v[0] == v[-1] is required; a leading " with trailing ' is left alone.
        assert parse_kv('"value\'') == '"value\''

    def test_leading_quote_no_trailing_quote_not_stripped(self):
        assert parse_kv('"value') == '"value'

    def test_inline_comment_not_stripped(self):
        # REGRESSION GUARD: the docstring promises "inline comment" stripping,
        # but the code does not strip inline comments. Pinning the REAL behavior
        # here means any change to the comment-handling is a deliberate,
        # reviewed decision (fixing the code or the docstring), not silent drift.
        assert parse_kv("value # comment") == "value # comment"
        assert parse_kv("value#x") == "value#x"
        assert parse_kv("# full comment") == "# full comment"

    def test_value_with_equals_sign(self):
        # Regex value group (.*)$ captures everything after the first =; an
        # equals inside the value survives parse_kv.
        assert parse_kv("a=b") == "a=b"


# ---------------------------------------------------------------------------
# mask
# ---------------------------------------------------------------------------

class TestMask:
    def test_empty_string(self):
        assert mask("") == "<empty>"

    def test_one_char(self):
        assert mask("x") == "*"

    def test_four_chars_fully_masked(self):
        assert mask("abcd") == "****"

    def test_five_chars_reveals_last_four(self):
        assert mask("abcde") == "***bcde"

    def test_long_secret_reveals_last_four(self):
        assert mask("sk-1234567890abcdef") == "***cdef"

    def test_does_not_mutate_input(self):
        s = "sk-secret-1234"
        mask(s)
        assert s == "sk-secret-1234"


# ---------------------------------------------------------------------------
# _source_priority
# ---------------------------------------------------------------------------

class TestSourcePriority:
    def test_service_env_is_canonical_priority_zero(self):
        # A service .env DEFINES a secret -> outranks clients (lower = higher).
        p = Path("/repo/docker-configurations/services/comfyui/.env")
        assert _source_priority(p) == 0

    def test_notebooks_env_is_client_priority_one(self):
        p = Path("/repo/MyIA.AI.Notebooks/GenAI/.env")
        assert _source_priority(p) == 1

    def test_arbitrary_env_is_client_priority_one(self):
        p = Path("/somewhere/else/.env")
        assert _source_priority(p) == 1

    def test_services_without_docker_config_is_client(self):
        # Both "docker-configurations" AND "services" must be in parts.
        p = Path("/repo/services/.env")
        assert _source_priority(p) == 1


# ---------------------------------------------------------------------------
# read_env
# ---------------------------------------------------------------------------

class TestReadEnv:
    def test_nonexistent_path_returns_empty(self):
        assert read_env(Path("/does/not/exist/.env")) == {}

    def test_simple_assignment(self, tmp_path):
        env = tmp_path / ".env"
        env.write_text("OPENAI_API_KEY=sk-abc\n", encoding="utf-8")
        assert read_env(env) == {"OPENAI_API_KEY": "sk-abc"}

    def test_multiple_assignments(self, tmp_path):
        env = tmp_path / ".env"
        env.write_text("A=1\nB=2\nC=3\n", encoding="utf-8")
        assert read_env(env) == {"A": "1", "B": "2", "C": "3"}

    def test_export_prefix(self, tmp_path):
        env = tmp_path / ".env"
        env.write_text("export HF_TOKEN=hf_xyz\n", encoding="utf-8")
        assert read_env(env) == {"HF_TOKEN": "hf_xyz"}

    def test_double_quoted_value(self, tmp_path):
        env = tmp_path / ".env"
        env.write_text('KEY="quoted value"\n', encoding="utf-8")
        assert read_env(env) == {"KEY": "quoted value"}

    def test_single_quoted_value(self, tmp_path):
        env = tmp_path / ".env"
        env.write_text("KEY='quoted value'\n", encoding="utf-8")
        assert read_env(env) == {"KEY": "quoted value"}

    def test_blank_lines_skipped(self, tmp_path):
        env = tmp_path / ".env"
        env.write_text("\nA=1\n\n  \nB=2\n", encoding="utf-8")
        assert read_env(env) == {"A": "1", "B": "2"}

    def test_comment_lines_skipped(self, tmp_path):
        env = tmp_path / ".env"
        env.write_text("# a comment\nA=1\n   # indented comment\nB=2\n",
                       encoding="utf-8")
        assert read_env(env) == {"A": "1", "B": "2"}

    def test_config_keys_preserved_not_filtered(self):
        # read_env returns ALL assignment lines; SECRET_KEYS filtering happens
        # in bootstrap/sync, NOT in read_env. Verify a non-secret config key
        # (e.g. a port) is still returned.
        import tempfile
        with tempfile.NamedTemporaryFile("w", suffix=".env", delete=False,
                                         encoding="utf-8") as f:
            f.write("PORT=8080\nOPENAI_API_KEY=sk-1\n")
            path = Path(f.name)
        try:
            result = read_env(path)
            assert result == {"PORT": "8080", "OPENAI_API_KEY": "sk-1"}
        finally:
            path.unlink()

    def test_last_assignment_wins_on_duplicate(self, tmp_path):
        env = tmp_path / ".env"
        env.write_text("A=1\nA=2\n", encoding="utf-8")
        assert read_env(env) == {"A": "2"}

    def test_empty_value(self, tmp_path):
        env = tmp_path / ".env"
        env.write_text("KEY=\n", encoding="utf-8")
        assert read_env(env) == {"KEY": ""}


# ---------------------------------------------------------------------------
# _LINE_RE (the dotenv line matcher underpinning read_env)
# ---------------------------------------------------------------------------

class TestLineRegex:
    def test_matches_simple_assignment(self):
        m = _LINE_RE.match("KEY=value")
        assert m is not None
        assert m.group(1) == "KEY"
        assert m.group(2) == "value"

    def test_matches_export_prefix(self):
        m = _LINE_RE.match("export KEY=value")
        assert m is not None and m.group(1) == "KEY"

    def test_matches_surrounding_whitespace(self):
        m = _LINE_RE.match("   KEY=value   ")
        assert m is not None and m.group(1) == "KEY" and m.group(2) == "value   "

    def test_rejects_comment(self):
        assert _LINE_RE.match("# comment") is None

    def test_rejects_blank(self):
        assert _LINE_RE.match("") is None
        assert _LINE_RE.match("   ") is None

    def test_rejects_leading_digit_key(self):
        # Key must start with letter or underscore.
        assert _LINE_RE.match("1KEY=value") is None

    def test_accepts_underscore_leading_key(self):
        m = _LINE_RE.match("_PRIVATE_KEY=value")
        assert m is not None and m.group(1) == "_PRIVATE_KEY"
