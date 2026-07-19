"""Tests for scripts/secrets/render_envs.py (centralized secrets propagation).

The module is the canonical source-of-truth propagation tool referenced by
the ``secrets-hygiene`` project rule: ``.secrets/master.env`` -> every service
``.env`` for the declared SECRET_KEYS, with ``--check`` (drift gate) and
``--bootstrap`` (one-shot legacy extraction) modes.

SECURITY DISCIPLINE: every fixture uses synthetic, obviously-fake values in a
``tmp_path`` tree. The real ``.secrets/master.env`` and real service ``.env``
files are NEVER read, imported, or asserted against. No real secret format is
reproduced. The tests pin the module's pure parsing/masking logic + its
sync/bootstrap state machines (driven via monkeypatched module globals
``MASTER_ENV`` and ``TARGET_ENVS``).
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest

# --- Load the module under test by path (it has no package __init__) -------- #
_MODULE_PATH = Path(__file__).resolve().parents[1] / "secrets" / "render_envs.py"
_spec = importlib.util.spec_from_file_location("render_envs_under_test", _MODULE_PATH)
render_envs = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(render_envs)


# --------------------------------------------------------------------------- #
# Helpers: build a tmp env tree whose paths carry the parts _source_priority
# inspects ("docker-configurations" + "services" => priority 0 / canonical).
# --------------------------------------------------------------------------- #
def _svc_env(tree: Path, svc: str) -> Path:
    """A service .env path that registers as CANONICAL (priority 0).

    The path carries the ``docker-configurations`` + ``services`` parts that
    ``_source_priority`` inspects. Parent dirs are created so a caller can
    ``.write_text`` immediately.
    """
    p = tree / "docker-configurations" / "services" / svc / ".env"
    p.parent.mkdir(parents=True, exist_ok=True)
    return p


# --------------------------------------------------------------------------- #
# parse_kv
# --------------------------------------------------------------------------- #
class TestParseKv:
    def test_unquoted(self):
        assert render_envs.parse_kv("hello") == "hello"

    def test_strips_outer_whitespace(self):
        assert render_envs.parse_kv("  hello  ") == "hello"

    def test_double_quoted(self):
        assert render_envs.parse_kv('"hello world"') == "hello world"

    def test_single_quoted(self):
        assert render_envs.parse_kv("'hello world'") == "hello world"

    def test_empty_string(self):
        assert render_envs.parse_kv("") == ""

    def test_empty_quotes(self):
        assert render_envs.parse_kv('""') == ""

    def test_quoted_inner_spaces_collapsed(self):
        # After stripping the matching quotes, the trailing .strip() collapses
        # inner padding -- pinned actual behavior.
        assert render_envs.parse_kv('"  padded  "') == "padded"

    def test_inline_comment_NOT_stripped(self):
        # G.9 firsthand finding: the docstring promises "inline comment"
        # stripping, but the impl only strips surrounding quotes + whitespace.
        # A " # ..." suffix is kept as part of the value. Pinned honestly;
        # flagged to ai-01 as a docstring/impl mismatch (same class as #7414).
        assert render_envs.parse_kv("value # comment") == "value # comment"


# --------------------------------------------------------------------------- #
# read_env
# --------------------------------------------------------------------------- #
class TestReadEnv:
    def test_missing_file_returns_empty(self, tmp_path):
        assert render_envs.read_env(tmp_path / "absent.env") == {}

    def test_basic_assignment(self, tmp_path):
        p = tmp_path / "a.env"
        p.write_text("HF_TOKEN=abc\n", encoding="utf-8")
        assert render_envs.read_env(p) == {"HF_TOKEN": "abc"}

    def test_export_prefix(self, tmp_path):
        p = tmp_path / "a.env"
        p.write_text("export OPENAI_API_KEY=sk\n", encoding="utf-8")
        assert render_envs.read_env(p) == {"OPENAI_API_KEY": "sk"}

    def test_spaces_around_equals(self, tmp_path):
        p = tmp_path / "a.env"
        p.write_text("KEY = value\n", encoding="utf-8")
        assert render_envs.read_env(p) == {"KEY": "value"}

    def test_quoted_value_unwrapped(self, tmp_path):
        p = tmp_path / "a.env"
        p.write_text('KEY="quoted value"\n', encoding="utf-8")
        assert render_envs.read_env(p) == {"KEY": "quoted value"}

    def test_comments_blanks_invalid_skipped(self, tmp_path):
        p = tmp_path / "a.env"
        p.write_text(
            "# a comment\n"
            "\n"
            "INVALID LINE WITHOUT EQUALS\n"
            "1NUM=key\n"            # key must start with letter/underscore
            "GOOD=keep\n",
            encoding="utf-8",
        )
        assert render_envs.read_env(p) == {"GOOD": "keep"}

    def test_duplicate_key_last_wins(self, tmp_path):
        p = tmp_path / "a.env"
        p.write_text("KEY=first\nKEY=second\n", encoding="utf-8")
        assert render_envs.read_env(p) == {"KEY": "second"}


# --------------------------------------------------------------------------- #
# mask
# --------------------------------------------------------------------------- #
class TestMask:
    def test_empty(self):
        assert render_envs.mask("") == "<empty>"

    def test_short_value_all_stars(self):
        assert render_envs.mask("ab") == "**"

    def test_exactly_four_chars(self):
        assert render_envs.mask("abcd") == "****"

    def test_long_value_shows_last_four(self):
        assert render_envs.mask("abcde") == "***bcde"

    def test_realistic_token_shape(self):
        # Synthetic value -- never a real key.
        assert render_envs.mask("fake-token-SUFFIX1234") == "***1234"


# --------------------------------------------------------------------------- #
# _source_priority
# --------------------------------------------------------------------------- #
class TestSourcePriority:
    def test_service_is_canonical(self):
        p = Path("/repo/docker-configurations/services/comfyui/.env")
        assert render_envs._source_priority(p) == 0

    def test_notebooks_is_client(self):
        p = Path("/repo/MyIA.AI.Notebooks/GenAI/.env")
        assert render_envs._source_priority(p) == 1


# --------------------------------------------------------------------------- #
# Constants
# --------------------------------------------------------------------------- #
class TestConstants:
    def test_secret_keys_is_frozenset(self):
        assert isinstance(render_envs.SECRET_KEYS, frozenset)

    def test_known_secret_keys_present(self):
        for k in ("HF_TOKEN", "OPENAI_API_KEY", "ANTHROPIC_API_KEY", "GITHUB_TOKEN"):
            assert k in render_envs.SECRET_KEYS

    def test_aliases_mapping(self):
        assert render_envs.ALIASES == {
            "HUGGINGFACE_TOKEN": "HF_TOKEN",
            "GITHUB_ACCESS_TOKEN": "GITHUB_TOKEN",
        }


# --------------------------------------------------------------------------- #
# bootstrap: state machine (monkeypatch MASTER_ENV + TARGET_ENVS)
# --------------------------------------------------------------------------- #
class TestBootstrap:
    def test_master_exists_aborts_one_shot(self, tmp_path, monkeypatch):
        master = tmp_path / "master.env"
        master.write_text("EXISTING=keep\n", encoding="utf-8")
        monkeypatch.setattr(render_envs, "MASTER_ENV", master)
        monkeypatch.setattr(render_envs, "TARGET_ENVS", [])
        assert render_envs.bootstrap() == 1
        # existing master is NOT overwritten
        assert "EXISTING=keep" in master.read_text(encoding="utf-8")

    def test_clean_gather_writes_sorted(self, tmp_path, monkeypatch):
        master = tmp_path / "master.env"
        a = _svc_env(tmp_path, "svcA")
        a.write_text("OPENAI_API_KEY=fake-openai\nPORT=8080\n", encoding="utf-8")
        b = _svc_env(tmp_path, "svcB")
        b.write_text("HF_TOKEN=fake-hf\n", encoding="utf-8")
        monkeypatch.setattr(render_envs, "MASTER_ENV", master)
        monkeypatch.setattr(render_envs, "TARGET_ENVS", [a, b])

        assert render_envs.bootstrap() == 0
        text = master.read_text(encoding="utf-8")
        # Only SECRET_KEYS are gathered; PORT is service config -> excluded.
        assert "HF_TOKEN=fake-hf" in text
        assert "OPENAI_API_KEY=fake-openai" in text
        assert "PORT" not in text
        # Sorted alphabetically (HF_TOKEN before OPENAI_API_KEY).
        assert text.index("HF_TOKEN=") < text.index("OPENAI_API_KEY=")

    def test_client_drift_service_wins(self, tmp_path, monkeypatch):
        master = tmp_path / "master.env"
        svc = _svc_env(tmp_path, "svc")
        svc.write_text("HF_TOKEN=canonical-val\n", encoding="utf-8")
        client = tmp_path / "notebooks" / ".env"
        client.parent.mkdir(parents=True, exist_ok=True)
        client.write_text("HF_TOKEN=stale-val\n", encoding="utf-8")
        monkeypatch.setattr(render_envs, "MASTER_ENV", master)
        monkeypatch.setattr(render_envs, "TARGET_ENVS", [svc, client])

        assert render_envs.bootstrap() == 0
        # Service (priority 0) outranks client (priority 1).
        assert "HF_TOKEN=canonical-val" in master.read_text(encoding="utf-8")

    def test_hard_conflict_same_priority_aborts(self, tmp_path, monkeypatch):
        master = tmp_path / "master.env"
        a = _svc_env(tmp_path, "svcA")
        a.write_text("HF_TOKEN=val-one\n", encoding="utf-8")
        b = _svc_env(tmp_path, "svcB")
        b.write_text("HF_TOKEN=val-two\n", encoding="utf-8")
        monkeypatch.setattr(render_envs, "MASTER_ENV", master)
        monkeypatch.setattr(render_envs, "TARGET_ENVS", [a, b])

        assert render_envs.bootstrap() == 2
        # Aborted -> master NOT written.
        assert not master.exists()

    def test_alias_mismatch_aborts(self, tmp_path, monkeypatch):
        master = tmp_path / "master.env"
        svc = _svc_env(tmp_path, "svc")
        svc.write_text("HF_TOKEN=canonical\nHUGGINGFACE_TOKEN=different\n",
                       encoding="utf-8")
        monkeypatch.setattr(render_envs, "MASTER_ENV", master)
        monkeypatch.setattr(render_envs, "TARGET_ENVS", [svc])

        assert render_envs.bootstrap() == 2
        assert not master.exists()


# --------------------------------------------------------------------------- #
# sync: state machine
# --------------------------------------------------------------------------- #
class TestSync:
    def _setup(self, tmp_path, monkeypatch, master_text, env_files):
        master = tmp_path / "master.env"
        if master_text is not None:
            master.write_text(master_text, encoding="utf-8")
        monkeypatch.setattr(render_envs, "MASTER_ENV", master)
        targets = []
        for name, body in env_files:
            p = _svc_env(tmp_path, name)
            p.write_text(body, encoding="utf-8")
            targets.append(p)
        monkeypatch.setattr(render_envs, "TARGET_ENVS", targets)
        return targets

    def test_no_master_returns_1(self, tmp_path, monkeypatch):
        monkeypatch.setattr(render_envs, "MASTER_ENV", tmp_path / "absent.env")
        monkeypatch.setattr(render_envs, "TARGET_ENVS", [])
        assert render_envs.sync(check_only=False) == 1

    def test_drift_check_only_no_write_exit1(self, tmp_path, monkeypatch):
        targets = self._setup(
            tmp_path, monkeypatch,
            "HF_TOKEN=new-val\n",
            [("svc", "HF_TOKEN=old-val\n")],
        )
        assert render_envs.sync(check_only=True) == 1
        # No write performed in check mode.
        assert "HF_TOKEN=old-val" in targets[0].read_text(encoding="utf-8")

    def test_drift_sync_writes_exit0(self, tmp_path, monkeypatch):
        targets = self._setup(
            tmp_path, monkeypatch,
            "HF_TOKEN=new-val\n",
            [("svc", "HF_TOKEN=old-val\n")],
        )
        assert render_envs.sync(check_only=False) == 0
        assert "HF_TOKEN=new-val" in targets[0].read_text(encoding="utf-8")

    def test_no_drift_exit0(self, tmp_path, monkeypatch):
        targets = self._setup(
            tmp_path, monkeypatch,
            "HF_TOKEN=stable\n",
            [("svc", "HF_TOKEN=stable\n")],
        )
        assert render_envs.sync(check_only=False) == 0
        assert "HF_TOKEN=stable" in targets[0].read_text(encoding="utf-8")

    def test_non_secret_key_untouched(self, tmp_path, monkeypatch):
        # A KEY present in service .env but ABSENT from master must be left
        # untouched (master only governs its own declared keys).
        targets = self._setup(
            tmp_path, monkeypatch,
            "HF_TOKEN=new-val\n",
            [("svc", "HF_TOKEN=old-val\nCUSTOM_PORT=9999\n")],
        )
        assert render_envs.sync(check_only=False) == 0
        text = targets[0].read_text(encoding="utf-8")
        assert "HF_TOKEN=new-val" in text
        assert "CUSTOM_PORT=9999" in text  # preserved


# --------------------------------------------------------------------------- #
# main(): argparse routing
# --------------------------------------------------------------------------- #
class TestMain:
    def test_default_runs_sync_check_false(self, tmp_path, monkeypatch):
        monkeypatch.setattr(render_envs, "MASTER_ENV", tmp_path / "absent.env")
        monkeypatch.setattr(render_envs, "TARGET_ENVS", [])
        monkeypatch.setattr(sys, "argv", ["render_envs.py"])
        # No master -> sync returns 1.
        assert render_envs.main() == 1

    def test_check_flag_routes_to_check_only(self, tmp_path, monkeypatch):
        master = tmp_path / "master.env"
        master.write_text("HF_TOKEN=new\n", encoding="utf-8")
        svc = _svc_env(tmp_path, "svc")
        svc.write_text("HF_TOKEN=old\n", encoding="utf-8")
        monkeypatch.setattr(render_envs, "MASTER_ENV", master)
        monkeypatch.setattr(render_envs, "TARGET_ENVS", [svc])
        monkeypatch.setattr(sys, "argv", ["render_envs.py", "--check"])
        # Drift in check mode -> exit 1, no write.
        assert render_envs.main() == 1
        assert "HF_TOKEN=old" in svc.read_text(encoding="utf-8")

    def test_bootstrap_flag_routes_to_bootstrap(self, tmp_path, monkeypatch):
        master = tmp_path / "master.env"
        master.write_text("EXISTING=x\n", encoding="utf-8")
        monkeypatch.setattr(render_envs, "MASTER_ENV", master)
        monkeypatch.setattr(render_envs, "TARGET_ENVS", [])
        monkeypatch.setattr(sys, "argv", ["render_envs.py", "--bootstrap"])
        # master exists -> bootstrap one-shot abort -> 1.
        assert render_envs.main() == 1

    def test_mutually_exclusive_flags_exit_2(self, tmp_path, monkeypatch):
        monkeypatch.setattr(render_envs, "MASTER_ENV", tmp_path / "absent.env")
        monkeypatch.setattr(render_envs, "TARGET_ENVS", [])
        monkeypatch.setattr(sys, "argv",
                            ["render_envs.py", "--bootstrap", "--check"])
        with pytest.raises(SystemExit) as exc:
            render_envs.main()
        assert exc.value.code == 2
