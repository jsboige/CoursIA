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
import render_envs  # noqa: E402  -- module object, for integration tests that
#   monkeypatch module globals (MASTER_ENV, TARGET_ENVS, SERVICES_ROOT) and call
#   bootstrap()/sync()/main()/bootstrap_missing_envs(). Ported from the deleted
#   legacy scripts/tests/test_render_envs.py shadow (#10066 consolidation).
from render_envs import (  # noqa: E402
    _LINE_RE,
    _source_priority,
    mask,
    parse_kv,
    read_env,
)


# --------------------------------------------------------------------------- #
# Helpers: build a tmp env tree whose paths carry the parts _source_priority
# inspects ("docker-configurations" + "services" => priority 0 / canonical).
# Ported from the deleted legacy shadow.
# --------------------------------------------------------------------------- #
def _svc_env(tree: Path, svc: str) -> Path:
    """A service .env path that registers as CANONICAL (priority 0)."""
    p = tree / "docker-configurations" / "services" / svc / ".env"
    p.parent.mkdir(parents=True, exist_ok=True)
    return p


def _svc_dir(tree: Path, svc: str) -> Path:
    """A service dir under SERVICES_ROOT-shaped tmp tree (no .env pre-created)."""
    return tree / "docker-configurations" / "services" / svc


# --------------------------------------------------------------------------- #
# Anti-recidive hermeticity guard (#10085)
#
# The #10085 defect: ``test_bootstrap_missing_flag_no_master_returns_1`` had an
# INERT monkeypatch (the impl's default args were bound at import time, so
# patching ``render_envs.MASTER_ENV`` did nothing). On every cluster machine
# (which owns a real ``.secrets/master.env``) the test silently bootstrapped
# the REAL ``docker-configurations/services`` tree, writing genuine key
# material to real service ``.env`` files; CI stayed green only because it has
# no master.env. "Vert sincere et sans valeur."
#
# This autouse organ makes a future inert-patch regression RED everywhere --
# not just on machines that happen to own a master.env. It snapshots the real
# services tree's ``*/. env`` (existence + mtime) before each test and asserts
# no test created or rewrote a real service .env. A regression self-cleans
# (created files are unlinked) then fails loudly with the offending paths.
# --------------------------------------------------------------------------- #
@pytest.fixture(autouse=True)
def _guard_real_service_envs():
    services_root = render_envs.REPO_ROOT / "docker-configurations" / "services"
    if not services_root.is_dir():
        yield
        return

    def _snapshot() -> dict[Path, int]:
        return {p: p.stat().st_mtime_ns for p in services_root.glob("*/.env")}

    before = _snapshot()
    yield
    after = _snapshot()
    created = sorted(set(after) - set(before))
    modified = {p for p in set(before) & set(after) if before[p] != after[p]}
    # Self-clean created files so a regression leaves no polluted .env on disk;
    # the assertion below still fails loudly with the paths.
    for p in created:
        try:
            p.unlink()
        except OSError:
            pass
    assert not created, (
        "#10085 hermeticity guard: test created real service .env "
        f"(monkeypatch was inert?); cleaned up: {created}"
    )
    assert not modified, (
        "#10085 hermeticity guard: test rewrote real service .env "
        f"(monkeypatch was inert?): {sorted(modified)}"
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


# =========================================================================== #
# INTEGRATION TESTS — ported verbatim from the deleted legacy
# scripts/tests/test_render_envs.py shadow (#10066 consolidation). These cover
# the module's STATE MACHINES (bootstrap/sync/main CLI) + constants + the
# compose-referenced-keys parser, none of which the pure-unit suite above
# touched. The module collision (both files shared basename
# ``test_render_envs`` -> sys.modules cached the legacy, shadowing the canon)
# meant the canon's 41 unit tests were DEAD in CI whenever both ran; deleting
# the legacy after porting these 29 unique tests resurrects the 41 AND unifies
# integration coverage in the canonical home (70 effective vs 51 before).
# References use the ``render_envs`` module object (imported above) so
# monkeypatching module globals drives the real state machines.
# =========================================================================== #


# --------------------------------------------------------------------------- #
# Constants
# --------------------------------------------------------------------------- #
class TestConstants:
    def test_secret_keys_is_frozenset(self):
        assert isinstance(render_envs.SECRET_KEYS, frozenset)

    def test_known_secret_keys_present(self):
        for k in ("HF_TOKEN", "OPENAI_API_KEY", "ANTHROPIC_API_KEY", "GITHUB_TOKEN",
                  # #10265: Qwen / ComfyUI-Login bearer, consumed by GenAI
                  # notebooks (00-5-ComfyUI-Local-Test.ipynb), auth_manager.py,
                  # and the legacy reconstruct_env.py sync path.
                  "QWEN_API_TOKEN"):
            assert k in render_envs.SECRET_KEYS

    def test_aliases_mapping(self):
        assert render_envs.ALIASES == {
            "HUGGINGFACE_TOKEN": "HF_TOKEN",
            "GITHUB_ACCESS_TOKEN": "GITHUB_TOKEN",
            # #10265: Qwen legacy alias (kept by auth_manager.py:233).
            "QWEN_API_USER_TOKEN": "QWEN_API_TOKEN",
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

    def test_bootstrap_missing_master_absent_returns_1(self, tmp_path, monkeypatch):
        # #10085: master absent -> bootstrap_missing_envs returns None -> exit 1.
        # The monkeypatch of MASTER_ENV / SERVICES_ROOT MUST bite (deferred
        # resolution at call time); on an unfixed build the patch was inert and
        # the function read the REAL master.env, so this passed in CI (no master)
        # yet wrote real service .env files on every cluster machine -- caught
        # by the autouse _guard_real_service_envs fixture.
        monkeypatch.setattr(render_envs, "MASTER_ENV", tmp_path / "absent.env")
        monkeypatch.setattr(render_envs, "SERVICES_ROOT", tmp_path / "svc")
        monkeypatch.setattr(sys, "argv", ["render_envs.py", "--bootstrap-missing"])
        assert render_envs.main() == 1

    def test_bootstrap_missing_master_present_writes_tmp_returns_0(
        self, tmp_path, monkeypatch
    ):
        # #10085 hermeticity proof: master PRESENT + a service gap -> the .env
        # must be written UNDER the patched tmp SERVICES_ROOT, proving the
        # monkeypatch bites. On an unfixed build the patch was inert: the
        # function read the real master, iterated the real SERVICES_ROOT, and
        # wrote a REAL service .env (caught by the autouse guard), while CI
        # (no real master) returned 1 and failed the == 0 assertion. Either
        # way the unfixed build is RED; the fixed build writes to tmp and is GREEN.
        services_root = tmp_path / "svc"
        services_root.mkdir()
        master = tmp_path / "master.env"
        master.write_text("WHISPER_API_KEY=canonical-wsk\n", encoding="utf-8")
        svc = services_root / "whisper-api"
        svc.mkdir()
        (svc / "docker-compose.yml").write_text(
            "services:\n  w:\n    environment:\n      - API_KEY=${WHISPER_API_KEY:-}\n",
            encoding="utf-8",
        )
        monkeypatch.setattr(render_envs, "MASTER_ENV", master)
        monkeypatch.setattr(render_envs, "SERVICES_ROOT", services_root)
        monkeypatch.setattr(sys, "argv", ["render_envs.py", "--bootstrap-missing"])
        assert render_envs.main() == 0
        # Hermeticity: the .env landed under the PATCHED tmp services_root.
        written = svc / ".env"
        assert written.exists(), "bootstrap should have created the missing .env"
        assert "WHISPER_API_KEY=canonical-wsk" in written.read_text(encoding="utf-8")

    def test_bootstrap_missing_exclusive_with_check(self, tmp_path, monkeypatch):
        monkeypatch.setattr(render_envs, "MASTER_ENV", tmp_path / "absent.env")
        monkeypatch.setattr(render_envs, "SERVICES_ROOT", tmp_path / "svc")
        monkeypatch.setattr(sys, "argv",
                            ["render_envs.py", "--bootstrap-missing", "--check"])
        with pytest.raises(SystemExit) as exc:
            render_envs.main()
        assert exc.value.code == 2


# --------------------------------------------------------------------------- #
# --bootstrap-missing: close the .env blind spot (#9351)
# --------------------------------------------------------------------------- #
class TestBootstrapMissing:
    def _setup_tree(self, tmp_path):
        """Build a tmp tree mirroring SERVICES_ROOT shape. Return (services_root, master)."""
        services_root = tmp_path / "docker-configurations" / "services"
        services_root.mkdir(parents=True)
        master = tmp_path / "master.env"
        return services_root, master

    def test_no_master_returns_none(self, tmp_path, monkeypatch):
        services_root, master = self._setup_tree(tmp_path)
        # master does NOT exist
        result = render_envs.bootstrap_missing_envs(
            services_root=services_root, master_path=master,
            secret_keys=render_envs.SECRET_KEYS,
        )
        assert result is None

    def test_creates_env_when_compose_references_secret_key(self, tmp_path, monkeypatch):
        services_root, master = self._setup_tree(tmp_path)
        master.write_text("WHISPER_API_KEY=canonical-wsk\nOPENAI_API_KEY=canonical-oai\n",
                          encoding="utf-8")
        svc = _svc_dir(tmp_path, "whisper-api")
        svc.mkdir(parents=True)
        (svc / "docker-compose.yml").write_text(
            "services:\n  whisper-api:\n    environment:\n      - API_KEY=${WHISPER_API_KEY:-}\n",
            encoding="utf-8",
        )
        # No .env yet.
        assert not (svc / ".env").exists()

        result = render_envs.bootstrap_missing_envs(
            services_root=services_root, master_path=master,
            secret_keys=render_envs.SECRET_KEYS,
        )
        assert result == ["whisper-api"]
        env_text = (svc / ".env").read_text(encoding="utf-8")
        # Only the referenced key is written (OPENAI_API_KEY is in master but
        # not in the compose file, so it is NOT emitted).
        assert "WHISPER_API_KEY=canonical-wsk" in env_text
        assert "OPENAI_API_KEY" not in env_text
        # Header comment is present so future maintainers know the provenance.
        assert "Auto-generated by render_envs.py --bootstrap-missing" in env_text

    def test_skips_service_without_compose(self, tmp_path, monkeypatch):
        services_root, master = self._setup_tree(tmp_path)
        master.write_text("WHISPER_API_KEY=canonical-wsk\n", encoding="utf-8")
        svc = _svc_dir(tmp_path, "no-compose")
        svc.mkdir(parents=True)
        # NO docker-compose.yml in this dir.

        result = render_envs.bootstrap_missing_envs(
            services_root=services_root, master_path=master,
            secret_keys=render_envs.SECRET_KEYS,
        )
        assert result == []
        assert not (svc / ".env").exists()

    def test_skips_compose_with_no_secret_refs(self, tmp_path, monkeypatch):
        services_root, master = self._setup_tree(tmp_path)
        master.write_text("WHISPER_API_KEY=canonical-wsk\n", encoding="utf-8")
        svc = _svc_dir(tmp_path, "no-refs")
        svc.mkdir(parents=True)
        (svc / "docker-compose.yml").write_text(
            "services:\n  foo:\n    environment:\n      - PORT=8080\n",
            encoding="utf-8",
        )

        result = render_envs.bootstrap_missing_envs(
            services_root=services_root, master_path=master,
            secret_keys=render_envs.SECRET_KEYS,
        )
        assert result == []
        assert not (svc / ".env").exists()

    def test_existing_env_left_untouched(self, tmp_path, monkeypatch):
        services_root, master = self._setup_tree(tmp_path)
        master.write_text("WHISPER_API_KEY=master-canonical\n", encoding="utf-8")
        svc = _svc_dir(tmp_path, "already")
        svc.mkdir(parents=True)
        (svc / "docker-compose.yml").write_text(
            "services:\n  foo:\n    environment:\n      - API_KEY=${WHISPER_API_KEY:-}\n",
            encoding="utf-8",
        )
        existing = svc / ".env"
        existing.write_text("WHISPER_API_KEY=local-override\n# curated by hand\n",
                            encoding="utf-8")

        result = render_envs.bootstrap_missing_envs(
            services_root=services_root, master_path=master,
            secret_keys=render_envs.SECRET_KEYS,
        )
        # Not in write list -- sync() owns existing .env.
        assert result == []
        # Local override preserved (no overwrite).
        assert "local-override" in existing.read_text(encoding="utf-8")

    def test_hybrid_compose_also_scanned(self, tmp_path, monkeypatch):
        services_root, master = self._setup_tree(tmp_path)
        master.write_text("WHISPER_API_KEY=canonical-wsk\n", encoding="utf-8")
        svc = _svc_dir(tmp_path, "hybrid")
        svc.mkdir(parents=True)
        # No docker-compose.yml, but a docker-compose-hybrid.yml.
        (svc / "docker-compose-hybrid.yml").write_text(
            "services:\n  foo:\n    environment:\n      - API_KEY=${WHISPER_API_KEY:-}\n",
            encoding="utf-8",
        )

        result = render_envs.bootstrap_missing_envs(
            services_root=services_root, master_path=master,
            secret_keys=render_envs.SECRET_KEYS,
        )
        assert result == ["hybrid"]
        assert "WHISPER_API_KEY=canonical-wsk" in (svc / ".env").read_text(encoding="utf-8")


# --------------------------------------------------------------------------- #
# _compose_referenced_keys: parser helper
# --------------------------------------------------------------------------- #
class TestComposeReferencedKeys:
    def test_extracts_dollar_brace(self, tmp_path):
        p = tmp_path / "c.yml"
        p.write_text("API_KEY=${WHISPER_API_KEY:-}\nPORT=8080\n", encoding="utf-8")
        keys = render_envs._compose_referenced_keys(
            p, frozenset({"WHISPER_API_KEY", "OPENAI_API_KEY"}),
        )
        assert keys == {"WHISPER_API_KEY"}

    def test_strips_default_value(self, tmp_path):
        p = tmp_path / "c.yml"
        p.write_text("API_KEY=${WHISPER_API_KEY:-fallback}\n", encoding="utf-8")
        keys = render_envs._compose_referenced_keys(
            p, frozenset({"WHISPER_API_KEY"}),
        )
        assert keys == {"WHISPER_API_KEY"}

    def test_filters_non_secret_keys(self, tmp_path):
        p = tmp_path / "c.yml"
        p.write_text("API_KEY=${WHISPER_API_KEY:-}\nFOO=${PORT:-8080}\n",
                    encoding="utf-8")
        keys = render_envs._compose_referenced_keys(
            p, frozenset({"WHISPER_API_KEY", "PORT"}),
        )
        # Both are technically "secret keys" in this caller's frozenset;
        # the helper does no filtering by SECRET_KEYS semantics, that's the
        # caller's responsibility. Pin actual behavior here.
        assert keys == {"WHISPER_API_KEY", "PORT"}

    def test_missing_file_returns_empty(self, tmp_path):
        keys = render_envs._compose_referenced_keys(
            tmp_path / "absent.yml", frozenset({"WHISPER_API_KEY"}),
        )
        assert keys == set()


# --------------------------------------------------------------------------- #
# TARGET_ENVS -- notebook-side .env paths (#9929, c.10186)
#
# The ``TARGET_ENVS`` module constant enumerates the .env files the script
# propagates ``master.env`` secrets into. Before #9929, only 3 notebook-side
# paths were listed (GenAI/.env, SymbolicAI/Lean/.env, QuantConnect/projects/
# Portfolio-IBKR-Coinbase-Hybrid/.env). Per-series notebooks whose .env files
# carry shared SECRET_KEYS (OPENAI_API_KEY, OPENROUTER_API_KEY) lived OUTSIDE
# TARGET_ENVS, making their drift invisible to ``--check``. The c.10186
# extension added 5 paths:
#
#   - ML/DataScienceWithAgents/AgenticDataScience/.env  (ECE TP series)
#   - SemanticKernel/.env                               (0-AI-settings + 09-CLR)
#   - SymbolicAI/SmartContracts/.env                    (Solidity / foundry)
#   - QuantConnect/.env                                 (LLM summary channel)
#   - SymbolicAI/SymbolicLearning/.env                  (LLM-assisted proof)
#
# The tests below pin three things:
#   (1) all 5 paths are PRESENT in the module's TARGET_ENVS (a future
#       cleanup that drops one of them is a deliberate, reviewed decision
#       rather than silent blind-spot regression),
#   (2) ``sync()`` silently skips a notebook .env that does not exist on
#       the current machine (machines that have not provisioned a series
#       are no-ops for that series),
#   (3) ``sync()`` correctly DRIFTS a notebook .env that DOES exist on
#       this machine -- proving that adding the path closes the blind
#       spot on machines where the file is provisioned.
# --------------------------------------------------------------------------- #
class TestNotebookTargetEnvs:
    """Pinning the #9929 TARGET_ENVS extension."""

    EXPECTED_NEW_PATHS = (
        # (relative-to-REPO_ROOT substring; the script's TARGET_ENVS ends
        # with the .env path; we match by suffix to be tolerant of any
        # future restructuring of parents above the notebook series).
        "MyIA.AI.Notebooks/ML/DataScienceWithAgents/AgenticDataScience/.env",
        "MyIA.AI.Notebooks/SemanticKernel/.env",
        "MyIA.AI.Notebooks/SymbolicAI/SmartContracts/.env",
        "MyIA.AI.Notebooks/QuantConnect/.env",
        "MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/.env",
    )

    def _target_env_paths(self) -> list[str]:
        # Strip the REPO_ROOT prefix (no trailing slash on Path.__str__,
        # so add one) to compare against the relative suffixes below.
        # Note: normalize backslashes to forward slashes BEFORE the rstrip,
        # else the rstrip("/") doesn't catch any trailing path separator.
        repo_root = (
            str(render_envs.REPO_ROOT).replace("\\", "/").rstrip("/") + "/"
        )
        return [
            str(p).replace("\\", "/").split(repo_root, 1)[-1]
            for p in render_envs.TARGET_ENVS
        ]

    def test_all_five_paths_present(self):
        rels = self._target_env_paths()
        for expected in self.EXPECTED_NEW_PATHS:
            assert expected in rels, (
                f"#9929 regression: TARGET_ENVS no longer lists {expected!r}; "
                f"current TARGET_ENVS notebook-side paths: {rels}"
            )

    def test_count_includes_three_legacy_plus_five_new(self):
        # Legacy 3 (GenAI/.env, SymbolicAI/Lean/.env,
        # QuantConnect/projects/Portfolio-IBKR-Coinbase-Hybrid/.env) + 5 new.
        # The service glob is not enumerated by this test (machine-dependent).
        rels = self._target_env_paths()
        legacy = {
            "MyIA.AI.Notebooks/GenAI/.env",
            "MyIA.AI.Notebooks/SymbolicAI/Lean/.env",
            "MyIA.AI.Notebooks/QuantConnect/projects/Portfolio-IBKR-Coinbase-Hybrid/.env",
        }
        for lpath in legacy:
            assert lpath in rels, (
                f"Legacy notebook .env path dropped: {lpath!r}"
            )
        for npath in self.EXPECTED_NEW_PATHS:
            assert npath in rels, (
                f"New #9929 notebook .env path missing: {npath!r}"
            )

    def test_sync_skips_missing_notebook_env(
        self, tmp_path, monkeypatch
    ):
        """A TARGET_ENVS path that does not exist on disk must NOT crash sync()
        (silent skip). This is the safety property that lets us add paths
        unconditionally for ALL machines, regardless of which series they have
        provisioned."""
        master = tmp_path / "master.env"
        master.write_text("OPENAI_API_KEY=canonical-oai\n", encoding="utf-8")
        # Build a tmp tree mirroring REPO_ROOT layout so the absent .env path
        # is exactly the one the script's TARGET_ENVS expects -- but do NOT
        # create the file.
        nb_root = tmp_path / "MyIA.AI.Notebooks"
        nb_root.mkdir()
        (nb_root / "SemanticKernel").mkdir()
        # NB: NO (nb_root / "SemanticKernel" / ".env").write_text(...)

        monkeypatch.setattr(render_envs, "REPO_ROOT", tmp_path)
        monkeypatch.setattr(render_envs, "MASTER_ENV", master)
        monkeypatch.setattr(
            render_envs, "TARGET_ENVS",
            [tmp_path / "MyIA.AI.Notebooks" / "SemanticKernel" / ".env"],
        )
        # sync() must NOT raise -- silent skip is the contract.
        assert render_envs.sync(check_only=False) == 0
        # And the absent file must remain absent.
        assert not (tmp_path / "MyIA.AI.Notebooks" / "SemanticKernel" / ".env").exists()

    def test_sync_drifts_existing_notebook_env_to_master(
        self, tmp_path, monkeypatch
    ):
        """A TARGET_ENVS path that DOES exist with a stale OPENAI_API_KEY
        must be detected as drift by ``--check`` and rewritten by sync()."""
        master = tmp_path / "master.env"
        master.write_text("OPENAI_API_KEY=canonical-oai\n", encoding="utf-8")
        nb_root = tmp_path / "MyIA.AI.Notebooks"
        nb_root.mkdir()
        nb_env = nb_root / "SemanticKernel" / ".env"
        nb_env.parent.mkdir()
        nb_env.write_text(
            "# OpenAI key for SemanticKernel notebooks\n"
            "OPENAI_API_KEY=stale-dead-key\n",
            encoding="utf-8",
        )

        monkeypatch.setattr(render_envs, "REPO_ROOT", tmp_path)
        monkeypatch.setattr(render_envs, "MASTER_ENV", master)
        monkeypatch.setattr(render_envs, "TARGET_ENVS", [nb_env])

        # --check: stale key is drift -> exit 1, no write.
        assert render_envs.sync(check_only=True) == 1
        assert "OPENAI_API_KEY=stale-dead-key" in nb_env.read_text(encoding="utf-8")
        # sync (no --check): rewrites canonical value -> exit 0.
        assert render_envs.sync(check_only=False) == 0
        assert "OPENAI_API_KEY=canonical-oai" in nb_env.read_text(encoding="utf-8")

    def test_sync_preserves_non_secret_keys_in_notebook_env(
        self, tmp_path, monkeypatch
    ):
        """A TARGET_ENVS notebook .env may carry non-SECRET_KEYS config
        (e.g. SERVICE_NAME, semantic_kernel_version). sync() must leave
        those lines untouched -- master only governs declared SECRET_KEYS."""
        master = tmp_path / "master.env"
        master.write_text("OPENAI_API_KEY=canonical-oai\n", encoding="utf-8")
        nb_env = tmp_path / "SemanticKernel" / ".env"
        nb_env.parent.mkdir()
        nb_env.write_text(
            "# Series-local config (NOT in master)\n"
            "SK_VERSION=1.45.0\n"
            "OPENAI_API_KEY=stale\n"
            "NOTEBOOK_LOCALE=fr-FR\n",
            encoding="utf-8",
        )

        monkeypatch.setattr(render_envs, "MASTER_ENV", master)
        monkeypatch.setattr(render_envs, "TARGET_ENVS", [nb_env])

        assert render_envs.sync(check_only=False) == 0
        text = nb_env.read_text(encoding="utf-8")
        assert "OPENAI_API_KEY=canonical-oai" in text
        assert "SK_VERSION=1.45.0" in text, "non-secret key was wrongly clobbered"
        assert "NOTEBOOK_LOCALE=fr-FR" in text, "non-secret key was wrongly clobbered"
