"""Tests for ``scripts/secrets/render_settings_json.py``.

This generator writes the gitignored ``MyIA.AI.Notebooks/Config/settings.json``
from ``.secrets/master.env`` (the same canonical source that
``render_envs.py`` propagates into ``SemanticKernel/.env``). The 5-key schema
mirrors what ``Settings.WriteSettings`` (Settings.cs:218-225) produces, so the
JSON produced here is consumed by ``Settings.LoadFromFile`` without any change.

Coverage:
- ``parse_kv`` / ``read_env``: dotenv helpers (the same as in test_render_envs).
- ``load_template_model``: model field is REQUIRED; missing template / missing
  model / malformed JSON all raise informative errors.
- ``build_settings_payload``: OPENAI_API_KEY missing or empty in master -> KeyError.
- ``sync``: writes a JSON file with the 5-key schema; the apikey field equals
  the canonical master value; the model comes from the template.
- ``check``: missing output -> exit 1, output present + matching -> exit 0,
  output present + drift -> exit 1.
- ``main``: argparse routes ``--check`` and bare invocation to the right helper.

Hermeticity: every test uses ``tmp_path`` + ``monkeypatch`` so no real
``settings.json`` or real ``master.env`` is touched. The autouse guard from
``test_render_envs.py`` does not apply here (different module, different
guard) but we add a module-local guard that asserts the worktree's real
``Config/settings.json`` is not rewritten by any test.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import render_settings_json as rsj  # noqa: E402

# Real worktree path: tests must NEVER touch this file.
REAL_OUTPUT = rsj.REPO_ROOT / "MyIA.AI.Notebooks" / "Config" / "settings.json"


# --------------------------------------------------------------------------- #
# Hermeticity guard: snapshot the real worktree settings.json (if it exists)
# and assert tests don't write to it. Cf test_render_envs.py:72-101.
# --------------------------------------------------------------------------- #
@pytest.fixture(autouse=True)
def _guard_real_settings_json():
    if not REAL_OUTPUT.exists():
        yield
        return
    real_text = REAL_OUTPUT.read_text(encoding="utf-8")
    yield
    after_text = REAL_OUTPUT.read_text(encoding="utf-8")
    assert after_text == real_text, (
        f"#9929 hermeticity: test rewrote the real {REAL_OUTPUT}"
    )


# --------------------------------------------------------------------------- #
# Fixtures: build a tmp tree mirroring the relevant layout.
# --------------------------------------------------------------------------- #
def _write_master(tmp_path: Path, body: str) -> Path:
    """Write a tmp master.env. Caller patches ``rsj.MASTER_ENV`` to this path."""
    p = tmp_path / "master.env"
    p.write_text(body, encoding="utf-8")
    return p


def _write_template(tmp_path: Path, model: str = "gpt-3.5-turbo") -> Path:
    """Write a tmp settings.json.openai-example template."""
    p = tmp_path / "settings.json.openai-example"
    payload = {
        "type": "openai",
        "endpoint": "NOT-USED-BUT-REQUIRED-FOR-PARSER",
        "model": model,
        "apikey": "... your OpenAI key ...",
        "org": "",
    }
    p.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return p


# --------------------------------------------------------------------------- #
# parse_kv / read_env
# --------------------------------------------------------------------------- #
class TestParseKv:
    def test_double_quoted_stripped(self):
        assert rsj.parse_kv('"sk-secret"') == "sk-secret"

    def test_single_quoted_stripped(self):
        assert rsj.parse_kv("'sk-secret'") == "sk-secret"

    def test_unquoted_passthrough(self):
        assert rsj.parse_kv("sk-secret") == "sk-secret"

    def test_surrounding_whitespace_stripped(self):
        assert rsj.parse_kv("   sk-secret   ") == "sk-secret"

    def test_empty_double_quotes_become_empty(self):
        assert rsj.parse_kv('""') == ""


class TestReadEnv:
    def test_simple_assignment(self):
        p = Path(__file__).parent / "_dummy_simple.env"
        p.write_text("FOO=bar\nBAZ=qux\n", encoding="utf-8")
        try:
            assert rsj.read_env(p) == {"FOO": "bar", "BAZ": "qux"}
        finally:
            p.unlink()

    def test_nonexistent_returns_empty(self, tmp_path):
        assert rsj.read_env(tmp_path / "absent.env") == {}

    def test_quoted_values_stripped(self, tmp_path):
        p = tmp_path / "q.env"
        p.write_text('FOO="quoted val"\nBAR=\'single val\'\n', encoding="utf-8")
        assert rsj.read_env(p) == {"FOO": "quoted val", "BAR": "single val"}


# --------------------------------------------------------------------------- #
# load_template_model
# --------------------------------------------------------------------------- #
class TestLoadTemplateModel:
    def test_returns_model_field(self, tmp_path):
        tmpl = _write_template(tmp_path, model="gpt-4o-mini")
        assert rsj.load_template_model(tmpl) == "gpt-4o-mini"

    def test_default_model(self, tmp_path):
        tmpl = _write_template(tmp_path)
        assert rsj.load_template_model(tmpl) == "gpt-3.5-turbo"

    def test_missing_template_raises(self, tmp_path):
        with pytest.raises(FileNotFoundError, match="Template not found"):
            rsj.load_template_model(tmp_path / "absent.json")

    def test_missing_model_field_raises(self, tmp_path):
        p = tmp_path / "bad.json"
        p.write_text(json.dumps({"type": "openai", "apikey": "x"}), encoding="utf-8")
        with pytest.raises(ValueError, match="no 'model' field"):
            rsj.load_template_model(p)

    def test_empty_model_raises(self, tmp_path):
        p = tmp_path / "empty.json"
        p.write_text(json.dumps({"model": "", "type": "openai"}), encoding="utf-8")
        with pytest.raises(ValueError, match="no 'model' field"):
            rsj.load_template_model(p)

    def test_invalid_json_raises(self, tmp_path):
        p = tmp_path / "bad.json"
        p.write_text("{not json", encoding="utf-8")
        with pytest.raises(ValueError, match="not valid JSON"):
            rsj.load_template_model(p)


# --------------------------------------------------------------------------- #
# build_settings_payload
# --------------------------------------------------------------------------- #
class TestBuildSettingsPayload:
    def test_returns_five_key_dict_in_settings_cs_order(self, tmp_path):
        tmpl = _write_template(tmp_path, model="gpt-3.5-turbo")
        master = {"OPENAI_API_KEY": "sk-test-key"}
        payload = rsj.build_settings_payload(master, tmpl)
        assert tuple(payload.keys()) == rsj.SCHEMA_KEYS
        assert tuple(payload.keys()) == ("type", "endpoint", "model", "apikey", "org")
        assert payload["type"] == "openai"
        assert payload["model"] == "gpt-3.5-turbo"
        assert payload["apikey"] == "sk-test-key"
        assert payload["org"] == ""
        # Endpoint is a fixed placeholder, not interpolated from anywhere.
        assert "NOT-USED" in payload["endpoint"]

    def test_openai_api_key_missing_raises_keyerror(self, tmp_path):
        tmpl = _write_template(tmp_path)
        with pytest.raises(KeyError, match="OPENAI_API_KEY"):
            rsj.build_settings_payload({}, tmpl)

    def test_openai_api_key_empty_raises_keyerror(self, tmp_path):
        tmpl = _write_template(tmp_path)
        with pytest.raises(KeyError, match="OPENAI_API_KEY"):
            rsj.build_settings_payload({"OPENAI_API_KEY": "   "}, tmpl)

    def test_model_is_inherited_from_template(self, tmp_path):
        tmpl = _write_template(tmp_path, model="gpt-5-mini")
        payload = rsj.build_settings_payload({"OPENAI_API_KEY": "sk-x"}, tmpl)
        assert payload["model"] == "gpt-5-mini"


# --------------------------------------------------------------------------- #
# sync (writes settings.json)
# --------------------------------------------------------------------------- #
class TestSync:
    def test_writes_five_key_json_to_output(self, tmp_path, monkeypatch):
        master = _write_master(tmp_path, "OPENAI_API_KEY=sk-from-master\n")
        tmpl = _write_template(tmp_path, model="gpt-3.5-turbo")
        output = tmp_path / "settings.json"

        monkeypatch.setattr(rsj, "MASTER_ENV", master)
        monkeypatch.setattr(rsj, "DEFAULT_TEMPLATE", tmpl)
        monkeypatch.setattr(rsj, "DEFAULT_OUTPUT", output)

        assert rsj.sync(tmpl, output) == 0
        assert output.exists()
        data = json.loads(output.read_text(encoding="utf-8"))
        assert tuple(data.keys()) == ("type", "endpoint", "model", "apikey", "org")
        assert data["apikey"] == "sk-from-master"

    def test_creates_parent_directory(self, tmp_path, monkeypatch):
        master = _write_master(tmp_path, "OPENAI_API_KEY=sk-x\n")
        tmpl = _write_template(tmp_path)
        # Output points to a nested path that doesn't exist yet.
        output = tmp_path / "nested" / "deeper" / "settings.json"

        monkeypatch.setattr(rsj, "MASTER_ENV", master)
        monkeypatch.setattr(rsj, "DEFAULT_TEMPLATE", tmpl)

        assert rsj.sync(tmpl, output) == 0
        assert output.exists()

    def test_no_master_returns_1(self, tmp_path, monkeypatch):
        tmpl = _write_template(tmp_path)
        output = tmp_path / "settings.json"
        monkeypatch.setattr(rsj, "MASTER_ENV", tmp_path / "absent.env")
        monkeypatch.setattr(rsj, "DEFAULT_TEMPLATE", tmpl)
        assert rsj.sync(tmpl, output) == 1
        assert not output.exists()

    def test_idempotent_re_run_same_master(self, tmp_path, monkeypatch):
        master = _write_master(tmp_path, "OPENAI_API_KEY=sk-stable\n")
        tmpl = _write_template(tmp_path, model="gpt-3.5-turbo")
        output = tmp_path / "settings.json"

        monkeypatch.setattr(rsj, "MASTER_ENV", master)
        monkeypatch.setattr(rsj, "DEFAULT_TEMPLATE", tmpl)

        assert rsj.sync(tmpl, output) == 0
        first = output.read_text(encoding="utf-8")
        assert rsj.sync(tmpl, output) == 0
        second = output.read_text(encoding="utf-8")
        assert first == second, "re-run with same master should be idempotent"


# --------------------------------------------------------------------------- #
# check
# --------------------------------------------------------------------------- #
class TestCheck:
    def test_missing_output_returns_1(self, tmp_path, monkeypatch):
        master = _write_master(tmp_path, "OPENAI_API_KEY=sk-x\n")
        output = tmp_path / "absent.json"
        monkeypatch.setattr(rsj, "MASTER_ENV", master)
        assert rsj.check(output, master_key="OPENAI_API_KEY") == 1

    def test_matching_output_returns_0(self, tmp_path, monkeypatch):
        master = _write_master(tmp_path, "OPENAI_API_KEY=sk-match\n")
        output = tmp_path / "settings.json"
        payload = rsj.build_settings_payload(
            {"OPENAI_API_KEY": "sk-match"},
            _write_template(tmp_path),
        )
        output.write_text(
            json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )
        monkeypatch.setattr(rsj, "MASTER_ENV", master)
        assert rsj.check(output, master_key="OPENAI_API_KEY") == 0

    def test_drift_returns_1(self, tmp_path, monkeypatch):
        master = _write_master(tmp_path, "OPENAI_API_KEY=sk-canonical\n")
        output = tmp_path / "settings.json"
        # Hand-craft a drifted file: apikey does NOT match master.
        payload = {
            "type": "openai", "endpoint": "x", "model": "gpt-3.5-turbo",
            "apikey": "sk-stale", "org": "",
        }
        output.write_text(json.dumps(payload), encoding="utf-8")
        monkeypatch.setattr(rsj, "MASTER_ENV", master)
        assert rsj.check(output, master_key="OPENAI_API_KEY") == 1

    def test_empty_apikey_returns_1(self, tmp_path, monkeypatch):
        master = _write_master(tmp_path, "OPENAI_API_KEY=sk-canonical\n")
        output = tmp_path / "settings.json"
        payload = {
            "type": "openai", "endpoint": "x", "model": "gpt-3.5-turbo",
            "apikey": "", "org": "",
        }
        output.write_text(json.dumps(payload), encoding="utf-8")
        monkeypatch.setattr(rsj, "MASTER_ENV", master)
        assert rsj.check(output, master_key="OPENAI_API_KEY") == 1

    def test_invalid_json_returns_1(self, tmp_path, monkeypatch):
        master = _write_master(tmp_path, "OPENAI_API_KEY=sk-canonical\n")
        output = tmp_path / "settings.json"
        output.write_text("{not valid json", encoding="utf-8")
        monkeypatch.setattr(rsj, "MASTER_ENV", master)
        assert rsj.check(output, master_key="OPENAI_API_KEY") == 1


# --------------------------------------------------------------------------- #
# main: argparse routing
# --------------------------------------------------------------------------- #
class TestMain:
    def test_default_runs_sync(self, tmp_path, monkeypatch):
        master = _write_master(tmp_path, "OPENAI_API_KEY=sk-x\n")
        tmpl = _write_template(tmp_path)
        output = tmp_path / "settings.json"
        monkeypatch.setattr(rsj, "MASTER_ENV", master)
        monkeypatch.setattr(rsj, "DEFAULT_TEMPLATE", tmpl)
        monkeypatch.setattr(rsj, "DEFAULT_OUTPUT", output)
        monkeypatch.setattr(sys, "argv", ["render_settings_json.py"])
        assert rsj.main() == 0
        assert output.exists()

    def test_check_flag_routes_to_check(self, tmp_path, monkeypatch):
        master = _write_master(tmp_path, "OPENAI_API_KEY=sk-x\n")
        output = tmp_path / "absent.json"
        monkeypatch.setattr(rsj, "MASTER_ENV", master)
        monkeypatch.setattr(rsj, "DEFAULT_OUTPUT", output)
        monkeypatch.setattr(sys, "argv", ["render_settings_json.py", "--check"])
        # Missing output -> check returns 1.
        assert rsj.main() == 1

    def test_no_master_default_returns_1(self, tmp_path, monkeypatch):
        tmpl = _write_template(tmp_path)
        output = tmp_path / "settings.json"
        monkeypatch.setattr(rsj, "MASTER_ENV", tmp_path / "absent.env")
        monkeypatch.setattr(rsj, "DEFAULT_TEMPLATE", tmpl)
        monkeypatch.setattr(rsj, "DEFAULT_OUTPUT", output)
        monkeypatch.setattr(sys, "argv", ["render_settings_json.py"])
        assert rsj.main() == 1


# --------------------------------------------------------------------------- #
# fingerprint: sha256[:8] discriminant, NOT a slice of the secret.
#
# ai-01 review (PR #10275) : ``value[-4:]`` est le meme geste que
# ``key[:8]``, interdit par secrets-hygiene regle 6 §C (``jamais key[:N]`` /
# symetriquement ``jamais value[-4:]``). fingerprint() remplace par un
# prefixe de hash : empreinte non-inversible, discrimination identique
# pour DRIFT detection, zero tranche du secret.
# --------------------------------------------------------------------------- #
class TestFingerprint:
    def test_empty_value_returns_empty_marker(self):
        assert rsj.fingerprint("") == "<empty>"

    def test_format_is_sha256_prefix(self):
        # Format ``sha256:`` + 8 hex chars = discriminant non-inversible.
        fp = rsj.fingerprint("sk-test-key-with-more-than-4-chars")
        assert fp.startswith("sha256:")
        assert len(fp) == len("sha256:") + 8
        # The 8 chars are hex
        int(fp.split(":", 1)[1], 16)  # raises if not hex

    def test_distinct_secrets_give_distinct_fingerprints(self):
        # Discrimination identique a mask() pour DRIFT detection : deux
        # secrets differents => deux fingerprints differents.
        a = rsj.fingerprint("sk-aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
        b = rsj.fingerprint("sk-bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb")
        assert a != b

    def test_same_secret_gives_same_fingerprint(self):
        # Determinism: la meme valeur produit toujours la meme empreinte.
        assert rsj.fingerprint("x") == rsj.fingerprint("x")

    def test_no_substring_of_input_in_fingerprint(self):
        # Anti-regression : fingerprint() ne doit JAMAIS contenir une
        # tranche de l'input (cf secrets-hygiene regle 6 §C). On verifie
        # sur 3 inputs representatifs.
        for secret in ["sk-abc123def456ghi789jkl012mno", "abcdef", "X"]:
            fp = rsj.fingerprint(secret)
            assert secret not in fp, f"fingerprint({secret!r}) leaked a substring: {fp!r}"
            # Et symetriquement, aucune tranche de 4 chars en fin
            # d'input n'apparait dans la sortie (le geste interdit).
            if len(secret) >= 4:
                assert secret[-4:] not in fp