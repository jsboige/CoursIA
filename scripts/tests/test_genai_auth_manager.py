#!/usr/bin/env python3
"""
Tests for scripts/genai-stack/core/auth_manager.py

Covers testable units: constants, dataclasses, pure functions,
bcrypt round-trip, config loading, auth header generation.
CLI (main) and heavy side-effect methods (synchronize_credentials,
reconstruct_env_file, audit_security) are excluded.
"""

import json
import os
import sys
import tempfile
from dataclasses import asdict
from pathlib import Path
from unittest.mock import patch

import pytest

# Add genai-stack/core to sys.path
_genai_core = str(Path(__file__).resolve().parent.parent / "genai-stack" / "core")
if _genai_core not in sys.path:
    sys.path.insert(0, _genai_core)

from auth_manager import (
    PROJECT_ROOT,
    SECRETS_DIR,
    CONFIG_FILE,
    TokenLocation,
    AuditReport,
    GenAIAuthManager,
)


# ─── Module constants ────────────────────────────────────────────────


class TestProjectRoot:
    def test_is_path(self):
        assert isinstance(PROJECT_ROOT, Path)

    def test_is_absolute(self):
        assert PROJECT_ROOT.is_absolute()

    def test_resolved(self):
        # No symlinks remaining
        assert ".." not in PROJECT_ROOT.parts


class TestSecretsDir:
    def test_is_path(self):
        assert isinstance(SECRETS_DIR, Path)

    def test_is_subdir_of_project_root(self):
        assert SECRETS_DIR.parent == PROJECT_ROOT

    def test_dirname_is_secrets(self):
        assert SECRETS_DIR.name == ".secrets"


class TestConfigFile:
    def test_is_path(self):
        assert isinstance(CONFIG_FILE, Path)

    def test_is_in_secrets_dir(self):
        assert CONFIG_FILE.parent == SECRETS_DIR

    def test_filename(self):
        assert CONFIG_FILE.name == "comfyui_auth_tokens.conf"

    def test_suffix(self):
        assert CONFIG_FILE.suffix == ".conf"


# ─── TokenLocation dataclass ────────────────────────────────────────


class TestTokenLocation:
    def test_required_fields(self):
        loc = TokenLocation(path="/tmp/test", type="bcrypt", description="test loc")
        assert loc.path == "/tmp/test"
        assert loc.type == "bcrypt"
        assert loc.description == "test loc"

    def test_defaults(self):
        loc = TokenLocation(path="/x", type="raw", description="d")
        assert loc.exists is False
        assert loc.content is None
        assert loc.is_valid is False

    def test_custom_fields(self):
        loc = TokenLocation(
            path="/x", type="env", description="d",
            exists=True, content="abc", is_valid=True
        )
        assert loc.exists is True
        assert loc.content == "abc"
        assert loc.is_valid is True

    def test_is_dataclass(self):
        import dataclasses
        assert dataclasses.is_dataclass(TokenLocation)

    def test_all_fields_present(self):
        import dataclasses
        fields = {f.name for f in dataclasses.fields(TokenLocation)}
        expected = {"path", "type", "description", "exists", "content", "is_valid"}
        assert fields == expected

    def test_asdict_roundtrip(self):
        loc = TokenLocation(path="/p", type="t", description="d", exists=True, content="c", is_valid=True)
        d = asdict(loc)
        assert d["path"] == "/p"
        assert d["type"] == "t"
        assert d["exists"] is True
        assert d["content"] == "c"


# ─── AuditReport dataclass ──────────────────────────────────────────


class TestAuditReport:
    def test_required_fields(self):
        report = AuditReport(
            timestamp="2026-01-01T00:00:00",
            locations=[],
            inconsistencies=[],
            recommendations=[],
        )
        assert report.timestamp == "2026-01-01T00:00:00"
        assert report.locations == []
        assert report.inconsistencies == []
        assert report.recommendations == []

    def test_is_dataclass(self):
        import dataclasses
        assert dataclasses.is_dataclass(AuditReport)

    def test_to_dict_keys(self):
        report = AuditReport(
            timestamp="2026-01-01T00:00:00",
            locations=[],
            inconsistencies=[],
            recommendations=["test"],
        )
        d = report.to_dict()
        assert set(d.keys()) == {"timestamp", "locations", "inconsistencies", "recommendations"}

    def test_to_dict_locations_serialized(self):
        loc = TokenLocation(path="/p", type="t", description="d")
        report = AuditReport(
            timestamp="2026-01-01",
            locations=[loc],
            inconsistencies=[],
            recommendations=[],
        )
        d = report.to_dict()
        assert len(d["locations"]) == 1
        assert d["locations"][0]["path"] == "/p"

    def test_to_dict_inconsistencies(self):
        report = AuditReport(
            timestamp="2026-01-01",
            locations=[],
            inconsistencies=[{"path": "/x", "issue": "mismatch"}],
            recommendations=[],
        )
        d = report.to_dict()
        assert len(d["inconsistencies"]) == 1
        assert d["inconsistencies"][0]["issue"] == "mismatch"

    def test_to_dict_json_serializable(self):
        loc = TokenLocation(path="/p", type="t", description="d", content="c")
        report = AuditReport(
            timestamp="2026-01-01",
            locations=[loc],
            inconsistencies=[],
            recommendations=["rec1"],
        )
        # Should not raise
        json.dumps(report.to_dict())


# ─── GenAIAuthManager.__init__ ───────────────────────────────────────


class TestGenAIAuthManagerInit:
    def test_default_root(self):
        mgr = GenAIAuthManager()
        assert mgr.root_dir == PROJECT_ROOT

    def test_custom_root(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            assert mgr.root_dir == Path(tmpdir)

    def test_secrets_dir_is_subdir(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            assert mgr.secrets_dir == Path(tmpdir) / ".secrets"

    def test_config_file_path(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            assert mgr.config_file == Path(tmpdir) / ".secrets" / "comfyui_auth_tokens.conf"

    def test_docker_config_dir(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            assert mgr.docker_config_dir == Path(tmpdir) / "docker-configurations" / "services" / "comfyui-qwen"

    def test_secrets_dir_created(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            assert mgr.secrets_dir.exists()


# ─── generate_secure_token ──────────────────────────────────────────


class TestGenerateSecureToken:
    def _mgr(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            yield GenAIAuthManager(root_dir=Path(tmpdir))

    def test_returns_string(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            token = mgr.generate_secure_token()
            assert isinstance(token, str)

    def test_default_length_32(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            assert len(mgr.generate_secure_token()) == 32

    def test_custom_length(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            assert len(mgr.generate_secure_token(16)) == 16

    def test_custom_length_64(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            assert len(mgr.generate_secure_token(64)) == 64

    def test_alphanumeric_only(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            token = mgr.generate_secure_token()
            assert token.isalnum()

    def test_uniqueness(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            tokens = {mgr.generate_secure_token() for _ in range(10)}
            assert len(tokens) == 10

    def test_length_1(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            assert len(mgr.generate_secure_token(1)) == 1


# ─── generate_bcrypt_hash ───────────────────────────────────────────


class TestGenerateBcryptHash:
    def test_returns_string(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            h = mgr.generate_bcrypt_hash("password123")
            assert isinstance(h, str)

    def test_starts_with_bcrypt_prefix(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            h = mgr.generate_bcrypt_hash("password123")
            assert h.startswith("$2b$")

    def test_different_passwords_different_hashes(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            h1 = mgr.generate_bcrypt_hash("password1")
            h2 = mgr.generate_bcrypt_hash("password2")
            assert h1 != h2

    def test_same_password_different_hashes(self):
        """Bcrypt generates a random salt each time."""
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            h1 = mgr.generate_bcrypt_hash("same_pass")
            h2 = mgr.generate_bcrypt_hash("same_pass")
            assert h1 != h2


# ─── validate_bcrypt_pair ───────────────────────────────────────────


class TestValidateBcryptPair:
    def test_valid_pair(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            password = "test_password_123"
            h = mgr.generate_bcrypt_hash(password)
            assert mgr.validate_bcrypt_pair(password, h) is True

    def test_invalid_pair(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            h = mgr.generate_bcrypt_hash("correct_password")
            assert mgr.validate_bcrypt_pair("wrong_password", h) is False

    def test_empty_password(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            h = mgr.generate_bcrypt_hash("")
            assert mgr.validate_bcrypt_pair("", h) is True

    def test_invalid_hash_returns_false(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            assert mgr.validate_bcrypt_pair("test", "not_a_hash") is False

    def test_returns_bool(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            h = mgr.generate_bcrypt_hash("pw")
            result = mgr.validate_bcrypt_pair("pw", h)
            assert isinstance(result, bool)

    def test_roundtrip_multiple_passwords(self):
        """Bcrypt limits passwords to 72 bytes — test within that bound."""
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            for pw in ["a", "long password with spaces!", "x" * 50]:
                h = mgr.generate_bcrypt_hash(pw)
                assert mgr.validate_bcrypt_pair(pw, h) is True
                assert mgr.validate_bcrypt_pair(pw + "x", h) is False


# ─── is_bcrypt_hash ─────────────────────────────────────────────────


class TestIsBcryptHash:
    def _mgr(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            return GenAIAuthManager(root_dir=Path(tmpdir))

    def test_2b_prefix(self):
        mgr = self._mgr()
        assert mgr.is_bcrypt_hash("$2b$12$somehashvalue") is True

    def test_2a_prefix(self):
        mgr = self._mgr()
        assert mgr.is_bcrypt_hash("$2a$10$somehashvalue") is True

    def test_2y_prefix(self):
        mgr = self._mgr()
        assert mgr.is_bcrypt_hash("$2y$12$somehashvalue") is True

    def test_no_prefix(self):
        mgr = self._mgr()
        assert mgr.is_bcrypt_hash("justastring") is False

    def test_empty_string(self):
        mgr = self._mgr()
        assert mgr.is_bcrypt_hash("") is False

    def test_none_like_empty(self):
        mgr = self._mgr()
        assert mgr.is_bcrypt_hash("") is False

    def test_wrong_prefix(self):
        mgr = self._mgr()
        assert mgr.is_bcrypt_hash("$2c$12$value") is False

    def test_generated_hash_is_detected(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            h = mgr.generate_bcrypt_hash("test")
            assert mgr.is_bcrypt_hash(h) is True


# ─── load_config ─────────────────────────────────────────────────────


class TestLoadConfig:
    def test_missing_file_returns_none(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            assert mgr.load_config() is None

    def test_valid_json_returns_dict(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            config = {"version": "1.0", "bcrypt_hash": "$2b$12$test"}
            mgr.config_file.write_text(json.dumps(config), encoding="utf-8")
            loaded = mgr.load_config()
            assert loaded == config

    def test_invalid_json_returns_none(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            mgr.config_file.write_text("{invalid", encoding="utf-8")
            assert mgr.load_config() is None

    def test_empty_object(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            mgr.config_file.write_text("{}", encoding="utf-8")
            loaded = mgr.load_config()
            assert loaded == {}


# ─── get_auth_header ────────────────────────────────────────────────


class TestGetAuthHeader:
    def test_no_config_raises_value_error(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            with pytest.raises(ValueError, match="Authentification non configur"):
                mgr.get_auth_header()

    def test_with_config_returns_bearer(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            config = {"version": "1.0", "bcrypt_hash": "$2b$12$testhash"}
            mgr.config_file.write_text(json.dumps(config), encoding="utf-8")
            header = mgr.get_auth_header()
            assert header["Authorization"] == "Bearer $2b$12$testhash"

    def test_content_type(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            config = {"version": "1.0", "bcrypt_hash": "hash123"}
            mgr.config_file.write_text(json.dumps(config), encoding="utf-8")
            header = mgr.get_auth_header()
            assert header["Content-Type"] == "application/json"

    def test_returns_dict(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            config = {"version": "1.0", "bcrypt_hash": "h"}
            mgr.config_file.write_text(json.dumps(config), encoding="utf-8")
            assert isinstance(mgr.get_auth_header(), dict)

    def test_missing_bcrypt_hash_raises(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            config = {"version": "1.0"}
            mgr.config_file.write_text(json.dumps(config), encoding="utf-8")
            with pytest.raises(ValueError):
                mgr.get_auth_header()


# ─── Cross-invariants ────────────────────────────────────────────────


class TestCrossInvariants:
    def test_generated_hash_is_valid_bcrypt(self):
        """generate_bcrypt_hash output passes validate_bcrypt_pair."""
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            pw = "cross_check_password"
            h = mgr.generate_bcrypt_hash(pw)
            assert mgr.validate_bcrypt_pair(pw, h) is True
            assert mgr.is_bcrypt_hash(h) is True

    def test_token_and_hash_different(self):
        """Secure token and bcrypt hash are different strings."""
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            token = mgr.generate_secure_token()
            h = mgr.generate_bcrypt_hash(token)
            assert token != h

    def test_config_roundtrip(self):
        """Write config -> load back same data."""
        with tempfile.TemporaryDirectory() as tmpdir:
            mgr = GenAIAuthManager(root_dir=Path(tmpdir))
            config = {"version": "1.0", "bcrypt_hash": "$2b$12$roundtrip"}
            mgr.config_file.write_text(json.dumps(config), encoding="utf-8")
            loaded = mgr.load_config()
            assert loaded["version"] == "1.0"
            assert loaded["bcrypt_hash"] == "$2b$12$roundtrip"

    def test_secrets_dir_constants_match(self):
        """SECRETS_DIR constant matches what GenAIAuthManager computes."""
        mgr = GenAIAuthManager()
        assert mgr.secrets_dir == SECRETS_DIR

    def test_audit_report_roundtrip_json(self):
        """AuditReport.to_dict() produces valid JSON with TokenLocation."""
        loc = TokenLocation(
            path="/test", type="raw", description="test",
            exists=True, content="abc", is_valid=True
        )
        report = AuditReport(
            timestamp="2026-05-30",
            locations=[loc],
            inconsistencies=[],
            recommendations=["test rec"],
        )
        serialized = json.dumps(report.to_dict())
        parsed = json.loads(serialized)
        assert parsed["locations"][0]["path"] == "/test"
        assert parsed["recommendations"][0] == "test rec"
