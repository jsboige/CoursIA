"""Tests for scripts/genai-stack/core/auth_manager.py — GenAI authentication manager.

Tests focus on pure methods: token generation, bcrypt validation, hash detection,
config load/create. Filesystem methods use tmp_path for isolation.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "genai-stack" / "core"))
from auth_manager import GenAIAuthManager, TokenLocation, AuditReport


# ---------------------------------------------------------------------------
# generate_secure_token
# ---------------------------------------------------------------------------

class TestGenerateSecureToken:
    def test_default_length(self):
        mgr = GenAIAuthManager(root_dir=Path("dummy"))
        token = mgr.generate_secure_token()
        assert len(token) == 32

    def test_custom_length(self):
        mgr = GenAIAuthManager(root_dir=Path("dummy"))
        token = mgr.generate_secure_token(64)
        assert len(token) == 64

    def test_alphanumeric_only(self):
        mgr = GenAIAuthManager(root_dir=Path("dummy"))
        token = mgr.generate_secure_token(100)
        assert token.isalnum()

    def test_unique_tokens(self):
        mgr = GenAIAuthManager(root_dir=Path("dummy"))
        tokens = {mgr.generate_secure_token() for _ in range(20)}
        assert len(tokens) == 20  # All unique


# ---------------------------------------------------------------------------
# is_bcrypt_hash
# ---------------------------------------------------------------------------

class TestIsBcryptHash:
    def test_2b_prefix(self):
        mgr = GenAIAuthManager(root_dir=Path("dummy"))
        assert mgr.is_bcrypt_hash("$2b$12$somehash") is True

    def test_2a_prefix(self):
        mgr = GenAIAuthManager(root_dir=Path("dummy"))
        assert mgr.is_bcrypt_hash("$2a$10$abc") is True

    def test_2y_prefix(self):
        mgr = GenAIAuthManager(root_dir=Path("dummy"))
        assert mgr.is_bcrypt_hash("$2y$12$xyz") is True

    def test_plain_string(self):
        mgr = GenAIAuthManager(root_dir=Path("dummy"))
        assert mgr.is_bcrypt_hash("just-a-token") is False

    def test_empty_string(self):
        mgr = GenAIAuthManager(root_dir=Path("dummy"))
        assert mgr.is_bcrypt_hash("") is False

    def test_none_returns_false(self):
        mgr = GenAIAuthManager(root_dir=Path("dummy"))
        assert mgr.is_bcrypt_hash(None) is False


# ---------------------------------------------------------------------------
# validate_bcrypt_pair
# ---------------------------------------------------------------------------

class TestValidateBcryptPair:
    def test_valid_pair(self):
        mgr = GenAIAuthManager(root_dir=Path("dummy"))
        password = "test-password-123"
        hashed = mgr.generate_bcrypt_hash(password)
        assert mgr.validate_bcrypt_pair(password, hashed) is True

    def test_wrong_password(self):
        mgr = GenAIAuthManager(root_dir=Path("dummy"))
        hashed = mgr.generate_bcrypt_hash("correct")
        assert mgr.validate_bcrypt_pair("wrong", hashed) is False

    def test_invalid_hash(self):
        mgr = GenAIAuthManager(root_dir=Path("dummy"))
        assert mgr.validate_bcrypt_pair("test", "not-a-hash") is False


# ---------------------------------------------------------------------------
# generate_bcrypt_hash
# ---------------------------------------------------------------------------

class TestGenerateBcryptHash:
    def test_produces_bcrypt_format(self):
        mgr = GenAIAuthManager(root_dir=Path("dummy"))
        hashed = mgr.generate_bcrypt_hash("password")
        assert hashed.startswith("$2b$")
        assert len(hashed) == 60

    def test_different_hashes_for_same_password(self):
        mgr = GenAIAuthManager(root_dir=Path("dummy"))
        h1 = mgr.generate_bcrypt_hash("same")
        h2 = mgr.generate_bcrypt_hash("same")
        assert h1 != h2  # Different salts


# ---------------------------------------------------------------------------
# load_config / create_unified_config
# ---------------------------------------------------------------------------

class TestConfigManagement:
    def test_load_missing_config(self, tmp_path):
        mgr = GenAIAuthManager(root_dir=tmp_path)
        assert mgr.load_config() is None

    def test_create_and_load(self, tmp_path):
        mgr = GenAIAuthManager(root_dir=tmp_path)
        assert mgr.create_unified_config("test-token-123") is True
        config = mgr.load_config()
        assert config is not None
        assert config["raw_token"] == "test-token-123"
        assert "bcrypt_hash" in config

    def test_create_generates_token(self, tmp_path):
        mgr = GenAIAuthManager(root_dir=tmp_path)
        assert mgr.create_unified_config() is True
        config = mgr.load_config()
        assert config["raw_token"]  # Auto-generated
        assert len(config["raw_token"]) == 32

    def test_secrets_dir_created(self, tmp_path):
        mgr = GenAIAuthManager(root_dir=tmp_path)
        mgr.create_unified_config("tok")
        assert mgr.secrets_dir.exists()

    def test_load_invalid_json(self, tmp_path):
        mgr = GenAIAuthManager(root_dir=tmp_path)
        mgr.config_file.write_text("{invalid json!!!", encoding="utf-8")
        assert mgr.load_config() is None


# ---------------------------------------------------------------------------
# Dataclasses
# ---------------------------------------------------------------------------

class TestTokenLocation:
    def test_defaults(self):
        loc = TokenLocation(path="/test", type="raw", description="test")
        assert loc.exists is False
        assert loc.content is None
        assert loc.is_valid is False

class TestAuditReport:
    def test_to_dict(self):
        report = AuditReport(
            timestamp="2026-01-01",
            locations=[TokenLocation(path="/a", type="bcrypt", description="test")],
            inconsistencies=[],
            recommendations=[],
        )
        d = report.to_dict()
        assert d["timestamp"] == "2026-01-01"
        assert len(d["locations"]) == 1
        assert "path" in d["locations"][0]
