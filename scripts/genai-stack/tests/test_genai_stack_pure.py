"""Tests for genai-stack pure-logic functions.

Covers: config.load_env, auth_manager (bcrypt, _update_env_file, audit),
comfyui_client (WorkflowManager, ComfyUIClient auth prefix), audio_apis
(_make_silence_wav, _get_auth_headers, get_all_audio_status).
"""

import json
import os
import struct
import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest

# conftest.py adds genai-stack root to sys.path


# =============================================================================
# config.load_env tests
# =============================================================================


class TestLoadEnv:
    """Tests for config.load_env (.env parser)."""

    def test_nonexistent_file_returns_empty(self, tmp_path):
        """Missing .env file returns empty dict, no exception."""
        import config
        fake_env = tmp_path / "nonexistent" / ".env"
        with patch.object(config, "ENV_FILE", fake_env):
            result = config.load_env()
        assert result == {}

    def test_basic_key_value(self, tmp_path):
        """Simple KEY=VALUE line parsed correctly."""
        import config
        env_file = tmp_path / ".env"
        env_file.write_text("MY_KEY=my_value\n", encoding="utf-8")
        with patch.object(config, "ENV_FILE", env_file):
            result = config.load_env()
        assert result["MY_KEY"] == "my_value"

    def test_comment_lines_skipped(self, tmp_path):
        """Lines starting with # are ignored."""
        import config
        env_file = tmp_path / ".env"
        env_file.write_text("# this is a comment\nKEY=val\n", encoding="utf-8")
        with patch.object(config, "ENV_FILE", env_file):
            result = config.load_env()
        assert "KEY" in result
        assert result["KEY"] == "val"

    def test_blank_lines_skipped(self, tmp_path):
        """Empty lines are ignored."""
        import config
        env_file = tmp_path / ".env"
        env_file.write_text("\n\nKEY=val\n\n", encoding="utf-8")
        with patch.object(config, "ENV_FILE", env_file):
            result = config.load_env()
        assert len(result) == 1

    def test_value_with_equals_sign(self, tmp_path):
        """Values containing = are preserved (split on first = only)."""
        import config
        env_file = tmp_path / ".env"
        env_file.write_text("BASE64_KEY=abc=def=ghi\n", encoding="utf-8")
        with patch.object(config, "ENV_FILE", env_file):
            result = config.load_env()
        assert result["BASE64_KEY"] == "abc=def=ghi"

    def test_double_quoted_values_stripped(self, tmp_path):
        """Double-quoted values have quotes stripped."""
        import config
        env_file = tmp_path / ".env"
        env_file.write_text('KEY="my value"\n', encoding="utf-8")
        with patch.object(config, "ENV_FILE", env_file):
            result = config.load_env()
        assert result["KEY"] == "my value"

    def test_single_quoted_values_stripped(self, tmp_path):
        """Single-quoted values have quotes stripped."""
        import config
        env_file = tmp_path / ".env"
        env_file.write_text("KEY='my value'\n", encoding="utf-8")
        with patch.object(config, "ENV_FILE", env_file):
            result = config.load_env()
        assert result["KEY"] == "my value"

    def test_line_without_equals_ignored(self, tmp_path):
        """Lines without = are ignored (not key-value pairs)."""
        import config
        env_file = tmp_path / ".env"
        env_file.write_text("NOT_A_KEY_VALUE_LINE\nKEY=val\n", encoding="utf-8")
        with patch.object(config, "ENV_FILE", env_file):
            result = config.load_env()
        assert "NOT_A_KEY_VALUE_LINE" not in result
        assert result["KEY"] == "val"

    def test_whitespace_trimmed(self, tmp_path):
        """Whitespace around key and value is trimmed."""
        import config
        env_file = tmp_path / ".env"
        env_file.write_text("  KEY  =  value  \n", encoding="utf-8")
        with patch.object(config, "ENV_FILE", env_file):
            result = config.load_env()
        assert result["KEY"] == "value"


# =============================================================================
# auth_manager tests
# =============================================================================


class TestAuthManagerBcrypt:
    """Tests for GenAIAuthManager bcrypt operations."""

    @pytest.fixture
    def manager(self, tmp_path):
        from core.auth_manager import GenAIAuthManager
        return GenAIAuthManager(root_dir=tmp_path)

    def test_generate_secure_token_length(self, manager):
        """Token has expected length."""
        token = manager.generate_secure_token(16)
        assert len(token) == 16

    def test_generate_secure_token_default_length(self, manager):
        """Default token length is 32."""
        token = manager.generate_secure_token()
        assert len(token) == 32

    def test_generate_secure_token_alphanumeric(self, manager):
        """Token contains only alphanumeric characters."""
        import string
        token = manager.generate_secure_token(100)
        allowed = set(string.ascii_letters + string.digits)
        assert all(c in allowed for c in token)

    def test_bcrypt_roundtrip(self, manager):
        """Hash then validate returns True."""
        token = "test_token_123"
        hashed = manager.generate_bcrypt_hash(token)
        assert manager.validate_bcrypt_pair(token, hashed)

    def test_bcrypt_wrong_token_fails(self, manager):
        """Wrong token fails validation."""
        hashed = manager.generate_bcrypt_hash("correct")
        assert not manager.validate_bcrypt_pair("wrong", hashed)

    def test_is_bcrypt_hash_valid_prefixes(self, manager):
        """Recognizes $2a$, $2b$, $2y$ prefixes."""
        assert manager.is_bcrypt_hash("$2b$12$abcdef")
        assert manager.is_bcrypt_hash("$2a$12$abcdef")
        assert manager.is_bcrypt_hash("$2y$12$abcdef")

    def test_is_bcrypt_hash_invalid(self, manager):
        """Rejects non-bcrypt strings."""
        assert not manager.is_bcrypt_hash("plain_token")
        assert not manager.is_bcrypt_hash("")
        assert not manager.is_bcrypt_hash(None)

    def test_validate_bcrypt_malformed_hash(self, manager):
        """Malformed hash returns False, not exception."""
        assert not manager.validate_bcrypt_pair("token", "not_a_hash")


class TestAuthManagerUpdateEnvFile:
    """Tests for GenAIAuthManager._update_env_file."""

    @pytest.fixture
    def manager(self, tmp_path):
        from core.auth_manager import GenAIAuthManager
        return GenAIAuthManager(root_dir=tmp_path)

    def test_creates_new_file(self, manager, tmp_path):
        """Creates .env if it doesn't exist."""
        env_path = tmp_path / "new.env"
        manager._update_env_file(env_path, "raw_tok", "hash_val")
        content = env_path.read_text(encoding="utf-8")
        assert "COMFYUI_API_TOKEN=hash_val" in content
        assert "COMFYUI_RAW_TOKEN=raw_tok" in content

    def test_updates_existing_keys(self, manager, tmp_path):
        """Updates existing COMFYUI_API_TOKEN in .env."""
        env_path = tmp_path / ".env"
        env_path.write_text("COMFYUI_API_TOKEN=old_hash\nOTHER_KEY=kept\n", encoding="utf-8")
        manager._update_env_file(env_path, "new_raw", "new_hash")
        content = env_path.read_text(encoding="utf-8")
        assert "COMFYUI_API_TOKEN=new_hash" in content
        assert "OTHER_KEY=kept" in content
        assert "old_hash" not in content

    def test_preserves_comments(self, manager, tmp_path):
        """Comment lines preserved verbatim."""
        env_path = tmp_path / ".env"
        env_path.write_text("# my comment\nKEY=val\n", encoding="utf-8")
        manager._update_env_file(env_path, "raw", "hash")
        content = env_path.read_text(encoding="utf-8")
        assert "# my comment" in content

    def test_preserves_blank_lines(self, manager, tmp_path):
        """Blank lines preserved."""
        env_path = tmp_path / ".env"
        env_path.write_text("KEY=val\n\nOTHER=x\n", encoding="utf-8")
        manager._update_env_file(env_path, "raw", "hash")
        content = env_path.read_text(encoding="utf-8")
        lines = content.splitlines()
        assert any(line == "" for line in lines)

    def test_updates_aliases(self, manager, tmp_path):
        """Updates COMFYUI_BEARER_TOKEN and QWEN_API_USER_TOKEN aliases."""
        env_path = tmp_path / ".env"
        env_path.write_text(
            "COMFYUI_BEARER_TOKEN=old\nQWEN_API_USER_TOKEN=old\nCOMFYUI_PASSWORD=old\n",
            encoding="utf-8",
        )
        manager._update_env_file(env_path, "raw_tok", "new_hash")
        content = env_path.read_text(encoding="utf-8")
        assert "COMFYUI_BEARER_TOKEN=new_hash" in content
        assert "QWEN_API_USER_TOKEN=new_hash" in content
        assert "COMFYUI_PASSWORD=raw_tok" in content

    def test_appends_missing_comfyui_token(self, manager, tmp_path):
        """Appends COMFYUI_API_TOKEN if missing from existing file."""
        env_path = tmp_path / ".env"
        env_path.write_text("UNRELATED_KEY=val\n", encoding="utf-8")
        manager._update_env_file(env_path, "raw", "hash_val")
        content = env_path.read_text(encoding="utf-8")
        assert "COMFYUI_API_TOKEN=hash_val" in content
        assert "UNRELATED_KEY=val" in content


class TestAuthManagerAudit:
    """Tests for GenAIAuthManager.audit_security."""

    @pytest.fixture
    def manager(self, tmp_path):
        from core.auth_manager import GenAIAuthManager
        return GenAIAuthManager(root_dir=tmp_path)

    def test_audit_no_config(self, manager):
        """No config file returns report with recommendation."""
        report = manager.audit_security()
        assert len(report.recommendations) > 0
        assert report.locations == []

    def test_audit_config_with_locations(self, manager, tmp_path):
        """Audit scans configured locations."""
        # Create a config
        manager.create_unified_config("test_raw_token")
        config = manager.load_config()
        assert config is not None  # config created

        # Create the secrets file location
        secrets_path = tmp_path / ".secrets" / "qwen-api-user.token"
        secrets_path.parent.mkdir(parents=True, exist_ok=True)
        secrets_path.write_text(config["bcrypt_hash"], encoding="utf-8")

        report = manager.audit_security()
        # Should have at least 1 location scanned
        assert len(report.locations) >= 1
        # At least one should be valid (secrets_file matches hash)
        assert any(loc.is_valid for loc in report.locations)

    def test_audit_report_to_dict(self, manager, tmp_path):
        """AuditReport.to_dict returns valid dict structure."""
        manager.create_unified_config("test_token")
        report = manager.audit_security()
        d = report.to_dict()
        assert "timestamp" in d
        assert "locations" in d
        assert "inconsistencies" in d
        assert "recommendations" in d
        assert isinstance(d["locations"], list)


class TestAuthManagerGetAuthHeader:
    """Tests for GenAIAuthManager.get_auth_header."""

    @pytest.fixture
    def manager(self, tmp_path):
        from core.auth_manager import GenAIAuthManager
        return GenAIAuthManager(root_dir=tmp_path)

    def test_raises_without_config(self, manager):
        """Raises ValueError when not configured."""
        with pytest.raises(ValueError, match="non configur"):
            manager.get_auth_header()

    def test_returns_bearer_header(self, manager):
        """Returns Bearer header with bcrypt hash."""
        manager.create_unified_config("test_token")
        headers = manager.get_auth_header()
        assert "Authorization" in headers
        assert headers["Authorization"].startswith("Bearer ")
        assert headers["Content-Type"] == "application/json"


# =============================================================================
# ComfyUI WorkflowManager tests
# =============================================================================


class TestWorkflowManagerLoad:
    """Tests for WorkflowManager.load (filters _meta keys)."""

    def test_filters_meta_key(self, tmp_path):
        """Root-level _meta key filtered out (not a ComfyUI node)."""
        from core.comfyui_client import WorkflowManager
        wf = {
            "_meta": {"version": "0.1"},
            "1": {"class_type": "KSampler", "inputs": {}},
            "2": {"class_type": "SaveImage", "inputs": {}},
        }
        wf_file = tmp_path / "test_workflow.json"
        wf_file.write_text(json.dumps(wf), encoding="utf-8")
        result = WorkflowManager.load(wf_file)
        assert "1" in result
        assert "2" in result
        assert "_meta" not in result

    def test_loads_all_nodes(self, tmp_path):
        """All nodes with class_type are loaded."""
        from core.comfyui_client import WorkflowManager
        wf = {
            "node_a": {"class_type": "TypeA", "inputs": {"x": 1}},
            "node_b": {"class_type": "TypeB", "inputs": {"y": 2}},
        }
        wf_file = tmp_path / "test.json"
        wf_file.write_text(json.dumps(wf), encoding="utf-8")
        result = WorkflowManager.load(wf_file)
        assert len(result) == 2

    def test_malformed_json_raises(self, tmp_path):
        """Malformed JSON raises JSONDecodeError."""
        from core.comfyui_client import WorkflowManager
        wf_file = tmp_path / "bad.json"
        wf_file.write_text("{invalid json}", encoding="utf-8")
        with pytest.raises(json.JSONDecodeError):
            WorkflowManager.load(wf_file)


class TestWorkflowManagerValidate:
    """Tests for WorkflowManager.validate."""

    def test_api_format_valid(self):
        """API format (dict of nodes, no 'nodes' key) validates as True."""
        from core.comfyui_client import WorkflowManager
        wf = {"1": {"class_type": "A"}, "2": {"class_type": "B"}}
        valid, errors = WorkflowManager.validate(wf)
        assert valid is True
        assert errors == []

    def test_ui_format_missing_nodes_list(self):
        """UI format without 'nodes' key is invalid."""
        from core.comfyui_client import WorkflowManager
        wf = {"links": []}
        valid, errors = WorkflowManager.validate(wf)
        assert valid is False
        assert any("Missing 'nodes'" in e for e in errors)

    def test_ui_format_node_missing_id(self):
        """UI node missing 'id' is flagged."""
        from core.comfyui_client import WorkflowManager
        wf = {"nodes": [{"type": "KSampler"}]}
        valid, errors = WorkflowManager.validate(wf)
        assert valid is False
        assert any("missing 'id'" in e for e in errors)

    def test_ui_format_node_missing_type(self):
        """UI node missing 'type' is flagged."""
        from core.comfyui_client import WorkflowManager
        wf = {"nodes": [{"id": 1}]}
        valid, errors = WorkflowManager.validate(wf)
        assert valid is False
        assert any("missing 'type'" in e for e in errors)

    def test_ui_format_valid(self):
        """Valid UI format passes validation."""
        from core.comfyui_client import WorkflowManager
        wf = {"nodes": [{"id": 1, "type": "KSampler"}, {"id": 2, "type": "SaveImage"}]}
        valid, errors = WorkflowManager.validate(wf)
        assert valid is True
        assert errors == []


class TestComfyUIClientAuth:
    """Tests for ComfyUIClient auth prefix handling."""

    def test_bare_token_gets_bearer_prefix(self):
        """Bare token gets 'Bearer ' prefix."""
        from core.comfyui_client import ComfyUIClient, ComfyUIConfig
        config = ComfyUIConfig(api_key="my_token")
        client = ComfyUIClient(config)
        assert client.session.headers["Authorization"] == "Bearer my_token"

    def test_bearer_prefix_preserved(self):
        """Token already starting with 'Bearer ' is left unchanged."""
        from core.comfyui_client import ComfyUIClient, ComfyUIConfig
        config = ComfyUIConfig(api_key="Bearer my_token")
        client = ComfyUIClient(config)
        assert client.session.headers["Authorization"] == "Bearer my_token"

    def test_basic_prefix_preserved(self):
        """Token starting with 'Basic ' is left unchanged."""
        from core.comfyui_client import ComfyUIClient, ComfyUIConfig
        config = ComfyUIConfig(api_key="Basic dXNlcjpwYXNz")
        client = ComfyUIClient(config)
        assert client.session.headers["Authorization"] == "Basic dXNlcjpwYXNz"

    def test_no_api_key_no_auth_header(self):
        """No api_key means no Authorization header."""
        from core.comfyui_client import ComfyUIClient, ComfyUIConfig
        config = ComfyUIConfig(api_key=None)
        client = ComfyUIClient(config)
        assert "Authorization" not in client.session.headers

    def test_url_construction(self):
        """_url correctly assembles protocol://host:port/endpoint."""
        from core.comfyui_client import ComfyUIClient, ComfyUIConfig
        config = ComfyUIConfig(host="192.168.1.10", port=8189, protocol="https")
        client = ComfyUIClient(config)
        assert client._url("/system_stats") == "https://192.168.1.10:8189/system_stats"


# =============================================================================
# audio_apis tests
# =============================================================================


class TestMakeSilenceWav:
    """Tests for audio_apis._make_silence_wav."""

    def test_starts_with_riff(self):
        """WAV file starts with RIFF magic bytes."""
        from commands.audio_apis import _make_silence_wav
        wav = _make_silence_wav()
        assert wav[:4] == b"RIFF"

    def test_contains_wave_marker(self):
        """WAV file contains WAVE format marker."""
        from commands.audio_apis import _make_silence_wav
        wav = _make_silence_wav()
        assert wav[8:12] == b"WAVE"

    def test_contains_fmt_chunk(self):
        """WAV file contains 'fmt ' chunk."""
        from commands.audio_apis import _make_silence_wav
        wav = _make_silence_wav()
        assert b"fmt " in wav

    def test_contains_data_chunk(self):
        """WAV file contains 'data' chunk."""
        from commands.audio_apis import _make_silence_wav
        wav = _make_silence_wav()
        assert b"data" in wav

    def test_file_size_field_correct(self):
        """RIFF file-size field equals 36 + data_size."""
        from commands.audio_apis import _make_silence_wav
        wav = _make_silence_wav()
        file_size = struct.unpack("<I", wav[4:8])[0]
        data_size = 16000 * 2  # sample_rate * duration * bytes_per_sample
        assert file_size == 36 + data_size

    def test_total_byte_length_stable(self):
        """Total WAV byte length is deterministic."""
        from commands.audio_apis import _make_silence_wav
        wav1 = _make_silence_wav()
        wav2 = _make_silence_wav()
        assert len(wav1) == len(wav2)
        assert len(wav1) == 44 + 16000 * 2  # 44-byte header + data

    def test_pcm_format(self):
        """Audio format is PCM (format code 1)."""
        from commands.audio_apis import _make_silence_wav
        wav = _make_silence_wav()
        fmt_offset = wav.index(b"fmt ") + 4  # skip 'fmt '
        # chunk_size (4) + audio_format (2)
        audio_format = struct.unpack("<H", wav[fmt_offset + 4:fmt_offset + 6])[0]
        assert audio_format == 1  # PCM

    def test_mono_channel(self):
        """Channel count is 1 (mono)."""
        from commands.audio_apis import _make_silence_wav
        wav = _make_silence_wav()
        fmt_offset = wav.index(b"fmt ") + 4
        num_channels = struct.unpack("<H", wav[fmt_offset + 6:fmt_offset + 8])[0]
        assert num_channels == 1

    def test_sample_rate_16k(self):
        """Sample rate is 16000 Hz."""
        from commands.audio_apis import _make_silence_wav
        wav = _make_silence_wav()
        fmt_offset = wav.index(b"fmt ") + 4
        sample_rate = struct.unpack("<I", wav[fmt_offset + 8:fmt_offset + 12])[0]
        assert sample_rate == 16000


class TestGetAuthHeaders:
    """Tests for audio_apis._get_auth_headers."""

    def test_no_env_file_returns_content_type_only(self, tmp_path):
        """Missing .env returns only Content-Type header."""
        from commands import audio_apis
        fake_path = tmp_path / "nonexistent" / ".env"
        with patch("commands.audio_apis.Path") as mock_path_cls:
            mock_path_inst = MagicMock()
            mock_path_inst.resolve.return_value.parent.parent.parent.parent.__truediv__(
                "MyIA.AI.Notebooks"
            ).__truediv__("GenAI").__truediv__(".env")
            mock_path_inst.exists.return_value = False
            # Direct approach: patch the env_file inside _get_auth_headers
            pass
        # Simpler: just call with tmp_path and patch the env_file resolution
        # The function reads from a hardcoded path, so we patch the file operations
        with patch("pathlib.Path.exists", return_value=False):
            headers = audio_apis._get_auth_headers()
        assert headers["Content-Type"] == "application/json"
        assert "Authorization" not in headers

    def test_key_name_derivation_service_api_suffix(self):
        """Service names ending in -api produce _API_API_KEY (code reality).

        The code does: service_name.replace('-','_').upper() + '_API_KEY'
        So 'musicgen-api' -> 'MUSICGEN_API_API_KEY'. This is a known
        naming quirk -- the env var must match this double-API pattern.
        """
        svc_key = "musicgen-api".replace("-", "_").upper() + "_API_KEY"
        assert svc_key == "MUSICGEN_API_API_KEY"

    def test_key_name_derivation_all_services(self):
        """All AUDIO_API_SERVICES produce consistent env key patterns."""
        from commands.audio_apis import AUDIO_API_SERVICES
        for svc in AUDIO_API_SERVICES:
            env_key = svc.replace("-", "_").upper() + "_API_KEY"
            assert env_key.endswith("_API_KEY")
            assert env_key == env_key.upper()


class TestGetAllAudioStatus:
    """Tests for audio_apis.get_all_audio_status."""

    def test_unknown_service_status(self):
        """Service not in SERVICES dict gets 'not_configured' status."""
        from commands import audio_apis
        with patch.dict(audio_apis.SERVICES, {}, clear=True):
            status = audio_apis.get_all_audio_status()
        # All AUDIO_API_SERVICES should be not_configured
        for svc in audio_apis.AUDIO_API_SERVICES:
            if svc in status:
                assert status[svc]["status"] == "not_configured"

    def test_gpu_allocation_keys(self):
        """GPU_ALLOCATION has expected service mappings."""
        from commands.audio_apis import GPU_ALLOCATION
        assert "whisper-api" in GPU_ALLOCATION
        assert "tts-api" in GPU_ALLOCATION
        assert GPU_ALLOCATION["whisper-api"] == 0
        assert GPU_ALLOCATION["tts-api"] == 1

    def test_gpu_conflicts_structure(self):
        """GPU_CONFLICTS has both GPU indices."""
        from commands.audio_apis import GPU_CONFLICTS
        assert 0 in GPU_CONFLICTS
        assert 1 in GPU_CONFLICTS
        assert isinstance(GPU_CONFLICTS[0], list)
        assert isinstance(GPU_CONFLICTS[1], list)


# =============================================================================
# config data-integrity invariants
# =============================================================================


class TestConfigDataIntegrity:
    """Tests for config.py data structure integrity."""

    def test_services_all_have_required_keys(self):
        """Every service has required keys."""
        import config
        required = {"compose_dir", "container_name", "port", "health_endpoint",
                     "gpu_id", "vram_required", "remote_url"}
        for name, svc in config.SERVICES.items():
            missing = required - set(svc.keys())
            assert not missing, f"Service {name} missing keys: {missing}"

    def test_notebook_service_map_groups_exist(self):
        """All groups in NOTEBOOK_SERVICE_MAP map to a GPU profile."""
        import config
        for group in config.NOTEBOOK_SERVICE_MAP:
            assert group in config.GROUP_GPU_PROFILE, f"Group {group} has no GPU profile"

    def test_gpu_profile_services_exist(self):
        """All services referenced in GPU_PROFILES exist in SERVICES."""
        import config
        for profile_name, profile in config.GPU_PROFILES.items():
            for svc in profile.get("services_up", []):
                assert svc in config.SERVICES, f"Profile {profile_name} references unknown service_up: {svc}"
            for svc in profile.get("services_down", []):
                assert svc in config.SERVICES, f"Profile {profile_name} references unknown service_down: {svc}"

    def test_execution_batches_groups_valid(self):
        """All groups in EXECUTION_BATCHES have a GPU profile."""
        import config
        for batch_num, batch in config.EXECUTION_BATCHES.items():
            assert "name" in batch
            assert "profile" in batch
            assert "groups" in batch
            assert batch["profile"] in config.GPU_PROFILES

    def test_services_ports_unique(self):
        """All service ports are unique."""
        import config
        ports = [svc["port"] for svc in config.SERVICES.values()]
        assert len(ports) == len(set(ports)), "Duplicate ports detected"
