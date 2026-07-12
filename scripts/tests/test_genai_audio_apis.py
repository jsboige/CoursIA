"""Tests for scripts/genai-stack/commands/audio_apis.py — static config and pure helpers.

Tests cover testable pure logic: AUDIO_API_SERVICES, GPU_ALLOCATION, GPU_CONFLICTS
(static constants), _make_silence_wav (binary WAV generation), _get_auth_headers
(env-based token loading). Network/Docker functions (get_container_status,
start_service, switch_to_service, test_service, e2e_test_service, etc.) are
excluded — they require live Docker containers and HTTP endpoints.
"""

import struct
import sys
from pathlib import Path
from unittest.mock import patch

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "genai-stack"))
from commands.audio_apis import (
    AUDIO_API_SERVICES,
    GPU_ALLOCATION,
    GPU_CONFLICTS,
    _get_auth_headers,
    _make_silence_wav,
)


# ---------------------------------------------------------------------------
# AUDIO_API_SERVICES constant
# ---------------------------------------------------------------------------


class TestAudioApiServices:
    """Tests for the AUDIO_API_SERVICES list."""

    def test_is_list(self):
        """AUDIO_API_SERVICES is a list."""
        assert isinstance(AUDIO_API_SERVICES, list)

    def test_contains_expected_services(self):
        """Contains the 5 known audio API services."""
        expected = {"whisper-api", "tts-api", "musicgen-api", "demucs-api", "funasr-api"}
        assert set(AUDIO_API_SERVICES) == expected

    def test_count(self):
        """Has exactly 5 services."""
        assert len(AUDIO_API_SERVICES) == 5

    def test_all_strings(self):
        """All entries are strings."""
        assert all(isinstance(s, str) for s in AUDIO_API_SERVICES)

    def test_no_duplicates(self):
        """No duplicate service names."""
        assert len(AUDIO_API_SERVICES) == len(set(AUDIO_API_SERVICES))


# ---------------------------------------------------------------------------
# GPU_ALLOCATION constant
# ---------------------------------------------------------------------------


class TestGpuAllocation:
    """Tests for the GPU_ALLOCATION mapping."""

    def test_is_dict(self):
        """GPU_ALLOCATION is a dict."""
        assert isinstance(GPU_ALLOCATION, dict)

    def test_gpu_ids_are_integers(self):
        """All GPU IDs are integers."""
        for svc, gpu_id in GPU_ALLOCATION.items():
            assert isinstance(gpu_id, int), f"{svc} has non-int GPU ID: {gpu_id}"

    def test_covers_all_except_funasr(self):
        """All AUDIO_API_SERVICES except funasr-api have GPU allocation."""
        for svc in AUDIO_API_SERVICES:
            if svc == "funasr-api":
                assert svc not in GPU_ALLOCATION
            else:
                assert svc in GPU_ALLOCATION, f"{svc} missing from GPU_ALLOCATION"

    def test_whisper_and_demucs_on_same_gpu(self):
        """whisper-api and demucs-api share GPU 0."""
        assert GPU_ALLOCATION["whisper-api"] == GPU_ALLOCATION["demucs-api"]

    def test_tts_and_musicgen_on_same_gpu(self):
        """tts-api and musicgen-api share GPU 1."""
        assert GPU_ALLOCATION["tts-api"] == GPU_ALLOCATION["musicgen-api"]

    def test_two_distinct_gpus(self):
        """Services span exactly 2 distinct GPU IDs."""
        gpu_ids = set(GPU_ALLOCATION.values())
        assert len(gpu_ids) == 2


# ---------------------------------------------------------------------------
# GPU_CONFLICTS constant
# ---------------------------------------------------------------------------


class TestGpuConflicts:
    """Tests for the GPU_CONFLICTS mapping."""

    def test_is_dict(self):
        """GPU_CONFLICTS is a dict."""
        assert isinstance(GPU_CONFLICTS, dict)

    def test_keys_are_integers(self):
        """GPU IDs in keys are integers."""
        for gpu_id in GPU_CONFLICTS:
            assert isinstance(gpu_id, int)

    def test_values_are_lists(self):
        """Each GPU maps to a list of conflicting services."""
        for gpu_id, services in GPU_CONFLICTS.items():
            assert isinstance(services, list)

    def test_audio_services_in_conflicts(self):
        """Allocated audio services appear in their GPU's conflict list."""
        for svc, gpu_id in GPU_ALLOCATION.items():
            assert svc in GPU_CONFLICTS[gpu_id], f"{svc} not in GPU_CONFLICTS[{gpu_id}]"

    def test_all_entries_are_strings(self):
        """All conflict list entries are strings."""
        for services in GPU_CONFLICTS.values():
            for svc in services:
                assert isinstance(svc, str)

    def test_no_empty_conflict_lists(self):
        """No GPU has an empty conflict list."""
        for gpu_id, services in GPU_CONFLICTS.items():
            assert len(services) > 0, f"GPU {gpu_id} has empty conflict list"


# ---------------------------------------------------------------------------
# _make_silence_wav
# ---------------------------------------------------------------------------


class TestMakeSilenceWav:
    """Tests for _make_silence_wav pure helper."""

    def test_returns_bytes(self):
        """Returns a bytes object."""
        result = _make_silence_wav()
        assert isinstance(result, bytes)

    def test_riff_header(self):
        """Starts with RIFF header."""
        result = _make_silence_wav()
        assert result[:4] == b"RIFF"

    def test_wave_marker(self):
        """Contains WAVE marker at offset 8."""
        result = _make_silence_wav()
        assert result[8:12] == b"WAVE"

    def test_file_size_correct(self):
        """File size field matches actual data."""
        result = _make_silence_wav()
        declared_size = struct.unpack("<I", result[4:8])[0]
        assert declared_size == len(result) - 8

    def test_data_chunk_size(self):
        """Data chunk size = sample_rate * duration * bytes_per_sample."""
        result = _make_silence_wav()
        data_size = struct.unpack("<I", result[40:44])[0]
        expected = 16000 * 1 * 2  # 16kHz, 1s, 16-bit
        assert data_size == expected

    def test_total_size(self):
        """Total file size = 44 header bytes + data."""
        result = _make_silence_wav()
        assert len(result) == 44 + 16000 * 1 * 2

    def test_silence_content(self):
        """All audio data bytes are zero (silence)."""
        result = _make_silence_wav()
        data = result[44:]
        assert data == b"\x00" * len(data)

    def test_pcm_format(self):
        """Audio format is PCM (value 1)."""
        result = _make_silence_wav()
        audio_format = struct.unpack("<H", result[20:22])[0]
        assert audio_format == 1

    def test_mono_channel(self):
        """Number of channels is 1 (mono)."""
        result = _make_silence_wav()
        num_channels = struct.unpack("<H", result[22:24])[0]
        assert num_channels == 1

    def test_sample_rate_16khz(self):
        """Sample rate is 16000 Hz."""
        result = _make_silence_wav()
        sample_rate = struct.unpack("<I", result[24:28])[0]
        assert sample_rate == 16000

    def test_bits_per_sample_16(self):
        """Bits per sample is 16."""
        result = _make_silence_wav()
        bits = struct.unpack("<H", result[34:36])[0]
        assert bits == 16

    def test_deterministic(self):
        """Calling twice produces identical output."""
        assert _make_silence_wav() == _make_silence_wav()


# ---------------------------------------------------------------------------
# _get_auth_headers
# ---------------------------------------------------------------------------


class TestGetAuthHeaders:
    """Tests for _get_auth_headers env-based token loader."""

    def test_returns_dict(self):
        """Returns a dictionary."""
        result = _get_auth_headers()
        assert isinstance(result, dict)

    def test_content_type_header(self):
        """Always includes Content-Type header."""
        result = _get_auth_headers()
        assert result["Content-Type"] == "application/json"

    def test_no_auth_without_env(self):
        """Without env vars or files, no Authorization header."""
        with patch.dict("os.environ", {}, clear=True), \
             patch.object(Path, "exists", return_value=False):
            result = _get_auth_headers()
            assert "Authorization" not in result

    def _mock_env_file(self, content: str):
        """Create a mock that patches the .env file read inside _get_auth_headers.

        The function constructs a Path to MyIA.AI.Notebooks/GenAI/.env and checks
        exists() then read_text(). We mock exists() to return True for that path
        and read_text() to return our content.
        """
        original_exists = Path.exists
        original_read_text = Path.read_text

        def patched_exists(self_path):
            if str(self_path).endswith("GenAI" + "\\" + ".env") or str(self_path).endswith("GenAI/.env"):
                return True
            return original_exists(self_path)

        def patched_read_text(self_path, *args, **kwargs):
            if str(self_path).endswith("GenAI" + "\\" + ".env") or str(self_path).endswith("GenAI/.env"):
                return content
            return original_read_text(self_path, *args, **kwargs)

        return patch.object(Path, "exists", patched_exists), patch.object(Path, "read_text", patched_read_text)

    def test_with_service_specific_key(self):
        """Service-specific key takes priority over VLLM_API_KEY.

        NOTE: service_name normalization does replace("-","_").upper() + "_API_KEY",
        so "whisper-api" -> "WHISPER_API_API_KEY" (double _API). The env key must
        match this pattern. This is a known naming quirk in the source code.
        """
        env_content = "WHISPER_API_API_KEY=sk-test-whisper\nVLLM_API_KEY=sk-test-vllm\n"
        exists_patch, read_patch = self._mock_env_file(env_content)
        with exists_patch, read_patch:
            result = _get_auth_headers("whisper-api")
            assert "Authorization" in result
            assert "sk-test-whisper" in result["Authorization"]

    def test_with_generic_key(self):
        """Falls back to VLLM_API_KEY if no service-specific key."""
        env_content = "VLLM_API_KEY=sk-test-vllm\n"
        exists_patch, read_patch = self._mock_env_file(env_content)
        with exists_patch, read_patch:
            result = _get_auth_headers("whisper-api")
            assert "Authorization" in result
            assert "sk-test-vllm" in result["Authorization"]

    def test_none_service_returns_headers(self):
        """Calling with service_name=None still returns valid headers."""
        result = _get_auth_headers(None)
        assert "Content-Type" in result

    def test_bearer_prefix(self):
        """Authorization header uses Bearer prefix."""
        env_content = "VLLM_API_KEY=sk-test-123\n"
        exists_patch, read_patch = self._mock_env_file(env_content)
        with exists_patch, read_patch:
            result = _get_auth_headers("tts-api")
            assert "Authorization" in result
            assert result["Authorization"].startswith("Bearer ")

    def test_service_name_normalized(self):
        """Service name is normalized (hyphens to underscores, uppercase).

        NOTE: "musicgen-api" -> "MUSICGEN_API_API_KEY" (double _API suffix).
        """
        env_content = "MUSICGEN_API_API_KEY=sk-music\n"
        exists_patch, read_patch = self._mock_env_file(env_content)
        with exists_patch, read_patch:
            result = _get_auth_headers("musicgen-api")
            assert "Authorization" in result
            assert "sk-music" in result["Authorization"]

    def test_comments_ignored(self):
        """Comment lines in .env are ignored."""
        env_content = "# This is a comment\nVLLM_API_KEY=sk-test\n"
        exists_patch, read_patch = self._mock_env_file(env_content)
        with exists_patch, read_patch:
            result = _get_auth_headers("tts-api")
            assert "Authorization" in result
            assert "sk-test" in result["Authorization"]

    def test_no_equals_ignored(self):
        """Lines without = are ignored."""
        env_content = "JUST_A_WORD\nVLLM_API_KEY=sk-test\n"
        exists_patch, read_patch = self._mock_env_file(env_content)
        with exists_patch, read_patch:
            result = _get_auth_headers()
            assert "Authorization" in result


# ---------------------------------------------------------------------------
# Cross-constant invariants
# ---------------------------------------------------------------------------


class TestCrossInvariants:
    """Tests for invariants across multiple constants."""

    def test_gpu_allocation_subset_of_services(self):
        """GPU_ALLOCATION keys are a subset of AUDIO_API_SERVICES."""
        for svc in GPU_ALLOCATION:
            assert svc in AUDIO_API_SERVICES

    def test_conflict_lists_contain_allocated(self):
        """GPU_CONFLICTS lists contain all GPU_ALLOCATION entries for that GPU."""
        for svc, gpu_id in GPU_ALLOCATION.items():
            assert svc in GPU_CONFLICTS[gpu_id]

    def test_two_gpu_groups(self):
        """Services split into exactly 2 GPU groups (0 and 1)."""
        gpus = set(GPU_ALLOCATION.values())
        assert gpus == {0, 1}

    def test_gpu_0_has_whisper_demucs(self):
        """GPU 0 has whisper-api and demucs-api."""
        gpu_0_services = GPU_ALLOCATION.get("whisper-api"), GPU_ALLOCATION.get("demucs-api")
        assert gpu_0_services == (0, 0)

    def test_gpu_1_has_tts_musicgen(self):
        """GPU 1 has tts-api and musicgen-api."""
        gpu_1_services = GPU_ALLOCATION.get("tts-api"), GPU_ALLOCATION.get("musicgen-api")
        assert gpu_1_services == (1, 1)
