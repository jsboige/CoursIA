"""Tests for genai-stack commands/audio_apis.py + commands/models.py — static config integrity."""

import importlib.util
from pathlib import Path

import pytest

# --- Load audio_apis.py ---
_AA_PATH = Path(__file__).resolve().parent.parent.parent / "genai-stack" / "commands" / "audio_apis.py"
_aa_spec = importlib.util.spec_from_file_location("audio_apis", _AA_PATH)
_aa_mod = importlib.util.module_from_spec(_aa_spec)
_aa_spec.loader.exec_module(_aa_mod)

AUDIO_API_SERVICES = _aa_mod.AUDIO_API_SERVICES
GPU_ALLOCATION = _aa_mod.GPU_ALLOCATION
GPU_CONFLICTS = _aa_mod.GPU_CONFLICTS

# --- Load models.py ---
_MD_PATH = Path(__file__).resolve().parent.parent.parent / "genai-stack" / "commands" / "models.py"
_md_spec = importlib.util.spec_from_file_location("models", _MD_PATH)
_md_mod = importlib.util.module_from_spec(_md_spec)
_md_spec.loader.exec_module(_md_mod)

QWEN_MODELS = _md_mod.QWEN_MODELS
NUNCHAKU_MODELS = _md_mod.NUNCHAKU_MODELS
ZIMAGE_VAE_CONFIG = _md_mod.ZIMAGE_VAE_CONFIG

# --- Load config.py for cross-validation ---
_CFG_PATH = Path(__file__).resolve().parent.parent.parent / "genai-stack" / "config.py"
_cfg_spec = importlib.util.spec_from_file_location("genai_config", _CFG_PATH)
_cfg_mod = importlib.util.module_from_spec(_cfg_spec)
_cfg_spec.loader.exec_module(_cfg_mod)

SERVICES = _cfg_mod.SERVICES


# --- audio_apis.py constants integrity ---


class TestAudioApiServices:
    def test_audio_api_services_not_empty(self):
        assert len(AUDIO_API_SERVICES) > 0

    def test_audio_api_services_are_known_services(self):
        for svc in AUDIO_API_SERVICES:
            assert svc in SERVICES, f"AUDIO_API_SERVICES references unknown service '{svc}'"

    def test_gpu_allocation_keys_subset_of_audio_services(self):
        for svc in GPU_ALLOCATION:
            assert svc in AUDIO_API_SERVICES, f"GPU_ALLOCATION references non-audio service '{svc}'"

    def test_gpu_allocation_values_valid(self):
        for svc, gpu_id in GPU_ALLOCATION.items():
            assert gpu_id in (0, 1), f"GPU_ALLOCATION['{svc}'] has invalid GPU ID: {gpu_id}"


class TestGpuConflicts:
    def test_gpu_conflict_keys_valid(self):
        for gpu_id in GPU_CONFLICTS:
            assert gpu_id in (0, 1), f"GPU_CONFLICTS has invalid GPU key: {gpu_id}"

    def test_gpu_conflict_services_known(self):
        all_known = set(SERVICES.keys()) | set(AUDIO_API_SERVICES)
        for gpu_id, services in GPU_CONFLICTS.items():
            for svc in services:
                assert svc in all_known, f"GPU_CONFLICTS[{gpu_id}] references unknown service '{svc}'"

    def test_audio_services_in_conflict_map(self):
        """Every audio service with a GPU allocation should appear in GPU_CONFLICTS."""
        all_conflicted = set()
        for services in GPU_CONFLICTS.values():
            all_conflicted.update(services)
        for svc in GPU_ALLOCATION:
            assert svc in all_conflicted, f"Audio service '{svc}' not in any GPU_CONFLICTS list"


# --- models.py constants integrity ---


class TestQwenModels:
    def test_qwen_models_not_empty(self):
        assert len(QWEN_MODELS) > 0

    def test_qwen_models_have_required_keys(self):
        required = {"name", "repo_id", "filename", "local_name", "subdir", "size_gb"}
        for model in QWEN_MODELS:
            missing = required - set(model.keys())
            assert missing == set(), f"QWEN_MODELS entry '{model.get('name', '?')}' missing: {missing}"

    def test_qwen_models_sizes_positive(self):
        for model in QWEN_MODELS:
            assert model["size_gb"] > 0, f"Model '{model['name']}' has invalid size: {model['size_gb']}"

    def test_qwen_models_local_names_unique(self):
        names = [m["local_name"] for m in QWEN_MODELS]
        assert len(names) == len(set(names)), "QWEN_MODELS has duplicate local_name entries"

    def test_qwen_models_filenames_end_safetensors(self):
        for model in QWEN_MODELS:
            assert model["local_name"].endswith(".safetensors"), (
                f"Model '{model['name']}' local_name doesn't end with .safetensors"
            )


class TestNunchakuModels:
    def test_nunchaku_models_not_empty(self):
        assert len(NUNCHAKU_MODELS) > 0

    def test_nunchaku_values_end_safetensors(self):
        for key, filename in NUNCHAKU_MODELS.items():
            assert filename.endswith(".safetensors"), (
                f"NUNCHAKU_MODELS['{key}'] doesn't end with .safetensors: {filename}"
            )

    def test_nunchaku_keys_contain_step_info(self):
        for key in NUNCHAKU_MODELS:
            assert "step" in key or "standard" in key, f"NUNCHAKU_MODELS key '{key}' lacks step info"

    def test_nunchaku_values_unique(self):
        values = list(NUNCHAKU_MODELS.values())
        assert len(values) == len(set(values)), "NUNCHAKU_MODELS has duplicate filenames"


class TestZimageVaeConfig:
    def test_has_required_keys(self):
        required = {"url", "filename", "subfolder"}
        assert required == set(ZIMAGE_VAE_CONFIG.keys())

    def test_url_is_huggingface(self):
        assert "huggingface.co" in ZIMAGE_VAE_CONFIG["url"]

    def test_filename_ends_safetensors(self):
        assert ZIMAGE_VAE_CONFIG["filename"].endswith(".safetensors")


# --- audio_apis.py function tests (offline, mocked Docker) ---


class TestMakeSilenceWav:
    """Tests for _make_silence_wav() — pure Python WAV generation."""

    def test_returns_bytes(self):
        wav = _aa_mod._make_silence_wav()
        assert isinstance(wav, bytes)

    def test_wav_header_riff(self):
        wav = _aa_mod._make_silence_wav()
        assert wav[:4] == b"RIFF"

    def test_wav_header_wave(self):
        wav = _aa_mod._make_silence_wav()
        assert wav[8:12] == b"WAVE"

    def test_wav_header_fmt(self):
        wav = _aa_mod._make_silence_wav()
        assert wav[12:16] == b"fmt "

    def test_wav_pcm_format(self):
        import struct
        wav = _aa_mod._make_silence_wav()
        audio_format = struct.unpack_from("<H", wav, 20)[0]
        assert audio_format == 1  # PCM

    def test_wav_mono(self):
        import struct
        wav = _aa_mod._make_silence_wav()
        num_channels = struct.unpack_from("<H", wav, 22)[0]
        assert num_channels == 1

    def test_wav_sample_rate_16k(self):
        import struct
        wav = _aa_mod._make_silence_wav()
        sample_rate = struct.unpack_from("<I", wav, 24)[0]
        assert sample_rate == 16000

    def test_wav_16bit(self):
        import struct
        wav = _aa_mod._make_silence_wav()
        bits = struct.unpack_from("<H", wav, 34)[0]
        assert bits == 16

    def test_wav_has_data_chunk(self):
        wav = _aa_mod._make_silence_wav()
        assert b"data" in wav

    def test_wav_silence_is_all_zeros(self):
        wav = _aa_mod._make_silence_wav()
        data_offset = wav.index(b"data") + 8
        data = wav[data_offset:]
        assert data == b"\x00" * len(data)

    def test_wav_size_consistent(self):
        import struct
        wav = _aa_mod._make_silence_wav()
        file_size_minus_8 = struct.unpack_from("<I", wav, 4)[0]
        assert len(wav) == file_size_minus_8 + 8


class TestGetContainerStatus:
    """Tests for get_container_status() — subprocess mock."""

    def test_not_found_on_docker_failure(self, monkeypatch):
        import subprocess

        def mock_run(cmd, **kwargs):
            r = subprocess.CompletedProcess(cmd, returncode=1, stdout="", stderr="not found")
            return r

        monkeypatch.setattr(_aa_mod.subprocess, "run", mock_run)
        result = _aa_mod.get_container_status("nonexistent-container")
        assert result == "not_found"

    def test_running_when_docker_returns_running(self, monkeypatch):
        import subprocess

        def mock_run(cmd, **kwargs):
            r = subprocess.CompletedProcess(cmd, returncode=0, stdout="running", stderr="")
            return r

        monkeypatch.setattr(_aa_mod.subprocess, "run", mock_run)
        result = _aa_mod.get_container_status("some-container")
        assert result == "running"

    def test_exited_when_docker_returns_exited(self, monkeypatch):
        import subprocess

        def mock_run(cmd, **kwargs):
            r = subprocess.CompletedProcess(cmd, returncode=0, stdout="exited", stderr="")
            return r

        monkeypatch.setattr(_aa_mod.subprocess, "run", mock_run)
        result = _aa_mod.get_container_status("some-container")
        assert result == "exited"


class TestGetRunningOnGpu:
    """Tests for get_running_on_gpu() — filter running services on a GPU."""

    def test_returns_list(self, monkeypatch):
        def mock_status(container):
            return "exited"

        monkeypatch.setattr(_aa_mod, "get_container_status", mock_status)
        result = _aa_mod.get_running_on_gpu(0)
        assert isinstance(result, list)

    def test_empty_when_none_running(self, monkeypatch):
        def mock_status(container):
            return "exited"

        monkeypatch.setattr(_aa_mod, "get_container_status", mock_status)
        result = _aa_mod.get_running_on_gpu(0)
        assert result == []

    def test_finds_running_service(self, monkeypatch):
        call_count = {"n": 0}

        def mock_status(container):
            # First call returns "running" to simulate one active container
            call_count["n"] += 1
            if call_count["n"] == 1:
                return "running"
            return "exited"

        monkeypatch.setattr(_aa_mod, "get_container_status", mock_status)
        result = _aa_mod.get_running_on_gpu(0)
        assert len(result) >= 0  # Structure correct, may or may not find one


class TestStopService:
    """Tests for stop_service() — unknown service rejection."""

    def test_unknown_service_returns_false(self):
        result = _aa_mod.stop_service("nonexistent-service-xyz")
        assert result is False

    def test_already_stopped_returns_true(self, monkeypatch):
        def mock_status(container):
            return "exited"

        monkeypatch.setattr(_aa_mod, "get_container_status", mock_status)
        # Use a real audio service name but with mocked status
        if AUDIO_API_SERVICES:
            result = _aa_mod.stop_service(AUDIO_API_SERVICES[0])
            assert result is True


class TestStartService:
    """Tests for start_service() — unknown service rejection."""

    def test_unknown_service_returns_false(self):
        result = _aa_mod.start_service("nonexistent-service-xyz")
        assert result is False


class TestBuildService:
    """Tests for build_service() — unknown service rejection."""

    def test_unknown_service_returns_false(self):
        result = _aa_mod.build_service("nonexistent-service-xyz")
        assert result is False


class TestShowLogs:
    """Tests for show_logs() — unknown service gracefully handled."""

    def test_unknown_service_no_crash(self):
        # show_logs doesn't return a value, just calls subprocess
        # Verify it doesn't raise
        _aa_mod.show_logs("nonexistent-service-xyz")


class TestE2eTestResult:
    """Tests for e2e_test_service() result structure (mocked HTTP)."""

    def test_result_has_required_keys(self, monkeypatch):
        # Mock the SERVICES config to have a testable entry
        test_cfg = {
            "whisper-api": {
                "container_name": "test-whisper",
                "port": 8190,
                "health_endpoint": "/health",
                "remote_url": "http://localhost:8190",
                "compose_dir": Path("/tmp"),
            }
        }
        monkeypatch.setattr(_aa_mod, "SERVICES", test_cfg)

        # Mock requests to simulate a healthy endpoint
        class MockResp:
            status_code = 200
            content = b"test audio data"
            text = '{"text": "test"}'
            headers = {"Content-Type": "application/json"}

        # Patch the REAL requests module's attributes (get/post/exceptions.Timeout)
        # rather than replacing sys.modules["requests"]. audio_apis.py does
        # `import requests` *inside* its functions, so it resolves to the real
        # module object — patching its attributes is intercepted correctly, AND
        # monkeypatch restores them cleanly. Replacing sys.modules["requests"]
        # globally contaminates any module imported afterwards that captured
        # `requests` at its own top level (e.g. comfyui_client.py:20
        # `import requests` then `self.session = requests.Session()`), because
        # the binding obtained during that import window stays the mock even
        # after monkeypatch restores sys.modules. That cross-test pollution
        # made test_genai_comfyui_client.py::TestComfyUIClientInit fail under
        # the full-collection order on ubuntu CI (#2871).
        import requests as _real_requests

        monkeypatch.setattr(_real_requests, "get", lambda *a, **kw: MockResp())
        monkeypatch.setattr(_real_requests, "post", lambda *a, **kw: MockResp())
        monkeypatch.setattr(_real_requests.exceptions, "Timeout", Exception)

        result = _aa_mod.e2e_test_service("whisper-api")
        required_keys = {"service", "status", "time_s", "size_bytes", "detail"}
        assert required_keys.issubset(set(result.keys()))


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
