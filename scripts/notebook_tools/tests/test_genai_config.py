"""Tests for genai-stack config.py — load_env() + config dict integrity."""

import importlib.util
from pathlib import Path

import pytest

# Load module by file path
_MOD_PATH = Path(__file__).resolve().parent.parent.parent / "genai-stack" / "config.py"
_spec = importlib.util.spec_from_file_location("genai_config", _MOD_PATH)
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)

load_env = _mod.load_env
SERVICES = _mod.SERVICES
NOTEBOOK_SERVICE_MAP = _mod.NOTEBOOK_SERVICE_MAP
NOTEBOOK_SERIES = _mod.NOTEBOOK_SERIES
GPU_PROFILES = _mod.GPU_PROFILES
GROUP_GPU_PROFILE = _mod.GROUP_GPU_PROFILE
EXECUTION_BATCHES = _mod.EXECUTION_BATCHES
MODEL_CONFIGS = _mod.MODEL_CONFIGS
ENV_FILE = _mod.ENV_FILE


# --- load_env ---


def _call_load_env(env_path):
    """Helper: patch _mod.ENV_FILE, call load_env, restore."""
    original = _mod.ENV_FILE
    _mod.ENV_FILE = env_path
    try:
        return _mod.load_env()
    finally:
        _mod.ENV_FILE = original


class TestLoadEnv:
    def test_parses_key_value(self, tmp_path):
        env = tmp_path / ".env"
        env.write_text("MY_KEY=my_value\n", encoding="utf-8")
        result = _call_load_env(env)
        assert result["MY_KEY"] == "my_value"

    def test_strips_quotes(self, tmp_path):
        env = tmp_path / ".env"
        env.write_text('KEY1="val1"\nKEY2=\'val2\'\n', encoding="utf-8")
        result = _call_load_env(env)
        assert result["KEY1"] == "val1"
        assert result["KEY2"] == "val2"

    def test_skips_comments(self, tmp_path):
        env = tmp_path / ".env"
        env.write_text("# This is a comment\nKEY=val\n", encoding="utf-8")
        result = _call_load_env(env)
        assert "KEY" in result
        assert len(result) == 1

    def test_skips_blank_lines(self, tmp_path):
        env = tmp_path / ".env"
        env.write_text("\nKEY=val\n\n", encoding="utf-8")
        result = _call_load_env(env)
        assert len(result) == 1

    def test_skips_lines_without_equals(self, tmp_path):
        env = tmp_path / ".env"
        env.write_text("NOEQUALSSIGN\nKEY=val\n", encoding="utf-8")
        result = _call_load_env(env)
        assert len(result) == 1
        assert "NOEQUALSSIGN" not in result

    def test_missing_file_returns_empty(self, tmp_path):
        env = tmp_path / "nonexistent.env"
        result = _call_load_env(env)
        assert result == {}

    def test_value_with_equals_sign(self, tmp_path):
        """Value containing = should be preserved (split on first = only)."""
        env = tmp_path / ".env"
        env.write_text("URL=http://host:8080/api?key=abc\n", encoding="utf-8")
        result = _call_load_env(env)
        assert result["URL"] == "http://host:8080/api?key=abc"

    def test_strips_whitespace(self, tmp_path):
        env = tmp_path / ".env"
        env.write_text("  KEY  =  val  \n", encoding="utf-8")
        result = _call_load_env(env)
        assert result["KEY"] == "val"


# --- SERVICES integrity ---


class TestServicesConfig:
    def test_all_services_have_required_keys(self):
        required = {"compose_dir", "container_name", "port", "health_endpoint", "gpu_id"}
        for name, svc in SERVICES.items():
            missing = required - set(svc.keys())
            assert missing == set(), f"Service '{name}' missing keys: {missing}"

    def test_ports_are_positive(self):
        for name, svc in SERVICES.items():
            assert svc["port"] > 0, f"Service '{name}' has invalid port: {svc['port']}"

    def test_gpu_ids_are_0_or_1(self):
        for name, svc in SERVICES.items():
            assert svc["gpu_id"] in (0, 1), f"Service '{name}' has invalid gpu_id: {svc['gpu_id']}"

    def test_comfyui_qwen_port(self):
        assert SERVICES["comfyui-qwen"]["port"] == 8188

    def test_forge_turbo_port(self):
        assert SERVICES["forge-turbo"]["port"] == 17861


# --- NOTEBOOK_SERVICE_MAP integrity ---


class TestNotebookServiceMap:
    def test_all_groups_have_notebooks(self):
        for group, notebooks in NOTEBOOK_SERVICE_MAP.items():
            assert len(notebooks) > 0, f"Group '{group}' has no notebooks"

    def test_notebooks_are_strings(self):
        for group, notebooks in NOTEBOOK_SERVICE_MAP.items():
            for nb in notebooks:
                assert isinstance(nb, str), f"Group '{group}' has non-string notebook: {nb}"
                assert nb.endswith(".ipynb"), f"Non-ipynb in group '{group}': {nb}"


# --- NOTEBOOK_SERIES integrity ---


class TestNotebookSeries:
    def test_series_keys_are_image_audio_video(self):
        assert set(NOTEBOOK_SERIES.keys()) == {"image", "audio", "video"}

    def test_all_series_groups_exist_in_service_map(self):
        for series, groups in NOTEBOOK_SERIES.items():
            for group in groups:
                assert group in NOTEBOOK_SERVICE_MAP, (
                    f"Series '{series}' references unknown group '{group}'"
                )


# --- GPU_PROFILES integrity ---


class TestGpuProfiles:
    def test_all_profiles_have_required_keys(self):
        required = {"description", "services_up", "services_down", "gpu_0_usage", "gpu_1_usage"}
        for name, profile in GPU_PROFILES.items():
            missing = required - set(profile.keys())
            assert missing == set(), f"Profile '{name}' missing keys: {missing}"

    def test_services_up_are_known_services(self):
        for name, profile in GPU_PROFILES.items():
            for svc in profile["services_up"]:
                assert svc in SERVICES, f"Profile '{name}' references unknown service '{svc}'"

    def test_services_down_are_known_services(self):
        for name, profile in GPU_PROFILES.items():
            for svc in profile["services_down"]:
                assert svc in SERVICES, f"Profile '{name}' references unknown service '{svc}'"


# --- GROUP_GPU_PROFILE integrity ---


class TestGroupGpuProfile:
    def test_all_groups_have_profiles(self):
        for group, profile_name in GROUP_GPU_PROFILE.items():
            assert profile_name in GPU_PROFILES, (
                f"Group '{group}' references unknown profile '{profile_name}'"
            )

    def test_all_service_map_groups_have_gpu_profile(self):
        """Every group in NOTEBOOK_SERVICE_MAP should have a GPU profile."""
        for group in NOTEBOOK_SERVICE_MAP:
            assert group in GROUP_GPU_PROFILE, f"Group '{group}' missing from GROUP_GPU_PROFILE"


# --- EXECUTION_BATCHES integrity ---


class TestExecutionBatches:
    def test_all_batches_have_required_keys(self):
        required = {"name", "profile", "groups"}
        for batch_id, batch in EXECUTION_BATCHES.items():
            missing = required - set(batch.keys())
            assert missing == set(), f"Batch {batch_id} missing keys: {missing}"

    def test_batch_profiles_are_known(self):
        for batch_id, batch in EXECUTION_BATCHES.items():
            assert batch["profile"] in GPU_PROFILES, (
                f"Batch {batch_id} references unknown profile '{batch['profile']}'"
            )

    def test_batch_groups_are_known(self):
        for batch_id, batch in EXECUTION_BATCHES.items():
            for group in batch["groups"]:
                assert group in NOTEBOOK_SERVICE_MAP, (
                    f"Batch {batch_id} references unknown group '{group}'"
                )


# --- MODEL_CONFIGS integrity ---


class TestModelConfigs:
    def test_model_configs_not_empty(self):
        assert len(MODEL_CONFIGS) > 0

    def test_all_models_have_vram_required(self):
        for name, cfg in MODEL_CONFIGS.items():
            assert "vram_required_mb" in cfg, f"Model '{name}' missing vram_required_mb"

    def test_vram_positive(self):
        for name, cfg in MODEL_CONFIGS.items():
            assert cfg["vram_required_mb"] > 0, f"Model '{name}' has invalid VRAM"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
