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


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
